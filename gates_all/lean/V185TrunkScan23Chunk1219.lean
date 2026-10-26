import V185TrunkScan23Chunk1218

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7223452 : List Nat := [2, 2, 3, 2, 1, 1, 1, 5, 1, 2, 3]
def baseStart_7223452 : Nat := 118140960795 + 7223452 * 2 ^ 59
def prefixEnd_7223452 : Nat := 4983230072969 + 3 ^ 40 * 7223452 * 2
def baseEnd_7223452 : Nat := 3709102860681177444529955

theorem tailTrace_7223452 : CollatzResearch.WordTrace tailWord_7223452 prefixEnd_7223452 3709102860681177444529955 := by
  unfold tailWord_7223452
  simp only [CollatzResearch.WordTrace]
  refine ⟨131730469313337273114716305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175640625751116364152955073 131730469313337273114716305)
  ·
    refine ⟨98797851985002954836037229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131730469313337273114716305 98797851985002954836037229)
    ·
      refine ⟨37049194494376108063513961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98797851985002954836037229 37049194494376108063513961)
      ·
        refine ⟨27786895870782081047635471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37049194494376108063513961 27786895870782081047635471)
        ·
          refine ⟨41680343806173121571453207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27786895870782081047635471 41680343806173121571453207)
          ·
            refine ⟨62520515709259682357179811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41680343806173121571453207 62520515709259682357179811)
            ·
              refine ⟨93780773563889523535769717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62520515709259682357179811 93780773563889523535769717)
              ·
                refine ⟨8791947521614642831478411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93780773563889523535769717 8791947521614642831478411)
                ·
                  refine ⟨13187921282421964247217617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8791947521614642831478411 13187921282421964247217617)
                  ·
                    refine ⟨9890940961816473185413213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13187921282421964247217617 9890940961816473185413213)
                    ·
                      refine ⟨3709102860681177444529955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9890940961816473185413213 3709102860681177444529955)
                      ·
                        rfl

theorem cell23_7223452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_7223452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223452 prefixEnd_7223452 := by exact prefixLift 7223452
  have htrace : WordTrace (prefixWord ++ tailWord_7223452) baseStart_7223452 baseEnd_7223452 := by
    simpa [prefixWord, tailWord_7223452, baseEnd_7223452] using wordTrace_append hprefix tailTrace_7223452
  have hstable : (prefixWord ++ tailWord_7223452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223452).length < 2 ^ (prefixWord ++ tailWord_7223452).sum := by decide
  have hdescent : baseEnd_7223452 < baseStart_7223452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223455 : List Nat := [1, 1, 2, 6, 1, 3, 9]
def baseStart_7223455 : Nat := 118140960795 + 7223455 * 2 ^ 59
def prefixEnd_7223455 : Nat := 4983230072969 + 3 ^ 40 * 7223455 * 2
def baseEnd_7223455 : Nat := 45791412359544949787561

theorem tailTrace_7223455 : CollatzResearch.WordTrace tailWord_7223455 prefixEnd_7223455 45791412359544949787561 := by
  unfold tailWord_7223455
  simp only [CollatzResearch.WordTrace]
  refine ⟨263461048045663677741791819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175640698697109118494527879 263461048045663677741791819)
  ·
    refine ⟨395191572068495516612687729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263461048045663677741791819 395191572068495516612687729)
    ·
      refine ⟨296393679051371637459515797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395191572068495516612687729 296393679051371637459515797)
      ·
        refine ⟨13893453705533045505914803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 296393679051371637459515797 13893453705533045505914803)
        ·
          refine ⟨20840180558299568258872205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13893453705533045505914803 20840180558299568258872205)
          ·
            refine ⟨7815067709362338097077077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20840180558299568258872205 7815067709362338097077077)
            ·
              refine ⟨45791412359544949787561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7815067709362338097077077 45791412359544949787561)
              ·
                rfl

theorem cell23_7223455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 9].length) (baseStart_7223455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223455 prefixEnd_7223455 := by exact prefixLift 7223455
  have htrace : WordTrace (prefixWord ++ tailWord_7223455) baseStart_7223455 baseEnd_7223455 := by
    simpa [prefixWord, tailWord_7223455, baseEnd_7223455] using wordTrace_append hprefix tailTrace_7223455
  have hstable : (prefixWord ++ tailWord_7223455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223455).length < 2 ^ (prefixWord ++ tailWord_7223455).sum := by decide
  have hdescent : baseEnd_7223455 < baseStart_7223455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223475 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 2, 7, 2]
def baseStart_7223475 : Nat := 118140960795 + 7223475 * 2 ^ 59
def prefixEnd_7223475 : Nat := 4983230072969 + 3 ^ 40 * 7223475 * 2
def baseEnd_7223475 : Nat := 3709114670736230854542349

theorem tailTrace_7223475 : CollatzResearch.WordTrace tailWord_7223475 prefixEnd_7223475 3709114670736230854542349 := by
  unfold tailWord_7223475
  simp only [CollatzResearch.WordTrace]
  refine ⟨263461777505591221157519879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175641185003727480771679919 263461777505591221157519879)
  ·
    refine ⟨395192666258386831736279819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263461777505591221157519879 395192666258386831736279819)
    ·
      refine ⟨592788999387580247604419729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395192666258386831736279819 592788999387580247604419729)
      ·
        refine ⟨444591749540685185703314797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 592788999387580247604419729 444591749540685185703314797)
        ·
          refine ⟨166721906077756944638743049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 444591749540685185703314797 166721906077756944638743049)
          ·
            refine ⟨125041429558317708479057287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166721906077756944638743049 125041429558317708479057287)
            ·
              refine ⟨187562144337476562718585931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125041429558317708479057287 187562144337476562718585931)
              ·
                refine ⟨281343216506214844077878897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187562144337476562718585931 281343216506214844077878897)
                ·
                  refine ⟨211007412379661133058409173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281343216506214844077878897 211007412379661133058409173)
                  ·
                    refine ⟨4945486227648307806056465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 211007412379661133058409173 4945486227648307806056465)
                    ·
                      refine ⟨3709114670736230854542349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4945486227648307806056465 3709114670736230854542349)
                      ·
                        rfl

theorem cell23_7223475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 7, 2].length) (baseStart_7223475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223475 prefixEnd_7223475 := by exact prefixLift 7223475
  have htrace : WordTrace (prefixWord ++ tailWord_7223475) baseStart_7223475 baseEnd_7223475 := by
    simpa [prefixWord, tailWord_7223475, baseEnd_7223475] using wordTrace_append hprefix tailTrace_7223475
  have hstable : (prefixWord ++ tailWord_7223475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223475).length < 2 ^ (prefixWord ++ tailWord_7223475).sum := by decide
  have hdescent : baseEnd_7223475 < baseStart_7223475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223486 : List Nat := [4, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3]
def baseStart_7223486 : Nat := 118140960795 + 7223486 * 2 ^ 59
def prefixEnd_7223486 : Nat := 4983230072969 + 3 ^ 40 * 7223486 * 2
def baseEnd_7223486 : Nat := 3709120319023430311504799

theorem tailTrace_7223486 : CollatzResearch.WordTrace tailWord_7223486 prefixEnd_7223486 3709120319023430311504799 := by
  unfold tailWord_7223486
  simp only [CollatzResearch.WordTrace]
  refine ⟨32932772338568921254521289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175641452472367580024113541 32932772338568921254521289)
  ·
    refine ⟨24699579253926690940890967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32932772338568921254521289 24699579253926690940890967)
    ·
      refine ⟨37049368880890036411336451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24699579253926690940890967 37049368880890036411336451)
      ·
        refine ⟨55574053321335054617004677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37049368880890036411336451 55574053321335054617004677)
        ·
          refine ⟨10420134997750322740688377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55574053321335054617004677 10420134997750322740688377)
          ·
            refine ⟨7815101248312742055516283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10420134997750322740688377 7815101248312742055516283)
            ·
              refine ⟨11722651872469113083274425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7815101248312742055516283 11722651872469113083274425)
              ·
                refine ⟨8791988904351834812455819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11722651872469113083274425 8791988904351834812455819)
                ·
                  refine ⟨13187983356527752218683729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8791988904351834812455819 13187983356527752218683729)
                  ·
                    refine ⟨9890987517395814164012797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13187983356527752218683729 9890987517395814164012797)
                    ·
                      refine ⟨3709120319023430311504799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9890987517395814164012797 3709120319023430311504799)
                      ·
                        rfl

theorem cell23_7223486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_7223486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223486 prefixEnd_7223486 := by exact prefixLift 7223486
  have htrace : WordTrace (prefixWord ++ tailWord_7223486) baseStart_7223486 baseEnd_7223486 := by
    simpa [prefixWord, tailWord_7223486, baseEnd_7223486] using wordTrace_append hprefix tailTrace_7223486
  have hstable : (prefixWord ++ tailWord_7223486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223486).length < 2 ^ (prefixWord ++ tailWord_7223486).sum := by decide
  have hdescent : baseEnd_7223486 < baseStart_7223486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223535 : List Nat := [1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 4]
def baseStart_7223535 : Nat := 118140960795 + 7223535 * 2 ^ 59
def prefixEnd_7223535 : Nat := 4983230072969 + 3 ^ 40 * 7223535 * 2
def baseEnd_7223535 : Nat := 3709145479575500619792073

theorem tailTrace_7223535 : CollatzResearch.WordTrace tailWord_7223535 prefixEnd_7223535 3709145479575500619792073 := by
  unfold tailWord_7223535
  simp only [CollatzResearch.WordTrace]
  refine ⟨263463965885373851404704059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175642643923582567603136039 263463965885373851404704059)
  ·
    refine ⟨395195948828060777107056089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263463965885373851404704059 395195948828060777107056089)
    ·
      refine ⟨296396961621045582830292067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395195948828060777107056089 296396961621045582830292067)
      ·
        refine ⟨444595442431568374245438101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296396961621045582830292067 444595442431568374245438101)
        ·
          refine ⟨20840411363979767542754911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 444595442431568374245438101 20840411363979767542754911)
          ·
            refine ⟨31260617045969651314132367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20840411363979767542754911 31260617045969651314132367)
            ·
              refine ⟨46890925568954476971198551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31260617045969651314132367 46890925568954476971198551)
              ·
                refine ⟨70336388353431715456797827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46890925568954476971198551 70336388353431715456797827)
                ·
                  refine ⟨105504582530147573185196741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70336388353431715456797827 105504582530147573185196741)
                  ·
                    refine ⟨19782109224402669972224389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105504582530147573185196741 19782109224402669972224389)
                    ·
                      refine ⟨3709145479575500619792073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19782109224402669972224389 3709145479575500619792073)
                      ·
                        rfl

theorem cell23_7223535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 4].length) (baseStart_7223535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223535 prefixEnd_7223535 := by exact prefixLift 7223535
  have htrace : WordTrace (prefixWord ++ tailWord_7223535) baseStart_7223535 baseEnd_7223535 := by
    simpa [prefixWord, tailWord_7223535, baseEnd_7223535] using wordTrace_append hprefix tailTrace_7223535
  have hstable : (prefixWord ++ tailWord_7223535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223535).length < 2 ^ (prefixWord ++ tailWord_7223535).sum := by decide
  have hdescent : baseEnd_7223535 < baseStart_7223535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223539 : List Nat := [1, 1, 1, 2, 2, 4, 1, 5, 2, 2, 2]
def baseStart_7223539 : Nat := 118140960795 + 7223539 * 2 ^ 59
def prefixEnd_7223539 : Nat := 4983230072969 + 3 ^ 40 * 7223539 * 2
def baseEnd_7223539 : Nat := 3709147533498118604142055

theorem tailTrace_7223539 : CollatzResearch.WordTrace tailWord_7223539 prefixEnd_7223539 3709147533498118604142055 := by
  unfold tailWord_7223539
  simp only [CollatzResearch.WordTrace]
  refine ⟨263464111777359360087849671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175642741184906240058566447 263464111777359360087849671)
  ·
    refine ⟨395196167666039040131774507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263464111777359360087849671 395196167666039040131774507)
    ·
      refine ⟨592794251499058560197661761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395196167666039040131774507 592794251499058560197661761)
      ·
        refine ⟨444595688624293920148246321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 592794251499058560197661761 444595688624293920148246321)
        ·
          refine ⟨333446766468220440111184741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444595688624293920148246321 333446766468220440111184741)
          ·
            refine ⟨62521268712791332520847139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 333446766468220440111184741 62521268712791332520847139)
            ·
              refine ⟨93781903069186998781270709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62521268712791332520847139 93781903069186998781270709)
              ·
                refine ⟨8792053412736281135744129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93781903069186998781270709 8792053412736281135744129)
                ·
                  refine ⟨6594040059552210851808097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8792053412736281135744129 6594040059552210851808097)
                  ·
                    refine ⟨4945530044664158138856073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6594040059552210851808097 4945530044664158138856073)
                    ·
                      refine ⟨3709147533498118604142055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4945530044664158138856073 3709147533498118604142055)
                      ·
                        rfl

theorem cell23_7223539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 2, 2, 2].length) (baseStart_7223539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223539 prefixEnd_7223539 := by exact prefixLift 7223539
  have htrace : WordTrace (prefixWord ++ tailWord_7223539) baseStart_7223539 baseEnd_7223539 := by
    simpa [prefixWord, tailWord_7223539, baseEnd_7223539] using wordTrace_append hprefix tailTrace_7223539
  have hstable : (prefixWord ++ tailWord_7223539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223539).length < 2 ^ (prefixWord ++ tailWord_7223539).sum := by decide
  have hdescent : baseEnd_7223539 < baseStart_7223539 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223555 : List Nat := [1, 1, 1, 3, 2, 3, 1, 2, 1, 5, 3]
def baseStart_7223555 : Nat := 118140960795 + 7223555 * 2 ^ 59
def prefixEnd_7223555 : Nat := 4983230072969 + 3 ^ 40 * 7223555 * 2
def baseEnd_7223555 : Nat := 3709155749188590541541981

theorem tailTrace_7223555 : CollatzResearch.WordTrace tailWord_7223555 prefixEnd_7223555 3709155749188590541541981 := by
  unfold tailWord_7223555
  simp only [CollatzResearch.WordTrace]
  refine ⟨263464695345301394820432119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175643130230200929880288079 263464695345301394820432119)
  ·
    refine ⟨395197043017952092230648179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263464695345301394820432119 395197043017952092230648179)
    ·
      refine ⟨592795564526928138345972269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395197043017952092230648179 592795564526928138345972269)
      ·
        refine ⟨222298336697598051879739601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 592795564526928138345972269 222298336697598051879739601)
        ·
          refine ⟨166723752523198538909804701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222298336697598051879739601 166723752523198538909804701)
          ·
            refine ⟨62521407196199452091176763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166723752523198538909804701 62521407196199452091176763)
            ·
              refine ⟨93782110794299178136765145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62521407196199452091176763 93782110794299178136765145)
              ·
                refine ⟨70336583095724383602573859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93782110794299178136765145 70336583095724383602573859)
                ·
                  refine ⟨105504874643586575403860789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70336583095724383602573859 105504874643586575403860789)
                  ·
                    refine ⟨9891081997836241444111949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105504874643586575403860789 9891081997836241444111949)
                    ·
                      refine ⟨3709155749188590541541981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9891081997836241444111949 3709155749188590541541981)
                      ·
                        rfl

theorem cell23_7223555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 5, 3].length) (baseStart_7223555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223555 prefixEnd_7223555 := by exact prefixLift 7223555
  have htrace : WordTrace (prefixWord ++ tailWord_7223555) baseStart_7223555 baseEnd_7223555 := by
    simpa [prefixWord, tailWord_7223555, baseEnd_7223555] using wordTrace_append hprefix tailTrace_7223555
  have hstable : (prefixWord ++ tailWord_7223555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223555).length < 2 ^ (prefixWord ++ tailWord_7223555).sum := by decide
  have hdescent : baseEnd_7223555 < baseStart_7223555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223562 : List Nat := [3, 1, 2, 2, 1, 1, 3, 5, 5]
def baseStart_7223562 : Nat := 118140960795 + 7223562 * 2 ^ 59
def prefixEnd_7223562 : Nat := 4983230072969 + 3 ^ 40 * 7223562 * 2
def baseEnd_7223562 : Nat := 412128815950352446017161

theorem tailTrace_7223562 : CollatzResearch.WordTrace tailWord_7223562 prefixEnd_7223562 412128815950352446017161 := by
  unfold tailWord_7223562
  simp only [CollatzResearch.WordTrace]
  refine ⟨65866237664069008753984235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175643300437517356677291293 65866237664069008753984235)
  ·
    refine ⟨98799356496103513130976353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65866237664069008753984235 98799356496103513130976353)
    ·
      refine ⟨74099517372077634848232265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98799356496103513130976353 74099517372077634848232265)
      ·
        refine ⟨55574638029058226136174199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74099517372077634848232265 55574638029058226136174199)
        ·
          refine ⟨83361957043587339204261299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55574638029058226136174199 83361957043587339204261299)
          ·
            refine ⟨125042935565381008806391949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83361957043587339204261299 125042935565381008806391949)
            ·
              refine ⟨46891100837017878302396981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125042935565381008806391949 46891100837017878302396981)
              ·
                refine ⟨4396040703470426090849717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46891100837017878302396981 4396040703470426090849717)
                ·
                  refine ⟨412128815950352446017161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4396040703470426090849717 412128815950352446017161)
                  ·
                    rfl

theorem cell23_7223562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 5, 5].length) (baseStart_7223562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223562 prefixEnd_7223562 := by exact prefixLift 7223562
  have htrace : WordTrace (prefixWord ++ tailWord_7223562) baseStart_7223562 baseEnd_7223562 := by
    simpa [prefixWord, tailWord_7223562, baseEnd_7223562] using wordTrace_append hprefix tailTrace_7223562
  have hstable : (prefixWord ++ tailWord_7223562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223562).length < 2 ^ (prefixWord ++ tailWord_7223562).sum := by decide
  have hdescent : baseEnd_7223562 < baseStart_7223562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223585 : List Nat := [1, 2, 3, 2, 1, 1, 2, 3, 1, 2, 5]
def baseStart_7223585 : Nat := 118140960795 + 7223585 * 2 ^ 59
def prefixEnd_7223585 : Nat := 4983230072969 + 3 ^ 40 * 7223585 * 2
def baseEnd_7223585 : Nat := 3709171153608225424166843

theorem tailTrace_7223585 : CollatzResearch.WordTrace tailWord_7223585 prefixEnd_7223585 3709171153608225424166843 := by
  unfold tailWord_7223585
  simp only [CollatzResearch.WordTrace]
  refine ⟨263465789535192709944024209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175643859690128473296016139 263465789535192709944024209)
  ·
    refine ⟨197599342151394532458018157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263465789535192709944024209 197599342151394532458018157)
    ·
      refine ⟨74099753306772949671756809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197599342151394532458018157 74099753306772949671756809)
      ·
        refine ⟨55574814980079712253817607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74099753306772949671756809 55574814980079712253817607)
        ·
          refine ⟨83362222470119568380726411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55574814980079712253817607 83362222470119568380726411)
          ·
            refine ⟨125043333705179352571089617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83362222470119568380726411 125043333705179352571089617)
            ·
              refine ⟨93782500278884514428317213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125043333705179352571089617 93782500278884514428317213)
              ·
                refine ⟨35168437604581692910618955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93782500278884514428317213 35168437604581692910618955)
                ·
                  refine ⟨52752656406872539365928433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35168437604581692910618955 52752656406872539365928433)
                  ·
                    refine ⟨39564492305154404524446325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52752656406872539365928433 39564492305154404524446325)
                    ·
                      refine ⟨3709171153608225424166843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39564492305154404524446325 3709171153608225424166843)
                      ·
                        rfl

theorem cell23_7223585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_7223585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223585 prefixEnd_7223585 := by exact prefixLift 7223585
  have htrace : WordTrace (prefixWord ++ tailWord_7223585) baseStart_7223585 baseEnd_7223585 := by
    simpa [prefixWord, tailWord_7223585, baseEnd_7223585] using wordTrace_append hprefix tailTrace_7223585
  have hstable : (prefixWord ++ tailWord_7223585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223585).length < 2 ^ (prefixWord ++ tailWord_7223585).sum := by decide
  have hdescent : baseEnd_7223585 < baseStart_7223585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223605 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 2, 8]
def baseStart_7223605 : Nat := 118140960795 + 7223605 * 2 ^ 59
def prefixEnd_7223605 : Nat := 4983230072969 + 3 ^ 40 * 7223605 * 2
def baseEnd_7223605 : Nat := 1236393807740438448638917

theorem tailTrace_7223605 : CollatzResearch.WordTrace tailWord_7223605 prefixEnd_7223605 1236393807740438448638917 := by
  unfold tailWord_7223605
  simp only [CollatzResearch.WordTrace]
  refine ⟨263466518995120253359752269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175644345996746835573168179 263466518995120253359752269)
  ·
    refine ⟨98799944623170095009907101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263466518995120253359752269 98799944623170095009907101)
    ·
      refine ⟨37049979233688785628715163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98799944623170095009907101 37049979233688785628715163)
      ·
        refine ⟨55574968850533178443072745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37049979233688785628715163 55574968850533178443072745)
        ·
          refine ⟨41681226637899883832304559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55574968850533178443072745 41681226637899883832304559)
          ·
            refine ⟨62521839956849825748456839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41681226637899883832304559 62521839956849825748456839)
            ·
              refine ⟨93782759935274738622685259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62521839956849825748456839 93782759935274738622685259)
              ·
                refine ⟨140674139902912107934027889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93782759935274738622685259 140674139902912107934027889)
                ·
                  refine ⟨105505604927184080950520917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140674139902912107934027889 105505604927184080950520917)
                  ·
                    refine ⟨1236393807740438448638917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105505604927184080950520917 1236393807740438448638917)
                    ·
                      rfl

theorem cell23_7223605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_7223605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223605 prefixEnd_7223605 := by exact prefixLift 7223605
  have htrace : WordTrace (prefixWord ++ tailWord_7223605) baseStart_7223605 baseEnd_7223605 := by
    simpa [prefixWord, tailWord_7223605, baseEnd_7223605] using wordTrace_append hprefix tailTrace_7223605
  have hstable : (prefixWord ++ tailWord_7223605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223605).length < 2 ^ (prefixWord ++ tailWord_7223605).sum := by decide
  have hdescent : baseEnd_7223605 < baseStart_7223605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223612 : List Nat := [2, 2, 2, 2, 1, 2, 2, 3, 2, 1, 4]
def baseStart_7223612 : Nat := 118140960795 + 7223612 * 2 ^ 59
def prefixEnd_7223612 : Nat := 4983230072969 + 3 ^ 40 * 7223612 * 2
def baseEnd_7223612 : Nat := 3709185017585896818529219

theorem tailTrace_7223612 : CollatzResearch.WordTrace tailWord_7223612 prefixEnd_7223612 3709185017585896818529219 := by
  unfold tailWord_7223612
  simp only [CollatzResearch.WordTrace]
  refine ⟨131733387153047446777628545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175644516204063262370171393 131733387153047446777628545)
  ·
    refine ⟨98800040364785585083221409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131733387153047446777628545 98800040364785585083221409)
    ·
      refine ⟨74100030273589188812416057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98800040364785585083221409 74100030273589188812416057)
      ·
        refine ⟨55575022705191891609312043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74100030273589188812416057 55575022705191891609312043)
        ·
          refine ⟨83362534057787837413968065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55575022705191891609312043 83362534057787837413968065)
          ·
            refine ⟨62521900543340878060476049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83362534057787837413968065 62521900543340878060476049)
            ·
              refine ⟨46891425407505658545357037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62521900543340878060476049 46891425407505658545357037)
              ·
                refine ⟨17584284527814621954508889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46891425407505658545357037 17584284527814621954508889)
                ·
                  refine ⟨13188213395860966465881667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17584284527814621954508889 13188213395860966465881667)
                  ·
                    refine ⟨19782320093791449698822501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13188213395860966465881667 19782320093791449698822501)
                    ·
                      refine ⟨3709185017585896818529219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19782320093791449698822501 3709185017585896818529219)
                      ·
                        rfl

theorem cell23_7223612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_7223612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223612 prefixEnd_7223612 := by exact prefixLift 7223612
  have htrace : WordTrace (prefixWord ++ tailWord_7223612) baseStart_7223612 baseEnd_7223612 := by
    simpa [prefixWord, tailWord_7223612, baseEnd_7223612] using wordTrace_append hprefix tailTrace_7223612
  have hstable : (prefixWord ++ tailWord_7223612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223612).length < 2 ^ (prefixWord ++ tailWord_7223612).sum := by decide
  have hdescent : baseEnd_7223612 < baseStart_7223612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223632 : List Nat := [2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 3]
def baseStart_7223632 : Nat := 118140960795 + 7223632 * 2 ^ 59
def prefixEnd_7223632 : Nat := 4983230072969 + 3 ^ 40 * 7223632 * 2
def baseEnd_7223632 : Nat := 3709195287198986740279127

theorem tailTrace_7223632 : CollatzResearch.WordTrace tailWord_7223632 prefixEnd_7223632 3709195287198986740279127 := by
  unfold tailWord_7223632
  simp only [CollatzResearch.WordTrace]
  refine ⟨131733751883011218485492575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175645002510681624647323433 131733751883011218485492575)
  ·
    refine ⟨197600627824516827728238863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131733751883011218485492575 197600627824516827728238863)
    ·
      refine ⟨296400941736775241592358295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197600627824516827728238863 296400941736775241592358295)
      ·
        refine ⟨444601412605162862388537443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296400941736775241592358295 444601412605162862388537443)
        ·
          refine ⟨666902118907744293582806165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444601412605162862388537443 666902118907744293582806165)
          ·
            refine ⟨31261036823800513761694039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 666902118907744293582806165 31261036823800513761694039)
            ·
              refine ⟨46891555235700770642541059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31261036823800513761694039 46891555235700770642541059)
              ·
                refine ⟨70337332853551155963811589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46891555235700770642541059 70337332853551155963811589)
                ·
                  refine ⟨13188249910040841743214673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70337332853551155963811589 13188249910040841743214673)
                  ·
                    refine ⟨9891187432530631307411005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13188249910040841743214673 9891187432530631307411005)
                    ·
                      refine ⟨3709195287198986740279127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9891187432530631307411005 3709195287198986740279127)
                      ·
                        rfl

theorem cell23_7223632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 3].length) (baseStart_7223632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223632 prefixEnd_7223632 := by exact prefixLift 7223632
  have htrace : WordTrace (prefixWord ++ tailWord_7223632) baseStart_7223632 baseEnd_7223632 := by
    simpa [prefixWord, tailWord_7223632, baseEnd_7223632] using wordTrace_append hprefix tailTrace_7223632
  have hstable : (prefixWord ++ tailWord_7223632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223632).length < 2 ^ (prefixWord ++ tailWord_7223632).sum := by decide
  have hdescent : baseEnd_7223632 < baseStart_7223632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223652 : List Nat := [2, 3, 1, 1, 3, 1, 3, 3, 6]
def baseStart_7223652 : Nat := 118140960795 + 7223652 * 2 ^ 59
def prefixEnd_7223652 : Nat := 4983230072969 + 3 ^ 40 * 7223652 * 2
def baseEnd_7223652 : Nat := 412133950756897406892115

theorem tailTrace_7223652 : CollatzResearch.WordTrace tailWord_7223652 prefixEnd_7223652 412133950756897406892115 := by
  unfold tailWord_7223652
  simp only [CollatzResearch.WordTrace]
  refine ⟨131734116612974990193356605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175645488817299986924475473 131734116612974990193356605)
  ·
    refine ⟨49400293729865621322508727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131734116612974990193356605 49400293729865621322508727)
    ·
      refine ⟨74100440594798431983763091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49400293729865621322508727 74100440594798431983763091)
      ·
        refine ⟨111150660892197647975644637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74100440594798431983763091 111150660892197647975644637)
        ·
          refine ⟨41681497834574117990866739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111150660892197647975644637 41681497834574117990866739)
          ·
            refine ⟨62522246751861176986300109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41681497834574117990866739 62522246751861176986300109)
            ·
              refine ⟨23445842531947941369862541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62522246751861176986300109 23445842531947941369862541)
              ·
                refine ⟨8792190949480478013698453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23445842531947941369862541 8792190949480478013698453)
                ·
                  refine ⟨412133950756897406892115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8792190949480478013698453 412133950756897406892115)
                  ·
                    rfl

theorem cell23_7223652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 6].length) (baseStart_7223652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223652 prefixEnd_7223652 := by exact prefixLift 7223652
  have htrace : WordTrace (prefixWord ++ tailWord_7223652) baseStart_7223652 baseEnd_7223652 := by
    simpa [prefixWord, tailWord_7223652, baseEnd_7223652] using wordTrace_append hprefix tailTrace_7223652
  have hstable : (prefixWord ++ tailWord_7223652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223652).length < 2 ^ (prefixWord ++ tailWord_7223652).sum := by decide
  have hdescent : baseEnd_7223652 < baseStart_7223652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223712 : List Nat := [2, 1, 1, 4, 1, 3, 1, 3, 1, 6]
def baseStart_7223712 : Nat := 118140960795 + 7223712 * 2 ^ 59
def prefixEnd_7223712 : Nat := 4983230072969 + 3 ^ 40 * 7223712 * 2
def baseEnd_7223712 : Nat := 1236412121883782142426253

theorem tailTrace_7223712 : CollatzResearch.WordTrace tailWord_7223712 prefixEnd_7223712 1236412121883782142426253 := by
  unfold tailWord_7223712
  simp only [CollatzResearch.WordTrace]
  refine ⟨131735210802866305316948695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175646947737155073755931593 131735210802866305316948695)
  ·
    refine ⟨197602816204299457975423043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131735210802866305316948695 197602816204299457975423043)
    ·
      refine ⟨296404224306449186963134565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197602816204299457975423043 296404224306449186963134565)
      ·
        refine ⟨55575792057459222555587731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 296404224306449186963134565 55575792057459222555587731)
        ·
          refine ⟨83363688086188833833381597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55575792057459222555587731 83363688086188833833381597)
          ·
            refine ⟨31261383032320812687518099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83363688086188833833381597 31261383032320812687518099)
            ·
              refine ⟨46892074548481219031277149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31261383032320812687518099 46892074548481219031277149)
              ·
                refine ⟨17584527955680457136728931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46892074548481219031277149 17584527955680457136728931)
                ·
                  refine ⟨26376791933520685705093397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17584527955680457136728931 26376791933520685705093397)
                  ·
                    refine ⟨1236412121883782142426253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26376791933520685705093397 1236412121883782142426253)
                    ·
                      rfl

theorem cell23_7223712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 1, 6].length) (baseStart_7223712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223712 prefixEnd_7223712 := by exact prefixLift 7223712
  have htrace : WordTrace (prefixWord ++ tailWord_7223712) baseStart_7223712 baseEnd_7223712 := by
    simpa [prefixWord, tailWord_7223712, baseEnd_7223712] using wordTrace_append hprefix tailTrace_7223712
  have hstable : (prefixWord ++ tailWord_7223712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223712).length < 2 ^ (prefixWord ++ tailWord_7223712).sum := by decide
  have hdescent : baseEnd_7223712 < baseStart_7223712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223713 : List Nat := [1, 2, 3, 5, 1, 1, 1, 2, 3, 1, 3]
def baseStart_7223713 : Nat := 118140960795 + 7223713 * 2 ^ 59
def prefixEnd_7223713 : Nat := 4983230072969 + 3 ^ 40 * 7223713 * 2
def baseEnd_7223713 : Nat := 3709236879132000923366255

theorem tailTrace_7223713 : CollatzResearch.WordTrace tailWord_7223713 prefixEnd_7223713 3709236879132000923366255 := by
  unfold tailWord_7223713
  simp only [CollatzResearch.WordTrace]
  refine ⟨263470458078728987804683793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175646972052485991869789195 263470458078728987804683793)
  ·
    refine ⟨197602843559046740853512845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263470458078728987804683793 197602843559046740853512845)
    ·
      refine ⟨74101066334642527820067317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197602843559046740853512845 74101066334642527820067317)
      ·
        refine ⟨6946974968872736983131311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74101066334642527820067317 6946974968872736983131311)
        ·
          refine ⟨10420462453309105474696967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6946974968872736983131311 10420462453309105474696967)
          ·
            refine ⟨15630693679963658212045451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10420462453309105474696967 15630693679963658212045451)
            ·
              refine ⟨23446040519945487318068177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15630693679963658212045451 23446040519945487318068177)
              ·
                refine ⟨17584530389959115488551133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23446040519945487318068177 17584530389959115488551133)
                ·
                  refine ⟨6594198896234668308206675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17584530389959115488551133 6594198896234668308206675)
                  ·
                    refine ⟨9891298344352002462310013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6594198896234668308206675 9891298344352002462310013)
                    ·
                      refine ⟨3709236879132000923366255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9891298344352002462310013 3709236879132000923366255)
                      ·
                        rfl

theorem cell23_7223713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_7223713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223713 prefixEnd_7223713 := by exact prefixLift 7223713
  have htrace : WordTrace (prefixWord ++ tailWord_7223713) baseStart_7223713 baseEnd_7223713 := by
    simpa [prefixWord, tailWord_7223713, baseEnd_7223713] using wordTrace_append hprefix tailTrace_7223713
  have hstable : (prefixWord ++ tailWord_7223713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223713).length < 2 ^ (prefixWord ++ tailWord_7223713).sum := by decide
  have hdescent : baseEnd_7223713 < baseStart_7223713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223719 : List Nat := [1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_7223719 : Nat := 118140960795 + 7223719 * 2 ^ 59
def prefixEnd_7223719 : Nat := 4983230072969 + 3 ^ 40 * 7223719 * 2
def baseEnd_7223719 : Nat := 3709239960015927899891227

theorem tailTrace_7223719 : CollatzResearch.WordTrace tailWord_7223719 prefixEnd_7223719 3709239960015927899891227 := by
  unfold tailWord_7223719
  simp only [CollatzResearch.WordTrace]
  refine ⟨263470676916707250829402211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175647117944471500552934807 263470676916707250829402211)
  ·
    refine ⟨395206015375060876244103317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263470676916707250829402211 395206015375060876244103317)
    ·
      refine ⟨18525281970705978573942343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 395206015375060876244103317 18525281970705978573942343)
      ·
        refine ⟨27787922956058967860913515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18525281970705978573942343 27787922956058967860913515)
        ·
          refine ⟨41681884434088451791370273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27787922956058967860913515 41681884434088451791370273)
          ·
            refine ⟨31261413325566338843527705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41681884434088451791370273 31261413325566338843527705)
            ·
              refine ⟨23446059994174754132645779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31261413325566338843527705 23446059994174754132645779)
              ·
                refine ⟨35169089991262131198968669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23446059994174754132645779 35169089991262131198968669)
                ·
                  refine ⟨13188408746723299199613251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35169089991262131198968669 13188408746723299199613251)
                  ·
                    refine ⟨19782613120084948799419877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13188408746723299199613251 19782613120084948799419877)
                    ·
                      refine ⟨3709239960015927899891227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19782613120084948799419877 3709239960015927899891227)
                      ·
                        rfl

theorem cell23_7223719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_7223719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223719 prefixEnd_7223719 := by exact prefixLift 7223719
  have htrace : WordTrace (prefixWord ++ tailWord_7223719) baseStart_7223719 baseEnd_7223719 := by
    simpa [prefixWord, tailWord_7223719, baseEnd_7223719] using wordTrace_append hprefix tailTrace_7223719
  have hstable : (prefixWord ++ tailWord_7223719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223719).length < 2 ^ (prefixWord ++ tailWord_7223719).sum := by decide
  have hdescent : baseEnd_7223719 < baseStart_7223719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223733 : List Nat := [1, 3, 3, 2, 3, 2, 2, 1, 1, 5]
def baseStart_7223733 : Nat := 118140960795 + 7223733 * 2 ^ 59
def prefixEnd_7223733 : Nat := 4983230072969 + 3 ^ 40 * 7223733 * 2
def baseEnd_7223733 : Nat := 1236415716248363615038721

theorem tailTrace_7223733 : CollatzResearch.WordTrace tailWord_7223733 prefixEnd_7223733 1236415716248363615038721 := by
  unfold tailWord_7223733
  simp only [CollatzResearch.WordTrace]
  refine ⟨263471187538656531220411853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175647458359104354146941235 263471187538656531220411853)
  ·
    refine ⟨98801695326996199207654445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263471187538656531220411853 98801695326996199207654445)
    ·
      refine ⟨37050635747623574702870417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98801695326996199207654445 37050635747623574702870417)
      ·
        refine ⟨27787976810717681027152813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37050635747623574702870417 27787976810717681027152813)
        ·
          refine ⟨10420491304019130385182305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27787976810717681027152813 10420491304019130385182305)
          ·
            refine ⟨7815368478014347788886729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10420491304019130385182305 7815368478014347788886729)
            ·
              refine ⟨5861526358510760841665047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7815368478014347788886729 5861526358510760841665047)
              ·
                refine ⟨8792289537766141262497571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5861526358510760841665047 8792289537766141262497571)
                ·
                  refine ⟨13188434306649211893746357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8792289537766141262497571 13188434306649211893746357)
                  ·
                    refine ⟨1236415716248363615038721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13188434306649211893746357 1236415716248363615038721)
                    ·
                      rfl

theorem cell23_7223733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_7223733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223733 prefixEnd_7223733 := by exact prefixLift 7223733
  have htrace : WordTrace (prefixWord ++ tailWord_7223733) baseStart_7223733 baseEnd_7223733 := by
    simpa [prefixWord, tailWord_7223733, baseEnd_7223733] using wordTrace_append hprefix tailTrace_7223733
  have hstable : (prefixWord ++ tailWord_7223733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223733).length < 2 ^ (prefixWord ++ tailWord_7223733).sum := by decide
  have hdescent : baseEnd_7223733 < baseStart_7223733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223753 : List Nat := [1, 2, 1, 1, 2, 1, 6, 4, 1, 2, 2]
def baseStart_7223753 : Nat := 118140960795 + 7223753 * 2 ^ 59
def prefixEnd_7223753 : Nat := 4983230072969 + 3 ^ 40 * 7223753 * 2
def baseEnd_7223753 : Nat := 3709257418358180766866071

theorem tailTrace_7223753 : CollatzResearch.WordTrace tailWord_7223753 prefixEnd_7223753 3709257418358180766866071 := by
  unfold tailWord_7223753
  simp only [CollatzResearch.WordTrace]
  refine ⟨263471916998584074636139913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175647944665722716424093275 263471916998584074636139913)
  ·
    refine ⟨197603937748938055977104935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263471916998584074636139913 197603937748938055977104935)
    ·
      refine ⟨296405906623407083965657403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197603937748938055977104935 296405906623407083965657403)
      ·
        refine ⟨444608859935110625948486105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296405906623407083965657403 444608859935110625948486105)
        ·
          refine ⟨333456644951332969461364579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444608859935110625948486105 333456644951332969461364579)
          ·
            refine ⟨500184967426999454192046869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333456644951332969461364579 500184967426999454192046869)
            ·
              refine ⟨23446170348140599415252197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 500184967426999454192046869 23446170348140599415252197)
              ·
                refine ⟨4396156940276362390359787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23446170348140599415252197 4396156940276362390359787)
                ·
                  refine ⟨6594235410414543585539681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4396156940276362390359787 6594235410414543585539681)
                  ·
                    refine ⟨4945676557810907689154761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6594235410414543585539681 4945676557810907689154761)
                    ·
                      refine ⟨3709257418358180766866071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4945676557810907689154761 3709257418358180766866071)
                      ·
                        rfl

theorem cell23_7223753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 4, 1, 2, 2].length) (baseStart_7223753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223753 prefixEnd_7223753 := by exact prefixLift 7223753
  have htrace : WordTrace (prefixWord ++ tailWord_7223753) baseStart_7223753 baseEnd_7223753 := by
    simpa [prefixWord, tailWord_7223753, baseEnd_7223753] using wordTrace_append hprefix tailTrace_7223753
  have hstable : (prefixWord ++ tailWord_7223753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223753).length < 2 ^ (prefixWord ++ tailWord_7223753).sum := by decide
  have hdescent : baseEnd_7223753 < baseStart_7223753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223786 : List Nat := [3, 1, 3, 1, 3, 1, 1, 2, 4, 1, 3]
def baseStart_7223786 : Nat := 118140960795 + 7223786 * 2 ^ 59
def prefixEnd_7223786 : Nat := 4983230072969 + 3 ^ 40 * 7223786 * 2
def baseEnd_7223786 : Nat := 3709274363219779137753419

theorem tailTrace_7223786 : CollatzResearch.WordTrace tailWord_7223786 prefixEnd_7223786 3709274363219779137753419 := by
  unfold tailWord_7223786
  simp only [CollatzResearch.WordTrace]
  refine ⟨65868280151866130318022803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175648747071643014181394141 65868280151866130318022803)
  ·
    refine ⟨98802420227799195477034205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65868280151866130318022803 98802420227799195477034205)
    ·
      refine ⟨37050907585424698303887827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98802420227799195477034205 37050907585424698303887827)
      ·
        refine ⟨55576361378137047455831741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37050907585424698303887827 55576361378137047455831741)
        ·
          refine ⟨20841135516801392795936903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55576361378137047455831741 20841135516801392795936903)
          ·
            refine ⟨31261703275202089193905355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20841135516801392795936903 31261703275202089193905355)
            ·
              refine ⟨46892554912803133790858033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31261703275202089193905355 46892554912803133790858033)
              ·
                refine ⟨35169416184602350343143525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46892554912803133790858033 35169416184602350343143525)
                ·
                  refine ⟨6594265534612940689339411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35169416184602350343143525 6594265534612940689339411)
                  ·
                    refine ⟨9891398301919411034009117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6594265534612940689339411 9891398301919411034009117)
                    ·
                      refine ⟨3709274363219779137753419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9891398301919411034009117 3709274363219779137753419)
                      ·
                        rfl

theorem cell23_7223786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_7223786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223786 prefixEnd_7223786 := by exact prefixLift 7223786
  have htrace : WordTrace (prefixWord ++ tailWord_7223786) baseStart_7223786 baseEnd_7223786 := by
    simpa [prefixWord, tailWord_7223786, baseEnd_7223786] using wordTrace_append hprefix tailTrace_7223786
  have hstable : (prefixWord ++ tailWord_7223786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223786).length < 2 ^ (prefixWord ++ tailWord_7223786).sum := by decide
  have hdescent : baseEnd_7223786 < baseStart_7223786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223802 : List Nat := [3, 1, 1, 1, 1, 2, 2, 4, 2, 6]
def baseStart_7223802 : Nat := 118140960795 + 7223802 * 2 ^ 59
def prefixEnd_7223802 : Nat := 4983230072969 + 3 ^ 40 * 7223802 * 2
def baseEnd_7223802 : Nat := 1236427526303417025051115

theorem tailTrace_7223802 : CollatzResearch.WordTrace tailWord_7223802 prefixEnd_7223802 1236427526303417025051115 := by
  unfold tailWord_7223802
  simp only [CollatzResearch.WordTrace]
  refine ⟨65868426043851639001168415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175649136116937704003115773 65868426043851639001168415)
  ·
    refine ⟨98802639065777458501752623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65868426043851639001168415 98802639065777458501752623)
    ·
      refine ⟨148203958598666187752628935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98802639065777458501752623 148203958598666187752628935)
      ·
        refine ⟨222305937897999281628943403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148203958598666187752628935 222305937897999281628943403)
        ·
          refine ⟨333458906846998922443415105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222305937897999281628943403 333458906846998922443415105)
          ·
            refine ⟨250094180135249191832561329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333458906846998922443415105 250094180135249191832561329)
            ·
              refine ⟨187570635101436893874420997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250094180135249191832561329 187570635101436893874420997)
              ·
                refine ⟨35169494081519417601453937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187570635101436893874420997 35169494081519417601453937)
                ·
                  refine ⟨26377120561139563201090453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35169494081519417601453937 26377120561139563201090453)
                  ·
                    refine ⟨1236427526303417025051115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26377120561139563201090453 1236427526303417025051115)
                    ·
                      rfl

theorem cell23_7223802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 2, 6].length) (baseStart_7223802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223802 prefixEnd_7223802 := by exact prefixLift 7223802
  have htrace : WordTrace (prefixWord ++ tailWord_7223802) baseStart_7223802 baseEnd_7223802 := by
    simpa [prefixWord, tailWord_7223802, baseEnd_7223802] using wordTrace_append hprefix tailTrace_7223802
  have hstable : (prefixWord ++ tailWord_7223802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223802).length < 2 ^ (prefixWord ++ tailWord_7223802).sum := by decide
  have hdescent : baseEnd_7223802 < baseStart_7223802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223814 : List Nat := [6, 2, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_7223814 : Nat := 118140960795 + 7223814 * 2 ^ 59
def prefixEnd_7223814 : Nat := 4983230072969 + 3 ^ 40 * 7223814 * 2
def baseEnd_7223814 : Nat := 1236429580226035009401097

theorem tailTrace_7223814 : CollatzResearch.WordTrace tailWord_7223814 prefixEnd_7223814 1236429580226035009401097 := by
  unfold tailWord_7223814
  simp only [CollatzResearch.WordTrace]
  refine ⟨8233566932855096314190953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 175649427900908721369406997 8233566932855096314190953)
  ·
    refine ⟨6175175199641322235643215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8233566932855096314190953 6175175199641322235643215)
    ·
      refine ⟨9262762799461983353464823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6175175199641322235643215 9262762799461983353464823)
      ·
        refine ⟨13894144199192975030197235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9262762799461983353464823 13894144199192975030197235)
        ·
          refine ⟨20841216298789462545295853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13894144199192975030197235 20841216298789462545295853)
          ·
            refine ⟨7815456112046048454485945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20841216298789462545295853 7815456112046048454485945)
            ·
              refine ⟨5861592084034536340864459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7815456112046048454485945 5861592084034536340864459)
              ·
                refine ⟨8792388126051804511296689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5861592084034536340864459 8792388126051804511296689)
                ·
                  refine ⟨6594291094538853383472517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8792388126051804511296689 6594291094538853383472517)
                  ·
                    refine ⟨1236429580226035009401097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6594291094538853383472517 1236429580226035009401097)
                    ·
                      rfl

theorem cell23_7223814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_7223814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223814 prefixEnd_7223814 := by exact prefixLift 7223814
  have htrace : WordTrace (prefixWord ++ tailWord_7223814) baseStart_7223814 baseEnd_7223814 := by
    simpa [prefixWord, tailWord_7223814, baseEnd_7223814] using wordTrace_append hprefix tailTrace_7223814
  have hstable : (prefixWord ++ tailWord_7223814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223814).length < 2 ^ (prefixWord ++ tailWord_7223814).sum := by decide
  have hdescent : baseEnd_7223814 < baseStart_7223814 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223820 : List Nat := [2, 2, 1, 2, 4, 3, 2, 1, 2, 1, 3]
def baseStart_7223820 : Nat := 118140960795 + 7223820 * 2 ^ 59
def prefixEnd_7223820 : Nat := 4983230072969 + 3 ^ 40 * 7223820 * 2
def baseEnd_7223820 : Nat := 3709291821562032004728263

theorem tailTrace_7223820 : CollatzResearch.WordTrace tailWord_7223820 prefixEnd_7223820 3709291821562032004728263 := by
  unfold tailWord_7223820
  simp only [CollatzResearch.WordTrace]
  refine ⟨131737180344670672539414457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175649573792894230052552609 131737180344670672539414457)
  ·
    refine ⟨98802885258503004404560843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131737180344670672539414457 98802885258503004404560843)
    ·
      refine ⟨148204327887754506606841265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98802885258503004404560843 148204327887754506606841265)
      ·
        refine ⟨111153245915815879955130949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148204327887754506606841265 111153245915815879955130949)
        ·
          refine ⟨20841233609215477491587053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111153245915815879955130949 20841233609215477491587053)
          ·
            refine ⟨7815462603455804059345145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20841233609215477491587053 7815462603455804059345145)
            ·
              refine ⟨5861596952591853044508859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7815462603455804059345145 5861596952591853044508859)
              ·
                refine ⟨8792395428887779566763289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5861596952591853044508859 8792395428887779566763289)
                ·
                  refine ⟨6594296571665834675072467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8792395428887779566763289 6594296571665834675072467)
                  ·
                    refine ⟨9891444857498752012608701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6594296571665834675072467 9891444857498752012608701)
                    ·
                      refine ⟨3709291821562032004728263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9891444857498752012608701 3709291821562032004728263)
                      ·
                        rfl

theorem cell23_7223820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 2, 1, 3].length) (baseStart_7223820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223820 prefixEnd_7223820 := by exact prefixLift 7223820
  have htrace : WordTrace (prefixWord ++ tailWord_7223820) baseStart_7223820 baseEnd_7223820 := by
    simpa [prefixWord, tailWord_7223820, baseEnd_7223820] using wordTrace_append hprefix tailTrace_7223820
  have hstable : (prefixWord ++ tailWord_7223820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223820).length < 2 ^ (prefixWord ++ tailWord_7223820).sum := by decide
  have hdescent : baseEnd_7223820 < baseStart_7223820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223859 : List Nat := [1, 1, 1, 2, 4, 2, 2, 2, 2, 3, 3]
def baseStart_7223859 : Nat := 118140960795 + 7223859 * 2 ^ 59
def prefixEnd_7223859 : Nat := 4983230072969 + 3 ^ 40 * 7223859 * 2
def baseEnd_7223859 : Nat := 3709311847307557352140583

theorem tailTrace_7223859 : CollatzResearch.WordTrace tailWord_7223859 prefixEnd_7223859 3709311847307557352140583 := by
  unfold tailWord_7223859
  simp only [CollatzResearch.WordTrace]
  refine ⟨263475783136200054739498631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175650522090800036492999087 263475783136200054739498631)
  ·
    refine ⟨395213674704300082109247947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263475783136200054739498631 395213674704300082109247947)
    ·
      refine ⟨592820512056450123163871921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395213674704300082109247947 592820512056450123163871921)
      ·
        refine ⟨444615384042337592372903941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 592820512056450123163871921 444615384042337592372903941)
        ·
          refine ⟨83365384507938298569919489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 444615384042337592372903941 83365384507938298569919489)
          ·
            refine ⟨62524038380953723927439617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83365384507938298569919489 62524038380953723927439617)
            ·
              refine ⟨46893028785715292945579713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62524038380953723927439617 46893028785715292945579713)
              ·
                refine ⟨35169771589286469709184785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46893028785715292945579713 35169771589286469709184785)
                ·
                  refine ⟨26377328691964852281888589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35169771589286469709184785 26377328691964852281888589)
                  ·
                    refine ⟨9891498259486819605708221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26377328691964852281888589 9891498259486819605708221)
                    ·
                      refine ⟨3709311847307557352140583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9891498259486819605708221 3709311847307557352140583)
                      ·
                        rfl

theorem cell23_7223859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 3, 3].length) (baseStart_7223859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223859 prefixEnd_7223859 := by exact prefixLift 7223859
  have htrace : WordTrace (prefixWord ++ tailWord_7223859) baseStart_7223859 baseEnd_7223859 := by
    simpa [prefixWord, tailWord_7223859, baseEnd_7223859] using wordTrace_append hprefix tailTrace_7223859
  have hstable : (prefixWord ++ tailWord_7223859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223859).length < 2 ^ (prefixWord ++ tailWord_7223859).sum := by decide
  have hdescent : baseEnd_7223859 < baseStart_7223859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223866 : List Nat := [3, 1, 1, 1, 3, 4, 1, 4, 5]
def baseStart_7223866 : Nat := 118140960795 + 7223866 * 2 ^ 59
def prefixEnd_7223866 : Nat := 4983230072969 + 3 ^ 40 * 7223866 * 2
def baseEnd_7223866 : Nat := 412146160185793202750339

theorem tailTrace_7223866 : CollatzResearch.WordTrace tailWord_7223866 prefixEnd_7223866 412146160185793202750339 := by
  unfold tailWord_7223866
  simp only [CollatzResearch.WordTrace]
  refine ⟨65869009611793673733750863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175650692298116463290002301 65869009611793673733750863)
  ·
    refine ⟨98803514417690510600626295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65869009611793673733750863 98803514417690510600626295)
    ·
      refine ⟨148205271626535765900939443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98803514417690510600626295 148205271626535765900939443)
      ·
        refine ⟨222307907439803648851409165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148205271626535765900939443 222307907439803648851409165)
        ·
          refine ⟨83365465289926368319278437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222307907439803648851409165 83365465289926368319278437)
          ·
            refine ⟨15631024741861194059864707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83365465289926368319278437 15631024741861194059864707)
            ·
              refine ⟨23446537112791791089797061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15631024741861194059864707 23446537112791791089797061)
              ·
                refine ⟨4396225708648460829336949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23446537112791791089797061 4396225708648460829336949)
                ·
                  refine ⟨412146160185793202750339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4396225708648460829336949 412146160185793202750339)
                  ·
                    rfl

theorem cell23_7223866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 4, 5].length) (baseStart_7223866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223866 prefixEnd_7223866 := by exact prefixLift 7223866
  have htrace : WordTrace (prefixWord ++ tailWord_7223866) baseStart_7223866 baseEnd_7223866 := by
    simpa [prefixWord, tailWord_7223866, baseEnd_7223866] using wordTrace_append hprefix tailTrace_7223866
  have hstable : (prefixWord ++ tailWord_7223866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223866).length < 2 ^ (prefixWord ++ tailWord_7223866).sum := by decide
  have hdescent : baseEnd_7223866 < baseStart_7223866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223916 : List Nat := [2, 2, 1, 1, 3, 1, 3, 2, 2, 4, 2]
def baseStart_7223916 : Nat := 118140960795 + 7223916 * 2 ^ 59
def prefixEnd_7223916 : Nat := 4983230072969 + 3 ^ 40 * 7223916 * 2
def baseEnd_7223916 : Nat := 3709341115704863629127821

theorem tailTrace_7223916 : CollatzResearch.WordTrace tailWord_7223916 prefixEnd_7223916 3709341115704863629127821 := by
  unfold tailWord_7223916
  simp only [CollatzResearch.WordTrace]
  refine ⟨131738931048496776737161801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175651908064662368982882401 131738931048496776737161801)
  ·
    refine ⟨98804198286372582552871351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131738931048496776737161801 98804198286372582552871351)
    ·
      refine ⟨148206297429558873829307027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98804198286372582552871351 148206297429558873829307027)
      ·
        refine ⟨222309446144338310743960541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148206297429558873829307027 222309446144338310743960541)
        ·
          refine ⟨83366042304126866528985203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222309446144338310743960541 83366042304126866528985203)
          ·
            refine ⟨125049063456190299793477805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83366042304126866528985203 125049063456190299793477805)
            ·
              refine ⟨46893398796071362422554177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125049063456190299793477805 46893398796071362422554177)
              ·
                refine ⟨35170049097053521816915633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46893398796071362422554177 35170049097053521816915633)
                ·
                  refine ⟨26377536822790141362686725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35170049097053521816915633 26377536822790141362686725)
                  ·
                    refine ⟨4945788154273151505503761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26377536822790141362686725 4945788154273151505503761)
                    ·
                      refine ⟨3709341115704863629127821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4945788154273151505503761 3709341115704863629127821)
                      ·
                        rfl

theorem cell23_7223916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 4, 2].length) (baseStart_7223916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223916 prefixEnd_7223916 := by exact prefixLift 7223916
  have htrace : WordTrace (prefixWord ++ tailWord_7223916) baseStart_7223916 baseEnd_7223916 := by
    simpa [prefixWord, tailWord_7223916, baseEnd_7223916] using wordTrace_append hprefix tailTrace_7223916
  have hstable : (prefixWord ++ tailWord_7223916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223916).length < 2 ^ (prefixWord ++ tailWord_7223916).sum := by decide
  have hdescent : baseEnd_7223916 < baseStart_7223916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223939 : List Nat := [1, 1, 1, 3, 3, 1, 2, 5, 6]
def baseStart_7223939 : Nat := 118140960795 + 7223939 * 2 ^ 59
def prefixEnd_7223939 : Nat := 4983230072969 + 3 ^ 40 * 7223939 * 2
def baseEnd_7223939 : Nat := 412150325084435226571135

theorem tailTrace_7223939 : CollatzResearch.WordTrace tailWord_7223939 prefixEnd_7223939 412150325084435226571135 := by
  unfold tailWord_7223939
  simp only [CollatzResearch.WordTrace]
  refine ⟨263478700975910228402410871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175652467317273485601607247 263478700975910228402410871)
  ·
    refine ⟨395218051463865342603616307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263478700975910228402410871 395218051463865342603616307)
    ·
      refine ⟨592827077195798013905424461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395218051463865342603616307 592827077195798013905424461)
      ·
        refine ⟨222310153948424255214534173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 592827077195798013905424461 222310153948424255214534173)
        ·
          refine ⟨83366307730659095705450315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222310153948424255214534173 83366307730659095705450315)
          ·
            refine ⟨125049461595988643558175473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83366307730659095705450315 125049461595988643558175473)
            ·
              refine ⟨93787096196991482668631605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125049461595988643558175473 93787096196991482668631605)
              ·
                refine ⟨8792540268467951500184213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93787096196991482668631605 8792540268467951500184213)
                ·
                  refine ⟨412150325084435226571135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8792540268467951500184213 412150325084435226571135)
                  ·
                    rfl

theorem cell23_7223939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 6].length) (baseStart_7223939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223939 prefixEnd_7223939 := by exact prefixLift 7223939
  have htrace : WordTrace (prefixWord ++ tailWord_7223939) baseStart_7223939 baseEnd_7223939 := by
    simpa [prefixWord, tailWord_7223939, baseEnd_7223939] using wordTrace_append hprefix tailTrace_7223939
  have hstable : (prefixWord ++ tailWord_7223939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223939).length < 2 ^ (prefixWord ++ tailWord_7223939).sum := by decide
  have hdescent : baseEnd_7223939 < baseStart_7223939 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223956 : List Nat := [2, 4, 2, 2, 1, 1, 1, 2, 8]
def baseStart_7223956 : Nat := 118140960795 + 7223956 * 2 ^ 59
def prefixEnd_7223956 : Nat := 4983230072969 + 3 ^ 40 * 7223956 * 2
def baseEnd_7223956 : Nat := 412151294992338163625293

theorem tailTrace_7223956 : CollatzResearch.WordTrace tailWord_7223956 prefixEnd_7223956 412151294992338163625293 := by
  unfold tailWord_7223956
  simp only [CollatzResearch.WordTrace]
  refine ⟨131739660508424320152889861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175652880677899093537186481 131739660508424320152889861)
  ·
    refine ⟨24701186345329560028666849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131739660508424320152889861 24701186345329560028666849)
    ·
      refine ⟨18525889758997170021500137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24701186345329560028666849 18525889758997170021500137)
      ·
        refine ⟨13894417319247877516125103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18525889758997170021500137 13894417319247877516125103)
        ·
          refine ⟨20841625978871816274187655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13894417319247877516125103 20841625978871816274187655)
          ·
            refine ⟨31262438968307724411281483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20841625978871816274187655 31262438968307724411281483)
            ·
              refine ⟨46893658452461586616922225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31262438968307724411281483 46893658452461586616922225)
              ·
                refine ⟨35170243839346189962691669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46893658452461586616922225 35170243839346189962691669)
                ·
                  refine ⟨412151294992338163625293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35170243839346189962691669 412151294992338163625293)
                  ·
                    rfl

theorem cell23_7223956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_7223956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223956 prefixEnd_7223956 := by exact prefixLift 7223956
  have htrace : WordTrace (prefixWord ++ tailWord_7223956) baseStart_7223956 baseEnd_7223956 := by
    simpa [prefixWord, tailWord_7223956, baseEnd_7223956] using wordTrace_append hprefix tailTrace_7223956
  have hstable : (prefixWord ++ tailWord_7223956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223956).length < 2 ^ (prefixWord ++ tailWord_7223956).sum := by decide
  have hdescent : baseEnd_7223956 < baseStart_7223956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223983 : List Nat := [1, 1, 2, 1, 2, 5, 3, 1, 3, 1, 3]
def baseStart_7223983 : Nat := 118140960795 + 7223983 * 2 ^ 59
def prefixEnd_7223983 : Nat := 4983230072969 + 3 ^ 40 * 7223983 * 2
def baseEnd_7223983 : Nat := 3709375518908714866990013

theorem tailTrace_7223983 : CollatzResearch.WordTrace tailWord_7223983 prefixEnd_7223983 3709375518908714866990013 := by
  unfold tailWord_7223983
  simp only [CollatzResearch.WordTrace]
  refine ⟨263480305787750823917012603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175653537191833882611341735 263480305787750823917012603)
  ·
    refine ⟨395220458681626235875518905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263480305787750823917012603 395220458681626235875518905)
    ·
      refine ⟨296415344011219676906639179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395220458681626235875518905 296415344011219676906639179)
      ·
        refine ⟨444623016016829515359958769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296415344011219676906639179 444623016016829515359958769)
        ·
          refine ⟨333467262012622136519969077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444623016016829515359958769 333467262012622136519969077)
          ·
            refine ⟨31262555813683325298747101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 333467262012622136519969077 31262555813683325298747101)
            ·
              refine ⟨11723458430131246987030163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31262555813683325298747101 11723458430131246987030163)
              ·
                refine ⟨17585187645196870480545245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11723458430131246987030163 17585187645196870480545245)
                ·
                  refine ⟨6594445366948826430204467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17585187645196870480545245 6594445366948826430204467)
                  ·
                    refine ⟨9891668050423239645306701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6594445366948826430204467 9891668050423239645306701)
                    ·
                      refine ⟨3709375518908714866990013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9891668050423239645306701 3709375518908714866990013)
                      ·
                        rfl

theorem cell23_7223983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 3, 1, 3].length) (baseStart_7223983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223983 prefixEnd_7223983 := by exact prefixLift 7223983
  have htrace : WordTrace (prefixWord ++ tailWord_7223983) baseStart_7223983 baseEnd_7223983 := by
    simpa [prefixWord, tailWord_7223983, baseEnd_7223983] using wordTrace_append hprefix tailTrace_7223983
  have hstable : (prefixWord ++ tailWord_7223983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223983).length < 2 ^ (prefixWord ++ tailWord_7223983).sum := by decide
  have hdescent : baseEnd_7223983 < baseStart_7223983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7223990 : List Nat := [5, 1, 3, 1, 2, 1, 1, 3, 6]
def baseStart_7223990 : Nat := 118140960795 + 7223990 * 2 ^ 59
def prefixEnd_7223990 : Nat := 4983230072969 + 3 ^ 40 * 7223990 * 2
def baseEnd_7223990 : Nat := 412153234808144037733609

theorem tailTrace_7223990 : CollatzResearch.WordTrace tailWord_7223990 prefixEnd_7223990 412153234808144037733609 := by
  unfold tailWord_7223990
  simp only [CollatzResearch.WordTrace]
  refine ⟨16467535068670341507032339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175653707399150309408344949 16467535068670341507032339)
  ·
    refine ⟨24701302603005512260548509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16467535068670341507032339 24701302603005512260548509)
    ·
      refine ⟨9262988476127067097705691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24701302603005512260548509 9262988476127067097705691)
      ·
        refine ⟨13894482714190600646558537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9262988476127067097705691 13894482714190600646558537)
        ·
          refine ⟨10420862035642950484918903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13894482714190600646558537 10420862035642950484918903)
          ·
            refine ⟨15631293053464425727378355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10420862035642950484918903 15631293053464425727378355)
            ·
              refine ⟨23446939580196638591067533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15631293053464425727378355 23446939580196638591067533)
              ·
                refine ⟨8792602342573739471650325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23446939580196638591067533 8792602342573739471650325)
                ·
                  refine ⟨412153234808144037733609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8792602342573739471650325 412153234808144037733609)
                  ·
                    rfl

theorem cell23_7223990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_7223990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7223990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7223990 prefixEnd_7223990 := by exact prefixLift 7223990
  have htrace : WordTrace (prefixWord ++ tailWord_7223990) baseStart_7223990 baseEnd_7223990 := by
    simpa [prefixWord, tailWord_7223990, baseEnd_7223990] using wordTrace_append hprefix tailTrace_7223990
  have hstable : (prefixWord ++ tailWord_7223990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7223990).length < 2 ^ (prefixWord ++ tailWord_7223990).sum := by decide
  have hdescent : baseEnd_7223990 < baseStart_7223990 := by decide
  rcases family_descends (prefixWord ++ tailWord_7223990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224010 : List Nat := [3, 1, 2, 1, 4, 2, 2, 1, 2, 3, 2]
def baseStart_7224010 : Nat := 118140960795 + 7224010 * 2 ^ 59
def prefixEnd_7224010 : Nat := 4983230072969 + 3 ^ 40 * 7224010 * 2
def baseEnd_7224010 : Nat := 3709389382886386261352389

theorem tailTrace_7224010 : CollatzResearch.WordTrace tailWord_7224010 prefixEnd_7224010 3709389382886386261352389 := by
  unfold tailWord_7224010
  simp only [CollatzResearch.WordTrace]
  refine ⟨65870322639663251882061371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175654193705768671685496989 65870322639663251882061371)
  ·
    refine ⟨98805483959494877823092057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65870322639663251882061371 98805483959494877823092057)
    ·
      refine ⟨74104112969621158367319043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98805483959494877823092057 74104112969621158367319043)
      ·
        refine ⟨111156169454431737550978565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74104112969621158367319043 111156169454431737550978565)
        ·
          refine ⟨20841781772705950790808481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111156169454431737550978565 20841781772705950790808481)
          ·
            refine ⟨15631336329529463093106361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20841781772705950790808481 15631336329529463093106361)
            ·
              refine ⟨11723502247147097319829771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15631336329529463093106361 11723502247147097319829771)
              ·
                refine ⟨17585253370720645979744657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11723502247147097319829771 17585253370720645979744657)
                ·
                  refine ⟨13188940028040484484808493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17585253370720645979744657 13188940028040484484808493)
                  ·
                    refine ⟨4945852510515181681803185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13188940028040484484808493 4945852510515181681803185)
                    ·
                      refine ⟨3709389382886386261352389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4945852510515181681803185 3709389382886386261352389)
                      ·
                        rfl

theorem cell23_7224010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 2, 3, 2].length) (baseStart_7224010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224010 prefixEnd_7224010 := by exact prefixLift 7224010
  have htrace : WordTrace (prefixWord ++ tailWord_7224010) baseStart_7224010 baseEnd_7224010 := by
    simpa [prefixWord, tailWord_7224010, baseEnd_7224010] using wordTrace_append hprefix tailTrace_7224010
  have hstable : (prefixWord ++ tailWord_7224010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224010).length < 2 ^ (prefixWord ++ tailWord_7224010).sum := by decide
  have hdescent : baseEnd_7224010 < baseStart_7224010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224029 : List Nat := [1, 4, 3, 15]
def baseStart_7224029 : Nat := 118140960795 + 7224029 * 2 ^ 59
def prefixEnd_7224029 : Nat := 4983230072969 + 3 ^ 40 * 7224029 * 2
def baseEnd_7224029 : Nat := 1696113003666585133523

theorem tailTrace_7224029 : CollatzResearch.WordTrace tailWord_7224029 prefixEnd_7224029 1696113003666585133523 := by
  unfold tailWord_7224029
  simp only [CollatzResearch.WordTrace]
  refine ⟨263481983545584173773187141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175654655697056115848791427 263481983545584173773187141)
  ·
    refine ⟨49402871914797032582472589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263481983545584173773187141 49402871914797032582472589)
    ·
      refine ⟨18526076968048887218427221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49402871914797032582472589 18526076968048887218427221)
      ·
        refine ⟨1696113003666585133523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 18526076968048887218427221 1696113003666585133523)
        ·
          rfl

theorem cell23_7224029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 15].length) (baseStart_7224029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224029 prefixEnd_7224029 := by exact prefixLift 7224029
  have htrace : WordTrace (prefixWord ++ tailWord_7224029) baseStart_7224029 baseEnd_7224029 := by
    simpa [prefixWord, tailWord_7224029, baseEnd_7224029] using wordTrace_append hprefix tailTrace_7224029
  have hstable : (prefixWord ++ tailWord_7224029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224029).length < 2 ^ (prefixWord ++ tailWord_7224029).sum := by decide
  have hdescent : baseEnd_7224029 < baseStart_7224029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224033 : List Nat := [1, 2, 3, 1, 4, 1, 1, 4, 2, 4]
def baseStart_7224033 : Nat := 118140960795 + 7224033 * 2 ^ 59
def prefixEnd_7224033 : Nat := 4983230072969 + 3 ^ 40 * 7224033 * 2
def baseEnd_7224033 : Nat := 1236467064313813223788261

theorem tailTrace_7224033 : CollatzResearch.WordTrace tailWord_7224033 prefixEnd_7224033 1236467064313813223788261 := by
  unfold tailWord_7224033
  simp only [CollatzResearch.WordTrace]
  refine ⟨263482129437569682456332753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175654752958379788304221835 263482129437569682456332753)
  ·
    refine ⟨197611597078177261842249565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263482129437569682456332753 197611597078177261842249565)
    ·
      refine ⟨74104348904316473190843587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197611597078177261842249565 74104348904316473190843587)
      ·
        refine ⟨111156523356474709786265381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74104348904316473190843587 111156523356474709786265381)
        ·
          refine ⟨20841848129339008084924759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111156523356474709786265381 20841848129339008084924759)
          ·
            refine ⟨31262772194008512127387139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20841848129339008084924759 31262772194008512127387139)
            ·
              refine ⟨46894158291012768191080709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31262772194008512127387139 46894158291012768191080709)
              ·
                refine ⟨8792654679564894035827633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46894158291012768191080709 8792654679564894035827633)
                ·
                  refine ⟨6594491009673670526870725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8792654679564894035827633 6594491009673670526870725)
                  ·
                    refine ⟨1236467064313813223788261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6594491009673670526870725 1236467064313813223788261)
                    ·
                      rfl

theorem cell23_7224033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_7224033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224033 prefixEnd_7224033 := by exact prefixLift 7224033
  have htrace : WordTrace (prefixWord ++ tailWord_7224033) baseStart_7224033 baseEnd_7224033 := by
    simpa [prefixWord, tailWord_7224033, baseEnd_7224033] using wordTrace_append hprefix tailTrace_7224033
  have hstable : (prefixWord ++ tailWord_7224033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224033).length < 2 ^ (prefixWord ++ tailWord_7224033).sum := by decide
  have hdescent : baseEnd_7224033 < baseStart_7224033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224046 : List Nat := [4, 1, 2, 1, 1, 3, 3, 8]
def baseStart_7224046 : Nat := 118140960795 + 7224046 * 2 ^ 59
def prefixEnd_7224046 : Nat := 4983230072969 + 3 ^ 40 * 7224046 * 2
def baseEnd_7224046 : Nat := 137385476599627708166749

theorem tailTrace_7224046 : CollatzResearch.WordTrace tailWord_7224046 prefixEnd_7224046 137385476599627708166749 := by
  unfold tailWord_7224046
  simp only [CollatzResearch.WordTrace]
  refine ⟨32935325448315323209569499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175655069057681723784370661 32935325448315323209569499)
  ·
    refine ⟨49402988172472984814354249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32935325448315323209569499 49402988172472984814354249)
    ·
      refine ⟨37052241129354738610765687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49402988172472984814354249 37052241129354738610765687)
      ·
        refine ⟨55578361694032107916148531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37052241129354738610765687 55578361694032107916148531)
        ·
          refine ⟨83367542541048161874222797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55578361694032107916148531 83367542541048161874222797)
          ·
            refine ⟨31262828452893060702833549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83367542541048161874222797 31262828452893060702833549)
            ·
              refine ⟨11723560669834897763562581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31262828452893060702833549 11723560669834897763562581)
              ·
                refine ⟨137385476599627708166749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11723560669834897763562581 137385476599627708166749)
                ·
                  rfl

theorem cell23_7224046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 8].length) (baseStart_7224046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224046 prefixEnd_7224046 := by exact prefixLift 7224046
  have htrace : WordTrace (prefixWord ++ tailWord_7224046) baseStart_7224046 baseEnd_7224046 := by
    simpa [prefixWord, tailWord_7224046, baseEnd_7224046] using wordTrace_append hprefix tailTrace_7224046
  have hstable : (prefixWord ++ tailWord_7224046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224046).length < 2 ^ (prefixWord ++ tailWord_7224046).sum := by decide
  have hdescent : baseEnd_7224046 < baseStart_7224046 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224117 : List Nat := [1, 3, 3, 1, 3, 2, 2, 2, 1, 3, 2]
def baseStart_7224117 : Nat := 118140960795 + 7224117 * 2 ^ 59
def prefixEnd_7224117 : Nat := 4983230072969 + 3 ^ 40 * 7224117 * 2
def baseEnd_7224117 : Nat := 3709444325316417342714397

theorem tailTrace_7224117 : CollatzResearch.WordTrace tailWord_7224117 prefixEnd_7224117 3709444325316417342714397 := by
  unfold tailWord_7224117
  simp only [CollatzResearch.WordTrace]
  refine ⟨263485193169265364802390605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175656795446176909868260403 263485193169265364802390605)
  ·
    refine ⟨98806947438474511800896477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263485193169265364802390605 98806947438474511800896477)
    ·
      refine ⟨37052605289427941925336179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98806947438474511800896477 37052605289427941925336179)
      ·
        refine ⟨55578907934141912888004269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37052605289427941925336179 55578907934141912888004269)
        ·
          refine ⟨20842090475303217333001601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55578907934141912888004269 20842090475303217333001601)
          ·
            refine ⟨15631567856477412999751201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20842090475303217333001601 15631567856477412999751201)
            ·
              refine ⟨11723675892358059749813401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15631567856477412999751201 11723675892358059749813401)
              ·
                refine ⟨8792756919268544812360051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11723675892358059749813401 8792756919268544812360051)
                ·
                  refine ⟨13189135378902817218540077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8792756919268544812360051 13189135378902817218540077)
                  ·
                    refine ⟨4945925767088556456952529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13189135378902817218540077 4945925767088556456952529)
                    ·
                      refine ⟨3709444325316417342714397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4945925767088556456952529 3709444325316417342714397)
                      ·
                        rfl

theorem cell23_7224117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_7224117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224117 prefixEnd_7224117 := by exact prefixLift 7224117
  have htrace : WordTrace (prefixWord ++ tailWord_7224117) baseStart_7224117 baseEnd_7224117 := by
    simpa [prefixWord, tailWord_7224117, baseEnd_7224117] using wordTrace_append hprefix tailTrace_7224117
  have hstable : (prefixWord ++ tailWord_7224117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224117).length < 2 ^ (prefixWord ++ tailWord_7224117).sum := by decide
  have hdescent : baseEnd_7224117 < baseStart_7224117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224146 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7]
def baseStart_7224146 : Nat := 118140960795 + 7224146 * 2 ^ 59
def prefixEnd_7224146 : Nat := 4983230072969 + 3 ^ 40 * 7224146 * 2
def baseEnd_7224146 : Nat := 3709459216255397729251763

theorem tailTrace_7224146 : CollatzResearch.WordTrace tailWord_7224146 prefixEnd_7224146 3709459216255397729251763 := by
  unfold tailWord_7224146
  simp only [CollatzResearch.WordTrace]
  refine ⟨65871562721540075688799073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175657500590773535170130861 65871562721540075688799073)
  ·
    refine ⟨49403672041155056766599305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65871562721540075688799073 49403672041155056766599305)
    ·
      refine ⟨37052754030866292574949479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49403672041155056766599305 37052754030866292574949479)
      ·
        refine ⟨55579131046299438862424219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37052754030866292574949479 55579131046299438862424219)
        ·
          refine ⟨83368696569449158293636329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55579131046299438862424219 83368696569449158293636329)
          ·
            refine ⟨62526522427086868720227247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83368696569449158293636329 62526522427086868720227247)
            ·
              refine ⟨93789783640630303080340871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62526522427086868720227247 93789783640630303080340871)
              ·
                refine ⟨140684675460945454620511307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93789783640630303080340871 140684675460945454620511307)
                ·
                  refine ⟨211027013191418181930766961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140684675460945454620511307 211027013191418181930766961)
                  ·
                    refine ⟨158270259893563636448075221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 211027013191418181930766961 158270259893563636448075221)
                    ·
                      refine ⟨3709459216255397729251763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 158270259893563636448075221 3709459216255397729251763)
                      ·
                        rfl

theorem cell23_7224146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_7224146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224146 prefixEnd_7224146 := by exact prefixLift 7224146
  have htrace : WordTrace (prefixWord ++ tailWord_7224146) baseStart_7224146 baseEnd_7224146 := by
    simpa [prefixWord, tailWord_7224146, baseEnd_7224146] using wordTrace_append hprefix tailTrace_7224146
  have hstable : (prefixWord ++ tailWord_7224146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224146).length < 2 ^ (prefixWord ++ tailWord_7224146).sum := by decide
  have hdescent : baseEnd_7224146 < baseStart_7224146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224153 : List Nat := [1, 2, 1, 2, 2, 6, 1, 1, 7]
def baseStart_7224153 : Nat := 118140960795 + 7224153 * 2 ^ 59
def prefixEnd_7224153 : Nat := 4983230072969 + 3 ^ 40 * 7224153 * 2
def baseEnd_7224153 : Nat := 412162534513331022429359

theorem tailTrace_7224153 : CollatzResearch.WordTrace tailWord_7224153 prefixEnd_7224153 412162534513331022429359 := by
  unfold tailWord_7224153
  simp only [CollatzResearch.WordTrace]
  refine ⟨263486506197134942950701113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175657670798089961967134075 263486506197134942950701113)
  ·
    refine ⟨197614879647851207213025835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263486506197134942950701113 197614879647851207213025835)
    ·
      refine ⟨296422319471776810819538753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197614879647851207213025835 296422319471776810819538753)
      ·
        refine ⟨222316739603832608114654065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296422319471776810819538753 222316739603832608114654065)
        ·
          refine ⟨166737554702874456085990549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222316739603832608114654065 166737554702874456085990549)
          ·
            refine ⟨7815822876697240129030807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 166737554702874456085990549 7815822876697240129030807)
            ·
              refine ⟨11723734315045860193546211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7815822876697240129030807 11723734315045860193546211)
              ·
                refine ⟨17585601472568790290319317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11723734315045860193546211 17585601472568790290319317)
                ·
                  refine ⟨412162534513331022429359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17585601472568790290319317 412162534513331022429359)
                  ·
                    rfl

theorem cell23_7224153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 7].length) (baseStart_7224153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224153 prefixEnd_7224153 := by exact prefixLift 7224153
  have htrace : WordTrace (prefixWord ++ tailWord_7224153) baseStart_7224153 baseEnd_7224153 := by
    simpa [prefixWord, tailWord_7224153, baseEnd_7224153] using wordTrace_append hprefix tailTrace_7224153
  have hstable : (prefixWord ++ tailWord_7224153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224153).length < 2 ^ (prefixWord ++ tailWord_7224153).sum := by decide
  have hdescent : baseEnd_7224153 < baseStart_7224153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224164 : List Nat := [2, 3, 1, 1, 4, 1, 4, 1, 2, 2, 2]
def baseStart_7224164 : Nat := 118140960795 + 7224164 * 2 ^ 59
def prefixEnd_7224164 : Nat := 4983230072969 + 3 ^ 40 * 7224164 * 2
def baseEnd_7224164 : Nat := 3709468458907178658826681

theorem tailTrace_7224164 : CollatzResearch.WordTrace tailWord_7224164 prefixEnd_7224164 3709468458907178658826681 := by
  unfold tailWord_7224164
  simp only [CollatzResearch.WordTrace]
  refine ⟨131743453700047545914675773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175657938266730061219567697 131743453700047545914675773)
  ·
    refine ⟨49403795137517829718003415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131743453700047545914675773 49403795137517829718003415)
    ·
      refine ⟨74105692706276744577005123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49403795137517829718003415 74105692706276744577005123)
      ·
        refine ⟨111158539059415116865507685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74105692706276744577005123 111158539059415116865507685)
        ·
          refine ⟨20842226073640334412282691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111158539059415116865507685 20842226073640334412282691)
          ·
            refine ⟨31263339110460501618424037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20842226073640334412282691 31263339110460501618424037)
            ·
              refine ⟨5861876083211344053454507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31263339110460501618424037 5861876083211344053454507)
              ·
                refine ⟨8792814124817016080181761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5861876083211344053454507 8792814124817016080181761)
                ·
                  refine ⟨6594610593612762060136321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8792814124817016080181761 6594610593612762060136321)
                  ·
                    refine ⟨4945957945209571545102241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6594610593612762060136321 4945957945209571545102241)
                    ·
                      refine ⟨3709468458907178658826681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4945957945209571545102241 3709468458907178658826681)
                      ·
                        rfl

theorem cell23_7224164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 2, 2, 2].length) (baseStart_7224164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224164 prefixEnd_7224164 := by exact prefixLift 7224164
  have htrace : WordTrace (prefixWord ++ tailWord_7224164) baseStart_7224164 baseEnd_7224164 := by
    simpa [prefixWord, tailWord_7224164, baseEnd_7224164] using wordTrace_append hprefix tailTrace_7224164
  have hstable : (prefixWord ++ tailWord_7224164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224164).length < 2 ^ (prefixWord ++ tailWord_7224164).sum := by decide
  have hdescent : baseEnd_7224164 < baseStart_7224164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224203 : List Nat := [1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 4]
def baseStart_7224203 : Nat := 118140960795 + 7224203 * 2 ^ 59
def prefixEnd_7224203 : Nat := 4983230072969 + 3 ^ 40 * 7224203 * 2
def baseEnd_7224203 : Nat := 3709488484652704006239001

theorem tailTrace_7224203 : CollatzResearch.WordTrace tailWord_7224203 prefixEnd_7224203 3709488484652704006239001 := by
  unfold tailWord_7224203
  simp only [CollatzResearch.WordTrace]
  refine ⟨263488329846953801490021263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175658886564635867660014175 263488329846953801490021263)
  ·
    refine ⟨395232494770430702235031895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263488329846953801490021263 395232494770430702235031895)
    ·
      refine ⟨592848742155646053352547843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395232494770430702235031895 592848742155646053352547843)
      ·
        refine ⟨889273113233469080028821765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 592848742155646053352547843 889273113233469080028821765)
        ·
          refine ⟨166738708731275452505404081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 889273113233469080028821765 166738708731275452505404081)
          ·
            refine ⟨125054031548456589379053061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166738708731275452505404081 125054031548456589379053061)
            ·
              refine ⟨23447630915335610508572449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125054031548456589379053061 23447630915335610508572449)
              ·
                refine ⟨17585723186501707881429337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23447630915335610508572449 17585723186501707881429337)
                ·
                  refine ⟨13189292389876280911072003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17585723186501707881429337 13189292389876280911072003)
                  ·
                    refine ⟨19783938584814421366608005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13189292389876280911072003 19783938584814421366608005)
                    ·
                      refine ⟨3709488484652704006239001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19783938584814421366608005 3709488484652704006239001)
                      ·
                        rfl

theorem cell23_7224203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 4].length) (baseStart_7224203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224203 prefixEnd_7224203 := by exact prefixLift 7224203
  have htrace : WordTrace (prefixWord ++ tailWord_7224203) baseStart_7224203 baseEnd_7224203 := by
    simpa [prefixWord, tailWord_7224203, baseEnd_7224203] using wordTrace_append hprefix tailTrace_7224203
  have hstable : (prefixWord ++ tailWord_7224203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224203).length < 2 ^ (prefixWord ++ tailWord_7224203).sum := by decide
  have hdescent : baseEnd_7224203 < baseStart_7224203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224214 : List Nat := [5, 3, 1, 1, 1, 2, 1, 1, 2, 3, 3]
def baseStart_7224214 : Nat := 118140960795 + 7224214 * 2 ^ 59
def prefixEnd_7224214 : Nat := 4983230072969 + 3 ^ 40 * 7224214 * 2
def baseEnd_7224214 : Nat := 3709494132939903463201451

theorem tailTrace_7224214 : CollatzResearch.WordTrace tailWord_7224214 prefixEnd_7224214 3709494132939903463201451 := by
  unfold tailWord_7224214
  simp only [CollatzResearch.WordTrace]
  refine ⟨16468045690619621898041981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175659154033275966912447797 16468045690619621898041981)
  ·
    refine ⟨6175517133982358211765743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16468045690619621898041981 6175517133982358211765743)
    ·
      refine ⟨9263275700973537317648615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6175517133982358211765743 9263275700973537317648615)
      ·
        refine ⟨13894913551460305976472923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9263275700973537317648615 13894913551460305976472923)
        ·
          refine ⟨20842370327190458964709385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13894913551460305976472923 20842370327190458964709385)
          ·
            refine ⟨15631777745392844223532039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20842370327190458964709385 15631777745392844223532039)
            ·
              refine ⟨23447666618089266335298059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15631777745392844223532039 23447666618089266335298059)
              ·
                refine ⟨35171499927133899502947089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23447666618089266335298059 35171499927133899502947089)
                ·
                  refine ⟨26378624945350424627210317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35171499927133899502947089 26378624945350424627210317)
                  ·
                    refine ⟨9891984354506409235203869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26378624945350424627210317 9891984354506409235203869)
                    ·
                      refine ⟨3709494132939903463201451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9891984354506409235203869 3709494132939903463201451)
                      ·
                        rfl

theorem cell23_7224214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_7224214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224214 prefixEnd_7224214 := by exact prefixLift 7224214
  have htrace : WordTrace (prefixWord ++ tailWord_7224214) baseStart_7224214 baseEnd_7224214 := by
    simpa [prefixWord, tailWord_7224214, baseEnd_7224214] using wordTrace_append hprefix tailTrace_7224214
  have hstable : (prefixWord ++ tailWord_7224214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224214).length < 2 ^ (prefixWord ++ tailWord_7224214).sum := by decide
  have hdescent : baseEnd_7224214 < baseStart_7224214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224237 : List Nat := [1, 5, 2, 3, 1, 1, 1, 1, 1, 3, 4]
def baseStart_7224237 : Nat := 118140960795 + 7224237 * 2 ^ 59
def prefixEnd_7224237 : Nat := 4983230072969 + 3 ^ 40 * 7224237 * 2
def baseEnd_7224237 : Nat := 3709505942994956873213845

theorem tailTrace_7224237 : CollatzResearch.WordTrace tailWord_7224237 prefixEnd_7224237 3709505942994956873213845 := by
  unfold tailWord_7224237
  simp only [CollatzResearch.WordTrace]
  refine ⟨263489569928830625296758965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175659713285887083531172643 263489569928830625296758965)
  ·
    refine ⟨24702147180827871121571153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 263489569928830625296758965 24702147180827871121571153)
    ·
      refine ⟨18526610385620903341178365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24702147180827871121571153 18526610385620903341178365)
      ·
        refine ⟨6947478894607838752941887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18526610385620903341178365 6947478894607838752941887)
        ·
          refine ⟨10421218341911758129412831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6947478894607838752941887 10421218341911758129412831)
          ·
            refine ⟨15631827512867637194119247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10421218341911758129412831 15631827512867637194119247)
            ·
              refine ⟨23447741269301455791178871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15631827512867637194119247 23447741269301455791178871)
              ·
                refine ⟨35171611903952183686768307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23447741269301455791178871 35171611903952183686768307)
                ·
                  refine ⟨52757417855928275530152461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35171611903952183686768307 52757417855928275530152461)
                  ·
                    refine ⟨19784031695973103323807173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52757417855928275530152461 19784031695973103323807173)
                    ·
                      refine ⟨3709505942994956873213845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19784031695973103323807173 3709505942994956873213845)
                      ·
                        rfl

theorem cell23_7224237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_7224237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224237 prefixEnd_7224237 := by exact prefixLift 7224237
  have htrace : WordTrace (prefixWord ++ tailWord_7224237) baseStart_7224237 baseEnd_7224237 := by
    simpa [prefixWord, tailWord_7224237, baseEnd_7224237] using wordTrace_append hprefix tailTrace_7224237
  have hstable : (prefixWord ++ tailWord_7224237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224237).length < 2 ^ (prefixWord ++ tailWord_7224237).sum := by decide
  have hdescent : baseEnd_7224237 < baseStart_7224237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224277 : List Nat := [1, 3, 2, 3, 3, 1, 3, 1, 6]
def baseStart_7224277 : Nat := 118140960795 + 7224277 * 2 ^ 59
def prefixEnd_7224277 : Nat := 4983230072969 + 3 ^ 40 * 7224277 * 2
def baseEnd_7224277 : Nat := 412169609135681857412629

theorem tailTrace_7224277 : CollatzResearch.WordTrace tailWord_7224277 prefixEnd_7224277 412169609135681857412629 := by
  unfold tailWord_7224277
  simp only [CollatzResearch.WordTrace]
  refine ⟨263491028848685712128215085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175660685899123808085476723 263491028848685712128215085)
  ·
    refine ⟨98809135818257142048080657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263491028848685712128215085 98809135818257142048080657)
    ·
      refine ⟨74106851863692856536060493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98809135818257142048080657 74106851863692856536060493)
      ·
        refine ⟨27790069448884821201022685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74106851863692856536060493 27790069448884821201022685)
        ·
          refine ⟨10421276043331807950383507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27790069448884821201022685 10421276043331807950383507)
          ·
            refine ⟨15631914064997711925575261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10421276043331807950383507 15631914064997711925575261)
            ·
              refine ⟨5861967774374141972090723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15631914064997711925575261 5861967774374141972090723)
              ·
                refine ⟨8792951661561212958136085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5861967774374141972090723 8792951661561212958136085)
                ·
                  refine ⟨412169609135681857412629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8792951661561212958136085 412169609135681857412629)
                  ·
                    rfl

theorem cell23_7224277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 6].length) (baseStart_7224277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224277 prefixEnd_7224277 := by exact prefixLift 7224277
  have htrace : WordTrace (prefixWord ++ tailWord_7224277) baseStart_7224277 baseEnd_7224277 := by
    simpa [prefixWord, tailWord_7224277, baseEnd_7224277] using wordTrace_append hprefix tailTrace_7224277
  have hstable : (prefixWord ++ tailWord_7224277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224277).length < 2 ^ (prefixWord ++ tailWord_7224277).sum := by decide
  have hdescent : baseEnd_7224277 < baseStart_7224277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224280 : List Nat := [2, 1, 2, 2, 2, 3, 1, 2, 1, 5, 2]
def baseStart_7224280 : Nat := 118140960795 + 7224280 * 2 ^ 59
def prefixEnd_7224280 : Nat := 4983230072969 + 3 ^ 40 * 7224280 * 2
def baseEnd_7224280 : Nat := 3709528022663100204976147

theorem tailTrace_7224280 : CollatzResearch.WordTrace tailWord_7224280 prefixEnd_7224280 3709528022663100204976147 := by
  unfold tailWord_7224280
  simp only [CollatzResearch.WordTrace]
  refine ⟨131745569133837421820287147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175660758845116562427049529 131745569133837421820287147)
  ·
    refine ⟨197618353700756132730430721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131745569133837421820287147 197618353700756132730430721)
    ·
      refine ⟨148213765275567099547823041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197618353700756132730430721 148213765275567099547823041)
      ·
        refine ⟨111160323956675324660867281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148213765275567099547823041 111160323956675324660867281)
        ·
          refine ⟨83370242967506493495650461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111160323956675324660867281 83370242967506493495650461)
          ·
            refine ⟨31263841112814935060868923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83370242967506493495650461 31263841112814935060868923)
            ·
              refine ⟨46895761669222402591303385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31263841112814935060868923 46895761669222402591303385)
              ·
                refine ⟨35171821251916801943477539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46895761669222402591303385 35171821251916801943477539)
                ·
                  refine ⟨52757731877875202915216309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35171821251916801943477539 52757731877875202915216309)
                  ·
                    refine ⟨4946037363550800273301529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52757731877875202915216309 4946037363550800273301529)
                    ·
                      refine ⟨3709528022663100204976147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4946037363550800273301529 3709528022663100204976147)
                      ·
                        rfl

theorem cell23_7224280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 1, 5, 2].length) (baseStart_7224280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224280 prefixEnd_7224280 := by exact prefixLift 7224280
  have htrace : WordTrace (prefixWord ++ tailWord_7224280) baseStart_7224280 baseEnd_7224280 := by
    simpa [prefixWord, tailWord_7224280, baseEnd_7224280] using wordTrace_append hprefix tailTrace_7224280
  have hstable : (prefixWord ++ tailWord_7224280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224280).length < 2 ^ (prefixWord ++ tailWord_7224280).sum := by decide
  have hdescent : baseEnd_7224280 < baseStart_7224280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224308 : List Nat := [2, 6, 2, 1, 1, 1, 1, 2, 2, 2, 3]
def baseStart_7224308 : Nat := 118140960795 + 7224308 * 2 ^ 59
def prefixEnd_7224308 : Nat := 4983230072969 + 3 ^ 40 * 7224308 * 2
def baseEnd_7224308 : Nat := 3709542400121426095426019

theorem tailTrace_7224308 : CollatzResearch.WordTrace tailWord_7224308 prefixEnd_7224308 3709542400121426095426019 := by
  unfold tailWord_7224308
  simp only [CollatzResearch.WordTrace]
  refine ⟨131746079755786702211296789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175661439674382269615062385 131746079755786702211296789)
  ·
    refine ⟨6175597488552501666154537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 131746079755786702211296789 6175597488552501666154537)
    ·
      refine ⟨4631698116414376249615903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6175597488552501666154537 4631698116414376249615903)
      ·
        refine ⟨6947547174621564374423855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4631698116414376249615903 6947547174621564374423855)
        ·
          refine ⟨10421320761932346561635783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6947547174621564374423855 10421320761932346561635783)
          ·
            refine ⟨15631981142898519842453675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10421320761932346561635783 15631981142898519842453675)
            ·
              refine ⟨23447971714347779763680513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15631981142898519842453675 23447971714347779763680513)
              ·
                refine ⟨17585978785760834822760385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23447971714347779763680513 17585978785760834822760385)
                ·
                  refine ⟨13189484089320626117070289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17585978785760834822760385 13189484089320626117070289)
                  ·
                    refine ⟨9892113066990469587802717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13189484089320626117070289 9892113066990469587802717)
                    ·
                      refine ⟨3709542400121426095426019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9892113066990469587802717 3709542400121426095426019)
                      ·
                        rfl

theorem cell23_7224308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_7224308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224308 prefixEnd_7224308 := by exact prefixLift 7224308
  have htrace : WordTrace (prefixWord ++ tailWord_7224308) baseStart_7224308 baseEnd_7224308 := by
    simpa [prefixWord, tailWord_7224308, baseEnd_7224308] using wordTrace_append hprefix tailTrace_7224308
  have hstable : (prefixWord ++ tailWord_7224308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224308).length < 2 ^ (prefixWord ++ tailWord_7224308).sum := by decide
  have hdescent : baseEnd_7224308 < baseStart_7224308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224321 : List Nat := [1, 2, 4, 1, 2, 3, 3, 2, 1, 1, 3]
def baseStart_7224321 : Nat := 118140960795 + 7224321 * 2 ^ 59
def prefixEnd_7224321 : Nat := 4983230072969 + 3 ^ 40 * 7224321 * 2
def baseEnd_7224321 : Nat := 3709549075369934544563459

theorem tailTrace_7224321 : CollatzResearch.WordTrace tailWord_7224321 prefixEnd_7224321 3709549075369934544563459 := by
  unfold tailWord_7224321
  simp only [CollatzResearch.WordTrace]
  refine ⟨263492633660526307642816817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175661755773684205095211211 263492633660526307642816817)
  ·
    refine ⟨197619475245394730732112613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263492633660526307642816817 197619475245394730732112613)
    ·
      refine ⟨37053651608511512012271115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197619475245394730732112613 37053651608511512012271115)
      ·
        refine ⟨55580477412767268018406673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37053651608511512012271115 55580477412767268018406673)
        ·
          refine ⟨41685358059575451013805005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55580477412767268018406673 41685358059575451013805005)
          ·
            refine ⟨15632009272340794130176877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41685358059575451013805005 15632009272340794130176877)
            ·
              refine ⟨5862003477127797798816329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15632009272340794130176877 5862003477127797798816329)
              ·
                refine ⟨4396502607845848349112247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5862003477127797798816329 4396502607845848349112247)
                ·
                  refine ⟨6594753911768772523668371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4396502607845848349112247 6594753911768772523668371)
                  ·
                    refine ⟨9892130867653158785502557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6594753911768772523668371 9892130867653158785502557)
                    ·
                      refine ⟨3709549075369934544563459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9892130867653158785502557 3709549075369934544563459)
                      ·
                        rfl

theorem cell23_7224321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_7224321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224321 prefixEnd_7224321 := by exact prefixLift 7224321
  have htrace : WordTrace (prefixWord ++ tailWord_7224321) baseStart_7224321 baseEnd_7224321 := by
    simpa [prefixWord, tailWord_7224321, baseEnd_7224321] using wordTrace_append hprefix tailTrace_7224321
  have hstable : (prefixWord ++ tailWord_7224321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224321).length < 2 ^ (prefixWord ++ tailWord_7224321).sum := by decide
  have hdescent : baseEnd_7224321 < baseStart_7224321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224330 : List Nat := [3, 1, 2, 2, 3, 1, 2, 2, 1, 1, 5]
def baseStart_7224330 : Nat := 118140960795 + 7224330 * 2 ^ 59
def prefixEnd_7224330 : Nat := 4983230072969 + 3 ^ 40 * 7224330 * 2
def baseEnd_7224330 : Nat := 3709553696695825009350917

theorem tailTrace_7224330 : CollatzResearch.WordTrace tailWord_7224330 prefixEnd_7224330 3709553696695825009350917 := by
  unfold tailWord_7224330
  simp only [CollatzResearch.WordTrace]
  refine ⟨65873240479373425544973611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175661974611662468119929629 65873240479373425544973611)
  ·
    refine ⟨98809860719060138317460417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65873240479373425544973611 98809860719060138317460417)
    ·
      refine ⟨74107395539295103738095313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98809860719060138317460417 74107395539295103738095313)
      ·
        refine ⟨55580546654471327803571485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74107395539295103738095313 55580546654471327803571485)
        ·
          refine ⟨20842704995426747926339307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55580546654471327803571485 20842704995426747926339307)
          ·
            refine ⟨31264057493140121889508961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20842704995426747926339307 31264057493140121889508961)
            ·
              refine ⟨23448043119855091417131721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31264057493140121889508961 23448043119855091417131721)
              ·
                refine ⟨17586032339891318562848791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23448043119855091417131721 17586032339891318562848791)
                ·
                  refine ⟨26379048509836977844273187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17586032339891318562848791 26379048509836977844273187)
                  ·
                    refine ⟨39568572764755466766409781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26379048509836977844273187 39568572764755466766409781)
                    ·
                      refine ⟨3709553696695825009350917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39568572764755466766409781 3709553696695825009350917)
                      ·
                        rfl

theorem cell23_7224330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_7224330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224330 prefixEnd_7224330 := by exact prefixLift 7224330
  have htrace : WordTrace (prefixWord ++ tailWord_7224330) baseStart_7224330 baseEnd_7224330 := by
    simpa [prefixWord, tailWord_7224330, baseEnd_7224330] using wordTrace_append hprefix tailTrace_7224330
  have hstable : (prefixWord ++ tailWord_7224330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224330).length < 2 ^ (prefixWord ++ tailWord_7224330).sum := by decide
  have hdescent : baseEnd_7224330 < baseStart_7224330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224417 : List Nat := [1, 2, 3, 1, 1, 2, 4, 2, 1, 4, 2]
def baseStart_7224417 : Nat := 118140960795 + 7224417 * 2 ^ 59
def prefixEnd_7224417 : Nat := 4983230072969 + 3 ^ 40 * 7224417 * 2
def baseEnd_7224417 : Nat := 3709598369512766168963017

theorem tailTrace_7224417 : CollatzResearch.WordTrace tailWord_7224417 prefixEnd_7224417 3709598369512766168963017 := by
  unfold tailWord_7224417
  simp only [CollatzResearch.WordTrace]
  refine ⟨263496135068178516038311505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175664090045452344025541003 263496135068178516038311505)
  ·
    refine ⟨197622101301133887028733629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263496135068178516038311505 197622101301133887028733629)
    ·
      refine ⟨74108287987925207635775111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197622101301133887028733629 74108287987925207635775111)
      ·
        refine ⟨111162431981887811453662667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74108287987925207635775111 111162431981887811453662667)
        ·
          refine ⟨166743647972831717180494001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111162431981887811453662667 166743647972831717180494001)
          ·
            refine ⟨125057735979623787885370501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166743647972831717180494001 125057735979623787885370501)
            ·
              refine ⟨23448325496179460228506969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125057735979623787885370501 23448325496179460228506969)
              ·
                refine ⟨17586244122134595171380227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23448325496179460228506969 17586244122134595171380227)
                ·
                  refine ⟨26379366183201892757070341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17586244122134595171380227 26379366183201892757070341)
                  ·
                    refine ⟨4946131159350354891950689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26379366183201892757070341 4946131159350354891950689)
                    ·
                      refine ⟨3709598369512766168963017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4946131159350354891950689 3709598369512766168963017)
                      ·
                        rfl

theorem cell23_7224417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 4, 2].length) (baseStart_7224417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224417 prefixEnd_7224417 := by exact prefixLift 7224417
  have htrace : WordTrace (prefixWord ++ tailWord_7224417) baseStart_7224417 baseEnd_7224417 := by
    simpa [prefixWord, tailWord_7224417, baseEnd_7224417] using wordTrace_append hprefix tailTrace_7224417
  have hstable : (prefixWord ++ tailWord_7224417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224417).length < 2 ^ (prefixWord ++ tailWord_7224417).sum := by decide
  have hdescent : baseEnd_7224417 < baseStart_7224417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224433 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 1, 1, 9]
def baseStart_7224433 : Nat := 118140960795 + 7224433 * 2 ^ 59
def prefixEnd_7224433 : Nat := 4983230072969 + 3 ^ 40 * 7224433 * 2
def baseEnd_7224433 : Nat := 3709606585203238106362943

theorem tailTrace_7224433 : CollatzResearch.WordTrace tailWord_7224433 prefixEnd_7224433 3709606585203238106362943 := by
  unfold tailWord_7224433
  simp only [CollatzResearch.WordTrace]
  refine ⟨263496718636120550770893953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175664479090747033847262635 263496718636120550770893953)
  ·
    refine ⟨197622538977090413078170465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263496718636120550770893953 197622538977090413078170465)
    ·
      refine ⟨148216904232817809808627849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197622538977090413078170465 148216904232817809808627849)
      ·
        refine ⟨111162678174613357356470887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148216904232817809808627849 111162678174613357356470887)
        ·
          refine ⟨166744017261920036034706331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111162678174613357356470887 166744017261920036034706331)
          ·
            refine ⟨250116025892880054052059497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166744017261920036034706331 250116025892880054052059497)
            ·
              refine ⟨187587019419660040539044623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250116025892880054052059497 187587019419660040539044623)
              ·
                refine ⟨281380529129490060808566935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187587019419660040539044623 281380529129490060808566935)
                ·
                  refine ⟨422070793694235091212850403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 281380529129490060808566935 422070793694235091212850403)
                  ·
                    refine ⟨633106190541352636819275605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 422070793694235091212850403 633106190541352636819275605)
                    ·
                      refine ⟨3709606585203238106362943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 633106190541352636819275605 3709606585203238106362943)
                      ·
                        rfl

theorem cell23_7224433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_7224433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224433 prefixEnd_7224433 := by exact prefixLift 7224433
  have htrace : WordTrace (prefixWord ++ tailWord_7224433) baseStart_7224433 baseEnd_7224433 := by
    simpa [prefixWord, tailWord_7224433, baseEnd_7224433] using wordTrace_append hprefix tailTrace_7224433
  have hstable : (prefixWord ++ tailWord_7224433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224433).length < 2 ^ (prefixWord ++ tailWord_7224433).sum := by decide
  have hdescent : baseEnd_7224433 < baseStart_7224433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224434 : List Nat := [3, 2, 1, 2, 2, 1, 3, 1, 4, 2, 2]
def baseStart_7224434 : Nat := 118140960795 + 7224434 * 2 ^ 59
def prefixEnd_7224434 : Nat := 4983230072969 + 3 ^ 40 * 7224434 * 2
def baseEnd_7224434 : Nat := 3709607098683892602450439

theorem tailTrace_7224434 : CollatzResearch.WordTrace tailWord_7224434 prefixEnd_7224434 3709607098683892602450439 := by
  unfold tailWord_7224434
  simp only [CollatzResearch.WordTrace]
  refine ⟨65874188777279231985420089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175664503406077951961120237 65874188777279231985420089)
  ·
    refine ⟨49405641582959423989065067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65874188777279231985420089 49405641582959423989065067)
    ·
      refine ⟨74108462374439135983597601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49405641582959423989065067 74108462374439135983597601)
      ·
        refine ⟨55581346780829351987698201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74108462374439135983597601 55581346780829351987698201)
        ·
          refine ⟨41686010085622013990773651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55581346780829351987698201 41686010085622013990773651)
          ·
            refine ⟨62529015128433020986160477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41686010085622013990773651 62529015128433020986160477)
            ·
              refine ⟨23448380673162382869810179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62529015128433020986160477 23448380673162382869810179)
              ·
                refine ⟨35172571009743574304715269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23448380673162382869810179 35172571009743574304715269)
                ·
                  refine ⟨6594857064326920182134113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35172571009743574304715269 6594857064326920182134113)
                  ·
                    refine ⟨4946142798245190136600585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6594857064326920182134113 4946142798245190136600585)
                    ·
                      refine ⟨3709607098683892602450439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4946142798245190136600585 3709607098683892602450439)
                      ·
                        rfl

theorem cell23_7224434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_7224434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224434 prefixEnd_7224434 := by exact prefixLift 7224434
  have htrace : WordTrace (prefixWord ++ tailWord_7224434) baseStart_7224434 baseEnd_7224434 := by
    simpa [prefixWord, tailWord_7224434, baseEnd_7224434] using wordTrace_append hprefix tailTrace_7224434
  have hstable : (prefixWord ++ tailWord_7224434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224434).length < 2 ^ (prefixWord ++ tailWord_7224434).sum := by decide
  have hdescent : baseEnd_7224434 < baseStart_7224434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224451 : List Nat := [1, 1, 1, 3, 3, 2, 5, 1, 2, 2, 2]
def baseStart_7224451 : Nat := 118140960795 + 7224451 * 2 ^ 59
def prefixEnd_7224451 : Nat := 4983230072969 + 3 ^ 40 * 7224451 * 2
def baseEnd_7224451 : Nat := 3709615827855019035937861

theorem tailTrace_7224451 : CollatzResearch.WordTrace tailWord_7224451 prefixEnd_7224451 3709615827855019035937861 := by
  unfold tailWord_7224451
  simp only [CollatzResearch.WordTrace]
  refine ⟨263497375150055339845049207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175664916766703559896699471 263497375150055339845049207)
  ·
    refine ⟨395246062725083009767573811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263497375150055339845049207 395246062725083009767573811)
    ·
      refine ⟨592869094087624514651360717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395246062725083009767573811 592869094087624514651360717)
      ·
        refine ⟨222325910282859192994260269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 592869094087624514651360717 222325910282859192994260269)
        ·
          refine ⟨83372216356072197372847601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222325910282859192994260269 83372216356072197372847601)
          ·
            refine ⟨62529162267054148029635701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83372216356072197372847601 62529162267054148029635701)
            ·
              refine ⟨5862108962536326377778347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62529162267054148029635701 5862108962536326377778347)
              ·
                refine ⟨8793163443804489566667521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5862108962536326377778347 8793163443804489566667521)
                ·
                  refine ⟨6594872582853367175000641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8793163443804489566667521 6594872582853367175000641)
                  ·
                    refine ⟨4946154437140025381250481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6594872582853367175000641 4946154437140025381250481)
                    ·
                      refine ⟨3709615827855019035937861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4946154437140025381250481 3709615827855019035937861)
                      ·
                        rfl

theorem cell23_7224451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 2, 2, 2].length) (baseStart_7224451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224451 prefixEnd_7224451 := by exact prefixLift 7224451
  have htrace : WordTrace (prefixWord ++ tailWord_7224451) baseStart_7224451 baseEnd_7224451 := by
    simpa [prefixWord, tailWord_7224451, baseEnd_7224451] using wordTrace_append hprefix tailTrace_7224451
  have hstable : (prefixWord ++ tailWord_7224451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224451).length < 2 ^ (prefixWord ++ tailWord_7224451).sum := by decide
  have hdescent : baseEnd_7224451 < baseStart_7224451 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224474 : List Nat := [3, 1, 1, 5, 1, 1, 3, 3, 5]
def baseStart_7224474 : Nat := 118140960795 + 7224474 * 2 ^ 59
def prefixEnd_7224474 : Nat := 4983230072969 + 3 ^ 40 * 7224474 * 2
def baseEnd_7224474 : Nat := 412180848656674716216695

theorem tailTrace_7224474 : CollatzResearch.WordTrace tailWord_7224474 prefixEnd_7224474 412180848656674716216695 := by
  unfold tailWord_7224474
  simp only [CollatzResearch.WordTrace]
  refine ⟨65874553507243003693284119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175665476019314676515424317 65874553507243003693284119)
  ·
    refine ⟨98811830260864505539926179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65874553507243003693284119 98811830260864505539926179)
    ·
      refine ⟨148217745391296758309889269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98811830260864505539926179 148217745391296758309889269)
      ·
        refine ⟨13895413630434071091552119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148217745391296758309889269 13895413630434071091552119)
        ·
          refine ⟨20843120445651106637328179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13895413630434071091552119 20843120445651106637328179)
          ·
            refine ⟨31264680668476659955992269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20843120445651106637328179 31264680668476659955992269)
            ·
              refine ⟨11724255250678747483497101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31264680668476659955992269 11724255250678747483497101)
              ·
                refine ⟨4396595719004530306311413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11724255250678747483497101 4396595719004530306311413)
                ·
                  refine ⟨412180848656674716216695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4396595719004530306311413 412180848656674716216695)
                  ·
                    rfl

theorem cell23_7224474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 3, 5].length) (baseStart_7224474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224474 prefixEnd_7224474 := by exact prefixLift 7224474
  have htrace : WordTrace (prefixWord ++ tailWord_7224474) baseStart_7224474 baseEnd_7224474 := by
    simpa [prefixWord, tailWord_7224474, baseEnd_7224474] using wordTrace_append hprefix tailTrace_7224474
  have hstable : (prefixWord ++ tailWord_7224474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224474).length < 2 ^ (prefixWord ++ tailWord_7224474).sum := by decide
  have hdescent : baseEnd_7224474 < baseStart_7224474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224480 : List Nat := [2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 5]
def baseStart_7224480 : Nat := 118140960795 + 7224480 * 2 ^ 59
def prefixEnd_7224480 : Nat := 4983230072969 + 3 ^ 40 * 7224480 * 2
def baseEnd_7224480 : Nat := 3709630718793999422475227

theorem tailTrace_7224480 : CollatzResearch.WordTrace tailWord_7224480 prefixEnd_7224480 3709630718793999422475227 := by
  unfold tailWord_7224480
  simp only [CollatzResearch.WordTrace]
  refine ⟨131749216433475138898927447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175665621911300185198569929 131749216433475138898927447)
  ·
    refine ⟨197623824650212708348391171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131749216433475138898927447 197623824650212708348391171)
    ·
      refine ⟨296435736975319062522586757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197623824650212708348391171 296435736975319062522586757)
      ·
        refine ⟨55581700682872324222985017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 296435736975319062522586757 55581700682872324222985017)
        ·
          refine ⟨41686275512154243167238763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55581700682872324222985017 41686275512154243167238763)
          ·
            refine ⟨62529413268231364750858145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41686275512154243167238763 62529413268231364750858145)
            ·
              refine ⟨46897059951173523563143609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62529413268231364750858145 46897059951173523563143609)
              ·
                refine ⟨35172794963380142672357707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46897059951173523563143609 35172794963380142672357707)
                ·
                  refine ⟨52759192445070214008536561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35172794963380142672357707 52759192445070214008536561)
                  ·
                    refine ⟨39569394333802660506402421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52759192445070214008536561 39569394333802660506402421)
                    ·
                      refine ⟨3709630718793999422475227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39569394333802660506402421 3709630718793999422475227)
                      ·
                        rfl

theorem cell23_7224480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_7224480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224480 prefixEnd_7224480 := by exact prefixLift 7224480
  have htrace : WordTrace (prefixWord ++ tailWord_7224480) baseStart_7224480 baseEnd_7224480 := by
    simpa [prefixWord, tailWord_7224480, baseEnd_7224480] using wordTrace_append hprefix tailTrace_7224480
  have hstable : (prefixWord ++ tailWord_7224480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224480).length < 2 ^ (prefixWord ++ tailWord_7224480).sum := by decide
  have hdescent : baseEnd_7224480 < baseStart_7224480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224487 : List Nat := [1, 1, 6, 2, 1, 1, 1, 1, 4, 5]
def baseStart_7224487 : Nat := 118140960795 + 7224487 * 2 ^ 59
def prefixEnd_7224487 : Nat := 4983230072969 + 3 ^ 40 * 7224487 * 2
def baseEnd_7224487 : Nat := 1236544771052860298362565

theorem tailTrace_7224487 : CollatzResearch.WordTrace tailWord_7224487 prefixEnd_7224487 1236544771052860298362565 := by
  unfold tailWord_7224487
  simp only [CollatzResearch.WordTrace]
  refine ⟨263498688177924917993359715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175665792118616611995573143 263498688177924917993359715)
  ·
    refine ⟨395248032266887376990039573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263498688177924917993359715 395248032266887376990039573)
    ·
      refine ⟨18527251512510345796408105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 395248032266887376990039573 18527251512510345796408105)
      ·
        refine ⟨13895438634382759347306079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18527251512510345796408105 13895438634382759347306079)
        ·
          refine ⟨20843157951574139020959119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13895438634382759347306079 20843157951574139020959119)
          ·
            refine ⟨31264736927361208531438679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20843157951574139020959119 31264736927361208531438679)
            ·
              refine ⟨46897105391041812797158019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31264736927361208531438679 46897105391041812797158019)
              ·
                refine ⟨70345658086562719195737029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46897105391041812797158019 70345658086562719195737029)
                ·
                  refine ⟨13189810891230509849200693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70345658086562719195737029 13189810891230509849200693)
                  ·
                    refine ⟨1236544771052860298362565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13189810891230509849200693 1236544771052860298362565)
                    ·
                      rfl

theorem cell23_7224487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_7224487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224487 prefixEnd_7224487 := by exact prefixLift 7224487
  have htrace : WordTrace (prefixWord ++ tailWord_7224487) baseStart_7224487 baseEnd_7224487 := by
    simpa [prefixWord, tailWord_7224487, baseEnd_7224487] using wordTrace_append hprefix tailTrace_7224487
  have hstable : (prefixWord ++ tailWord_7224487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224487).length < 2 ^ (prefixWord ++ tailWord_7224487).sum := by decide
  have hdescent : baseEnd_7224487 < baseStart_7224487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224497 : List Nat := [1, 2, 2, 5, 1, 2, 1, 1, 1, 2, 5]
def baseStart_7224497 : Nat := 118140960795 + 7224497 * 2 ^ 59
def prefixEnd_7224497 : Nat := 4983230072969 + 3 ^ 40 * 7224497 * 2
def baseEnd_7224497 : Nat := 3709639447965125855962649

theorem tailTrace_7224497 : CollatzResearch.WordTrace tailWord_7224497 prefixEnd_7224497 3709639447965125855962649 := by
  unfold tailWord_7224497
  simp only [CollatzResearch.WordTrace]
  refine ⟨263499052907888689701223745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175666035271925793134149163 263499052907888689701223745)
  ·
    refine ⟨197624289680916517275917809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263499052907888689701223745 197624289680916517275917809)
    ·
      refine ⟨148218217260687387956938357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197624289680916517275917809 148218217260687387956938357)
      ·
        refine ⟨13895457868189442620962971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148218217260687387956938357 13895457868189442620962971)
        ·
          refine ⟨20843186802284163931444457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13895457868189442620962971 20843186802284163931444457)
          ·
            refine ⟨15632390101713122948583343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20843186802284163931444457 15632390101713122948583343)
            ·
              refine ⟨23448585152569684422875015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15632390101713122948583343 23448585152569684422875015)
              ·
                refine ⟨35172877728854526634312523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23448585152569684422875015 35172877728854526634312523)
                ·
                  refine ⟨52759316593281789951468785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35172877728854526634312523 52759316593281789951468785)
                  ·
                    refine ⟨39569487444961342463601589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52759316593281789951468785 39569487444961342463601589)
                    ·
                      refine ⟨3709639447965125855962649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39569487444961342463601589 3709639447965125855962649)
                      ·
                        rfl

theorem cell23_7224497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_7224497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224497 prefixEnd_7224497 := by exact prefixLift 7224497
  have htrace : WordTrace (prefixWord ++ tailWord_7224497) baseStart_7224497 baseEnd_7224497 := by
    simpa [prefixWord, tailWord_7224497, baseEnd_7224497] using wordTrace_append hprefix tailTrace_7224497
  have hstable : (prefixWord ++ tailWord_7224497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224497).length < 2 ^ (prefixWord ++ tailWord_7224497).sum := by decide
  have hdescent : baseEnd_7224497 < baseStart_7224497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224520 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 2, 4, 4]
def baseStart_7224520 : Nat := 118140960795 + 7224520 * 2 ^ 59
def prefixEnd_7224520 : Nat := 4983230072969 + 3 ^ 40 * 7224520 * 2
def baseEnd_7224520 : Nat := 3709651258020179265975043

theorem tailTrace_7224520 : CollatzResearch.WordTrace tailWord_7224520 prefixEnd_7224520 3709651258020179265975043 := by
  unfold tailWord_7224520
  simp only [CollatzResearch.WordTrace]
  refine ⟨131749945893402682314655507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175666594524536909752874009 131749945893402682314655507)
  ·
    refine ⟨197624918840104023471983261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131749945893402682314655507 197624918840104023471983261)
    ·
      refine ⟨74109344565039008801993723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197624918840104023471983261 74109344565039008801993723)
      ·
        refine ⟨111164016847558513202990585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74109344565039008801993723 111164016847558513202990585)
        ·
          refine ⟨83373012635668884902242939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111164016847558513202990585 83373012635668884902242939)
          ·
            refine ⟨125059518953503327353364409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83373012635668884902242939 125059518953503327353364409)
            ·
              refine ⟨93794639215127495515023307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125059518953503327353364409 93794639215127495515023307)
              ·
                refine ⟨140691958822691243272534961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93794639215127495515023307 140691958822691243272534961)
                ·
                  refine ⟨105518969117018432454401221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140691958822691243272534961 105518969117018432454401221)
                  ·
                    refine ⟨19784806709440956085200229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105518969117018432454401221 19784806709440956085200229)
                    ·
                      refine ⟨3709651258020179265975043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19784806709440956085200229 3709651258020179265975043)
                      ·
                        rfl

theorem cell23_7224520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_7224520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224520 prefixEnd_7224520 := by exact prefixLift 7224520
  have htrace : WordTrace (prefixWord ++ tailWord_7224520) baseStart_7224520 baseEnd_7224520 := by
    simpa [prefixWord, tailWord_7224520, baseEnd_7224520] using wordTrace_append hprefix tailTrace_7224520
  have hstable : (prefixWord ++ tailWord_7224520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224520).length < 2 ^ (prefixWord ++ tailWord_7224520).sum := by decide
  have hdescent : baseEnd_7224520 < baseStart_7224520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224567 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 3, 5, 2]
def baseStart_7224567 : Nat := 118140960795 + 7224567 * 2 ^ 59
def prefixEnd_7224567 : Nat := 4983230072969 + 3 ^ 40 * 7224567 * 2
def baseEnd_7224567 : Nat := 3709675391610940582087327

theorem tailTrace_7224567 : CollatzResearch.WordTrace tailWord_7224567 prefixEnd_7224567 3709675391610940582087327 := by
  unfold tailWord_7224567
  simp only [CollatzResearch.WordTrace]
  refine ⟨263501606017635091656271955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175667737345090061104181303 263501606017635091656271955)
  ·
    refine ⟨395252409026452637484407933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263501606017635091656271955 395252409026452637484407933)
    ·
      refine ⟨148219653384919739056652975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 395252409026452637484407933 148219653384919739056652975)
      ·
        refine ⟨222329480077379608584979463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148219653384919739056652975 222329480077379608584979463)
        ·
          refine ⟨333494220116069412877469195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222329480077379608584979463 333494220116069412877469195)
          ·
            refine ⟨500241330174104119316203793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333494220116069412877469195 500241330174104119316203793)
            ·
              refine ⟨375180997630578089487152845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 500241330174104119316203793 375180997630578089487152845)
              ·
                refine ⟨140692874111466783557682317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 375180997630578089487152845 140692874111466783557682317)
                ·
                  refine ⟨52759827791800043834130869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140692874111466783557682317 52759827791800043834130869)
                  ·
                    refine ⟨4946233855481254109449769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52759827791800043834130869 4946233855481254109449769)
                    ·
                      refine ⟨3709675391610940582087327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4946233855481254109449769 3709675391610940582087327)
                      ·
                        rfl

theorem cell23_7224567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 5, 2].length) (baseStart_7224567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224567 prefixEnd_7224567 := by exact prefixLift 7224567
  have htrace : WordTrace (prefixWord ++ tailWord_7224567) baseStart_7224567 baseEnd_7224567 := by
    simpa [prefixWord, tailWord_7224567, baseEnd_7224567] using wordTrace_append hprefix tailTrace_7224567
  have hstable : (prefixWord ++ tailWord_7224567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224567).length < 2 ^ (prefixWord ++ tailWord_7224567).sum := by decide
  have hdescent : baseEnd_7224567 < baseStart_7224567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224570 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 2, 1, 7]
def baseStart_7224570 : Nat := 118140960795 + 7224570 * 2 ^ 59
def prefixEnd_7224570 : Nat := 4983230072969 + 3 ^ 40 * 7224570 * 2
def baseEnd_7224570 : Nat := 3709676932052904070349813

theorem tailTrace_7224570 : CollatzResearch.WordTrace tailWord_7224570 prefixEnd_7224570 3709676932052904070349813 := by
  unfold tailWord_7224570
  simp only [CollatzResearch.WordTrace]
  refine ⟨65875428859156055792157791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175667810291082815445754109 65875428859156055792157791)
  ·
    refine ⟨98813143288734083688236687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65875428859156055792157791 98813143288734083688236687)
    ·
      refine ⟨148219714933101125532355031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98813143288734083688236687 148219714933101125532355031)
      ·
        refine ⟨222329572399651688298532547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148219714933101125532355031 222329572399651688298532547)
        ·
          refine ⟨333494358599477532447798821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222329572399651688298532547 333494358599477532447798821)
          ·
            refine ⟨62530192237402037333962279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 333494358599477532447798821 62530192237402037333962279)
            ·
              refine ⟨93795288356103056000943419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62530192237402037333962279 93795288356103056000943419)
              ·
                refine ⟨140692932534154584001415129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93795288356103056000943419 140692932534154584001415129)
                ·
                  refine ⟨105519699400615938001061347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140692932534154584001415129 105519699400615938001061347)
                  ·
                    refine ⟨158279549100923907001592021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105519699400615938001061347 158279549100923907001592021)
                    ·
                      refine ⟨3709676932052904070349813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 158279549100923907001592021 3709676932052904070349813)
                      ·
                        rfl

theorem cell23_7224570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_7224570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224570 prefixEnd_7224570 := by exact prefixLift 7224570
  have htrace : WordTrace (prefixWord ++ tailWord_7224570) baseStart_7224570 baseEnd_7224570 := by
    simpa [prefixWord, tailWord_7224570, baseEnd_7224570] using wordTrace_append hprefix tailTrace_7224570
  have hstable : (prefixWord ++ tailWord_7224570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224570).length < 2 ^ (prefixWord ++ tailWord_7224570).sum := by decide
  have hdescent : baseEnd_7224570 < baseStart_7224570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224577 : List Nat := [1, 2, 4, 1, 1, 3, 2, 1, 3, 5]
def baseStart_7224577 : Nat := 118140960795 + 7224577 * 2 ^ 59
def prefixEnd_7224577 : Nat := 4983230072969 + 3 ^ 40 * 7224577 * 2
def baseEnd_7224577 : Nat := 1236560175472495180987427

theorem tailTrace_7224577 : CollatzResearch.WordTrace tailWord_7224577 prefixEnd_7224577 1236560175472495180987427 := by
  unfold tailWord_7224577
  simp only [CollatzResearch.WordTrace]
  refine ⟨263501970747598863364135985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175667980498399242242757323 263501970747598863364135985)
  ·
    refine ⟨197626478060699147523101989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263501970747598863364135985 197626478060699147523101989)
    ·
      refine ⟨37054964636381090160581623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197626478060699147523101989 37054964636381090160581623)
      ·
        refine ⟨55582446954571635240872435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37054964636381090160581623 55582446954571635240872435)
        ·
          refine ⟨83373670431857452861308653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55582446954571635240872435 83373670431857452861308653)
          ·
            refine ⟨31265126411946544822990745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83373670431857452861308653 31265126411946544822990745)
            ·
              refine ⟨23448844808959908617243059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31265126411946544822990745 23448844808959908617243059)
              ·
                refine ⟨35173267213439862925864589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23448844808959908617243059 35173267213439862925864589)
                ·
                  refine ⟨13189975205039948597199221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35173267213439862925864589 13189975205039948597199221)
                  ·
                    refine ⟨1236560175472495180987427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13189975205039948597199221 1236560175472495180987427)
                    ·
                      rfl

theorem cell23_7224577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_7224577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224577 prefixEnd_7224577 := by exact prefixLift 7224577
  have htrace : WordTrace (prefixWord ++ tailWord_7224577) baseStart_7224577 baseEnd_7224577 := by
    simpa [prefixWord, tailWord_7224577, baseEnd_7224577] using wordTrace_append hprefix tailTrace_7224577
  have hstable : (prefixWord ++ tailWord_7224577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224577).length < 2 ^ (prefixWord ++ tailWord_7224577).sum := by decide
  have hdescent : baseEnd_7224577 < baseStart_7224577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224578 : List Nat := [3, 4, 1, 1, 3, 2, 1, 1, 2, 2, 3]
def baseStart_7224578 : Nat := 118140960795 + 7224578 * 2 ^ 59
def prefixEnd_7224578 : Nat := 4983230072969 + 3 ^ 40 * 7224578 * 2
def baseEnd_7224578 : Nat := 3709681039898140039049777

theorem tailTrace_7224578 : CollatzResearch.WordTrace tailWord_7224578 prefixEnd_7224578 3709681039898140039049777 := by
  unfold tailWord_7224578
  simp only [CollatzResearch.WordTrace]
  refine ⟨65875501805148810133730597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175668004813730160356614925 65875501805148810133730597)
  ·
    refine ⟨12351656588465401900074487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65875501805148810133730597 12351656588465401900074487)
    ·
      refine ⟨18527484882698102850111731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12351656588465401900074487 18527484882698102850111731)
      ·
        refine ⟨27791227324047154275167597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18527484882698102850111731 27791227324047154275167597)
        ·
          refine ⟨10421710246517682853187849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27791227324047154275167597 10421710246517682853187849)
          ·
            refine ⟨7816282684888262139890887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10421710246517682853187849 7816282684888262139890887)
            ·
              refine ⟨11724424027332393209836331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7816282684888262139890887 11724424027332393209836331)
              ·
                refine ⟨17586636040998589814754497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11724424027332393209836331 17586636040998589814754497)
                ·
                  refine ⟨13189977030748942361065873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17586636040998589814754497 13189977030748942361065873)
                  ·
                    refine ⟨9892482773061706770799405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13189977030748942361065873 9892482773061706770799405)
                    ·
                      refine ⟨3709681039898140039049777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9892482773061706770799405 3709681039898140039049777)
                      ·
                        rfl

theorem cell23_7224578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_7224578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224578 prefixEnd_7224578 := by exact prefixLift 7224578
  have htrace : WordTrace (prefixWord ++ tailWord_7224578) baseStart_7224578 baseEnd_7224578 := by
    simpa [prefixWord, tailWord_7224578, baseEnd_7224578] using wordTrace_append hprefix tailTrace_7224578
  have hstable : (prefixWord ++ tailWord_7224578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224578).length < 2 ^ (prefixWord ++ tailWord_7224578).sum := by decide
  have hdescent : baseEnd_7224578 < baseStart_7224578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224620 : List Nat := [2, 2, 1, 1, 1, 3, 1, 12]
def baseStart_7224620 : Nat := 118140960795 + 7224620 * 2 ^ 59
def prefixEnd_7224620 : Nat := 4983230072969 + 3 ^ 40 * 7224620 * 2
def baseEnd_7224620 : Nat := 137396392817986254619429

theorem tailTrace_7224620 : CollatzResearch.WordTrace tailWord_7224620 prefixEnd_7224620 137396392817986254619429 := by
  unfold tailWord_7224620
  simp only [CollatzResearch.WordTrace]
  refine ⟨131751769543221540853975657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175669026057628721138634209 131751769543221540853975657)
  ·
    refine ⟨98813827157416155640481743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131751769543221540853975657 98813827157416155640481743)
    ·
      refine ⟨148220740736124233460722615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98813827157416155640481743 148220740736124233460722615)
      ·
        refine ⟨222331111104186350191083923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148220740736124233460722615 222331111104186350191083923)
        ·
          refine ⟨333496666656279525286625885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222331111104186350191083923 333496666656279525286625885)
          ·
            refine ⟨125061249996104821982484707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 333496666656279525286625885 125061249996104821982484707)
            ·
              refine ⟨187591874994157232973727061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125061249996104821982484707 187591874994157232973727061)
              ·
                refine ⟨137396392817986254619429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 187591874994157232973727061 137396392817986254619429)
                ·
                  rfl

theorem cell23_7224620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 12].length) (baseStart_7224620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224620 prefixEnd_7224620 := by exact prefixLift 7224620
  have htrace : WordTrace (prefixWord ++ tailWord_7224620) baseStart_7224620 baseEnd_7224620 := by
    simpa [prefixWord, tailWord_7224620, baseEnd_7224620] using wordTrace_append hprefix tailTrace_7224620
  have hstable : (prefixWord ++ tailWord_7224620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224620).length < 2 ^ (prefixWord ++ tailWord_7224620).sum := by decide
  have hdescent : baseEnd_7224620 < baseStart_7224620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224627 : List Nat := [1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 6]
def baseStart_7224627 : Nat := 118140960795 + 7224627 * 2 ^ 59
def prefixEnd_7224627 : Nat := 4983230072969 + 3 ^ 40 * 7224627 * 2
def baseEnd_7224627 : Nat := 3709706200450210347337051

theorem tailTrace_7224627 : CollatzResearch.WordTrace tailWord_7224627 prefixEnd_7224627 3709706200450210347337051 := by
  unfold tailWord_7224627
  simp only [CollatzResearch.WordTrace]
  refine ⟨263503794397417721903456135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175669196264945147935637423 263503794397417721903456135)
  ·
    refine ⟨395255691596126582855184203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263503794397417721903456135 395255691596126582855184203)
    ·
      refine ⟨592883537394189874282776305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395255691596126582855184203 592883537394189874282776305)
      ·
        refine ⟨444662653045642405712082229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 592883537394189874282776305 444662653045642405712082229)
        ·
          refine ⟨41687123723028975535507709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 444662653045642405712082229 41687123723028975535507709)
          ·
            refine ⟨15632671396135865825815391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41687123723028975535507709 15632671396135865825815391)
            ·
              refine ⟨23449007094203798738723087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15632671396135865825815391 23449007094203798738723087)
              ·
                refine ⟨35173510641305698108084631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23449007094203798738723087 35173510641305698108084631)
                ·
                  refine ⟨52760265961958547162126947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35173510641305698108084631 52760265961958547162126947)
                  ·
                    refine ⟨79140398942937820743190421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52760265961958547162126947 79140398942937820743190421)
                    ·
                      refine ⟨3709706200450210347337051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79140398942937820743190421 3709706200450210347337051)
                      ·
                        rfl

theorem cell23_7224627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 6].length) (baseStart_7224627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224627 prefixEnd_7224627 := by exact prefixLift 7224627
  have htrace : WordTrace (prefixWord ++ tailWord_7224627) baseStart_7224627 baseEnd_7224627 := by
    simpa [prefixWord, tailWord_7224627, baseEnd_7224627] using wordTrace_append hprefix tailTrace_7224627
  have hstable : (prefixWord ++ tailWord_7224627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224627).length < 2 ^ (prefixWord ++ tailWord_7224627).sum := by decide
  have hdescent : baseEnd_7224627 < baseStart_7224627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224664 : List Nat := [2, 1, 2, 2, 1, 1, 3, 3, 4, 1, 3]
def baseStart_7224664 : Nat := 118140960795 + 7224664 * 2 ^ 59
def prefixEnd_7224664 : Nat := 4983230072969 + 3 ^ 40 * 7224664 * 2
def baseEnd_7224664 : Nat := 3709725199234426702574381

theorem tailTrace_7224664 : CollatzResearch.WordTrace tailWord_7224664 prefixEnd_7224664 3709725199234426702574381 := by
  unfold tailWord_7224664
  simp only [CollatzResearch.WordTrace]
  refine ⟨131752571949141838611276523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175670095932189118148368697 131752571949141838611276523)
  ·
    refine ⟨197628857923712757916914785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131752571949141838611276523 197628857923712757916914785)
    ·
      refine ⟨148221643442784568437686089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197628857923712757916914785 148221643442784568437686089)
      ·
        refine ⟨111166232582088426328264567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148221643442784568437686089 111166232582088426328264567)
        ·
          refine ⟨166749348873132639492396851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111166232582088426328264567 166749348873132639492396851)
          ·
            refine ⟨250124023309698959238595277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166749348873132639492396851 250124023309698959238595277)
            ·
              refine ⟨93796508741137109714473229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250124023309698959238595277 93796508741137109714473229)
              ·
                refine ⟨35173690777926416142927461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93796508741137109714473229 35173690777926416142927461)
                ·
                  refine ⟨6595067020861203026798899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35173690777926416142927461 6595067020861203026798899)
                  ·
                    refine ⟨9892600531291804540198349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6595067020861203026798899 9892600531291804540198349)
                    ·
                      refine ⟨3709725199234426702574381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9892600531291804540198349 3709725199234426702574381)
                      ·
                        rfl

theorem cell23_7224664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 4, 1, 3].length) (baseStart_7224664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224664 prefixEnd_7224664 := by exact prefixLift 7224664
  have htrace : WordTrace (prefixWord ++ tailWord_7224664) baseStart_7224664 baseEnd_7224664 := by
    simpa [prefixWord, tailWord_7224664, baseEnd_7224664] using wordTrace_append hprefix tailTrace_7224664
  have hstable : (prefixWord ++ tailWord_7224664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224664).length < 2 ^ (prefixWord ++ tailWord_7224664).sum := by decide
  have hdescent : baseEnd_7224664 < baseStart_7224664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224702 : List Nat := [4, 2, 3, 2, 1, 1, 3, 1, 1, 2, 3]
def baseStart_7224702 : Nat := 118140960795 + 7224702 * 2 ^ 59
def prefixEnd_7224702 : Nat := 4983230072969 + 3 ^ 40 * 7224702 * 2
def baseEnd_7224702 : Nat := 3709744711499297553899207

theorem tailTrace_7224702 : CollatzResearch.WordTrace tailWord_7224702 prefixEnd_7224702 3709744711499297553899207 := by
  unfold tailWord_7224702
  simp only [CollatzResearch.WordTrace]
  refine ⟨32938316234018251214054545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175671019914764006474957573 32938316234018251214054545)
  ·
    refine ⟨24703737175513688410540909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32938316234018251214054545 24703737175513688410540909)
    ·
      refine ⟨9263901440817633153952841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24703737175513688410540909 9263901440817633153952841)
      ·
        refine ⟨6947926080613224865464631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9263901440817633153952841 6947926080613224865464631)
        ·
          refine ⟨10421889120919837298196947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6947926080613224865464631 10421889120919837298196947)
          ·
            refine ⟨15632833681379755947295421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10421889120919837298196947 15632833681379755947295421)
            ·
              refine ⟨5862312630517408480235783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15632833681379755947295421 5862312630517408480235783)
              ·
                refine ⟨8793468945776112720353675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5862312630517408480235783 8793468945776112720353675)
                ·
                  refine ⟨13190203418664169080530513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8793468945776112720353675 13190203418664169080530513)
                  ·
                    refine ⟨9892652563998126810397885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13190203418664169080530513 9892652563998126810397885)
                    ·
                      refine ⟨3709744711499297553899207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9892652563998126810397885 3709744711499297553899207)
                      ·
                        rfl

theorem cell23_7224702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_7224702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224702 prefixEnd_7224702 := by exact prefixLift 7224702
  have htrace : WordTrace (prefixWord ++ tailWord_7224702) baseStart_7224702 baseEnd_7224702 := by
    simpa [prefixWord, tailWord_7224702, baseEnd_7224702] using wordTrace_append hprefix tailTrace_7224702
  have hstable : (prefixWord ++ tailWord_7224702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224702).length < 2 ^ (prefixWord ++ tailWord_7224702).sum := by decide
  have hdescent : baseEnd_7224702 < baseStart_7224702 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224727 : List Nat := [1, 1, 3, 3, 1, 1, 1, 5, 7]
def baseStart_7224727 : Nat := 118140960795 + 7224727 * 2 ^ 59
def prefixEnd_7224727 : Nat := 4983230072969 + 3 ^ 40 * 7224727 * 2
def baseEnd_7224727 : Nat := 412195283168406661787399

theorem tailTrace_7224727 : CollatzResearch.WordTrace tailWord_7224727 prefixEnd_7224727 412195283168406661787399 := by
  unfold tailWord_7224727
  simp only [CollatzResearch.WordTrace]
  refine ⟨263507441697055438982096435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175671627798036959321397623 263507441697055438982096435)
  ·
    refine ⟨395261162545583158473144653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263507441697055438982096435 395261162545583158473144653)
    ·
      refine ⟨148222935954593684427429245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 395261162545583158473144653 148222935954593684427429245)
      ·
        refine ⟨55583600982972631660285967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148222935954593684427429245 55583600982972631660285967)
        ·
          refine ⟨83375401474458947490428951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55583600982972631660285967 83375401474458947490428951)
          ·
            refine ⟨125063102211688421235643427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83375401474458947490428951 125063102211688421235643427)
            ·
              refine ⟨187594653317532631853465141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125063102211688421235643427 187594653317532631853465141)
              ·
                refine ⟨17586998748518684236262357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 187594653317532631853465141 17586998748518684236262357)
                ·
                  refine ⟨412195283168406661787399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17586998748518684236262357 412195283168406661787399)
                  ·
                    rfl

theorem cell23_7224727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 7].length) (baseStart_7224727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224727 prefixEnd_7224727 := by exact prefixLift 7224727
  have htrace : WordTrace (prefixWord ++ tailWord_7224727) baseStart_7224727 baseEnd_7224727 := by
    simpa [prefixWord, tailWord_7224727, baseEnd_7224727] using wordTrace_append hprefix tailTrace_7224727
  have hstable : (prefixWord ++ tailWord_7224727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224727).length < 2 ^ (prefixWord ++ tailWord_7224727).sum := by decide
  have hdescent : baseEnd_7224727 < baseStart_7224727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224738 : List Nat := [3, 3, 1, 2, 1, 3, 2, 1, 1, 4, 2]
def baseStart_7224738 : Nat := 118140960795 + 7224738 * 2 ^ 59
def prefixEnd_7224738 : Nat := 4983230072969 + 3 ^ 40 * 7224738 * 2
def baseEnd_7224738 : Nat := 3709763196802859413049041

theorem tailTrace_7224738 : CollatzResearch.WordTrace tailWord_7224738 prefixEnd_7224738 3709763196802859413049041 := by
  unfold tailWord_7224738
  simp only [CollatzResearch.WordTrace]
  refine ⟨65876960725003896965186717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175671895266677058573831245 65876960725003896965186717)
  ·
    refine ⟨24703860271876461361945019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65876960725003896965186717 24703860271876461361945019)
    ·
      refine ⟨37055790407814692042917529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24703860271876461361945019 37055790407814692042917529)
      ·
        refine ⟨27791842805861019032188147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37055790407814692042917529 27791842805861019032188147)
        ·
          refine ⟨41687764208791528548282221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27791842805861019032188147 41687764208791528548282221)
          ·
            refine ⟨15632911578296823205605833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41687764208791528548282221 15632911578296823205605833)
            ·
              refine ⟨11724683683722617404204375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15632911578296823205605833 11724683683722617404204375)
              ·
                refine ⟨17587025525583926106306563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11724683683722617404204375 17587025525583926106306563)
                ·
                  refine ⟨26380538288375889159459845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17587025525583926106306563 26380538288375889159459845)
                  ·
                    refine ⟨4946350929070479217398721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26380538288375889159459845 4946350929070479217398721)
                    ·
                      refine ⟨3709763196802859413049041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4946350929070479217398721 3709763196802859413049041)
                      ·
                        rfl

theorem cell23_7224738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_7224738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224738 prefixEnd_7224738 := by exact prefixLift 7224738
  have htrace : WordTrace (prefixWord ++ tailWord_7224738) baseStart_7224738 baseEnd_7224738 := by
    simpa [prefixWord, tailWord_7224738, baseEnd_7224738] using wordTrace_append hprefix tailTrace_7224738
  have hstable : (prefixWord ++ tailWord_7224738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224738).length < 2 ^ (prefixWord ++ tailWord_7224738).sum := by decide
  have hdescent : baseEnd_7224738 < baseStart_7224738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224767 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 5]
def baseStart_7224767 : Nat := 118140960795 + 7224767 * 2 ^ 59
def prefixEnd_7224767 : Nat := 4983230072969 + 3 ^ 40 * 7224767 * 2
def baseEnd_7224767 : Nat := 3709778087741839799586407

theorem tailTrace_7224767 : CollatzResearch.WordTrace tailWord_7224767 prefixEnd_7224767 3709778087741839799586407 := by
  unfold tailWord_7224767
  simp only [CollatzResearch.WordTrace]
  refine ⟨263508900616910525813552555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175672600411273683875701703 263508900616910525813552555)
  ·
    refine ⟨395263350925365788720328833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263508900616910525813552555 395263350925365788720328833)
    ·
      refine ⟨296447513194024341540246625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395263350925365788720328833 296447513194024341540246625)
      ·
        refine ⟨222335634895518256155184969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296447513194024341540246625 222335634895518256155184969)
        ·
          refine ⟨166751726171638692116388727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222335634895518256155184969 166751726171638692116388727)
          ·
            refine ⟨250127589257458038174583091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166751726171638692116388727 250127589257458038174583091)
            ·
              refine ⟨375191383886187057261874637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250127589257458038174583091 375191383886187057261874637)
              ·
                refine ⟨140696768957320146473202989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 375191383886187057261874637 140696768957320146473202989)
                ·
                  refine ⟨52761288358995054927451121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140696768957320146473202989 52761288358995054927451121)
                  ·
                    refine ⟨39570966269246291195588341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52761288358995054927451121 39570966269246291195588341)
                    ·
                      refine ⟨3709778087741839799586407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39570966269246291195588341 3709778087741839799586407)
                      ·
                        rfl

theorem cell23_7224767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_7224767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224767 prefixEnd_7224767 := by exact prefixLift 7224767
  have htrace : WordTrace (prefixWord ++ tailWord_7224767) baseStart_7224767 baseEnd_7224767 := by
    simpa [prefixWord, tailWord_7224767, baseEnd_7224767] using wordTrace_append hprefix tailTrace_7224767
  have hstable : (prefixWord ++ tailWord_7224767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224767).length < 2 ^ (prefixWord ++ tailWord_7224767).sum := by decide
  have hdescent : baseEnd_7224767 < baseStart_7224767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224772 : List Nat := [2, 3, 3, 2, 1, 3, 1, 2, 2, 2, 2]
def baseStart_7224772 : Nat := 118140960795 + 7224772 * 2 ^ 59
def prefixEnd_7224772 : Nat := 4983230072969 + 3 ^ 40 * 7224772 * 2
def baseEnd_7224772 : Nat := 3709780655145112280023885

theorem tailTrace_7224772 : CollatzResearch.WordTrace tailWord_7224772 prefixEnd_7224772 3709780655145112280023885 := by
  unfold tailWord_7224772
  simp only [CollatzResearch.WordTrace]
  refine ⟨131754541490946205833742285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175672721987928274444989713 131754541490946205833742285)
  ·
    refine ⟨49407953059104827187653357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131754541490946205833742285 49407953059104827187653357)
    ·
      refine ⟨18527982397164310195370009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49407953059104827187653357 18527982397164310195370009)
      ·
        refine ⟨13895986797873232646527507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18527982397164310195370009 13895986797873232646527507)
        ·
          refine ⟨20843980196809848969791261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13895986797873232646527507 20843980196809848969791261)
          ·
            refine ⟨7816492573803693363671723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20843980196809848969791261 7816492573803693363671723)
            ·
              refine ⟨11724738860705540045507585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7816492573803693363671723 11724738860705540045507585)
              ·
                refine ⟨8793554145529155034130689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11724738860705540045507585 8793554145529155034130689)
                ·
                  refine ⟨6595165609146866275598017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8793554145529155034130689 6595165609146866275598017)
                  ·
                    refine ⟨4946374206860149706698513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6595165609146866275598017 4946374206860149706698513)
                    ·
                      refine ⟨3709780655145112280023885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4946374206860149706698513 3709780655145112280023885)
                      ·
                        rfl

theorem cell23_7224772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_7224772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224772 prefixEnd_7224772 := by exact prefixLift 7224772
  have htrace : WordTrace (prefixWord ++ tailWord_7224772) baseStart_7224772 baseEnd_7224772 := by
    simpa [prefixWord, tailWord_7224772, baseEnd_7224772] using wordTrace_append hprefix tailTrace_7224772
  have hstable : (prefixWord ++ tailWord_7224772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224772).length < 2 ^ (prefixWord ++ tailWord_7224772).sum := by decide
  have hdescent : baseEnd_7224772 < baseStart_7224772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224794 : List Nat := [3, 1, 1, 2, 3, 2, 1, 2, 1, 3, 4]
def baseStart_7224794 : Nat := 118140960795 + 7224794 * 2 ^ 59
def prefixEnd_7224794 : Nat := 4983230072969 + 3 ^ 40 * 7224794 * 2
def baseEnd_7224794 : Nat := 3709791951719511193948783

theorem tailTrace_7224794 : CollatzResearch.WordTrace tailWord_7224794 prefixEnd_7224794 3709791951719511193948783 := by
  unfold tailWord_7224794
  simp only [CollatzResearch.WordTrace]
  refine ⟨65877471346953177356196359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175673256925208472949856957 65877471346953177356196359)
  ·
    refine ⟨98816207020429766034294539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65877471346953177356196359 98816207020429766034294539)
    ·
      refine ⟨148224310530644649051441809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98816207020429766034294539 148224310530644649051441809)
      ·
        refine ⟨111168232897983486788581357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148224310530644649051441809 111168232897983486788581357)
        ·
          refine ⟨41688087336743807545718009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111168232897983486788581357 41688087336743807545718009)
          ·
            refine ⟨31266065502557855659288507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41688087336743807545718009 31266065502557855659288507)
            ·
              refine ⟨46899098253836783488932761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31266065502557855659288507 46899098253836783488932761)
              ·
                refine ⟨35174323690377587616699571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46899098253836783488932761 35174323690377587616699571)
                ·
                  refine ⟨52761485535566381425049357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35174323690377587616699571 52761485535566381425049357)
                  ·
                    refine ⟨19785557075837393034393509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52761485535566381425049357 19785557075837393034393509)
                    ·
                      refine ⟨3709791951719511193948783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19785557075837393034393509 3709791951719511193948783)
                      ·
                        rfl

theorem cell23_7224794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_7224794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224794 prefixEnd_7224794 := by exact prefixLift 7224794
  have htrace : WordTrace (prefixWord ++ tailWord_7224794) baseStart_7224794 baseEnd_7224794 := by
    simpa [prefixWord, tailWord_7224794, baseEnd_7224794] using wordTrace_append hprefix tailTrace_7224794
  have hstable : (prefixWord ++ tailWord_7224794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224794).length < 2 ^ (prefixWord ++ tailWord_7224794).sum := by decide
  have hdescent : baseEnd_7224794 < baseStart_7224794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224851 : List Nat := [1, 1, 1, 2, 1, 6, 4, 1, 6]
def baseStart_7224851 : Nat := 118140960795 + 7224851 * 2 ^ 59
def prefixEnd_7224851 : Nat := 4983230072969 + 3 ^ 40 * 7224851 * 2
def baseEnd_7224851 : Nat := 412202357790757496770669

theorem tailTrace_7224851 : CollatzResearch.WordTrace tailWord_7224851 prefixEnd_7224851 412202357790757496770669 := by
  unfold tailWord_7224851
  simp only [CollatzResearch.WordTrace]
  refine ⟨263511964348606208159610407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175674642899070805439740271 263511964348606208159610407)
  ·
    refine ⟨395267946522909312239415611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263511964348606208159610407 395267946522909312239415611)
    ·
      refine ⟨592901919784363968359123417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395267946522909312239415611 592901919784363968359123417)
      ·
        refine ⟨444676439838272976269342563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 592901919784363968359123417 444676439838272976269342563)
        ·
          refine ⟨667014659757409464404013845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444676439838272976269342563 667014659757409464404013845)
          ·
            refine ⟨31266312176128568643938149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 667014659757409464404013845 31266312176128568643938149)
            ·
              refine ⟨5862433533024106620738403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31266312176128568643938149 5862433533024106620738403)
              ·
                refine ⟨8793650299536159931107605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5862433533024106620738403 8793650299536159931107605)
                ·
                  refine ⟨412202357790757496770669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8793650299536159931107605 412202357790757496770669)
                  ·
                    rfl

theorem cell23_7224851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 6].length) (baseStart_7224851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224851 prefixEnd_7224851 := by exact prefixLift 7224851
  have htrace : WordTrace (prefixWord ++ tailWord_7224851) baseStart_7224851 baseEnd_7224851 := by
    simpa [prefixWord, tailWord_7224851, baseEnd_7224851] using wordTrace_append hprefix tailTrace_7224851
  have hstable : (prefixWord ++ tailWord_7224851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224851).length < 2 ^ (prefixWord ++ tailWord_7224851).sum := by decide
  have hdescent : baseEnd_7224851 < baseStart_7224851 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224888 : List Nat := [2, 1, 2, 1, 4, 2, 2, 2, 2, 3, 2]
def baseStart_7224888 : Nat := 118140960795 + 7224888 * 2 ^ 59
def prefixEnd_7224888 : Nat := 4983230072969 + 3 ^ 40 * 7224888 * 2
def baseEnd_7224888 : Nat := 3709840218901033826173351

theorem tailTrace_7224888 : CollatzResearch.WordTrace tailWord_7224888 prefixEnd_7224888 3709840218901033826173351 := by
  unfold tailWord_7224888
  simp only [CollatzResearch.WordTrace]
  refine ⟨131756656924736081739353659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175675542566314775652471545 131756656924736081739353659)
  ·
    refine ⟨197634985387104122609030489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131756656924736081739353659 197634985387104122609030489)
    ·
      refine ⟨148226239040328091956772867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197634985387104122609030489 148226239040328091956772867)
      ·
        refine ⟨222339358560492137935159301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148226239040328091956772867 222339358560492137935159301)
        ·
          refine ⟨41688629730092275862842369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222339358560492137935159301 41688629730092275862842369)
          ·
            refine ⟨31266472297569206897131777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41688629730092275862842369 31266472297569206897131777)
            ·
              refine ⟨23449854223176905172848833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31266472297569206897131777 23449854223176905172848833)
              ·
                refine ⟨17587390667382678879636625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23449854223176905172848833 17587390667382678879636625)
                ·
                  refine ⟨13190543000537009159727469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17587390667382678879636625 13190543000537009159727469)
                  ·
                    refine ⟨4946453625201378434897801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13190543000537009159727469 4946453625201378434897801)
                    ·
                      refine ⟨3709840218901033826173351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4946453625201378434897801 3709840218901033826173351)
                      ·
                        rfl

theorem cell23_7224888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 2, 3, 2].length) (baseStart_7224888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224888 prefixEnd_7224888 := by exact prefixLift 7224888
  have htrace : WordTrace (prefixWord ++ tailWord_7224888) baseStart_7224888 baseEnd_7224888 := by
    simpa [prefixWord, tailWord_7224888, baseEnd_7224888] using wordTrace_append hprefix tailTrace_7224888
  have hstable : (prefixWord ++ tailWord_7224888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224888).length < 2 ^ (prefixWord ++ tailWord_7224888).sum := by decide
  have hdescent : baseEnd_7224888 < baseStart_7224888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224895 : List Nat := [1, 1, 2, 2, 3, 4, 1, 4, 1, 1, 3]
def baseStart_7224895 : Nat := 118140960795 + 7224895 * 2 ^ 59
def prefixEnd_7224895 : Nat := 4983230072969 + 3 ^ 40 * 7224895 * 2
def baseEnd_7224895 : Nat := 3709843813265615298785819

theorem tailTrace_7224895 : CollatzResearch.WordTrace tailWord_7224895 prefixEnd_7224895 3709843813265615298785819 := by
  unfold tailWord_7224895
  simp only [CollatzResearch.WordTrace]
  refine ⟨263513569160446803674212139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175675712773631202449474759 263513569160446803674212139)
  ·
    refine ⟨395270353740670205511318209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263513569160446803674212139 395270353740670205511318209)
    ·
      refine ⟨296452765305502654133488657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395270353740670205511318209 296452765305502654133488657)
      ·
        refine ⟨222339573979126990600116493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296452765305502654133488657 222339573979126990600116493)
        ·
          refine ⟨83377340242172621475043685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222339573979126990600116493 83377340242172621475043685)
          ·
            refine ⟨15633251295407366526570691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83377340242172621475043685 15633251295407366526570691)
            ·
              refine ⟨23449876943111049789856037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15633251295407366526570691 23449876943111049789856037)
              ·
                refine ⟨4396851926833321835598007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23449876943111049789856037 4396851926833321835598007)
                ·
                  refine ⟨6595277890249982753397011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4396851926833321835598007 6595277890249982753397011)
                  ·
                    refine ⟨9892916835374974130095517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6595277890249982753397011 9892916835374974130095517)
                    ·
                      refine ⟨3709843813265615298785819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9892916835374974130095517 3709843813265615298785819)
                      ·
                        rfl

theorem cell23_7224895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 4, 1, 1, 3].length) (baseStart_7224895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224895 prefixEnd_7224895 := by exact prefixLift 7224895
  have htrace : WordTrace (prefixWord ++ tailWord_7224895) baseStart_7224895 baseEnd_7224895 := by
    simpa [prefixWord, tailWord_7224895, baseEnd_7224895] using wordTrace_append hprefix tailTrace_7224895
  have hstable : (prefixWord ++ tailWord_7224895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224895).length < 2 ^ (prefixWord ++ tailWord_7224895).sum := by decide
  have hdescent : baseEnd_7224895 < baseStart_7224895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224931 : List Nat := [1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 4]
def baseStart_7224931 : Nat := 118140960795 + 7224931 * 2 ^ 59
def prefixEnd_7224931 : Nat := 4983230072969 + 3 ^ 40 * 7224931 * 2
def baseEnd_7224931 : Nat := 3709862298569177157935653

theorem tailTrace_7224931 : CollatzResearch.WordTrace tailWord_7224931 prefixEnd_7224931 3709862298569177157935653 := by
  unfold tailWord_7224931
  simp only [CollatzResearch.WordTrace]
  refine ⟨263514882188316381822522647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175676588125544254548348431 263514882188316381822522647)
  ·
    refine ⟨395272323282474572733783971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263514882188316381822522647 395272323282474572733783971)
    ·
      refine ⟨592908484923711859100675957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395272323282474572733783971 592908484923711859100675957)
      ·
        refine ⟨55585170461597986790688371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 592908484923711859100675957 55585170461597986790688371)
        ·
          refine ⟨83377755692396980186032557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55585170461597986790688371 83377755692396980186032557)
          ·
            refine ⟨31266658384648867569762209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83377755692396980186032557 31266658384648867569762209)
            ·
              refine ⟨23449993788486650677321657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31266658384648867569762209 23449993788486650677321657)
              ·
                refine ⟨17587495341364988007991243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23449993788486650677321657 17587495341364988007991243)
                ·
                  refine ⟨26381243012047482011986865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17587495341364988007991243 26381243012047482011986865)
                  ·
                    refine ⟨19785932259035611508990149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26381243012047482011986865 19785932259035611508990149)
                    ·
                      refine ⟨3709862298569177157935653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19785932259035611508990149 3709862298569177157935653)
                      ·
                        rfl

theorem cell23_7224931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_7224931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224931 prefixEnd_7224931 := by exact prefixLift 7224931
  have htrace : WordTrace (prefixWord ++ tailWord_7224931) baseStart_7224931 baseEnd_7224931 := by
    simpa [prefixWord, tailWord_7224931, baseEnd_7224931] using wordTrace_append hprefix tailTrace_7224931
  have hstable : (prefixWord ++ tailWord_7224931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224931).length < 2 ^ (prefixWord ++ tailWord_7224931).sum := by decide
  have hdescent : baseEnd_7224931 < baseStart_7224931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224941 : List Nat := [1, 5, 1, 1, 4, 1, 10]
def baseStart_7224941 : Nat := 118140960795 + 7224941 * 2 ^ 59
def prefixEnd_7224941 : Nat := 4983230072969 + 3 ^ 40 * 7224941 * 2
def baseEnd_7224941 : Nat := 45800832510811384182847

theorem tailTrace_7224941 : CollatzResearch.WordTrace tailWord_7224941 prefixEnd_7224941 45800832510811384182847 := by
  unfold tailWord_7224941
  simp only [CollatzResearch.WordTrace]
  refine ⟨263515246918280153530386677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175676831278853435686924451 263515246918280153530386677)
  ·
    refine ⟨24704554398588764393473751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 263515246918280153530386677 24704554398588764393473751)
    ·
      refine ⟨37056831597883146590210627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24704554398588764393473751 37056831597883146590210627)
      ·
        refine ⟨55585247396824719885315941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37056831597883146590210627 55585247396824719885315941)
        ·
          refine ⟨10422233886904634978496739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55585247396824719885315941 10422233886904634978496739)
          ·
            refine ⟨15633350830356952467745109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10422233886904634978496739 15633350830356952467745109)
            ·
              refine ⟨45800832510811384182847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15633350830356952467745109 45800832510811384182847)
              ·
                rfl

theorem cell23_7224941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 10].length) (baseStart_7224941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224941 prefixEnd_7224941 := by exact prefixLift 7224941
  have htrace : WordTrace (prefixWord ++ tailWord_7224941) baseStart_7224941 baseEnd_7224941 := by
    simpa [prefixWord, tailWord_7224941, baseEnd_7224941] using wordTrace_append hprefix tailTrace_7224941
  have hstable : (prefixWord ++ tailWord_7224941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224941).length < 2 ^ (prefixWord ++ tailWord_7224941).sum := by decide
  have hdescent : baseEnd_7224941 < baseStart_7224941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7224954 : List Nat := [3, 1, 1, 1, 1, 1, 1, 5, 2, 7]
def baseStart_7224954 : Nat := 118140960795 + 7224954 * 2 ^ 59
def prefixEnd_7224954 : Nat := 4983230072969 + 3 ^ 40 * 7224954 * 2
def baseEnd_7224954 : Nat := 1236624702874743522649349

theorem tailTrace_7224954 : CollatzResearch.WordTrace tailWord_7224954 prefixEnd_7224954 1236624702874743522649349 := by
  unfold tailWord_7224954
  simp only [CollatzResearch.WordTrace]
  refine ⟨65878930266808264187652479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175677147378155371167073277 65878930266808264187652479)
  ·
    refine ⟨98818395400212396281478719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65878930266808264187652479 98818395400212396281478719)
    ·
      refine ⟨148227593100318594422218079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98818395400212396281478719 148227593100318594422218079)
      ·
        refine ⟨222341389650477891633327119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148227593100318594422218079 222341389650477891633327119)
        ·
          refine ⟨333512084475716837449990679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222341389650477891633327119 333512084475716837449990679)
          ·
            refine ⟨500268126713575256174986019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333512084475716837449990679 500268126713575256174986019)
            ·
              refine ⟨750402190070362884262479029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500268126713575256174986019 750402190070362884262479029)
              ·
                refine ⟨70350205319096520399607409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 750402190070362884262479029 70350205319096520399607409)
                ·
                  refine ⟨52762653989322390299705557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70350205319096520399607409 52762653989322390299705557)
                  ·
                    refine ⟨1236624702874743522649349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52762653989322390299705557 1236624702874743522649349)
                    ·
                      rfl

theorem cell23_7224954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 2, 7].length) (baseStart_7224954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7224954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7224954 prefixEnd_7224954 := by exact prefixLift 7224954
  have htrace : WordTrace (prefixWord ++ tailWord_7224954) baseStart_7224954 baseEnd_7224954 := by
    simpa [prefixWord, tailWord_7224954, baseEnd_7224954] using wordTrace_append hprefix tailTrace_7224954
  have hstable : (prefixWord ++ tailWord_7224954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7224954).length < 2 ^ (prefixWord ++ tailWord_7224954).sum := by decide
  have hdescent : baseEnd_7224954 < baseStart_7224954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7224954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225011 : List Nat := [1, 1, 1, 2, 3, 3, 2, 1, 2, 4, 3]
def baseStart_7225011 : Nat := 118140960795 + 7225011 * 2 ^ 59
def prefixEnd_7225011 : Nat := 4983230072969 + 3 ^ 40 * 7225011 * 2
def baseEnd_7225011 : Nat := 3709903377021536844935285

theorem tailTrace_7225011 : CollatzResearch.WordTrace tailWord_7225011 prefixEnd_7225011 3709903377021536844935285 := by
  unfold tailWord_7225011
  simp only [CollatzResearch.WordTrace]
  refine ⟨263517800028026555485434887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175678533352017703656956591 263517800028026555485434887)
  ·
    refine ⟨395276700042039833228152331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263517800028026555485434887 395276700042039833228152331)
    ·
      refine ⟨592915050063059749842228497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395276700042039833228152331 592915050063059749842228497)
      ·
        refine ⟨444686287547294812381671373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 592915050063059749842228497 444686287547294812381671373)
        ·
          refine ⟨166757357830235554643126765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 444686287547294812381671373 166757357830235554643126765)
          ·
            refine ⟨62534009186338332991172537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166757357830235554643126765 62534009186338332991172537)
            ·
              refine ⟨46900506889753749743379403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62534009186338332991172537 46900506889753749743379403)
              ·
                refine ⟨70350760334630624615069105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46900506889753749743379403 70350760334630624615069105)
                ·
                  refine ⟨52763070250972968461301829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70350760334630624615069105 52763070250972968461301829)
                  ·
                    refine ⟨9893075672057431586494093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52763070250972968461301829 9893075672057431586494093)
                    ·
                      refine ⟨3709903377021536844935285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9893075672057431586494093 3709903377021536844935285)
                      ·
                        rfl

theorem cell23_7225011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 4, 3].length) (baseStart_7225011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225011 prefixEnd_7225011 := by exact prefixLift 7225011
  have htrace : WordTrace (prefixWord ++ tailWord_7225011) baseStart_7225011 baseEnd_7225011 := by
    simpa [prefixWord, tailWord_7225011, baseEnd_7225011] using wordTrace_append hprefix tailTrace_7225011
  have hstable : (prefixWord ++ tailWord_7225011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225011).length < 2 ^ (prefixWord ++ tailWord_7225011).sum := by decide
  have hdescent : baseEnd_7225011 < baseStart_7225011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225021 : List Nat := [1, 4, 1, 2, 1, 2, 2, 1, 1, 4, 4]
def baseStart_7225021 : Nat := 118140960795 + 7225021 * 2 ^ 59
def prefixEnd_7225021 : Nat := 4983230072969 + 3 ^ 40 * 7225021 * 2
def baseEnd_7225021 : Nat := 3709908511828081805810239

theorem tailTrace_7225021 : CollatzResearch.WordTrace tailWord_7225021 prefixEnd_7225021 3709908511828081805810239 := by
  unfold tailWord_7225021
  simp only [CollatzResearch.WordTrace]
  refine ⟨263518164757990327193298917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175678776505326884795532611 263518164757990327193298917)
  ·
    refine ⟨49409655892123186348743547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263518164757990327193298917 49409655892123186348743547)
    ·
      refine ⟨74114483838184779523115321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49409655892123186348743547 74114483838184779523115321)
      ·
        refine ⟨55585862878638584642336491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74114483838184779523115321 55585862878638584642336491)
        ·
          refine ⟨83378794317957876963504737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55585862878638584642336491 83378794317957876963504737)
          ·
            refine ⟨62534095738468407722628553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83378794317957876963504737 62534095738468407722628553)
            ·
              refine ⟨46900571803851305791971415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62534095738468407722628553 46900571803851305791971415)
              ·
                refine ⟨70350857705776958687957123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46900571803851305791971415 70350857705776958687957123)
                ·
                  refine ⟨105526286558665438031935685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70350857705776958687957123 105526286558665438031935685)
                  ·
                    refine ⟨19786178729749769630987941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105526286558665438031935685 19786178729749769630987941)
                    ·
                      refine ⟨3709908511828081805810239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19786178729749769630987941 3709908511828081805810239)
                      ·
                        rfl

theorem cell23_7225021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_7225021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225021 prefixEnd_7225021 := by exact prefixLift 7225021
  have htrace : WordTrace (prefixWord ++ tailWord_7225021) baseStart_7225021 baseEnd_7225021 := by
    simpa [prefixWord, tailWord_7225021, baseEnd_7225021] using wordTrace_append hprefix tailTrace_7225021
  have hstable : (prefixWord ++ tailWord_7225021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225021).length < 2 ^ (prefixWord ++ tailWord_7225021).sum := by decide
  have hdescent : baseEnd_7225021 < baseStart_7225021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225048 : List Nat := [2, 1, 2, 2, 3, 1, 2, 5, 5]
def baseStart_7225048 : Nat := 118140960795 + 7225048 * 2 ^ 59
def prefixEnd_7225048 : Nat := 4983230072969 + 3 ^ 40 * 7225048 * 2
def baseEnd_7225048 : Nat := 412213597311750355574735

theorem tailTrace_7225048 : CollatzResearch.WordTrace tailWord_7225048 prefixEnd_7225048 412213597311750355574735 := by
  unfold tailWord_7225048
  simp only [CollatzResearch.WordTrace]
  refine ⟨131759574764446255402265899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175679433019261673869687865 131759574764446255402265899)
  ·
    refine ⟨197639362146669383103398849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131759574764446255402265899 197639362146669383103398849)
    ·
      refine ⟨148229521610002037327549137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197639362146669383103398849 148229521610002037327549137)
      ·
        refine ⟨111172141207501527995661853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148229521610002037327549137 111172141207501527995661853)
        ·
          refine ⟨41689552952813072998373195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111172141207501527995661853 41689552952813072998373195)
          ·
            refine ⟨62534329429219609497559793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41689552952813072998373195 62534329429219609497559793)
            ·
              refine ⟨46900747071914707123169845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62534329429219609497559793 46900747071914707123169845)
              ·
                refine ⟨4396945037992003792797173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46900747071914707123169845 4396945037992003792797173)
                ·
                  refine ⟨412213597311750355574735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4396945037992003792797173 412213597311750355574735)
                  ·
                    rfl

theorem cell23_7225048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 5, 5].length) (baseStart_7225048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225048 prefixEnd_7225048 := by exact prefixLift 7225048
  have htrace : WordTrace (prefixWord ++ tailWord_7225048) baseStart_7225048 baseEnd_7225048 := by
    simpa [prefixWord, tailWord_7225048, baseEnd_7225048] using wordTrace_append hprefix tailTrace_7225048
  have hstable : (prefixWord ++ tailWord_7225048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225048).length < 2 ^ (prefixWord ++ tailWord_7225048).sum := by decide
  have hdescent : baseEnd_7225048 < baseStart_7225048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225059 : List Nat := [1, 1, 1, 7, 2, 1, 2, 2, 2, 2, 2]
def baseStart_7225059 : Nat := 118140960795 + 7225059 * 2 ^ 59
def prefixEnd_7225059 : Nat := 4983230072969 + 3 ^ 40 * 7225059 * 2
def baseEnd_7225059 : Nat := 3709928024092952657135065

theorem tailTrace_7225059 : CollatzResearch.WordTrace tailWord_7225059 prefixEnd_7225059 3709928024092952657135065 := by
  unfold tailWord_7225059
  simp only [CollatzResearch.WordTrace]
  refine ⟨263519550731852659683182231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175679700487901773122121487 263519550731852659683182231)
  ·
    refine ⟨395279326097778989524773347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263519550731852659683182231 395279326097778989524773347)
    ·
      refine ⟨592918989146668484287160021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395279326097778989524773347 592918989146668484287160021)
      ·
        refine ⟨13896538808125042600480313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 592918989146668484287160021 13896538808125042600480313)
        ·
          refine ⟨10422404106093781950360235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13896538808125042600480313 10422404106093781950360235)
          ·
            refine ⟨15633606159140672925540353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10422404106093781950360235 15633606159140672925540353)
            ·
              refine ⟨11725204619355504694155265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15633606159140672925540353 11725204619355504694155265)
              ·
                refine ⟨8793903464516628520616449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11725204619355504694155265 8793903464516628520616449)
                ·
                  refine ⟨6595427598387471390462337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8793903464516628520616449 6595427598387471390462337)
                  ·
                    refine ⟨4946570698790603542846753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6595427598387471390462337 4946570698790603542846753)
                    ·
                      refine ⟨3709928024092952657135065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4946570698790603542846753 3709928024092952657135065)
                      ·
                        rfl

theorem cell23_7225059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_7225059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225059 prefixEnd_7225059 := by exact prefixLift 7225059
  have htrace : WordTrace (prefixWord ++ tailWord_7225059) baseStart_7225059 baseEnd_7225059 := by
    simpa [prefixWord, tailWord_7225059, baseEnd_7225059] using wordTrace_append hprefix tailTrace_7225059
  have hstable : (prefixWord ++ tailWord_7225059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225059).length < 2 ^ (prefixWord ++ tailWord_7225059).sum := by decide
  have hdescent : baseEnd_7225059 < baseStart_7225059 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225068 : List Nat := [2, 2, 1, 1, 2, 2, 3, 1, 2, 5, 2]
def baseStart_7225068 : Nat := 118140960795 + 7225068 * 2 ^ 59
def prefixEnd_7225068 : Nat := 4983230072969 + 3 ^ 40 * 7225068 * 2
def baseEnd_7225068 : Nat := 3709932645418843121922523

theorem tailTrace_7225068 : CollatzResearch.WordTrace tailWord_7225068 prefixEnd_7225068 3709932645418843121922523 := by
  unfold tailWord_7225068
  simp only [CollatzResearch.WordTrace]
  refine ⟨131759939494410027110129929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175679919325880036146839905 131759939494410027110129929)
  ·
    refine ⟨98819954620807520332597447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131759939494410027110129929 98819954620807520332597447)
    ·
      refine ⟨148229931931211280498896171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98819954620807520332597447 148229931931211280498896171)
      ·
        refine ⟨222344897896816920748344257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148229931931211280498896171 222344897896816920748344257)
        ·
          refine ⟨166758673422612690561258193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222344897896816920748344257 166758673422612690561258193)
          ·
            refine ⟨125069005066959517920943645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166758673422612690561258193 125069005066959517920943645)
            ·
              refine ⟨46900876900109819220353867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125069005066959517920943645 46900876900109819220353867)
              ·
                refine ⟨70351315350164728830530801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46900876900109819220353867 70351315350164728830530801)
                ·
                  refine ⟨52763486512623546622898101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70351315350164728830530801 52763486512623546622898101)
                  ·
                    refine ⟨4946576860558457495896697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52763486512623546622898101 4946576860558457495896697)
                    ·
                      refine ⟨3709932645418843121922523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4946576860558457495896697 3709932645418843121922523)
                      ·
                        rfl

theorem cell23_7225068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 5, 2].length) (baseStart_7225068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225068 prefixEnd_7225068 := by exact prefixLift 7225068
  have htrace : WordTrace (prefixWord ++ tailWord_7225068) baseStart_7225068 baseEnd_7225068 := by
    simpa [prefixWord, tailWord_7225068, baseEnd_7225068] using wordTrace_append hprefix tailTrace_7225068
  have hstable : (prefixWord ++ tailWord_7225068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225068).length < 2 ^ (prefixWord ++ tailWord_7225068).sum := by decide
  have hdescent : baseEnd_7225068 < baseStart_7225068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225071 : List Nat := [1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 5]
def baseStart_7225071 : Nat := 118140960795 + 7225071 * 2 ^ 59
def prefixEnd_7225071 : Nat := 4983230072969 + 3 ^ 40 * 7225071 * 2
def baseEnd_7225071 : Nat := 3709934185860806610185009

theorem tailTrace_7225071 : CollatzResearch.WordTrace tailWord_7225071 prefixEnd_7225071 3709934185860806610185009 := by
  unfold tailWord_7225071
  simp only [CollatzResearch.WordTrace]
  refine ⟨263519988407809185732619067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175679992271872790488412711 263519988407809185732619067)
  ·
    refine ⟨395279982611713778598928601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263519988407809185732619067 395279982611713778598928601)
    ·
      refine ⟨296459986958785333949196451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395279982611713778598928601 296459986958785333949196451)
      ·
        refine ⟨444689980438178000923794677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296459986958785333949196451 444689980438178000923794677)
        ·
          refine ⟨41689685666079187586605751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 444689980438178000923794677 41689685666079187586605751)
          ·
            refine ⟨62534528499118781379908627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41689685666079187586605751 62534528499118781379908627)
            ·
              refine ⟨93801792748678172069862941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62534528499118781379908627 93801792748678172069862941)
              ·
                refine ⟨35175672280754314526198603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93801792748678172069862941 35175672280754314526198603)
                ·
                  refine ⟨52763508421131471789297905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35175672280754314526198603 52763508421131471789297905)
                  ·
                    refine ⟨39572631315848603841973429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52763508421131471789297905 39572631315848603841973429)
                    ·
                      refine ⟨3709934185860806610185009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39572631315848603841973429 3709934185860806610185009)
                      ·
                        rfl

theorem cell23_7225071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 5].length) (baseStart_7225071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225071 prefixEnd_7225071 := by exact prefixLift 7225071
  have htrace : WordTrace (prefixWord ++ tailWord_7225071) baseStart_7225071 baseEnd_7225071 := by
    simpa [prefixWord, tailWord_7225071, baseEnd_7225071] using wordTrace_append hprefix tailTrace_7225071
  have hstable : (prefixWord ++ tailWord_7225071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225071).length < 2 ^ (prefixWord ++ tailWord_7225071).sum := by decide
  have hdescent : baseEnd_7225071 < baseStart_7225071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225076 : List Nat := [2, 6, 1, 1, 1, 1, 2, 3, 2, 2, 2]
def baseStart_7225076 : Nat := 118140960795 + 7225076 * 2 ^ 59
def prefixEnd_7225076 : Nat := 4983230072969 + 3 ^ 40 * 7225076 * 2
def baseEnd_7225076 : Nat := 3709936753264079090622487

theorem tailTrace_7225076 : CollatzResearch.WordTrace tailWord_7225076 prefixEnd_7225076 3709936753264079090622487 := by
  unfold tailWord_7225076
  simp only [CollatzResearch.WordTrace]
  refine ⟨131760085386395535793275541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175680113848527381057700721 131760085386395535793275541)
  ·
    refine ⟨6176254002487290740309791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 131760085386395535793275541 6176254002487290740309791)
    ·
      refine ⟨9264381003730936110464687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6176254002487290740309791 9264381003730936110464687)
      ·
        refine ⟨13896571505596404165697031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9264381003730936110464687 13896571505596404165697031)
        ·
          refine ⟨20844857258394606248545547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13896571505596404165697031 20844857258394606248545547)
          ·
            refine ⟨31267285887591909372818321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20844857258394606248545547 31267285887591909372818321)
            ·
              refine ⟨23450464415693932029613741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31267285887591909372818321 23450464415693932029613741)
              ·
                refine ⟨8793924155885224511105153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23450464415693932029613741 8793924155885224511105153)
                ·
                  refine ⟨6595443116913918383328865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8793924155885224511105153 6595443116913918383328865)
                  ·
                    refine ⟨4946582337685438787496649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6595443116913918383328865 4946582337685438787496649)
                    ·
                      refine ⟨3709936753264079090622487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4946582337685438787496649 3709936753264079090622487)
                      ·
                        rfl

theorem cell23_7225076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_7225076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225076 prefixEnd_7225076 := by exact prefixLift 7225076
  have htrace : WordTrace (prefixWord ++ tailWord_7225076) baseStart_7225076 baseEnd_7225076 := by
    simpa [prefixWord, tailWord_7225076, baseEnd_7225076] using wordTrace_append hprefix tailTrace_7225076
  have hstable : (prefixWord ++ tailWord_7225076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225076).length < 2 ^ (prefixWord ++ tailWord_7225076).sum := by decide
  have hdescent : baseEnd_7225076 < baseStart_7225076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225098 : List Nat := [3, 1, 2, 2, 1, 4, 1, 1, 1, 3, 4]
def baseStart_7225098 : Nat := 118140960795 + 7225098 * 2 ^ 59
def prefixEnd_7225098 : Nat := 4983230072969 + 3 ^ 40 * 7225098 * 2
def baseEnd_7225098 : Nat := 3709948049838478004547385

theorem tailTrace_7225098 : CollatzResearch.WordTrace tailWord_7225098 prefixEnd_7225098 3709948049838478004547385 := by
  unfold tailWord_7225098
  simp only [CollatzResearch.WordTrace]
  refine ⟨65880243294677842335962987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175680648785807579562567965 65880243294677842335962987)
  ·
    refine ⟨98820364942016763503944481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65880243294677842335962987 98820364942016763503944481)
    ·
      refine ⟨74115273706512572627958361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98820364942016763503944481 74115273706512572627958361)
      ·
        refine ⟨55586455279884429470968771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74115273706512572627958361 55586455279884429470968771)
        ·
          refine ⟨83379682919826644206453157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55586455279884429470968771 83379682919826644206453157)
          ·
            refine ⟨15633690547467495788709967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83379682919826644206453157 15633690547467495788709967)
            ·
              refine ⟨23450535821201243683064951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15633690547467495788709967 23450535821201243683064951)
              ·
                refine ⟨35175803731801865524597427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23450535821201243683064951 35175803731801865524597427)
                ·
                  refine ⟨52763705597702798286896141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35175803731801865524597427 52763705597702798286896141)
                  ·
                    refine ⟨19786389599138549357586053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52763705597702798286896141 19786389599138549357586053)
                    ·
                      refine ⟨3709948049838478004547385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19786389599138549357586053 3709948049838478004547385)
                      ·
                        rfl

theorem cell23_7225098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_7225098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225098 prefixEnd_7225098 := by exact prefixLift 7225098
  have htrace : WordTrace (prefixWord ++ tailWord_7225098) baseStart_7225098 baseEnd_7225098 := by
    simpa [prefixWord, tailWord_7225098, baseEnd_7225098] using wordTrace_append hprefix tailTrace_7225098
  have hstable : (prefixWord ++ tailWord_7225098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225098).length < 2 ^ (prefixWord ++ tailWord_7225098).sum := by decide
  have hdescent : baseEnd_7225098 < baseStart_7225098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225125 : List Nat := [1, 3, 1, 2, 3, 3, 2, 1, 3, 4]
def baseStart_7225125 : Nat := 118140960795 + 7225125 * 2 ^ 59
def prefixEnd_7225125 : Nat := 4983230072969 + 3 ^ 40 * 7225125 * 2
def baseEnd_7225125 : Nat := 1236653971272049799636587

theorem tailTrace_7225125 : CollatzResearch.WordTrace tailWord_7225125 prefixEnd_7225125 1236653971272049799636587 := by
  unfold tailWord_7225125
  simp only [CollatzResearch.WordTrace]
  refine ⟨263521957949613552955084829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175681305299742368636723219 263521957949613552955084829)
  ·
    refine ⟨98820734231105082358156811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263521957949613552955084829 98820734231105082358156811)
    ·
      refine ⟨148231101346657623537235217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98820734231105082358156811 148231101346657623537235217)
      ·
        refine ⟨111173326009993217652926413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148231101346657623537235217 111173326009993217652926413)
        ·
          refine ⟨41689997253747456619847405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111173326009993217652926413 41689997253747456619847405)
          ·
            refine ⟨15633748970155296232442777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41689997253747456619847405 15633748970155296232442777)
            ·
              refine ⟨11725311727616472174332083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15633748970155296232442777 11725311727616472174332083)
              ·
                refine ⟨17587967591424708261498125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11725311727616472174332083 17587967591424708261498125)
                ·
                  refine ⟨6595487846784265598061797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17587967591424708261498125 6595487846784265598061797)
                  ·
                    refine ⟨1236653971272049799636587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6595487846784265598061797 1236653971272049799636587)
                    ·
                      rfl

theorem cell23_7225125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 3, 4].length) (baseStart_7225125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225125 prefixEnd_7225125 := by exact prefixLift 7225125
  have htrace : WordTrace (prefixWord ++ tailWord_7225125) baseStart_7225125 baseEnd_7225125 := by
    simpa [prefixWord, tailWord_7225125, baseEnd_7225125] using wordTrace_append hprefix tailTrace_7225125
  have hstable : (prefixWord ++ tailWord_7225125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225125).length < 2 ^ (prefixWord ++ tailWord_7225125).sum := by decide
  have hdescent : baseEnd_7225125 < baseStart_7225125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225142 : List Nat := [5, 1, 2, 2, 1, 1, 2, 2, 3, 4]
def baseStart_7225142 : Nat := 118140960795 + 7225142 * 2 ^ 59
def prefixEnd_7225142 : Nat := 4983230072969 + 3 ^ 40 * 7225142 * 2
def baseEnd_7225142 : Nat := 1236656880995758610799061

theorem tailTrace_7225142 : CollatzResearch.WordTrace tailWord_7225142 prefixEnd_7225142 1236656880995758610799061 := by
  unfold tailWord_7225142
  simp only [CollatzResearch.WordTrace]
  refine ⟨16470161124409497803653355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175681718660367976572302453 16470161124409497803653355)
  ·
    refine ⟨24705241686614246705480033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16470161124409497803653355 24705241686614246705480033)
    ·
      refine ⟨18528931264960685029110025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24705241686614246705480033 18528931264960685029110025)
      ·
        refine ⟨13896698448720513771832519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18528931264960685029110025 13896698448720513771832519)
        ·
          refine ⟨20845047673080770657748779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13896698448720513771832519 20845047673080770657748779)
          ·
            refine ⟨31267571509621155986623169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20845047673080770657748779 31267571509621155986623169)
            ·
              refine ⟨23450678632215866989967377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31267571509621155986623169 23450678632215866989967377)
              ·
                refine ⟨17588008974161900242475533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23450678632215866989967377 17588008974161900242475533)
                ·
                  refine ⟨6595503365310712590928325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17588008974161900242475533 6595503365310712590928325)
                  ·
                    refine ⟨1236656880995758610799061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6595503365310712590928325 1236656880995758610799061)
                    ·
                      rfl

theorem cell23_7225142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_7225142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225142 prefixEnd_7225142 := by exact prefixLift 7225142
  have htrace : WordTrace (prefixWord ++ tailWord_7225142) baseStart_7225142 baseEnd_7225142 := by
    simpa [prefixWord, tailWord_7225142, baseEnd_7225142] using wordTrace_append hprefix tailTrace_7225142
  have hstable : (prefixWord ++ tailWord_7225142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225142).length < 2 ^ (prefixWord ++ tailWord_7225142).sum := by decide
  have hdescent : baseEnd_7225142 < baseStart_7225142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225205 : List Nat := [1, 3, 4, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_7225205 : Nat := 118140960795 + 7225205 * 2 ^ 59
def prefixEnd_7225205 : Nat := 4983230072969 + 3 ^ 40 * 7225205 * 2
def baseEnd_7225205 : Nat := 3710002992268509085909393

theorem tailTrace_7225205 : CollatzResearch.WordTrace tailWord_7225205 prefixEnd_7225205 3710002992268509085909393 := by
  unfold tailWord_7225205
  simp only [CollatzResearch.WordTrace]
  refine ⟨263524875789323726617997069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175683250526215817745331379 263524875789323726617997069)
  ·
    refine ⟨98821828420996397481748901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263524875789323726617997069 98821828420996397481748901)
    ·
      refine ⟨18529092828936824527827919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98821828420996397481748901 18529092828936824527827919)
      ·
        refine ⟨27793639243405236791741879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18529092828936824527827919 27793639243405236791741879)
        ·
          refine ⟨41690458865107855187612819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27793639243405236791741879 41690458865107855187612819)
          ·
            refine ⟨62535688297661782781419229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41690458865107855187612819 62535688297661782781419229)
            ·
              refine ⟨23450883111623168543032211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62535688297661782781419229 23450883111623168543032211)
              ·
                refine ⟨35176324667434752814548317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23450883111623168543032211 35176324667434752814548317)
                ·
                  refine ⟨13191121750288032305455619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35176324667434752814548317 13191121750288032305455619)
                  ·
                    refine ⟨19786682625432048458183429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13191121750288032305455619 19786682625432048458183429)
                    ·
                      refine ⟨3710002992268509085909393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19786682625432048458183429 3710002992268509085909393)
                      ·
                        rfl

theorem cell23_7225205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_7225205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225205 prefixEnd_7225205 := by exact prefixLift 7225205
  have htrace : WordTrace (prefixWord ++ tailWord_7225205) baseStart_7225205 baseEnd_7225205 := by
    simpa [prefixWord, tailWord_7225205, baseEnd_7225205] using wordTrace_append hprefix tailTrace_7225205
  have hstable : (prefixWord ++ tailWord_7225205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225205).length < 2 ^ (prefixWord ++ tailWord_7225205).sum := by decide
  have hdescent : baseEnd_7225205 < baseStart_7225205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225245 : List Nat := [1, 4, 2, 1, 2, 4, 1, 8]
def baseStart_7225245 : Nat := 118140960795 + 7225245 * 2 ^ 59
def prefixEnd_7225245 : Nat := 4983230072969 + 3 ^ 40 * 7225245 * 2
def baseEnd_7225245 : Nat := 137408278944247738126267

theorem tailTrace_7225245 : CollatzResearch.WordTrace tailWord_7225245 prefixEnd_7225245 137408278944247738126267 := by
  unfold tailWord_7225245
  simp only [CollatzResearch.WordTrace]
  refine ⟨263526334709178813449453189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175684223139452542299635459 263526334709178813449453189)
  ·
    refine ⟨49411187757971027521772473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263526334709178813449453189 49411187757971027521772473)
    ·
      refine ⟨37058390818478270641329355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49411187757971027521772473 37058390818478270641329355)
      ·
        refine ⟨55587586227717405961994033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37058390818478270641329355 55587586227717405961994033)
        ·
          refine ⟨41690689670788054471495525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55587586227717405961994033 41690689670788054471495525)
          ·
            refine ⟨7817004313272760213405411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41690689670788054471495525 7817004313272760213405411)
            ·
              refine ⟨11725506469909140320108117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7817004313272760213405411 11725506469909140320108117)
              ·
                refine ⟨137408278944247738126267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11725506469909140320108117 137408278944247738126267)
                ·
                  rfl

theorem cell23_7225245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 8].length) (baseStart_7225245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225245 prefixEnd_7225245 := by exact prefixLift 7225245
  have htrace : WordTrace (prefixWord ++ tailWord_7225245) baseStart_7225245 baseEnd_7225245 := by
    simpa [prefixWord, tailWord_7225245, baseEnd_7225245] using wordTrace_append hprefix tailTrace_7225245
  have hstable : (prefixWord ++ tailWord_7225245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225245).length < 2 ^ (prefixWord ++ tailWord_7225245).sum := by decide
  have hdescent : baseEnd_7225245 < baseStart_7225245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225306 : List Nat := [3, 1, 1, 2, 5, 1, 3, 1, 2, 1, 3]
def baseStart_7225306 : Nat := 118140960795 + 7225306 * 2 ^ 59
def prefixEnd_7225306 : Nat := 4983230072969 + 3 ^ 40 * 7225306 * 2
def baseEnd_7225306 : Nat := 3710054853814613190746429

theorem tailTrace_7225306 : CollatzResearch.WordTrace tailWord_7225306 prefixEnd_7225306 3710054853814613190746429 := by
  unfold tailWord_7225306
  simp only [CollatzResearch.WordTrace]
  refine ⟨65882139890489455216855943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175685706374638547244949181 65882139890489455216855943)
  ·
    refine ⟨98823209835734182825283915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65882139890489455216855943 98823209835734182825283915)
    ·
      refine ⟨148234814753601274237925873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98823209835734182825283915 148234814753601274237925873)
      ·
        refine ⟨111176111065200955678444405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148234814753601274237925873 111176111065200955678444405)
        ·
          refine ⟨10422760412362589594854163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111176111065200955678444405 10422760412362589594854163)
          ·
            refine ⟨15634140618543884392281245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10422760412362589594854163 15634140618543884392281245)
            ·
              refine ⟨5862802731953956647105467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15634140618543884392281245 5862802731953956647105467)
              ·
                refine ⟨8794204097930934970658201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5862802731953956647105467 8794204097930934970658201)
                ·
                  refine ⟨6595653073448201227993651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8794204097930934970658201 6595653073448201227993651)
                  ·
                    refine ⟨9893479610172301841990477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6595653073448201227993651 9893479610172301841990477)
                    ·
                      refine ⟨3710054853814613190746429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9893479610172301841990477 3710054853814613190746429)
                      ·
                        rfl

theorem cell23_7225306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 2, 1, 3].length) (baseStart_7225306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225306 prefixEnd_7225306 := by exact prefixLift 7225306
  have htrace : WordTrace (prefixWord ++ tailWord_7225306) baseStart_7225306 baseEnd_7225306 := by
    simpa [prefixWord, tailWord_7225306, baseEnd_7225306] using wordTrace_append hprefix tailTrace_7225306
  have hstable : (prefixWord ++ tailWord_7225306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225306).length < 2 ^ (prefixWord ++ tailWord_7225306).sum := by decide
  have hdescent : baseEnd_7225306 < baseStart_7225306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225338 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 2, 4, 6]
def baseStart_7225338 : Nat := 118140960795 + 7225338 * 2 ^ 59
def prefixEnd_7225338 : Nat := 4983230072969 + 3 ^ 40 * 7225338 * 2
def baseEnd_7225338 : Nat := 3710071285195557065546281

theorem tailTrace_7225338 : CollatzResearch.WordTrace tailWord_7225338 prefixEnd_7225338 3710071285195557065546281 := by
  unfold tailWord_7225338
  simp only [CollatzResearch.WordTrace]
  refine ⟨65882431674460472583147167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175686484465227926888392445 65882431674460472583147167)
  ·
    refine ⟨98823647511690708874720751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65882431674460472583147167 98823647511690708874720751)
    ·
      refine ⟨148235471267536063312081127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98823647511690708874720751 148235471267536063312081127)
      ·
        refine ⟨222353206901304094968121691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148235471267536063312081127 222353206901304094968121691)
        ·
          refine ⟨333529810351956142452182537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222353206901304094968121691 333529810351956142452182537)
          ·
            refine ⟨250147357763967106839136903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333529810351956142452182537 250147357763967106839136903)
            ·
              refine ⟨375221036645950660258705355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250147357763967106839136903 375221036645950660258705355)
              ·
                refine ⟨562831554968925990388058033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 375221036645950660258705355 562831554968925990388058033)
                ·
                  refine ⟨422123666226694492791043525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 562831554968925990388058033 422123666226694492791043525)
                  ·
                    refine ⟨79148187417505217398320661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 422123666226694492791043525 79148187417505217398320661)
                    ·
                      refine ⟨3710071285195557065546281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79148187417505217398320661 3710071285195557065546281)
                      ·
                        rfl

theorem cell23_7225338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_7225338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225338 prefixEnd_7225338 := by exact prefixLift 7225338
  have htrace : WordTrace (prefixWord ++ tailWord_7225338) baseStart_7225338 baseEnd_7225338 := by
    simpa [prefixWord, tailWord_7225338, baseEnd_7225338] using wordTrace_append hprefix tailTrace_7225338
  have hstable : (prefixWord ++ tailWord_7225338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225338).length < 2 ^ (prefixWord ++ tailWord_7225338).sum := by decide
  have hdescent : baseEnd_7225338 < baseStart_7225338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225357 : List Nat := [1, 7, 1, 2, 1, 2, 2, 1, 2, 1, 3]
def baseStart_7225357 : Nat := 118140960795 + 7225357 * 2 ^ 59
def prefixEnd_7225357 : Nat := 4983230072969 + 3 ^ 40 * 7225357 * 2
def baseEnd_7225357 : Nat := 3710081041327992491208695

theorem tailTrace_7225357 : CollatzResearch.WordTrace tailWord_7225357 prefixEnd_7225357 3710081041327992491208695 := by
  unfold tailWord_7225357
  simp only [CollatzResearch.WordTrace]
  refine ⟨263530419684773056577530325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175686946456515371051686883 263530419684773056577530325)
  ·
    refine ⟨6176494211361868513535867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 263530419684773056577530325 6176494211361868513535867)
    ·
      refine ⟨9264741317042802770303801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6176494211361868513535867 9264741317042802770303801)
      ·
        refine ⟨6948555987782102077727851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9264741317042802770303801 6948555987782102077727851)
        ·
          refine ⟨10422833981673153116591777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6948555987782102077727851 10422833981673153116591777)
          ·
            refine ⟨7817125486254864837443833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10422833981673153116591777 7817125486254864837443833)
            ·
              refine ⟨5862844114691148628082875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7817125486254864837443833 5862844114691148628082875)
              ·
                refine ⟨8794266172036722942124313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5862844114691148628082875 8794266172036722942124313)
                ·
                  refine ⟨6595699629027542206593235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8794266172036722942124313 6595699629027542206593235)
                  ·
                    refine ⟨9893549443541313309889853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6595699629027542206593235 9893549443541313309889853)
                    ·
                      refine ⟨3710081041327992491208695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9893549443541313309889853 3710081041327992491208695)
                      ·
                        rfl

theorem cell23_7225357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_7225357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225357 prefixEnd_7225357 := by exact prefixLift 7225357
  have htrace : WordTrace (prefixWord ++ tailWord_7225357) baseStart_7225357 baseEnd_7225357 := by
    simpa [prefixWord, tailWord_7225357, baseEnd_7225357] using wordTrace_append hprefix tailTrace_7225357
  have hstable : (prefixWord ++ tailWord_7225357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225357).length < 2 ^ (prefixWord ++ tailWord_7225357).sum := by decide
  have hdescent : baseEnd_7225357 < baseStart_7225357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225402 : List Nat := [3, 1, 1, 1, 3, 1, 1, 4, 2, 4, 2]
def baseStart_7225402 : Nat := 118140960795 + 7225402 * 2 ^ 59
def prefixEnd_7225402 : Nat := 4983230072969 + 3 ^ 40 * 7225402 * 2
def baseEnd_7225402 : Nat := 3710104147957444815145987

theorem tailTrace_7225402 : CollatzResearch.WordTrace tailWord_7225402 prefixEnd_7225402 3710104147957444815145987 := by
  unfold tailWord_7225402
  simp only [CollatzResearch.WordTrace]
  refine ⟨65883015242402507315729615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175688040646406686175278973 65883015242402507315729615)
  ·
    refine ⟨98824522863603760973594423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65883015242402507315729615 98824522863603760973594423)
    ·
      refine ⟨148236784295405641460391635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98824522863603760973594423 148236784295405641460391635)
      ·
        refine ⟨222355176443108462190587453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148236784295405641460391635 222355176443108462190587453)
        ·
          refine ⟨83383191166165673321470295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222355176443108462190587453 83383191166165673321470295)
          ·
            refine ⟨125074786749248509982205443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83383191166165673321470295 125074786749248509982205443)
            ·
              refine ⟨187612180123872764973308165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125074786749248509982205443 187612180123872764973308165)
              ·
                refine ⟨35177283773226143432495281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187612180123872764973308165 35177283773226143432495281)
                ·
                  refine ⟨26382962829919607574371461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35177283773226143432495281 26382962829919607574371461)
                  ·
                    refine ⟨4946805530609926420194649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26382962829919607574371461 4946805530609926420194649)
                    ·
                      refine ⟨3710104147957444815145987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4946805530609926420194649 3710104147957444815145987)
                      ·
                        rfl

theorem cell23_7225402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 2, 4, 2].length) (baseStart_7225402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225402 prefixEnd_7225402 := by exact prefixLift 7225402
  have htrace : WordTrace (prefixWord ++ tailWord_7225402) baseStart_7225402 baseEnd_7225402 := by
    simpa [prefixWord, tailWord_7225402, baseEnd_7225402] using wordTrace_append hprefix tailTrace_7225402
  have hstable : (prefixWord ++ tailWord_7225402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225402).length < 2 ^ (prefixWord ++ tailWord_7225402).sum := by decide
  have hdescent : baseEnd_7225402 < baseStart_7225402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225405 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 2, 3, 5]
def baseStart_7225405 : Nat := 118140960795 + 7225405 * 2 ^ 59
def prefixEnd_7225405 : Nat := 4983230072969 + 3 ^ 40 * 7225405 * 2
def baseEnd_7225405 : Nat := 3710105688399408303408473

theorem tailTrace_7225405 : CollatzResearch.WordTrace tailWord_7225405 prefixEnd_7225405 3710105688399408303408473 := by
  unfold tailWord_7225405
  simp only [CollatzResearch.WordTrace]
  refine ⟨263532170388599160775277669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175688113592399440516851779 263532170388599160775277669)
  ·
    refine ⟨49412281947862342645364563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263532170388599160775277669 49412281947862342645364563)
    ·
      refine ⟨74118422921793513968046845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49412281947862342645364563 74118422921793513968046845)
      ·
        refine ⟨27794408595672567738017567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74118422921793513968046845 27794408595672567738017567)
        ·
          refine ⟨41691612893508851607026351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27794408595672567738017567 41691612893508851607026351)
          ·
            refine ⟨62537419340263277410539527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41691612893508851607026351 62537419340263277410539527)
            ·
              refine ⟨93806129010394916115809291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62537419340263277410539527 93806129010394916115809291)
              ·
                refine ⟨140709193515592374173713937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93806129010394916115809291 140709193515592374173713937)
                ·
                  refine ⟨105531895136694280630285453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140709193515592374173713937 105531895136694280630285453)
                  ·
                    refine ⟨39574460676260355236357045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105531895136694280630285453 39574460676260355236357045)
                    ·
                      refine ⟨3710105688399408303408473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39574460676260355236357045 3710105688399408303408473)
                      ·
                        rfl

theorem cell23_7225405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_7225405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225405 prefixEnd_7225405 := by exact prefixLift 7225405
  have htrace : WordTrace (prefixWord ++ tailWord_7225405) baseStart_7225405 baseEnd_7225405 := by
    simpa [prefixWord, tailWord_7225405, baseEnd_7225405] using wordTrace_append hprefix tailTrace_7225405
  have hstable : (prefixWord ++ tailWord_7225405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225405).length < 2 ^ (prefixWord ++ tailWord_7225405).sum := by decide
  have hdescent : baseEnd_7225405 < baseStart_7225405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225462 : List Nat := [5, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6]
def baseStart_7225462 : Nat := 118140960795 + 7225462 * 2 ^ 59
def prefixEnd_7225462 : Nat := 4983230072969 + 3 ^ 40 * 7225462 * 2
def baseEnd_7225462 : Nat := 3710134956796714580395711

theorem tailTrace_7225462 : CollatzResearch.WordTrace tailWord_7225462 prefixEnd_7225462 3710134956796714580395711 := by
  unfold tailWord_7225462
  simp only [CollatzResearch.WordTrace]
  refine ⟨16470890584337041219381415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175689499566261773006735093 16470890584337041219381415)
  ·
    refine ⟨24706335876505561829072123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16470890584337041219381415 24706335876505561829072123)
    ·
      refine ⟨37059503814758342743608185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24706335876505561829072123 37059503814758342743608185)
      ·
        refine ⟨27794627861068757057706139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37059503814758342743608185 27794627861068757057706139)
        ·
          refine ⟨41691941791603135586559209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27794627861068757057706139 41691941791603135586559209)
          ·
            refine ⟨31268956343702351689919407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41691941791603135586559209 31268956343702351689919407)
            ·
              refine ⟨46903434515553527534879111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31268956343702351689919407 46903434515553527534879111)
              ·
                refine ⟨70355151773330291302318667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46903434515553527534879111 70355151773330291302318667)
                ·
                  refine ⟨105532727659995436953478001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70355151773330291302318667 105532727659995436953478001)
                  ·
                    refine ⟨79149545744996577715108501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105532727659995436953478001 79149545744996577715108501)
                    ·
                      refine ⟨3710134956796714580395711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79149545744996577715108501 3710134956796714580395711)
                      ·
                        rfl

theorem cell23_7225462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_7225462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225462 prefixEnd_7225462 := by exact prefixLift 7225462
  have htrace : WordTrace (prefixWord ++ tailWord_7225462) baseStart_7225462 baseEnd_7225462 := by
    simpa [prefixWord, tailWord_7225462, baseEnd_7225462] using wordTrace_append hprefix tailTrace_7225462
  have hstable : (prefixWord ++ tailWord_7225462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225462).length < 2 ^ (prefixWord ++ tailWord_7225462).sum := by decide
  have hdescent : baseEnd_7225462 < baseStart_7225462 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225469 : List Nat := [1, 4, 1, 1, 3, 2, 1, 3, 3, 1, 3]
def baseStart_7225469 : Nat := 118140960795 + 7225469 * 2 ^ 59
def prefixEnd_7225469 : Nat := 4983230072969 + 3 ^ 40 * 7225469 * 2
def baseEnd_7225469 : Nat := 3710138551161296053008179

theorem tailTrace_7225469 : CollatzResearch.WordTrace tailWord_7225469 prefixEnd_7225469 3710138551161296053008179 := by
  unfold tailWord_7225469
  simp only [CollatzResearch.WordTrace]
  refine ⟨263534504660367299705607461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175689669773578199803738307 263534504660367299705607461)
  ·
    refine ⟨49412719623818868694801399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263534504660367299705607461 49412719623818868694801399)
    ·
      refine ⟨74119079435728303042202099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49412719623818868694801399 74119079435728303042202099)
      ·
        refine ⟨111178619153592454563303149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74119079435728303042202099 111178619153592454563303149)
        ·
          refine ⟨41691982182597170461238681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111178619153592454563303149 41691982182597170461238681)
          ·
            refine ⟨31268986636947877845929011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41691982182597170461238681 31268986636947877845929011)
            ·
              refine ⟨46903479955421816768893517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31268986636947877845929011 46903479955421816768893517)
              ·
                refine ⟨17588804983283181288335069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46903479955421816768893517 17588804983283181288335069)
                ·
                  refine ⟨6595801868731192983125651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17588804983283181288335069 6595801868731192983125651)
                  ·
                    refine ⟨9893702803096789474688477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6595801868731192983125651 9893702803096789474688477)
                    ·
                      refine ⟨3710138551161296053008179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9893702803096789474688477 3710138551161296053008179)
                      ·
                        rfl

theorem cell23_7225469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 3, 1, 3].length) (baseStart_7225469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225469 prefixEnd_7225469 := by exact prefixLift 7225469
  have htrace : WordTrace (prefixWord ++ tailWord_7225469) baseStart_7225469 baseEnd_7225469 := by
    simpa [prefixWord, tailWord_7225469, baseEnd_7225469] using wordTrace_append hprefix tailTrace_7225469
  have hstable : (prefixWord ++ tailWord_7225469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225469).length < 2 ^ (prefixWord ++ tailWord_7225469).sum := by decide
  have hdescent : baseEnd_7225469 < baseStart_7225469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225503 : List Nat := [1, 1, 2, 6, 1, 1, 3, 3, 1, 1, 3]
def baseStart_7225503 : Nat := 118140960795 + 7225503 * 2 ^ 59
def prefixEnd_7225503 : Nat := 4983230072969 + 3 ^ 40 * 7225503 * 2
def baseEnd_7225503 : Nat := 3710156009503548919983023

theorem tailTrace_7225503 : CollatzResearch.WordTrace tailWord_7225503 prefixEnd_7225503 3710156009503548919983023 := by
  unfold tailWord_7225503
  simp only [CollatzResearch.WordTrace]
  refine ⟨263535744742244123512345163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175690496494829415674896775 263535744742244123512345163)
  ·
    refine ⟨395303617113366185268517745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263535744742244123512345163 395303617113366185268517745)
    ·
      refine ⟨296477712835024638951388309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395303617113366185268517745 296477712835024638951388309)
      ·
        refine ⟨13897392789141779950846327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 296477712835024638951388309 13897392789141779950846327)
        ·
          refine ⟨20846089183712669926269491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13897392789141779950846327 20846089183712669926269491)
          ·
            refine ⟨31269133775569004889404237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20846089183712669926269491 31269133775569004889404237)
            ·
              refine ⟨11725925165838376833526589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31269133775569004889404237 11725925165838376833526589)
              ·
                refine ⟨4397221937189391312572471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11725925165838376833526589 4397221937189391312572471)
                ·
                  refine ⟨6595832905784086968858707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4397221937189391312572471 6595832905784086968858707)
                  ·
                    refine ⟨9893749358676130453288061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6595832905784086968858707 9893749358676130453288061)
                    ·
                      refine ⟨3710156009503548919983023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9893749358676130453288061 3710156009503548919983023)
                      ·
                        rfl

theorem cell23_7225503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_7225503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225503 prefixEnd_7225503 := by exact prefixLift 7225503
  have htrace : WordTrace (prefixWord ++ tailWord_7225503) baseStart_7225503 baseEnd_7225503 := by
    simpa [prefixWord, tailWord_7225503, baseEnd_7225503] using wordTrace_append hprefix tailTrace_7225503
  have hstable : (prefixWord ++ tailWord_7225503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225503).length < 2 ^ (prefixWord ++ tailWord_7225503).sum := by decide
  have hdescent : baseEnd_7225503 < baseStart_7225503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225535 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 6]
def baseStart_7225535 : Nat := 118140960795 + 7225535 * 2 ^ 59
def prefixEnd_7225535 : Nat := 4983230072969 + 3 ^ 40 * 7225535 * 2
def baseEnd_7225535 : Nat := 3710172440884492794782875

theorem tailTrace_7225535 : CollatzResearch.WordTrace tailWord_7225535 prefixEnd_7225535 3710172440884492794782875 := by
  unfold tailWord_7225535
  simp only [CollatzResearch.WordTrace]
  refine ⟨263536911878128192977510059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175691274585418795318340039 263536911878128192977510059)
  ·
    refine ⟨395305367817192289466265089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263536911878128192977510059 395305367817192289466265089)
    ·
      refine ⟨296479025862894217099698817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395305367817192289466265089 296479025862894217099698817)
      ·
        refine ⟨222359269397170662824774113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296479025862894217099698817 222359269397170662824774113)
        ·
          refine ⟨166769452047877997118580585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222359269397170662824774113 166769452047877997118580585)
          ·
            refine ⟨125077089035908497838935439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166769452047877997118580585 125077089035908497838935439)
            ·
              refine ⟨187615633553862746758403159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125077089035908497838935439 187615633553862746758403159)
              ·
                refine ⟨281423450330794120137604739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187615633553862746758403159 281423450330794120137604739)
                ·
                  refine ⟨422135175496191180206407109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 281423450330794120137604739 422135175496191180206407109)
                  ·
                    refine ⟨79150345405535846288701333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 422135175496191180206407109 79150345405535846288701333)
                    ·
                      refine ⟨3710172440884492794782875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79150345405535846288701333 3710172440884492794782875)
                      ·
                        rfl

theorem cell23_7225535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_7225535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225535 prefixEnd_7225535 := by exact prefixLift 7225535
  have htrace : WordTrace (prefixWord ++ tailWord_7225535) baseStart_7225535 baseEnd_7225535 := by
    simpa [prefixWord, tailWord_7225535, baseEnd_7225535] using wordTrace_append hprefix tailTrace_7225535
  have hstable : (prefixWord ++ tailWord_7225535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225535).length < 2 ^ (prefixWord ++ tailWord_7225535).sum := by decide
  have hdescent : baseEnd_7225535 < baseStart_7225535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225536 : List Nat := [2, 1, 1, 2, 5, 1, 4, 1, 2, 4]
def baseStart_7225536 : Nat := 118140960795 + 7225536 * 2 ^ 59
def prefixEnd_7225536 : Nat := 4983230072969 + 3 ^ 40 * 7225536 * 2
def baseEnd_7225536 : Nat := 1236724318121715763623457

theorem tailTrace_7225536 : CollatzResearch.WordTrace tailWord_7225536 prefixEnd_7225536 1236724318121715763623457 := by
  unfold tailWord_7225536
  simp only [CollatzResearch.WordTrace]
  refine ⟨131768474175562285074148231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175691298900749713432197641 131768474175562285074148231)
  ·
    refine ⟨197652711263343427611222347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131768474175562285074148231 197652711263343427611222347)
    ·
      refine ⟨296479066895015141416833521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197652711263343427611222347 296479066895015141416833521)
      ·
        refine ⟨222359300171261356062625141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296479066895015141416833521 222359300171261356062625141)
        ·
          refine ⟨20846184391055752130871107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 222359300171261356062625141 20846184391055752130871107)
          ·
            refine ⟨31269276586583628196306661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20846184391055752130871107 31269276586583628196306661)
            ·
              refine ⟨5862989359984430286807499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31269276586583628196306661 5862989359984430286807499)
              ·
                refine ⟨8794484039976645430211249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5862989359984430286807499 8794484039976645430211249)
                ·
                  refine ⟨6595863029982484072658437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8794484039976645430211249 6595863029982484072658437)
                  ·
                    refine ⟨1236724318121715763623457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6595863029982484072658437 1236724318121715763623457)
                    ·
                      rfl

theorem cell23_7225536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 2, 4].length) (baseStart_7225536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225536 prefixEnd_7225536 := by exact prefixLift 7225536
  have htrace : WordTrace (prefixWord ++ tailWord_7225536) baseStart_7225536 baseEnd_7225536 := by
    simpa [prefixWord, tailWord_7225536, baseEnd_7225536] using wordTrace_append hprefix tailTrace_7225536
  have hstable : (prefixWord ++ tailWord_7225536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225536).length < 2 ^ (prefixWord ++ tailWord_7225536).sum := by decide
  have hdescent : baseEnd_7225536 < baseStart_7225536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225545 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 4, 7]
def baseStart_7225545 : Nat := 118140960795 + 7225545 * 2 ^ 59
def prefixEnd_7225545 : Nat := 4983230072969 + 3 ^ 40 * 7225545 * 2
def baseEnd_7225545 : Nat := 1236725858563679251885943

theorem tailTrace_7225545 : CollatzResearch.WordTrace tailWord_7225545 prefixEnd_7225545 1236725858563679251885943 := by
  unfold tailWord_7225545
  simp only [CollatzResearch.WordTrace]
  refine ⟨263537276608091964685374089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175691517738727976456916059 263537276608091964685374089)
  ·
    refine ⟨197652957456068973514030567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263537276608091964685374089 197652957456068973514030567)
    ·
      refine ⟨296479436184103460271045851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197652957456068973514030567 296479436184103460271045851)
      ·
        refine ⟨444719154276155190406568777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296479436184103460271045851 444719154276155190406568777)
        ·
          refine ⟨333539365707116392804926583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444719154276155190406568777 333539365707116392804926583)
          ·
            refine ⟨500309048560674589207389875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333539365707116392804926583 500309048560674589207389875)
            ·
              refine ⟨750463572841011883811084813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500309048560674589207389875 750463572841011883811084813)
              ·
                refine ⟨281423839815379456429156805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 750463572841011883811084813 281423839815379456429156805)
                ·
                  refine ⟨52766969965383648080466901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 281423839815379456429156805 52766969965383648080466901)
                  ·
                    refine ⟨1236725858563679251885943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52766969965383648080466901 1236725858563679251885943)
                    ·
                      rfl

theorem cell23_7225545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 7].length) (baseStart_7225545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225545 prefixEnd_7225545 := by exact prefixLift 7225545
  have htrace : WordTrace (prefixWord ++ tailWord_7225545) baseStart_7225545 baseEnd_7225545 := by
    simpa [prefixWord, tailWord_7225545, baseEnd_7225545] using wordTrace_append hprefix tailTrace_7225545
  have hstable : (prefixWord ++ tailWord_7225545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225545).length < 2 ^ (prefixWord ++ tailWord_7225545).sum := by decide
  have hdescent : baseEnd_7225545 < baseStart_7225545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225576 : List Nat := [2, 1, 4, 1, 2, 2, 1, 4, 2, 1, 3]
def baseStart_7225576 : Nat := 118140960795 + 7225576 * 2 ^ 59
def prefixEnd_7225576 : Nat := 4983230072969 + 3 ^ 40 * 7225576 * 2
def baseEnd_7225576 : Nat := 3710193493591327134370187

theorem tailTrace_7225576 : CollatzResearch.WordTrace tailWord_7225576 prefixEnd_7225576 3710193493591327134370187 := by
  unfold tailWord_7225576
  simp only [CollatzResearch.WordTrace]
  refine ⟨131769203635489828489876291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175692271513986437986501721 131769203635489828489876291)
  ·
    refine ⟨197653805453234742734814437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131769203635489828489876291 197653805453234742734814437)
    ·
      refine ⟨37060088522481514262777707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197653805453234742734814437 37060088522481514262777707)
      ·
        refine ⟨55590132783722271394166561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37060088522481514262777707 55590132783722271394166561)
        ·
          refine ⟨41692599587791703545624921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55590132783722271394166561 41692599587791703545624921)
          ·
            refine ⟨31269449690843777659218691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41692599587791703545624921 31269449690843777659218691)
            ·
              refine ⟨46904174536265666488828037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31269449690843777659218691 46904174536265666488828037)
              ·
                refine ⟨8794532725549812466655257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46904174536265666488828037 8794532725549812466655257)
                ·
                  refine ⟨6595899544162359349991443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8794532725549812466655257 6595899544162359349991443)
                  ·
                    refine ⟨9893849316243539024987165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6595899544162359349991443 9893849316243539024987165)
                    ·
                      refine ⟨3710193493591327134370187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9893849316243539024987165 3710193493591327134370187)
                      ·
                        rfl

theorem cell23_7225576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_7225576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225576 prefixEnd_7225576 := by exact prefixLift 7225576
  have htrace : WordTrace (prefixWord ++ tailWord_7225576) baseStart_7225576 baseEnd_7225576 := by
    simpa [prefixWord, tailWord_7225576, baseEnd_7225576] using wordTrace_append hprefix tailTrace_7225576
  have hstable : (prefixWord ++ tailWord_7225576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225576).length < 2 ^ (prefixWord ++ tailWord_7225576).sum := by decide
  have hdescent : baseEnd_7225576 < baseStart_7225576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225586 : List Nat := [3, 2, 1, 3, 2, 1, 1, 2, 3, 3, 2]
def baseStart_7225586 : Nat := 118140960795 + 7225586 * 2 ^ 59
def prefixEnd_7225586 : Nat := 4983230072969 + 3 ^ 40 * 7225586 * 2
def baseEnd_7225586 : Nat := 3710198628397872095245141

theorem tailTrace_7225586 : CollatzResearch.WordTrace tailWord_7225586 prefixEnd_7225586 3710198628397872095245141 := by
  unfold tailWord_7225586
  simp only [CollatzResearch.WordTrace]
  refine ⟨65884693000235857171904153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175692514667295619125077741 65884693000235857171904153)
  ·
    refine ⟨49413519750176892878928115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65884693000235857171904153 49413519750176892878928115)
    ·
      refine ⟨74120279625265339318392173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49413519750176892878928115 74120279625265339318392173)
      ·
        refine ⟨27795104859474502244397065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74120279625265339318392173 27795104859474502244397065)
        ·
          refine ⟨20846328644605876683297799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27795104859474502244397065 20846328644605876683297799)
          ·
            refine ⟨31269492966908815024946699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20846328644605876683297799 31269492966908815024946699)
            ·
              refine ⟨46904239450363222537420049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31269492966908815024946699 46904239450363222537420049)
              ·
                refine ⟨35178179587772416903065037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46904239450363222537420049 35178179587772416903065037)
                ·
                  refine ⟨13191817345414656338649389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35178179587772416903065037 13191817345414656338649389)
                  ·
                    refine ⟨4946931504530496126993521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13191817345414656338649389 4946931504530496126993521)
                    ·
                      refine ⟨3710198628397872095245141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4946931504530496126993521 3710198628397872095245141)
                      ·
                        rfl

theorem cell23_7225586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_7225586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225586 prefixEnd_7225586 := by exact prefixLift 7225586
  have htrace : WordTrace (prefixWord ++ tailWord_7225586) baseStart_7225586 baseEnd_7225586 := by
    simpa [prefixWord, tailWord_7225586, baseEnd_7225586] using wordTrace_append hprefix tailTrace_7225586
  have hstable : (prefixWord ++ tailWord_7225586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225586).length < 2 ^ (prefixWord ++ tailWord_7225586).sum := by decide
  have hdescent : baseEnd_7225586 < baseStart_7225586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225612 : List Nat := [2, 2, 1, 2, 2, 2, 1, 2, 1, 4, 4]
def baseStart_7225612 : Nat := 118140960795 + 7225612 * 2 ^ 59
def prefixEnd_7225612 : Nat := 4983230072969 + 3 ^ 40 * 7225612 * 2
def baseEnd_7225612 : Nat := 3710211978894888993520021

theorem tailTrace_7225612 : CollatzResearch.WordTrace tailWord_7225612 prefixEnd_7225612 3710211978894888993520021 := by
  unfold tailWord_7225612
  simp only [CollatzResearch.WordTrace]
  refine ⟨131769860149424617564031545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175693146865899490085375393 131769860149424617564031545)
  ·
    refine ⟨98827395112068463173023659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131769860149424617564031545 98827395112068463173023659)
    ·
      refine ⟨148241092668102694759535489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98827395112068463173023659 148241092668102694759535489)
      ·
        refine ⟨111180819501077021069651617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148241092668102694759535489 111180819501077021069651617)
        ·
          refine ⟨83385614625807765802238713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111180819501077021069651617 83385614625807765802238713)
          ·
            refine ⟨62539210969355824351679035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83385614625807765802238713 62539210969355824351679035)
            ·
              refine ⟨93808816454033736527518553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62539210969355824351679035 93808816454033736527518553)
              ·
                refine ⟨70356612340525302395638915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93808816454033736527518553 70356612340525302395638915)
                ·
                  refine ⟨105534918510787953593458373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70356612340525302395638915 105534918510787953593458373)
                  ·
                    refine ⟨19787797220772741298773445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105534918510787953593458373 19787797220772741298773445)
                    ·
                      refine ⟨3710211978894888993520021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19787797220772741298773445 3710211978894888993520021)
                      ·
                        rfl

theorem cell23_7225612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_7225612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225612 prefixEnd_7225612 := by exact prefixLift 7225612
  have htrace : WordTrace (prefixWord ++ tailWord_7225612) baseStart_7225612 baseEnd_7225612 := by
    simpa [prefixWord, tailWord_7225612, baseEnd_7225612] using wordTrace_append hprefix tailTrace_7225612
  have hstable : (prefixWord ++ tailWord_7225612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225612).length < 2 ^ (prefixWord ++ tailWord_7225612).sum := by decide
  have hdescent : baseEnd_7225612 < baseStart_7225612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225633 : List Nat := [1, 2, 3, 2, 1, 1, 5, 2, 2, 2, 2]
def baseStart_7225633 : Nat := 118140960795 + 7225633 * 2 ^ 59
def prefixEnd_7225633 : Nat := 4983230072969 + 3 ^ 40 * 7225633 * 2
def baseEnd_7225633 : Nat := 3710222761988633411357425

theorem tailTrace_7225633 : CollatzResearch.WordTrace tailWord_7225633 prefixEnd_7225633 3710222761988633411357425 := by
  unfold tailWord_7225633
  simp only [CollatzResearch.WordTrace]
  refine ⟨263540486231773155714577553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175693657487848770476385035 263540486231773155714577553)
  ·
    refine ⟨197655364673829866785933165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263540486231773155714577553 197655364673829866785933165)
    ·
      refine ⟨74120761752686200044724937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197655364673829866785933165 74120761752686200044724937)
      ·
        refine ⟨55590571314514650033543703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74120761752686200044724937 55590571314514650033543703)
        ·
          refine ⟨83385856971771975050315555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55590571314514650033543703 83385856971771975050315555)
          ·
            refine ⟨125078785457657962575473333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83385856971771975050315555 125078785457657962575473333)
            ·
              refine ⟨11726136136655433991450625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125078785457657962575473333 11726136136655433991450625)
              ·
                refine ⟨8794602102491575493587969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11726136136655433991450625 8794602102491575493587969)
                ·
                  refine ⟨6595951576868681620190977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8794602102491575493587969 6595951576868681620190977)
                  ·
                    refine ⟨4946963682651511215143233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6595951576868681620190977 4946963682651511215143233)
                    ·
                      refine ⟨3710222761988633411357425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4946963682651511215143233 3710222761988633411357425)
                      ·
                        rfl

theorem cell23_7225633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_7225633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225633 prefixEnd_7225633 := by exact prefixLift 7225633
  have htrace : WordTrace (prefixWord ++ tailWord_7225633) baseStart_7225633 baseEnd_7225633 := by
    simpa [prefixWord, tailWord_7225633, baseEnd_7225633] using wordTrace_append hprefix tailTrace_7225633
  have hstable : (prefixWord ++ tailWord_7225633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225633).length < 2 ^ (prefixWord ++ tailWord_7225633).sum := by decide
  have hdescent : baseEnd_7225633 < baseStart_7225633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225650 : List Nat := [3, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2]
def baseStart_7225650 : Nat := 118140960795 + 7225650 * 2 ^ 59
def prefixEnd_7225650 : Nat := 4983230072969 + 3 ^ 40 * 7225650 * 2
def baseEnd_7225650 : Nat := 3710231491159759844844847

theorem tailTrace_7225650 : CollatzResearch.WordTrace tailWord_7225650 prefixEnd_7225650 3710231491159759844844847 := by
  unfold tailWord_7225650
  simp only [CollatzResearch.WordTrace]
  refine ⟨65885276568177891904486601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175694070848474378411964269 65885276568177891904486601)
  ·
    refine ⟨49413957426133418928364951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65885276568177891904486601 49413957426133418928364951)
    ·
      refine ⟨74120936139200128392547427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49413957426133418928364951 74120936139200128392547427)
      ·
        refine ⟨111181404208800192588821141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74120936139200128392547427 111181404208800192588821141)
        ·
          refine ⟨5211628322287509027600991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 111181404208800192588821141 5211628322287509027600991)
          ·
            refine ⟨7817442483431263541401487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5211628322287509027600991 7817442483431263541401487)
            ·
              refine ⟨11726163725146895312102231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7817442483431263541401487 11726163725146895312102231)
              ·
                refine ⟨17589245587720342968153347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11726163725146895312102231 17589245587720342968153347)
                ·
                  refine ⟨26383868381580514452230021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17589245587720342968153347 26383868381580514452230021)
                  ·
                    refine ⟨4946975321546346459793129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26383868381580514452230021 4946975321546346459793129)
                    ·
                      refine ⟨3710231491159759844844847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4946975321546346459793129 3710231491159759844844847)
                      ·
                        rfl

theorem cell23_7225650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2].length) (baseStart_7225650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225650 prefixEnd_7225650 := by exact prefixLift 7225650
  have htrace : WordTrace (prefixWord ++ tailWord_7225650) baseStart_7225650 baseEnd_7225650 := by
    simpa [prefixWord, tailWord_7225650, baseEnd_7225650] using wordTrace_append hprefix tailTrace_7225650
  have hstable : (prefixWord ++ tailWord_7225650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225650).length < 2 ^ (prefixWord ++ tailWord_7225650).sum := by decide
  have hdescent : baseEnd_7225650 < baseStart_7225650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225722 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 2, 1, 9]
def baseStart_7225722 : Nat := 118140960795 + 7225722 * 2 ^ 59
def prefixEnd_7225722 : Nat := 4983230072969 + 3 ^ 40 * 7225722 * 2
def baseEnd_7225722 : Nat := 3710268461766883563144515

theorem tailTrace_7225722 : CollatzResearch.WordTrace tailWord_7225722 prefixEnd_7225722 3710268461766883563144515 := by
  unfold tailWord_7225722
  simp only [CollatzResearch.WordTrace]
  refine ⟨65885933082112680978641855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175695821552300482609711613 65885933082112680978641855)
  ·
    refine ⟨98828899623169021467962783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65885933082112680978641855 98828899623169021467962783)
    ·
      refine ⟨148243349434753532201944175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98828899623169021467962783 148243349434753532201944175)
      ·
        refine ⟨222365024152130298302916263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148243349434753532201944175 222365024152130298302916263)
        ·
          refine ⟨333547536228195447454374395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222365024152130298302916263 333547536228195447454374395)
          ·
            refine ⟨500321304342293171181561593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333547536228195447454374395 500321304342293171181561593)
            ·
              refine ⟨375240978256719878386171195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 500321304342293171181561593 375240978256719878386171195)
              ·
                refine ⟨562861467385079817579256793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 375240978256719878386171195 562861467385079817579256793)
                ·
                  refine ⟨422146100538809863184442595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 562861467385079817579256793 422146100538809863184442595)
                  ·
                    refine ⟨633219150808214794776663893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 422146100538809863184442595 633219150808214794776663893)
                    ·
                      refine ⟨3710268461766883563144515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 633219150808214794776663893 3710268461766883563144515)
                      ·
                        rfl

theorem cell23_7225722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_7225722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225722 prefixEnd_7225722 := by exact prefixLift 7225722
  have htrace : WordTrace (prefixWord ++ tailWord_7225722) baseStart_7225722 baseEnd_7225722 := by
    simpa [prefixWord, tailWord_7225722, baseEnd_7225722] using wordTrace_append hprefix tailTrace_7225722
  have hstable : (prefixWord ++ tailWord_7225722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225722).length < 2 ^ (prefixWord ++ tailWord_7225722).sum := by decide
  have hdescent : baseEnd_7225722 < baseStart_7225722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225759 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 5, 5]
def baseStart_7225759 : Nat := 118140960795 + 7225759 * 2 ^ 59
def prefixEnd_7225759 : Nat := 4983230072969 + 3 ^ 40 * 7225759 * 2
def baseEnd_7225759 : Nat := 1236762486850366639460615

theorem tailTrace_7225759 : CollatzResearch.WordTrace tailWord_7225759 prefixEnd_7225759 1236762486850366639460615 := by
  unfold tailWord_7225759
  simp only [CollatzResearch.WordTrace]
  refine ⟨263545081829316679233664331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175696721219544452822442887 263545081829316679233664331)
  ·
    refine ⟨395317622743975018850496497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263545081829316679233664331 395317622743975018850496497)
    ·
      refine ⟨296488217057981264137872373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395317622743975018850496497 296488217057981264137872373)
      ·
        refine ⟨27795770349185743512925535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 296488217057981264137872373 27795770349185743512925535)
        ·
          refine ⟨41693655523778615269388303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27795770349185743512925535 41693655523778615269388303)
          ·
            refine ⟨62540483285667922904082455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41693655523778615269388303 62540483285667922904082455)
            ·
              refine ⟨93810724928501884356123683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62540483285667922904082455 93810724928501884356123683)
              ·
                refine ⟨140716087392752826534185525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93810724928501884356123683 140716087392752826534185525)
                ·
                  refine ⟨13192133193070577487579893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140716087392752826534185525 13192133193070577487579893)
                  ·
                    refine ⟨1236762486850366639460615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13192133193070577487579893 1236762486850366639460615)
                    ·
                      rfl

theorem cell23_7225759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 5].length) (baseStart_7225759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225759 prefixEnd_7225759 := by exact prefixLift 7225759
  have htrace : WordTrace (prefixWord ++ tailWord_7225759) baseStart_7225759 baseEnd_7225759 := by
    simpa [prefixWord, tailWord_7225759, baseEnd_7225759] using wordTrace_append hprefix tailTrace_7225759
  have hstable : (prefixWord ++ tailWord_7225759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225759).length < 2 ^ (prefixWord ++ tailWord_7225759).sum := by decide
  have hdescent : baseEnd_7225759 < baseStart_7225759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225783 : List Nat := [1, 1, 3, 1, 3, 3, 3, 1, 2, 3, 2]
def baseStart_7225783 : Nat := 118140960795 + 7225783 * 2 ^ 59
def prefixEnd_7225783 : Nat := 4983230072969 + 3 ^ 40 * 7225783 * 2
def baseEnd_7225783 : Nat := 3710299784086807824481735

theorem tailTrace_7225783 : CollatzResearch.WordTrace tailWord_7225783 prefixEnd_7225783 3710299784086807824481735 := by
  unfold tailWord_7225783
  simp only [CollatzResearch.WordTrace]
  refine ⟨263545957181229731332538003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175697304787486487555025335 263545957181229731332538003)
  ·
    refine ⟨395318935771844596998807005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263545957181229731332538003 395318935771844596998807005)
    ·
      refine ⟨148244600914441723874552627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 395318935771844596998807005 148244600914441723874552627)
      ·
        refine ⟨222366901371662585811828941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148244600914441723874552627 222366901371662585811828941)
        ·
          refine ⟨83387588014373469679435853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222366901371662585811828941 83387588014373469679435853)
          ·
            refine ⟨31270345505390051129788445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83387588014373469679435853 31270345505390051129788445)
            ·
              refine ⟨11726379564521269173670667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31270345505390051129788445 11726379564521269173670667)
              ·
                refine ⟨17589569346781903760506001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11726379564521269173670667 17589569346781903760506001)
                ·
                  refine ⟨13192177010086427820379501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17589569346781903760506001 13192177010086427820379501)
                  ·
                    refine ⟨4947066378782410432642313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13192177010086427820379501 4947066378782410432642313)
                    ·
                      refine ⟨3710299784086807824481735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4947066378782410432642313 3710299784086807824481735)
                      ·
                        rfl

theorem cell23_7225783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 3, 2].length) (baseStart_7225783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225783 prefixEnd_7225783 := by exact prefixLift 7225783
  have htrace : WordTrace (prefixWord ++ tailWord_7225783) baseStart_7225783 baseEnd_7225783 := by
    simpa [prefixWord, tailWord_7225783, baseEnd_7225783] using wordTrace_append hprefix tailTrace_7225783
  have hstable : (prefixWord ++ tailWord_7225783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225783).length < 2 ^ (prefixWord ++ tailWord_7225783).sum := by decide
  have hdescent : baseEnd_7225783 < baseStart_7225783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225790 : List Nat := [4, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3]
def baseStart_7225790 : Nat := 118140960795 + 7225790 * 2 ^ 59
def prefixEnd_7225790 : Nat := 4983230072969 + 3 ^ 40 * 7225790 * 2
def baseEnd_7225790 : Nat := 3710303378451389297094203

theorem tailTrace_7225790 : CollatzResearch.WordTrace tailWord_7225790 prefixEnd_7225790 3710303378451389297094203 := by
  unfold tailWord_7225790
  simp only [CollatzResearch.WordTrace]
  refine ⟨32943276561525546441005353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175697474994802914352028549 32943276561525546441005353)
  ·
    refine ⟨24707457421144159830754015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32943276561525546441005353 24707457421144159830754015)
    ·
      refine ⟨37061186131716239746131023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24707457421144159830754015 37061186131716239746131023)
      ·
        refine ⟨55591779197574359619196535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37061186131716239746131023 55591779197574359619196535)
        ·
          refine ⟨83387668796361539428794803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55591779197574359619196535 83387668796361539428794803)
          ·
            refine ⟨125081503194542309143192205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83387668796361539428794803 125081503194542309143192205)
            ·
              refine ⟨46905563697953365928697077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125081503194542309143192205 46905563697953365928697077)
              ·
                refine ⟨4397396596683128055815351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46905563697953365928697077 4397396596683128055815351)
                ·
                  refine ⟨6596094895024692083723027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4397396596683128055815351 6596094895024692083723027)
                  ·
                    refine ⟨9894142342537038125584541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6596094895024692083723027 9894142342537038125584541)
                    ·
                      refine ⟨3710303378451389297094203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9894142342537038125584541 3710303378451389297094203)
                      ·
                        rfl

theorem cell23_7225790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_7225790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225790 prefixEnd_7225790 := by exact prefixLift 7225790
  have htrace : WordTrace (prefixWord ++ tailWord_7225790) baseStart_7225790 baseEnd_7225790 := by
    simpa [prefixWord, tailWord_7225790, baseEnd_7225790] using wordTrace_append hprefix tailTrace_7225790
  have hstable : (prefixWord ++ tailWord_7225790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225790).length < 2 ^ (prefixWord ++ tailWord_7225790).sum := by decide
  have hdescent : baseEnd_7225790 < baseStart_7225790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225809 : List Nat := [1, 2, 2, 1, 2, 1, 1, 4, 3, 2, 4]
def baseStart_7225809 : Nat := 118140960795 + 7225809 * 2 ^ 59
def prefixEnd_7225809 : Nat := 4983230072969 + 3 ^ 40 * 7225809 * 2
def baseEnd_7225809 : Nat := 3710313134583824722756615

theorem tailTrace_7225809 : CollatzResearch.WordTrace tailWord_7225809 prefixEnd_7225809 3710313134583824722756615 := by
  unfold tailWord_7225809
  simp only [CollatzResearch.WordTrace]
  refine ⟨263546905479135537772984481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175697936986090358515322987 263546905479135537772984481)
  ·
    refine ⟨197660179109351653329738361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263546905479135537772984481 197660179109351653329738361)
    ·
      refine ⟨148245134332013739997303771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197660179109351653329738361 148245134332013739997303771)
      ·
        refine ⟨222367701498020609995955657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148245134332013739997303771 222367701498020609995955657)
        ·
          refine ⟨166775776123515457496966743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222367701498020609995955657 166775776123515457496966743)
          ·
            refine ⟨250163664185273186245450115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166775776123515457496966743 250163664185273186245450115)
            ·
              refine ⟨375245496277909779368175173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250163664185273186245450115 375245496277909779368175173)
              ·
                refine ⟨70358530552108083631532845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 375245496277909779368175173 70358530552108083631532845)
                ·
                  refine ⟨26384448957040531361824817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70358530552108083631532845 26384448957040531361824817)
                  ·
                    refine ⟨19788336717780398521368613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26384448957040531361824817 19788336717780398521368613)
                    ·
                      refine ⟨3710313134583824722756615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19788336717780398521368613 3710313134583824722756615)
                      ·
                        rfl

theorem cell23_7225809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_7225809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225809 prefixEnd_7225809 := by exact prefixLift 7225809
  have htrace : WordTrace (prefixWord ++ tailWord_7225809) baseStart_7225809 baseEnd_7225809 := by
    simpa [prefixWord, tailWord_7225809, baseEnd_7225809] using wordTrace_append hprefix tailTrace_7225809
  have hstable : (prefixWord ++ tailWord_7225809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225809).length < 2 ^ (prefixWord ++ tailWord_7225809).sum := by decide
  have hdescent : baseEnd_7225809 < baseStart_7225809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225859 : List Nat := [1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 5]
def baseStart_7225859 : Nat := 118140960795 + 7225859 * 2 ^ 59
def prefixEnd_7225859 : Nat := 4983230072969 + 3 ^ 40 * 7225859 * 2
def baseEnd_7225859 : Nat := 3710338808616549527131385

theorem tailTrace_7225859 : CollatzResearch.WordTrace tailWord_7225859 prefixEnd_7225859 3710338808616549527131385 := by
  unfold tailWord_7225859
  simp only [CollatzResearch.WordTrace]
  refine ⟨263548729128954396312304631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175699152752636264208203087 263548729128954396312304631)
  ·
    refine ⟨395323093693431594468456947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263548729128954396312304631 395323093693431594468456947)
    ·
      refine ⟨592984640540147391702685421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395323093693431594468456947 592984640540147391702685421)
      ·
        refine ⟨222369240202555271888507033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 592984640540147391702685421 222369240202555271888507033)
        ·
          refine ⟨166776930151916453916380275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222369240202555271888507033 166776930151916453916380275)
          ·
            refine ⟨250165395227874680874570413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166776930151916453916380275 250165395227874680874570413)
            ·
              refine ⟨93812023210453005327963905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250165395227874680874570413 93812023210453005327963905)
              ·
                refine ⟨70359017407839753995972929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93812023210453005327963905 70359017407839753995972929)
                ·
                  refine ⟨52769263055879815496979697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70359017407839753995972929 52769263055879815496979697)
                  ·
                    refine ⟨39576947291909861622734773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52769263055879815496979697 39576947291909861622734773)
                    ·
                      refine ⟨3710338808616549527131385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39576947291909861622734773 3710338808616549527131385)
                      ·
                        rfl

theorem cell23_7225859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_7225859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225859 prefixEnd_7225859 := by exact prefixLift 7225859
  have htrace : WordTrace (prefixWord ++ tailWord_7225859) baseStart_7225859 baseEnd_7225859 := by
    simpa [prefixWord, tailWord_7225859, baseEnd_7225859] using wordTrace_append hprefix tailTrace_7225859
  have hstable : (prefixWord ++ tailWord_7225859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225859).length < 2 ^ (prefixWord ++ tailWord_7225859).sum := by decide
  have hdescent : baseEnd_7225859 < baseStart_7225859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225880 : List Nat := [2, 1, 2, 3, 3, 2, 1, 3, 2, 1, 3]
def baseStart_7225880 : Nat := 118140960795 + 7225880 * 2 ^ 59
def prefixEnd_7225880 : Nat := 4983230072969 + 3 ^ 40 * 7225880 * 2
def baseEnd_7225880 : Nat := 3710349591710293944968789

theorem tailTrace_7225880 : CollatzResearch.WordTrace tailWord_7225880 prefixEnd_7225880 3710349591710293944968789 := by
  unfold tailWord_7225880
  simp only [CollatzResearch.WordTrace]
  refine ⟨131774747530939158449409547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175699663374585544599212729 131774747530939158449409547)
  ·
    refine ⟨197662121296408737674114321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131774747530939158449409547 197662121296408737674114321)
    ·
      refine ⟨148246590972306553255585741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197662121296408737674114321 148246590972306553255585741)
      ·
        refine ⟨55592471614614957470844653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148246590972306553255585741 55592471614614957470844653)
        ·
          refine ⟨20847176855480609051566745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55592471614614957470844653 20847176855480609051566745)
          ·
            refine ⟨15635382641610456788675059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20847176855480609051566745 15635382641610456788675059)
            ·
              refine ⟨23453073962415685183012589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15635382641610456788675059 23453073962415685183012589)
              ·
                refine ⟨8794902735905881943629721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23453073962415685183012589 8794902735905881943629721)
                ·
                  refine ⟨6596177051929411457722291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8794902735905881943629721 6596177051929411457722291)
                  ·
                    refine ⟨9894265577894117186583437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6596177051929411457722291 9894265577894117186583437)
                    ·
                      refine ⟨3710349591710293944968789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9894265577894117186583437 3710349591710293944968789)
                      ·
                        rfl

theorem cell23_7225880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_7225880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225880 prefixEnd_7225880 := by exact prefixLift 7225880
  have htrace : WordTrace (prefixWord ++ tailWord_7225880) baseStart_7225880 baseEnd_7225880 := by
    simpa [prefixWord, tailWord_7225880, baseEnd_7225880] using wordTrace_append hprefix tailTrace_7225880
  have hstable : (prefixWord ++ tailWord_7225880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225880).length < 2 ^ (prefixWord ++ tailWord_7225880).sum := by decide
  have hdescent : baseEnd_7225880 < baseStart_7225880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225901 : List Nat := [1, 5, 4, 1, 1, 1, 3, 1, 1, 2, 3]
def baseStart_7225901 : Nat := 118140960795 + 7225901 * 2 ^ 59
def prefixEnd_7225901 : Nat := 4983230072969 + 3 ^ 40 * 7225901 * 2
def baseEnd_7225901 : Nat := 3710360374804038362806193

theorem tailTrace_7225901 : CollatzResearch.WordTrace tailWord_7225901 prefixEnd_7225901 3710360374804038362806193 := by
  unfold tailWord_7225901
  simp only [CollatzResearch.WordTrace]
  refine ⟨263550260994802237485333557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175700173996534824990222371 263550260994802237485333557)
  ·
    refine ⟨24707836968262709764250021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 263550260994802237485333557 24707836968262709764250021)
    ·
      refine ⟨4632719431549258080796879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24707836968262709764250021 4632719431549258080796879)
      ·
        refine ⟨6949079147323887121195319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4632719431549258080796879 6949079147323887121195319)
        ·
          refine ⟨10423618720985830681792979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6949079147323887121195319 10423618720985830681792979)
          ·
            refine ⟨15635428081478746022689469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10423618720985830681792979 15635428081478746022689469)
            ·
              refine ⟨5863285530554529758508551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15635428081478746022689469 5863285530554529758508551)
              ·
                refine ⟨8794928295831794637762827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5863285530554529758508551 8794928295831794637762827)
                ·
                  refine ⟨13192392443747691956644241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8794928295831794637762827 13192392443747691956644241)
                  ·
                    refine ⟨9894294332810768967483181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13192392443747691956644241 9894294332810768967483181)
                    ·
                      refine ⟨3710360374804038362806193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9894294332810768967483181 3710360374804038362806193)
                      ·
                        rfl

theorem cell23_7225901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_7225901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225901 prefixEnd_7225901 := by exact prefixLift 7225901
  have htrace : WordTrace (prefixWord ++ tailWord_7225901) baseStart_7225901 baseEnd_7225901 := by
    simpa [prefixWord, tailWord_7225901, baseEnd_7225901] using wordTrace_append hprefix tailTrace_7225901
  have hstable : (prefixWord ++ tailWord_7225901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225901).length < 2 ^ (prefixWord ++ tailWord_7225901).sum := by decide
  have hdescent : baseEnd_7225901 < baseStart_7225901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225906 : List Nat := [3, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5]
def baseStart_7225906 : Nat := 118140960795 + 7225906 * 2 ^ 59
def prefixEnd_7225906 : Nat := 4983230072969 + 3 ^ 40 * 7225906 * 2
def baseEnd_7225906 : Nat := 3710362942207310843243669

theorem tailTrace_7225906 : CollatzResearch.WordTrace tailWord_7225906 prefixEnd_7225906 3710362942207310843243669 := by
  unfold tailWord_7225906
  simp only [CollatzResearch.WordTrace]
  refine ⟨65887610839946030834816393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175700295573189415559510381 65887610839946030834816393)
  ·
    refine ⟨49415708129959523126112295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65887610839946030834816393 49415708129959523126112295)
    ·
      refine ⟨74123562194939284689168443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49415708129959523126112295 74123562194939284689168443)
      ·
        refine ⟨111185343292408927033752665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74123562194939284689168443 111185343292408927033752665)
        ·
          refine ⟨83389007469306695275314499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111185343292408927033752665 83389007469306695275314499)
          ·
            refine ⟨125083511203960042912971749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83389007469306695275314499 125083511203960042912971749)
            ·
              refine ⟨23453158350742508046182203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125083511203960042912971749 23453158350742508046182203)
              ·
                refine ⟨35179737526113762069273305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23453158350742508046182203 35179737526113762069273305)
                ·
                  refine ⟨26384803144585321551954979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35179737526113762069273305 26384803144585321551954979)
                  ·
                    refine ⟨39577204716877982327932469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26384803144585321551954979 39577204716877982327932469)
                    ·
                      refine ⟨3710362942207310843243669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39577204716877982327932469 3710362942207310843243669)
                      ·
                        rfl

theorem cell23_7225906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_7225906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225906 prefixEnd_7225906 := by exact prefixLift 7225906
  have htrace : WordTrace (prefixWord ++ tailWord_7225906) baseStart_7225906 baseEnd_7225906 := by
    simpa [prefixWord, tailWord_7225906, baseEnd_7225906] using wordTrace_append hprefix tailTrace_7225906
  have hstable : (prefixWord ++ tailWord_7225906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225906).length < 2 ^ (prefixWord ++ tailWord_7225906).sum := by decide
  have hdescent : baseEnd_7225906 < baseStart_7225906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225920 : List Nat := [2, 1, 1, 2, 2, 2, 3, 4, 2, 2, 2]
def baseStart_7225920 : Nat := 118140960795 + 7225920 * 2 ^ 59
def prefixEnd_7225920 : Nat := 4983230072969 + 3 ^ 40 * 7225920 * 2
def baseEnd_7225920 : Nat := 3710370130936473788468605

theorem tailTrace_7225920 : CollatzResearch.WordTrace tailWord_7225920 prefixEnd_7225920 3710370130936473788468605 := by
  unfold tailWord_7225920
  simp only [CollatzResearch.WordTrace]
  refine ⟨131775476990866701865137607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175700635987822269153516809 131775476990866701865137607)
  ·
    refine ⟨197663215486300052797706411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131775476990866701865137607 197663215486300052797706411)
    ·
      refine ⟨296494823229450079196559617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197663215486300052797706411 296494823229450079196559617)
      ·
        refine ⟨222371117422087559397419713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296494823229450079196559617 222371117422087559397419713)
        ·
          refine ⟨166778338066565669548064785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222371117422087559397419713 166778338066565669548064785)
          ·
            refine ⟨125083753549924252161048589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166778338066565669548064785 125083753549924252161048589)
            ·
              refine ⟨46906407581221594560393221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125083753549924252161048589 46906407581221594560393221)
              ·
                refine ⟨8794951421479048980073729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46906407581221594560393221 8794951421479048980073729)
                ·
                  refine ⟨6596213566109286735055297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8794951421479048980073729 6596213566109286735055297)
                  ·
                    refine ⟨4947160174581965051291473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6596213566109286735055297 4947160174581965051291473)
                    ·
                      refine ⟨3710370130936473788468605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4947160174581965051291473 3710370130936473788468605)
                      ·
                        rfl

theorem cell23_7225920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 2, 2, 2].length) (baseStart_7225920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225920 prefixEnd_7225920 := by exact prefixLift 7225920
  have htrace : WordTrace (prefixWord ++ tailWord_7225920) baseStart_7225920 baseEnd_7225920 := by
    simpa [prefixWord, tailWord_7225920, baseEnd_7225920] using wordTrace_append hprefix tailTrace_7225920
  have hstable : (prefixWord ++ tailWord_7225920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225920).length < 2 ^ (prefixWord ++ tailWord_7225920).sum := by decide
  have hdescent : baseEnd_7225920 < baseStart_7225920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225929 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 1, 3, 8]
def baseStart_7225929 : Nat := 118140960795 + 7225929 * 2 ^ 59
def prefixEnd_7225929 : Nat := 4983230072969 + 3 ^ 40 * 7225929 * 2
def baseEnd_7225929 : Nat := 3710374752262364253256063

theorem tailTrace_7225929 : CollatzResearch.WordTrace tailWord_7225929 prefixEnd_7225929 3710374752262364253256063 := by
  unfold tailWord_7225929
  simp only [CollatzResearch.WordTrace]
  refine ⟨263551282238700798267352841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175700854825800532178235227 263551282238700798267352841)
  ·
    refine ⟨197663461679025598700514631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263551282238700798267352841 197663461679025598700514631)
    ·
      refine ⟨296495192518538398050771947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197663461679025598700514631 296495192518538398050771947)
      ·
        refine ⟨444742788777807597076157921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296495192518538398050771947 444742788777807597076157921)
        ·
          refine ⟨333557091583355697807118441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444742788777807597076157921 333557091583355697807118441)
          ·
            refine ⟨250167818687516773355338831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333557091583355697807118441 250167818687516773355338831)
            ·
              refine ⟨375251728031275160033008247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250167818687516773355338831 375251728031275160033008247)
              ·
                refine ⟨562877592046912740049512371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 375251728031275160033008247 562877592046912740049512371)
                ·
                  refine ⟨844316388070369110074268557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 562877592046912740049512371 844316388070369110074268557)
                  ·
                    refine ⟨316618645526388416277850709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 844316388070369110074268557 316618645526388416277850709)
                    ·
                      refine ⟨3710374752262364253256063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 316618645526388416277850709 3710374752262364253256063)
                      ·
                        rfl

theorem cell23_7225929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 3, 8].length) (baseStart_7225929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225929 prefixEnd_7225929 := by exact prefixLift 7225929
  have htrace : WordTrace (prefixWord ++ tailWord_7225929) baseStart_7225929 baseEnd_7225929 := by
    simpa [prefixWord, tailWord_7225929, baseEnd_7225929] using wordTrace_append hprefix tailTrace_7225929
  have hstable : (prefixWord ++ tailWord_7225929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225929).length < 2 ^ (prefixWord ++ tailWord_7225929).sum := by decide
  have hdescent : baseEnd_7225929 < baseStart_7225929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225933 : List Nat := [1, 6, 1, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_7225933 : Nat := 118140960795 + 7225933 * 2 ^ 59
def prefixEnd_7225933 : Nat := 4983230072969 + 3 ^ 40 * 7225933 * 2
def baseEnd_7225933 : Nat := 3710376806184982237606045

theorem tailTrace_7225933 : CollatzResearch.WordTrace tailWord_7225933 prefixEnd_7225933 3710376806184982237606045 := by
  unfold tailWord_7225933
  simp only [CollatzResearch.WordTrace]
  refine ⟨263551428130686306950498453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175700952087124204633665635 263551428130686306950498453)
  ·
    refine ⟨12353973193625920638304615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 263551428130686306950498453 12353973193625920638304615)
    ·
      refine ⟨18530959790438880957456923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12353973193625920638304615 18530959790438880957456923)
      ·
        refine ⟨27796439685658321436185385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18530959790438880957456923 27796439685658321436185385)
        ·
          refine ⟨20847329764243741077139039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27796439685658321436185385 20847329764243741077139039)
          ·
            refine ⟨31270994646365611615708559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20847329764243741077139039 31270994646365611615708559)
            ·
              refine ⟨46906491969548417423562839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31270994646365611615708559 46906491969548417423562839)
              ·
                refine ⟨70359737954322626135344259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46906491969548417423562839 70359737954322626135344259)
                ·
                  refine ⟨105539606931483939203016389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70359737954322626135344259 105539606931483939203016389)
                  ·
                    refine ⟨19788676299653238600565573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105539606931483939203016389 19788676299653238600565573)
                    ·
                      refine ⟨3710376806184982237606045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19788676299653238600565573 3710376806184982237606045)
                      ·
                        rfl

theorem cell23_7225933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_7225933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225933 prefixEnd_7225933 := by exact prefixLift 7225933
  have htrace : WordTrace (prefixWord ++ tailWord_7225933) baseStart_7225933 baseEnd_7225933 := by
    simpa [prefixWord, tailWord_7225933, baseEnd_7225933] using wordTrace_append hprefix tailTrace_7225933
  have hstable : (prefixWord ++ tailWord_7225933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225933).length < 2 ^ (prefixWord ++ tailWord_7225933).sum := by decide
  have hdescent : baseEnd_7225933 < baseStart_7225933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7225956 : List Nat := [2, 3, 1, 1, 2, 2, 3, 1, 1, 7]
def baseStart_7225956 : Nat := 118140960795 + 7225956 * 2 ^ 59
def prefixEnd_7225956 : Nat := 4983230072969 + 3 ^ 40 * 7225956 * 2
def baseEnd_7225956 : Nat := 1236796205413345215872813

theorem tailTrace_7225956 : CollatzResearch.WordTrace tailWord_7225956 prefixEnd_7225956 1236796205413345215872813 := by
  unfold tailWord_7225956
  simp only [CollatzResearch.WordTrace]
  refine ⟨131776133504801490939292861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175701511339735321252390481 131776133504801490939292861)
  ·
    refine ⟨49416050064300559102234823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131776133504801490939292861 49416050064300559102234823)
    ·
      refine ⟨74124075096450838653352235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49416050064300559102234823 74124075096450838653352235)
      ·
        refine ⟨111186112644676257980028353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74124075096450838653352235 111186112644676257980028353)
        ·
          refine ⟨83389584483507193485021265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111186112644676257980028353 83389584483507193485021265)
          ·
            refine ⟨62542188362630395113765949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83389584483507193485021265 62542188362630395113765949)
            ·
              refine ⟨23453320635986398167662231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62542188362630395113765949 23453320635986398167662231)
              ·
                refine ⟨35179980953979597251493347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23453320635986398167662231 35179980953979597251493347)
                ·
                  refine ⟨52769971430969395877240021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35179980953979597251493347 52769971430969395877240021)
                  ·
                    refine ⟨1236796205413345215872813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52769971430969395877240021 1236796205413345215872813)
                    ·
                      rfl

theorem cell23_7225956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_7225956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7225956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7225956 prefixEnd_7225956 := by exact prefixLift 7225956
  have htrace : WordTrace (prefixWord ++ tailWord_7225956) baseStart_7225956 baseEnd_7225956 := by
    simpa [prefixWord, tailWord_7225956, baseEnd_7225956] using wordTrace_append hprefix tailTrace_7225956
  have hstable : (prefixWord ++ tailWord_7225956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7225956).length < 2 ^ (prefixWord ++ tailWord_7225956).sum := by decide
  have hdescent : baseEnd_7225956 < baseStart_7225956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7225956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226013 : List Nat := [1, 4, 2, 1, 1, 1, 4, 1, 1, 4, 3]
def baseStart_7226013 : Nat := 118140960795 + 7226013 * 2 ^ 59
def prefixEnd_7226013 : Nat := 4983230072969 + 3 ^ 40 * 7226013 * 2
def baseEnd_7226013 : Nat := 3710417884637341924605677

theorem tailTrace_7226013 : CollatzResearch.WordTrace tailWord_7226013 prefixEnd_7226013 3710417884637341924605677 := by
  unfold tailWord_7226013
  simp only [CollatzResearch.WordTrace]
  refine ⟨263554345970396480613410693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175702897313597653742273795 263554345970396480613410693)
  ·
    refine ⟨49416439869449340115014505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263554345970396480613410693 49416439869449340115014505)
    ·
      refine ⟨37062329902087005086260879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49416439869449340115014505 37062329902087005086260879)
      ·
        refine ⟨55593494853130507629391319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37062329902087005086260879 55593494853130507629391319)
        ·
          refine ⟨83390242279695761444086979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55593494853130507629391319 83390242279695761444086979)
          ·
            refine ⟨125085363419543642166130469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83390242279695761444086979 125085363419543642166130469)
            ·
              refine ⟨23453505641164432906149463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125085363419543642166130469 23453505641164432906149463)
              ·
                refine ⟨35180258461746649359224195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23453505641164432906149463 35180258461746649359224195)
                ·
                  refine ⟨52770387692619974038836293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35180258461746649359224195 52770387692619974038836293)
                  ·
                    refine ⟨9894447692366245132281805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52770387692619974038836293 9894447692366245132281805)
                    ·
                      refine ⟨3710417884637341924605677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9894447692366245132281805 3710417884637341924605677)
                      ·
                        rfl

theorem cell23_7226013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_7226013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226013 prefixEnd_7226013 := by exact prefixLift 7226013
  have htrace : WordTrace (prefixWord ++ tailWord_7226013) baseStart_7226013 baseEnd_7226013 := by
    simpa [prefixWord, tailWord_7226013, baseEnd_7226013] using wordTrace_append hprefix tailTrace_7226013
  have hstable : (prefixWord ++ tailWord_7226013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226013).length < 2 ^ (prefixWord ++ tailWord_7226013).sum := by decide
  have hdescent : baseEnd_7226013 < baseStart_7226013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226037 : List Nat := [1, 3, 3, 3, 1, 3, 1, 1, 3, 4]
def baseStart_7226037 : Nat := 118140960795 + 7226037 * 2 ^ 59
def prefixEnd_7226037 : Nat := 4983230072969 + 3 ^ 40 * 7226037 * 2
def baseEnd_7226037 : Nat := 1236810069391016610235189

theorem tailTrace_7226037 : CollatzResearch.WordTrace tailWord_7226037 prefixEnd_7226037 1236810069391016610235189 := by
  unfold tailWord_7226037
  simp only [CollatzResearch.WordTrace]
  refine ⟨263555221322309532712284365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175703480881539688474856243 263555221322309532712284365)
  ·
    refine ⟨98833207995866074767106637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263555221322309532712284365 98833207995866074767106637)
    ·
      refine ⟨37062452998449778037664989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98833207995866074767106637 37062452998449778037664989)
      ·
        refine ⟨13898419874418666764124371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37062452998449778037664989 13898419874418666764124371)
        ·
          refine ⟨20847629811628000146186557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13898419874418666764124371 20847629811628000146186557)
          ·
            refine ⟨7817861179360500054819959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20847629811628000146186557 7817861179360500054819959)
            ·
              refine ⟨11726791769040750082229939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7817861179360500054819959 11726791769040750082229939)
              ·
                refine ⟨17590187653561125123344909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11726791769040750082229939 17590187653561125123344909)
                ·
                  refine ⟨6596320370085421921254341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17590187653561125123344909 6596320370085421921254341)
                  ·
                    refine ⟨1236810069391016610235189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6596320370085421921254341 1236810069391016610235189)
                    ·
                      rfl

theorem cell23_7226037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_7226037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226037 prefixEnd_7226037 := by exact prefixLift 7226037
  have htrace : WordTrace (prefixWord ++ tailWord_7226037) baseStart_7226037 baseEnd_7226037 := by
    simpa [prefixWord, tailWord_7226037, baseEnd_7226037] using wordTrace_append hprefix tailTrace_7226037
  have hstable : (prefixWord ++ tailWord_7226037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226037).length < 2 ^ (prefixWord ++ tailWord_7226037).sum := by decide
  have hdescent : baseEnd_7226037 < baseStart_7226037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226093 : List Nat := [1, 5, 1, 2, 1, 1, 1, 2, 3, 6]
def baseStart_7226093 : Nat := 118140960795 + 7226093 * 2 ^ 59
def prefixEnd_7226093 : Nat := 4983230072969 + 3 ^ 40 * 7226093 * 2
def baseEnd_7226093 : Nat := 1236819654363233870535103

theorem tailTrace_7226093 : CollatzResearch.WordTrace tailWord_7226093 prefixEnd_7226093 1236819654363233870535103 := by
  unfold tailWord_7226093
  simp only [CollatzResearch.WordTrace]
  refine ⟨263557263810106654276322933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175704842540071102850881955 263557263810106654276322933)
  ·
    refine ⟨24708493482197498838405275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 263557263810106654276322933 24708493482197498838405275)
    ·
      refine ⟨37062740223296248257607913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24708493482197498838405275 37062740223296248257607913)
      ·
        refine ⟨27797055167472186193205935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37062740223296248257607913 27797055167472186193205935)
        ·
          refine ⟨41695582751208279289808903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27797055167472186193205935 41695582751208279289808903)
          ·
            refine ⟨62543374126812418934713355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41695582751208279289808903 62543374126812418934713355)
            ·
              refine ⟨93815061190218628402070033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62543374126812418934713355 93815061190218628402070033)
              ·
                refine ⟨70361295892663971301552525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93815061190218628402070033 70361295892663971301552525)
                ·
                  refine ⟨26385485959748989238082197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70361295892663971301552525 26385485959748989238082197)
                  ·
                    refine ⟨1236819654363233870535103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26385485959748989238082197 1236819654363233870535103)
                    ·
                      rfl

theorem cell23_7226093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_7226093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226093 prefixEnd_7226093 := by exact prefixLift 7226093
  have htrace : WordTrace (prefixWord ++ tailWord_7226093) baseStart_7226093 baseEnd_7226093 := by
    simpa [prefixWord, tailWord_7226093, baseEnd_7226093] using wordTrace_append hprefix tailTrace_7226093
  have hstable : (prefixWord ++ tailWord_7226093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226093).length < 2 ^ (prefixWord ++ tailWord_7226093).sum := by decide
  have hdescent : baseEnd_7226093 < baseStart_7226093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226094 : List Nat := [4, 1, 2, 1, 1, 4, 1, 4, 1, 1, 3]
def baseStart_7226094 : Nat := 118140960795 + 7226094 * 2 ^ 59
def prefixEnd_7226094 : Nat := 4983230072969 + 3 ^ 40 * 7226094 * 2
def baseEnd_7226094 : Nat := 3710459476570356107692805

theorem tailTrace_7226094 : CollatzResearch.WordTrace tailWord_7226094 prefixEnd_7226094 3710459476570356107692805 := by
  unfold tailWord_7226094
  simp only [CollatzResearch.WordTrace]
  refine ⟨32944662535387878930888667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175704866855402020964739557 32944662535387878930888667)
  ·
    refine ⟨49416993803081818396333001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32944662535387878930888667 49416993803081818396333001)
    ·
      refine ⟨37062745352311363797249751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49416993803081818396333001 37062745352311363797249751)
      ·
        refine ⟨55594118028467045695874627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37062745352311363797249751 55594118028467045695874627)
        ·
          refine ⟨83391177042700568543811941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55594118028467045695874627 83391177042700568543811941)
          ·
            refine ⟨15635845695506356601964739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83391177042700568543811941 15635845695506356601964739)
            ·
              refine ⟨23453768543259534902947109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15635845695506356601964739 23453768543259534902947109)
              ·
                refine ⟨4397581601861162794302583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23453768543259534902947109 4397581601861162794302583)
                ·
                  refine ⟨6596372402791744191453875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4397581601861162794302583 6596372402791744191453875)
                  ·
                    refine ⟨9894558604187616287180813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6596372402791744191453875 9894558604187616287180813)
                    ·
                      refine ⟨3710459476570356107692805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9894558604187616287180813 3710459476570356107692805)
                      ·
                        rfl

theorem cell23_7226094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_7226094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226094 prefixEnd_7226094 := by exact prefixLift 7226094
  have htrace : WordTrace (prefixWord ++ tailWord_7226094) baseStart_7226094 baseEnd_7226094 := by
    simpa [prefixWord, tailWord_7226094, baseEnd_7226094] using wordTrace_append hprefix tailTrace_7226094
  have hstable : (prefixWord ++ tailWord_7226094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226094).length < 2 ^ (prefixWord ++ tailWord_7226094).sum := by decide
  have hdescent : baseEnd_7226094 < baseStart_7226094 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226110 : List Nat := [4, 2, 2, 1, 2, 1, 1, 3, 1, 6]
def baseStart_7226110 : Nat := 118140960795 + 7226110 * 2 ^ 59
def prefixEnd_7226110 : Nat := 4983230072969 + 3 ^ 40 * 7226110 * 2
def baseEnd_7226110 : Nat := 1236822564086942681697577

theorem tailTrace_7226110 : CollatzResearch.WordTrace tailWord_7226110 prefixEnd_7226110 1236822564086942681697577 := by
  unfold tailWord_7226110
  simp only [CollatzResearch.WordTrace]
  refine ⟨32944735481380633272461473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175705255900696710786461189 32944735481380633272461473)
  ·
    refine ⟨24708551611035474954346105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32944735481380633272461473 24708551611035474954346105)
    ·
      refine ⟨18531413708276606215759579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24708551611035474954346105 18531413708276606215759579)
      ·
        refine ⟨27797120562414909323639369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18531413708276606215759579 27797120562414909323639369)
        ·
          refine ⟨20847840421811181992729527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27797120562414909323639369 20847840421811181992729527)
          ·
            refine ⟨31271760632716772989094291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20847840421811181992729527 31271760632716772989094291)
            ·
              refine ⟨46907640949075159483641437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31271760632716772989094291 46907640949075159483641437)
              ·
                refine ⟨17590365355903184806365539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46907640949075159483641437 17590365355903184806365539)
                ·
                  refine ⟨26385548033854777209548309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17590365355903184806365539 26385548033854777209548309)
                  ·
                    refine ⟨1236822564086942681697577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26385548033854777209548309 1236822564086942681697577)
                    ·
                      rfl

theorem cell23_7226110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_7226110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226110 prefixEnd_7226110 := by exact prefixLift 7226110
  have htrace : WordTrace (prefixWord ++ tailWord_7226110) baseStart_7226110 baseEnd_7226110 := by
    simpa [prefixWord, tailWord_7226110, baseEnd_7226110] using wordTrace_append hprefix tailTrace_7226110
  have hstable : (prefixWord ++ tailWord_7226110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226110).length < 2 ^ (prefixWord ++ tailWord_7226110).sum := by decide
  have hdescent : baseEnd_7226110 < baseStart_7226110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226120 : List Nat := [2, 1, 3, 2, 2, 2, 2, 1, 3, 2, 3]
def baseStart_7226120 : Nat := 118140960795 + 7226120 * 2 ^ 59
def prefixEnd_7226120 : Nat := 4983230072969 + 3 ^ 40 * 7226120 * 2
def baseEnd_7226120 : Nat := 3710472827067373005967685

theorem tailTrace_7226120 : CollatzResearch.WordTrace tailWord_7226120 prefixEnd_7226120 3710472827067373005967685 := by
  unfold tailWord_7226120
  simp only [CollatzResearch.WordTrace]
  refine ⟨131779124290504418943777907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175705499054005891925037209 131779124290504418943777907)
  ·
    refine ⟨197668686435756628415666861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131779124290504418943777907 197668686435756628415666861)
    ·
      refine ⟨74125757413408735655875073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197668686435756628415666861 74125757413408735655875073)
      ·
        refine ⟨55594318060056551741906305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74125757413408735655875073 55594318060056551741906305)
        ·
          refine ⟨41695738545042413806429729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55594318060056551741906305 41695738545042413806429729)
          ·
            refine ⟨31271803908781810354822297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41695738545042413806429729 31271803908781810354822297)
            ·
              refine ⟨23453852931586357766116723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31271803908781810354822297 23453852931586357766116723)
              ·
                refine ⟨35180779397379536649175085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23453852931586357766116723 35180779397379536649175085)
                ·
                  refine ⟨13192792274017326243440657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35180779397379536649175085 13192792274017326243440657)
                  ·
                    refine ⟨9894594205512994682580493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13192792274017326243440657 9894594205512994682580493)
                    ·
                      refine ⟨3710472827067373005967685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9894594205512994682580493 3710472827067373005967685)
                      ·
                        rfl

theorem cell23_7226120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_7226120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226120 prefixEnd_7226120 := by exact prefixLift 7226120
  have htrace : WordTrace (prefixWord ++ tailWord_7226120) baseStart_7226120 baseEnd_7226120 := by
    simpa [prefixWord, tailWord_7226120, baseEnd_7226120] using wordTrace_append hprefix tailTrace_7226120
  have hstable : (prefixWord ++ tailWord_7226120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226120).length < 2 ^ (prefixWord ++ tailWord_7226120).sum := by decide
  have hdescent : baseEnd_7226120 < baseStart_7226120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226160 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 5, 3, 2]
def baseStart_7226160 : Nat := 118140960795 + 7226160 * 2 ^ 59
def prefixEnd_7226160 : Nat := 4983230072969 + 3 ^ 40 * 7226160 * 2
def baseEnd_7226160 : Nat := 3710493366293552849467501

theorem tailTrace_7226160 : CollatzResearch.WordTrace tailWord_7226160 prefixEnd_7226160 3710493366293552849467501 := by
  unfold tailWord_7226160
  simp only [CollatzResearch.WordTrace]
  refine ⟨131779853750431962359505967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175706471667242616479341289 131779853750431962359505967)
  ·
    refine ⟨197669780625647943539258951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131779853750431962359505967 197669780625647943539258951)
    ·
      refine ⟨296504670938471915308888427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197669780625647943539258951 296504670938471915308888427)
      ·
        refine ⟨444757006407707872963332641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296504670938471915308888427 444757006407707872963332641)
        ·
          refine ⟨333567754805780904722499481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444757006407707872963332641 333567754805780904722499481)
          ·
            refine ⟨250175816104335678541874611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333567754805780904722499481 250175816104335678541874611)
            ·
              refine ⟨375263724156503517812811917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250175816104335678541874611 375263724156503517812811917)
              ·
                refine ⟨140723896558688819179804469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 375263724156503517812811917 140723896558688819179804469)
                ·
                  refine ⟨13192865302377076798106669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140723896558688819179804469 13192865302377076798106669)
                  ·
                    refine ⟨4947324488391403799290001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13192865302377076798106669 4947324488391403799290001)
                    ·
                      refine ⟨3710493366293552849467501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4947324488391403799290001 3710493366293552849467501)
                      ·
                        rfl

theorem cell23_7226160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 5, 3, 2].length) (baseStart_7226160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226160 prefixEnd_7226160 := by exact prefixLift 7226160
  have htrace : WordTrace (prefixWord ++ tailWord_7226160) baseStart_7226160 baseEnd_7226160 := by
    simpa [prefixWord, tailWord_7226160, baseEnd_7226160] using wordTrace_append hprefix tailTrace_7226160
  have hstable : (prefixWord ++ tailWord_7226160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226160).length < 2 ^ (prefixWord ++ tailWord_7226160).sum := by decide
  have hdescent : baseEnd_7226160 < baseStart_7226160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226164 : List Nat := [2, 5, 1, 1, 3, 2, 1, 1, 1, 2, 4]
def baseStart_7226164 : Nat := 118140960795 + 7226164 * 2 ^ 59
def prefixEnd_7226164 : Nat := 4983230072969 + 3 ^ 40 * 7226164 * 2
def baseEnd_7226164 : Nat := 3710495420216170833817483

theorem tailTrace_7226164 : CollatzResearch.WordTrace tailWord_7226164 prefixEnd_7226164 3710495420216170833817483 := by
  unfold tailWord_7226164
  simp only [CollatzResearch.WordTrace]
  refine ⟨131779926696424716701078773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175706568928566288934771697 131779926696424716701078773)
  ·
    refine ⟨12354368127789817190726135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131779926696424716701078773 12354368127789817190726135)
    ·
      refine ⟨18531552191684725786089203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12354368127789817190726135 18531552191684725786089203)
      ·
        refine ⟨27797328287527088679133805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18531552191684725786089203 27797328287527088679133805)
        ·
          refine ⟨10423998107822658254675177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27797328287527088679133805 10423998107822658254675177)
          ·
            refine ⟨7817998580866993691006383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10423998107822658254675177 7817998580866993691006383)
            ·
              refine ⟨11726997871300490536509575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7817998580866993691006383 11726997871300490536509575)
              ·
                refine ⟨17590496806950735804764363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11726997871300490536509575 17590496806950735804764363)
                ·
                  refine ⟨26385745210426103707146545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17590496806950735804764363 26385745210426103707146545)
                  ·
                    refine ⟨19789308907819577780359909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26385745210426103707146545 19789308907819577780359909)
                    ·
                      refine ⟨3710495420216170833817483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19789308907819577780359909 3710495420216170833817483)
                      ·
                        rfl

theorem cell23_7226164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_7226164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226164 prefixEnd_7226164 := by exact prefixLift 7226164
  have htrace : WordTrace (prefixWord ++ tailWord_7226164) baseStart_7226164 baseEnd_7226164 := by
    simpa [prefixWord, tailWord_7226164, baseEnd_7226164] using wordTrace_append hprefix tailTrace_7226164
  have hstable : (prefixWord ++ tailWord_7226164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226164).length < 2 ^ (prefixWord ++ tailWord_7226164).sum := by decide
  have hdescent : baseEnd_7226164 < baseStart_7226164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226174 : List Nat := [4, 2, 1, 2, 4, 1, 2, 7]
def baseStart_7226174 : Nat := 118140960795 + 7226174 * 2 ^ 59
def prefixEnd_7226174 : Nat := 4983230072969 + 3 ^ 40 * 7226174 * 2
def baseEnd_7226174 : Nat := 137425946482322807210831

theorem tailTrace_7226174 : CollatzResearch.WordTrace tailWord_7226174 prefixEnd_7226174 137425946482322807210831 := by
  unfold tailWord_7226174
  simp only [CollatzResearch.WordTrace]
  refine ⟨32945027265351650638752697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175706812081875470073347717 32945027265351650638752697)
  ·
    refine ⟨24708770449013737979064523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32945027265351650638752697 24708770449013737979064523)
    ·
      refine ⟨37063155673520606968596785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24708770449013737979064523 37063155673520606968596785)
      ·
        refine ⟨27797366755140455226447589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37063155673520606968596785 27797366755140455226447589)
        ·
          refine ⟨5212006266588835354958923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27797366755140455226447589 5212006266588835354958923)
          ·
            refine ⟨7818009399883253032438385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5212006266588835354958923 7818009399883253032438385)
            ·
              refine ⟨5863507049912439774328789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7818009399883253032438385 5863507049912439774328789)
              ·
                refine ⟨137425946482322807210831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5863507049912439774328789 137425946482322807210831)
                ·
                  rfl

theorem cell23_7226174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 7].length) (baseStart_7226174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226174 prefixEnd_7226174 := by exact prefixLift 7226174
  have htrace : WordTrace (prefixWord ++ tailWord_7226174) baseStart_7226174 baseEnd_7226174 := by
    simpa [prefixWord, tailWord_7226174, baseEnd_7226174] using wordTrace_append hprefix tailTrace_7226174
  have hstable : (prefixWord ++ tailWord_7226174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226174).length < 2 ^ (prefixWord ++ tailWord_7226174).sum := by decide
  have hdescent : baseEnd_7226174 < baseStart_7226174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226207 : List Nat := [1, 1, 2, 3, 1, 3, 1, 3, 4, 2, 2]
def baseStart_7226207 : Nat := 118140960795 + 7226207 * 2 ^ 59
def prefixEnd_7226207 : Nat := 4983230072969 + 3 ^ 40 * 7226207 * 2
def baseEnd_7226207 : Nat := 3710517499884314165579785

theorem tailTrace_7226207 : CollatzResearch.WordTrace tailWord_7226207 prefixEnd_7226207 3710517499884314165579785 := by
  unfold tailWord_7226207
  simp only [CollatzResearch.WordTrace]
  refine ⟨263561421731693651745972875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175707614487795767830648583 263561421731693651745972875)
  ·
    refine ⟨395342132597540477618959313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263561421731693651745972875 395342132597540477618959313)
    ·
      refine ⟨296506599448155358214219485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395342132597540477618959313 296506599448155358214219485)
      ·
        refine ⟨111189974793058259330332307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296506599448155358214219485 111189974793058259330332307)
        ·
          refine ⟨166784962189587388995498461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111189974793058259330332307 166784962189587388995498461)
          ·
            refine ⟨62544360821095270873311923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166784962189587388995498461 62544360821095270873311923)
            ·
              refine ⟨93816541231642906309967885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62544360821095270873311923 93816541231642906309967885)
              ·
                refine ⟨35181202961866089866237957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93816541231642906309967885 35181202961866089866237957)
                ·
                  refine ⟨6596475555349891849919617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35181202961866089866237957 6596475555349891849919617)
                  ·
                    refine ⟨4947356666512418887439713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6596475555349891849919617 4947356666512418887439713)
                    ·
                      refine ⟨3710517499884314165579785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4947356666512418887439713 3710517499884314165579785)
                      ·
                        rfl

theorem cell23_7226207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 4, 2, 2].length) (baseStart_7226207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226207 prefixEnd_7226207 := by exact prefixLift 7226207
  have htrace : WordTrace (prefixWord ++ tailWord_7226207) baseStart_7226207 baseEnd_7226207 := by
    simpa [prefixWord, tailWord_7226207, baseEnd_7226207] using wordTrace_append hprefix tailTrace_7226207
  have hstable : (prefixWord ++ tailWord_7226207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226207).length < 2 ^ (prefixWord ++ tailWord_7226207).sum := by decide
  have hdescent : baseEnd_7226207 < baseStart_7226207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226258 : List Nat := [3, 2, 3, 2, 2, 1, 2, 2, 2, 2, 2]
def baseStart_7226258 : Nat := 118140960795 + 7226258 * 2 ^ 59
def prefixEnd_7226258 : Nat := 4983230072969 + 3 ^ 40 * 7226258 * 2
def baseEnd_7226258 : Nat := 3710543687397693466042051

theorem tailTrace_7226258 : CollatzResearch.WordTrace tailWord_7226258 prefixEnd_7226258 3710543687397693466042051 := by
  unfold tailWord_7226258
  simp only [CollatzResearch.WordTrace]
  refine ⟨65890820463627221864019857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175708854569672591637386285 65890820463627221864019857)
  ·
    refine ⟨49418115347720416398014893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65890820463627221864019857 49418115347720416398014893)
    ·
      refine ⟨18531793255395156149255585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49418115347720416398014893 18531793255395156149255585)
      ·
        refine ⟨13898844941546367111941689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18531793255395156149255585 13898844941546367111941689)
        ·
          refine ⟨10424133706159775333956267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13898844941546367111941689 10424133706159775333956267)
          ·
            refine ⟨15636200559239663000934401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10424133706159775333956267 15636200559239663000934401)
            ·
              refine ⟨11727150419429747250700801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15636200559239663000934401 11727150419429747250700801)
              ·
                refine ⟨8795362814572310438025601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11727150419429747250700801 8795362814572310438025601)
                ·
                  refine ⟨6596522110929232828519201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8795362814572310438025601 6596522110929232828519201)
                  ·
                    refine ⟨4947391583196924621389401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6596522110929232828519201 4947391583196924621389401)
                    ·
                      refine ⟨3710543687397693466042051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4947391583196924621389401 3710543687397693466042051)
                      ·
                        rfl

theorem cell23_7226258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_7226258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226258 prefixEnd_7226258 := by exact prefixLift 7226258
  have htrace : WordTrace (prefixWord ++ tailWord_7226258) baseStart_7226258 baseEnd_7226258 := by
    simpa [prefixWord, tailWord_7226258, baseEnd_7226258] using wordTrace_append hprefix tailTrace_7226258
  have hstable : (prefixWord ++ tailWord_7226258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226258).length < 2 ^ (prefixWord ++ tailWord_7226258).sum := by decide
  have hdescent : baseEnd_7226258 < baseStart_7226258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226283 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 5]
def baseStart_7226283 : Nat := 118140960795 + 7226283 * 2 ^ 59
def prefixEnd_7226283 : Nat := 4983230072969 + 3 ^ 40 * 7226283 * 2
def baseEnd_7226283 : Nat := 3710556524414055868229435

theorem tailTrace_7226283 : CollatzResearch.WordTrace tailWord_7226283 prefixEnd_7226283 3710556524414055868229435 := by
  unfold tailWord_7226283
  simp only [CollatzResearch.WordTrace]
  refine ⟨263564193679418316725739503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175709462452945544483826335 263564193679418316725739503)
  ·
    refine ⟨395346290519127475088609255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263564193679418316725739503 395346290519127475088609255)
    ·
      refine ⟨593019435778691212632913883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395346290519127475088609255 593019435778691212632913883)
      ·
        refine ⟨889529153668036818949370825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593019435778691212632913883 889529153668036818949370825)
        ·
          refine ⟨667146865251027614212028119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 889529153668036818949370825 667146865251027614212028119)
          ·
            refine ⟨1000720297876541421318042179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667146865251027614212028119 1000720297876541421318042179)
            ·
              refine ⟨1501080446814812131977063269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1000720297876541421318042179 1501080446814812131977063269)
              ·
                refine ⟨281452583777777274745699363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1501080446814812131977063269 281452583777777274745699363)
                ·
                  refine ⟨422178875666665912118549045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 281452583777777274745699363 422178875666665912118549045)
                  ·
                    refine ⟨39579269593749929261113973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 422178875666665912118549045 39579269593749929261113973)
                    ·
                      refine ⟨3710556524414055868229435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39579269593749929261113973 3710556524414055868229435)
                      ·
                        rfl

theorem cell23_7226283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 5].length) (baseStart_7226283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226283 prefixEnd_7226283 := by exact prefixLift 7226283
  have htrace : WordTrace (prefixWord ++ tailWord_7226283) baseStart_7226283 baseEnd_7226283 := by
    simpa [prefixWord, tailWord_7226283, baseEnd_7226283] using wordTrace_append hprefix tailTrace_7226283
  have hstable : (prefixWord ++ tailWord_7226283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226283).length < 2 ^ (prefixWord ++ tailWord_7226283).sum := by decide
  have hdescent : baseEnd_7226283 < baseStart_7226283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226297 : List Nat := [1, 2, 1, 4, 2, 2, 3, 1, 2, 1, 4]
def baseStart_7226297 : Nat := 118140960795 + 7226297 * 2 ^ 59
def prefixEnd_7226297 : Nat := 4983230072969 + 3 ^ 40 * 7226297 * 2
def baseEnd_7226297 : Nat := 3710563713143218813454371

theorem tailTrace_7226297 : CollatzResearch.WordTrace tailWord_7226297 prefixEnd_7226297 3710563713143218813454371 := by
  unfold tailWord_7226297
  simp only [CollatzResearch.WordTrace]
  refine ⟨263564704301367597116749145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175709802867578398077832763 263564704301367597116749145)
  ·
    refine ⟨197673528226025697837561859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263564704301367597116749145 197673528226025697837561859)
    ·
      refine ⟨296510292339038546756342789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197673528226025697837561859 296510292339038546756342789)
      ·
        refine ⟨55595679813569727516814273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 296510292339038546756342789 55595679813569727516814273)
        ·
          refine ⟨41696759860177295637610705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55595679813569727516814273 41696759860177295637610705)
          ·
            refine ⟨31272569895132971728208029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41696759860177295637610705 31272569895132971728208029)
            ·
              refine ⟨11727213710674864398078011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31272569895132971728208029 11727213710674864398078011)
              ·
                refine ⟨17590820566012296597117017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11727213710674864398078011 17590820566012296597117017)
                ·
                  refine ⟨13193115424509222447837763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17590820566012296597117017 13193115424509222447837763)
                  ·
                    refine ⟨19789673136763833671756645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13193115424509222447837763 19789673136763833671756645)
                    ·
                      refine ⟨3710563713143218813454371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19789673136763833671756645 3710563713143218813454371)
                      ·
                        rfl

theorem cell23_7226297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_7226297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226297 prefixEnd_7226297 := by exact prefixLift 7226297
  have htrace : WordTrace (prefixWord ++ tailWord_7226297) baseStart_7226297 baseEnd_7226297 := by
    simpa [prefixWord, tailWord_7226297, baseEnd_7226297] using wordTrace_append hprefix tailTrace_7226297
  have hstable : (prefixWord ++ tailWord_7226297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226297).length < 2 ^ (prefixWord ++ tailWord_7226297).sum := by decide
  have hdescent : baseEnd_7226297 < baseStart_7226297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226324 : List Nat := [2, 4, 1, 2, 1, 3, 2, 1, 3, 4]
def baseStart_7226324 : Nat := 118140960795 + 7226324 * 2 ^ 59
def prefixEnd_7226324 : Nat := 4983230072969 + 3 ^ 40 * 7226324 * 2
def baseEnd_7226324 : Nat := 1236859192373630069272249

theorem tailTrace_7226324 : CollatzResearch.WordTrace tailWord_7226324 prefixEnd_7226324 1236859192373630069272249 := by
  unfold tailWord_7226324
  simp only [CollatzResearch.WordTrace]
  refine ⟨131782844536134890363991013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175710459381513187151988017 131782844536134890363991013)
  ·
    refine ⟨24709283350525291943248315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131782844536134890363991013 24709283350525291943248315)
    ·
      refine ⟨37063925025787937914872473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24709283350525291943248315 37063925025787937914872473)
      ·
        refine ⟨27797943769340953436154355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37063925025787937914872473 27797943769340953436154355)
        ·
          refine ⟨41696915654011430154231533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27797943769340953436154355 41696915654011430154231533)
          ·
            refine ⟨15636343370254286307836825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41696915654011430154231533 15636343370254286307836825)
            ·
              refine ⟨11727257527690714730877619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15636343370254286307836825 11727257527690714730877619)
              ·
                refine ⟨17590886291536072096316429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11727257527690714730877619 17590886291536072096316429)
                ·
                  refine ⟨6596582359326027036118661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17590886291536072096316429 6596582359326027036118661)
                  ·
                    refine ⟨1236859192373630069272249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6596582359326027036118661 1236859192373630069272249)
                    ·
                      rfl

theorem cell23_7226324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_7226324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226324 prefixEnd_7226324 := by exact prefixLift 7226324
  have htrace : WordTrace (prefixWord ++ tailWord_7226324) baseStart_7226324 baseEnd_7226324 := by
    simpa [prefixWord, tailWord_7226324, baseEnd_7226324] using wordTrace_append hprefix tailTrace_7226324
  have hstable : (prefixWord ++ tailWord_7226324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226324).length < 2 ^ (prefixWord ++ tailWord_7226324).sum := by decide
  have hdescent : baseEnd_7226324 < baseStart_7226324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226358 : List Nat := [5, 1, 1, 1, 3, 3, 1, 3, 1, 4]
def baseStart_7226358 : Nat := 118140960795 + 7226358 * 2 ^ 59
def prefixEnd_7226358 : Nat := 4983230072969 + 3 ^ 40 * 7226358 * 2
def baseEnd_7226358 : Nat := 1236865011821047691597197

theorem tailTrace_7226358 : CollatzResearch.WordTrace tailWord_7226358 prefixEnd_7226358 1236865011821047691597197 := by
  unfold tailWord_7226358
  simp only [CollatzResearch.WordTrace]
  refine ⟨16472933072134162783419983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175711286102764403023146485 16472933072134162783419983)
  ·
    refine ⟨24709399608201244175129975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16472933072134162783419983 24709399608201244175129975)
    ·
      refine ⟨37064099412301866262694963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24709399608201244175129975 37064099412301866262694963)
      ·
        refine ⟨55596149118452799394042445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37064099412301866262694963 55596149118452799394042445)
        ·
          refine ⟨20848555919419799772765917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55596149118452799394042445 20848555919419799772765917)
          ·
            refine ⟨7818208469782424914787219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20848555919419799772765917 7818208469782424914787219)
            ·
              refine ⟨11727312704673637372180829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7818208469782424914787219 11727312704673637372180829)
              ·
                refine ⟨4397742264252614014567811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11727312704673637372180829 4397742264252614014567811)
                ·
                  refine ⟨6596613396378921021851717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4397742264252614014567811 6596613396378921021851717)
                  ·
                    refine ⟨1236865011821047691597197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6596613396378921021851717 1236865011821047691597197)
                    ·
                      rfl

theorem cell23_7226358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_7226358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226358 prefixEnd_7226358 := by exact prefixLift 7226358
  have htrace : WordTrace (prefixWord ++ tailWord_7226358) baseStart_7226358 baseEnd_7226358 := by
    simpa [prefixWord, tailWord_7226358, baseEnd_7226358] using wordTrace_append hprefix tailTrace_7226358
  have hstable : (prefixWord ++ tailWord_7226358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226358).length < 2 ^ (prefixWord ++ tailWord_7226358).sum := by decide
  have hdescent : baseEnd_7226358 < baseStart_7226358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226404 : List Nat := [2, 3, 1, 4, 1, 2, 1, 1, 3, 1, 4]
def baseStart_7226404 : Nat := 118140960795 + 7226404 * 2 ^ 59
def prefixEnd_7226404 : Nat := 4983230072969 + 3 ^ 40 * 7226404 * 2
def baseEnd_7226404 : Nat := 3710618655573249894816379

theorem tailTrace_7226404 : CollatzResearch.WordTrace tailWord_7226404 prefixEnd_7226404 3710618655573249894816379 := by
  unfold tailWord_7226404
  simp only [CollatzResearch.WordTrace]
  refine ⟨131784303455989977195447133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175712404607986636260596177 131784303455989977195447133)
  ·
    refine ⟨49419113795996241448292675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131784303455989977195447133 49419113795996241448292675)
    ·
      refine ⟨74128670693994362172439013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49419113795996241448292675 74128670693994362172439013)
      ·
        refine ⟨13899125755123942907332315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74128670693994362172439013 13899125755123942907332315)
        ·
          refine ⟨20848688632685914360998473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13899125755123942907332315 20848688632685914360998473)
          ·
            refine ⟨15636516474514435770748855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20848688632685914360998473 15636516474514435770748855)
            ·
              refine ⟨23454774711771653656123283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15636516474514435770748855 23454774711771653656123283)
              ·
                refine ⟨35182162067657480484184925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23454774711771653656123283 35182162067657480484184925)
                ·
                  refine ⟨13193310775371555181569347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35182162067657480484184925 13193310775371555181569347)
                  ·
                    refine ⟨19789966163057332772354021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13193310775371555181569347 19789966163057332772354021)
                    ·
                      refine ⟨3710618655573249894816379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19789966163057332772354021 3710618655573249894816379)
                      ·
                        rfl

theorem cell23_7226404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_7226404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226404 prefixEnd_7226404 := by exact prefixLift 7226404
  have htrace : WordTrace (prefixWord ++ tailWord_7226404) baseStart_7226404 baseEnd_7226404 := by
    simpa [prefixWord, tailWord_7226404, baseEnd_7226404] using wordTrace_append hprefix tailTrace_7226404
  have hstable : (prefixWord ++ tailWord_7226404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226404).length < 2 ^ (prefixWord ++ tailWord_7226404).sum := by decide
  have hdescent : baseEnd_7226404 < baseStart_7226404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226417 : List Nat := [1, 2, 2, 3, 1, 2, 3, 2, 1, 2, 4]
def baseStart_7226417 : Nat := 118140960795 + 7226417 * 2 ^ 59
def prefixEnd_7226417 : Nat := 4983230072969 + 3 ^ 40 * 7226417 * 2
def baseEnd_7226417 : Nat := 3710625330821758343953819

theorem tailTrace_7226417 : CollatzResearch.WordTrace tailWord_7226417 prefixEnd_7226417 3710625330821758343953819 := by
  unfold tailWord_7226417
  simp only [CollatzResearch.WordTrace]
  refine ⟨263569081060932857611117505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175712720707288571740745003 263569081060932857611117505)
  ·
    refine ⟨197676810795699643208338129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263569081060932857611117505 197676810795699643208338129)
    ·
      refine ⟨148257608096774732406253597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197676810795699643208338129 148257608096774732406253597)
      ·
        refine ⟨55596603036290524652345099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148257608096774732406253597 55596603036290524652345099)
        ·
          refine ⟨83394904554435786978517649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55596603036290524652345099 83394904554435786978517649)
          ·
            refine ⟨62546178415826840233888237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83394904554435786978517649 62546178415826840233888237)
            ·
              refine ⟨23454816905935065087708089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62546178415826840233888237 23454816905935065087708089)
              ·
                refine ⟨17591112679451298815781067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23454816905935065087708089 17591112679451298815781067)
                ·
                  refine ⟨26386669019176948223671601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17591112679451298815781067 26386669019176948223671601)
                  ·
                    refine ⟨19790001764382711167753701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26386669019176948223671601 19790001764382711167753701)
                    ·
                      refine ⟨3710625330821758343953819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19790001764382711167753701 3710625330821758343953819)
                      ·
                        rfl

theorem cell23_7226417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_7226417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226417 prefixEnd_7226417 := by exact prefixLift 7226417
  have htrace : WordTrace (prefixWord ++ tailWord_7226417) baseStart_7226417 baseEnd_7226417 := by
    simpa [prefixWord, tailWord_7226417, baseEnd_7226417] using wordTrace_append hprefix tailTrace_7226417
  have hstable : (prefixWord ++ tailWord_7226417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226417).length < 2 ^ (prefixWord ++ tailWord_7226417).sum := by decide
  have hdescent : baseEnd_7226417 < baseStart_7226417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226424 : List Nat := [2, 1, 2, 1, 5, 3, 1, 1, 1, 1, 5]
def baseStart_7226424 : Nat := 118140960795 + 7226424 * 2 ^ 59
def prefixEnd_7226424 : Nat := 4983230072969 + 3 ^ 40 * 7226424 * 2
def baseEnd_7226424 : Nat := 3710628925186339816566287

theorem tailTrace_7226424 : CollatzResearch.WordTrace tailWord_7226424 prefixEnd_7226424 3710628925186339816566287 := by
  unfold tailWord_7226424
  simp only [CollatzResearch.WordTrace]
  refine ⟨131784668185953748903311163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175712890914604998537748217 131784668185953748903311163)
  ·
    refine ⟨197677002278930623354966745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131784668185953748903311163 197677002278930623354966745)
    ·
      refine ⟨148257751709197967516225059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197677002278930623354966745 148257751709197967516225059)
      ·
        refine ⟨222386627563796951274337589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148257751709197967516225059 222386627563796951274337589)
        ·
          refine ⟨20848746334105964181969149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 222386627563796951274337589 20848746334105964181969149)
          ·
            refine ⟨7818279875289736568238431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20848746334105964181969149 7818279875289736568238431)
            ·
              refine ⟨11727419812934604852357647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7818279875289736568238431 11727419812934604852357647)
              ·
                refine ⟨17591129719401907278536471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11727419812934604852357647 17591129719401907278536471)
                ·
                  refine ⟨26386694579102860917804707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17591129719401907278536471 26386694579102860917804707)
                  ·
                    refine ⟨39580041868654291376707061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26386694579102860917804707 39580041868654291376707061)
                    ·
                      refine ⟨3710628925186339816566287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39580041868654291376707061 3710628925186339816566287)
                      ·
                        rfl

theorem cell23_7226424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 1, 1, 5].length) (baseStart_7226424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226424 prefixEnd_7226424 := by exact prefixLift 7226424
  have htrace : WordTrace (prefixWord ++ tailWord_7226424) baseStart_7226424 baseEnd_7226424 := by
    simpa [prefixWord, tailWord_7226424, baseEnd_7226424] using wordTrace_append hprefix tailTrace_7226424
  have hstable : (prefixWord ++ tailWord_7226424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226424).length < 2 ^ (prefixWord ++ tailWord_7226424).sum := by decide
  have hdescent : baseEnd_7226424 < baseStart_7226424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226440 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 1, 9]
def baseStart_7226440 : Nat := 118140960795 + 7226440 * 2 ^ 59
def prefixEnd_7226440 : Nat := 4983230072969 + 3 ^ 40 * 7226440 * 2
def baseEnd_7226440 : Nat := 1236879046958937251322071

theorem tailTrace_7226440 : CollatzResearch.WordTrace tailWord_7226440 prefixEnd_7226440 1236879046958937251322071 := by
  unfold tailWord_7226440
  simp only [CollatzResearch.WordTrace]
  refine ⟨131784959969924766269602387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175713279959899688359469849 131784959969924766269602387)
  ·
    refine ⟨197677439954887149404403581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131784959969924766269602387 197677439954887149404403581)
    ·
      refine ⟨74129039983082681026651343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197677439954887149404403581 74129039983082681026651343)
      ·
        refine ⟨111193559974624021539977015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74129039983082681026651343 111193559974624021539977015)
        ·
          refine ⟨166790339961936032309965523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111193559974624021539977015 166790339961936032309965523)
          ·
            refine ⟨250185509942904048464948285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166790339961936032309965523 250185509942904048464948285)
            ·
              refine ⟨93819566228589018174355607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250185509942904048464948285 93819566228589018174355607)
              ·
                refine ⟨140729349342883527261533411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93819566228589018174355607 140729349342883527261533411)
                ·
                  refine ⟨211094024014325290892300117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140729349342883527261533411 211094024014325290892300117)
                  ·
                    refine ⟨1236879046958937251322071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 211094024014325290892300117 1236879046958937251322071)
                    ·
                      rfl

theorem cell23_7226440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_7226440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226440 prefixEnd_7226440 := by exact prefixLift 7226440
  have htrace : WordTrace (prefixWord ++ tailWord_7226440) baseStart_7226440 baseEnd_7226440 := by
    simpa [prefixWord, tailWord_7226440, baseEnd_7226440] using wordTrace_append hprefix tailTrace_7226440
  have hstable : (prefixWord ++ tailWord_7226440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226440).length < 2 ^ (prefixWord ++ tailWord_7226440).sum := by decide
  have hdescent : baseEnd_7226440 < baseStart_7226440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226447 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 1, 9, 2]
def baseStart_7226447 : Nat := 118140960795 + 7226447 * 2 ^ 59
def prefixEnd_7226447 : Nat := 4983230072969 + 3 ^ 40 * 7226447 * 2
def baseEnd_7226447 : Nat := 3710640735241393226578681

theorem tailTrace_7226447 : CollatzResearch.WordTrace tailWord_7226447 prefixEnd_7226447 3710640735241393226578681 := by
  unfold tailWord_7226447
  simp only [CollatzResearch.WordTrace]
  refine ⟨263570175250824172734709595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175713450167216115156473063 263570175250824172734709595)
  ·
    refine ⟨395355262876236259102064393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263570175250824172734709595 395355262876236259102064393)
    ·
      refine ⟨296516447157177194326548295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395355262876236259102064393 296516447157177194326548295)
      ·
        refine ⟨444774670735765791489822443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296516447157177194326548295 444774670735765791489822443)
        ·
          refine ⟨667162006103648687234733665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444774670735765791489822443 667162006103648687234733665)
          ·
            refine ⟨500371504577736515426050249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 667162006103648687234733665 500371504577736515426050249)
            ·
              refine ⟨375278628433302386569537687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 500371504577736515426050249 375278628433302386569537687)
              ·
                refine ⟨562917942649953579854306531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 375278628433302386569537687 562917942649953579854306531)
                ·
                  refine ⟨844376913974930369781459797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 562917942649953579854306531 844376913974930369781459797)
                  ·
                    refine ⟨4947520980321857635438241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 844376913974930369781459797 4947520980321857635438241)
                    ·
                      refine ⟨3710640735241393226578681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4947520980321857635438241 3710640735241393226578681)
                      ·
                        rfl

theorem cell23_7226447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 9, 2].length) (baseStart_7226447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226447 prefixEnd_7226447 := by exact prefixLift 7226447
  have htrace : WordTrace (prefixWord ++ tailWord_7226447) baseStart_7226447 baseEnd_7226447 := by
    simpa [prefixWord, tailWord_7226447, baseEnd_7226447] using wordTrace_append hprefix tailTrace_7226447
  have hstable : (prefixWord ++ tailWord_7226447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226447).length < 2 ^ (prefixWord ++ tailWord_7226447).sum := by decide
  have hdescent : baseEnd_7226447 < baseStart_7226447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226461 : List Nat := [1, 4, 4, 1, 2, 1, 3, 7]
def baseStart_7226461 : Nat := 118140960795 + 7226461 * 2 ^ 59
def prefixEnd_7226461 : Nat := 4983230072969 + 3 ^ 40 * 7226461 * 2
def baseEnd_7226461 : Nat := 137431404591502080437171

theorem tailTrace_7226461 : CollatzResearch.WordTrace tailWord_7226461 prefixEnd_7226461 137431404591502080437171 := by
  unfold tailWord_7226461
  simp only [CollatzResearch.WordTrace]
  refine ⟨263570685872773453125719237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175713790581848968750479491 263570685872773453125719237)
  ·
    refine ⟨49419503601145022461072357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263570685872773453125719237 49419503601145022461072357)
    ·
      refine ⟨9266156925214691711451067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49419503601145022461072357 9266156925214691711451067)
      ·
        refine ⟨13899235387822037567176601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9266156925214691711451067 13899235387822037567176601)
        ·
          refine ⟨10424426540866528175382451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13899235387822037567176601 10424426540866528175382451)
          ·
            refine ⟨15636639811299792263073677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10424426540866528175382451 15636639811299792263073677)
            ·
              refine ⟨5863739929237422098652629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15636639811299792263073677 5863739929237422098652629)
              ·
                refine ⟨137431404591502080437171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5863739929237422098652629 137431404591502080437171)
                ·
                  rfl

theorem cell23_7226461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 7].length) (baseStart_7226461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226461 prefixEnd_7226461 := by exact prefixLift 7226461
  have htrace : WordTrace (prefixWord ++ tailWord_7226461) baseStart_7226461 baseEnd_7226461 := by
    simpa [prefixWord, tailWord_7226461, baseEnd_7226461] using wordTrace_append hprefix tailTrace_7226461
  have hstable : (prefixWord ++ tailWord_7226461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226461).length < 2 ^ (prefixWord ++ tailWord_7226461).sum := by decide
  have hdescent : baseEnd_7226461 < baseStart_7226461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226464 : List Nat := [2, 1, 1, 3, 2, 2, 1, 3, 3, 3, 2]
def baseStart_7226464 : Nat := 118140960795 + 7226464 * 2 ^ 59
def prefixEnd_7226464 : Nat := 4983230072969 + 3 ^ 40 * 7226464 * 2
def baseEnd_7226464 : Nat := 3710649464412519660066103

theorem tailTrace_7226464 : CollatzResearch.WordTrace tailWord_7226464 prefixEnd_7226464 3710649464412519660066103 := by
  unfold tailWord_7226464
  simp only [CollatzResearch.WordTrace]
  refine ⟨131785397645881292319039223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175713863527841723092052297 131785397645881292319039223)
  ·
    refine ⟨197678096468821938478558835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131785397645881292319039223 197678096468821938478558835)
    ·
      refine ⟨296517144703232907717838253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197678096468821938478558835 296517144703232907717838253)
      ·
        refine ⟨111193929263712340394189345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296517144703232907717838253 111193929263712340394189345)
        ·
          refine ⟨83395446947784255295642009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111193929263712340394189345 83395446947784255295642009)
          ·
            refine ⟨62546585210838191471731507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83395446947784255295642009 62546585210838191471731507)
            ·
              refine ⟨93819877816257287207597261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62546585210838191471731507 93819877816257287207597261)
              ·
                refine ⟨35182454181096482702848973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93819877816257287207597261 35182454181096482702848973)
                ·
                  refine ⟨13193420317911181013568365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35182454181096482702848973 13193420317911181013568365)
                  ·
                    refine ⟨4947532619216692880088137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13193420317911181013568365 4947532619216692880088137)
                    ·
                      refine ⟨3710649464412519660066103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4947532619216692880088137 3710649464412519660066103)
                      ·
                        rfl

theorem cell23_7226464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 3, 3, 2].length) (baseStart_7226464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226464 prefixEnd_7226464 := by exact prefixLift 7226464
  have htrace : WordTrace (prefixWord ++ tailWord_7226464) baseStart_7226464 baseEnd_7226464 := by
    simpa [prefixWord, tailWord_7226464, baseEnd_7226464] using wordTrace_append hprefix tailTrace_7226464
  have hstable : (prefixWord ++ tailWord_7226464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226464).length < 2 ^ (prefixWord ++ tailWord_7226464).sum := by decide
  have hdescent : baseEnd_7226464 < baseStart_7226464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226472 : List Nat := [2, 1, 4, 4, 1, 1, 2, 3, 1, 2, 2]
def baseStart_7226472 : Nat := 118140960795 + 7226472 * 2 ^ 59
def prefixEnd_7226472 : Nat := 4983230072969 + 3 ^ 40 * 7226472 * 2
def baseEnd_7226472 : Nat := 3710653572257755628766067

theorem tailTrace_7226472 : CollatzResearch.WordTrace tailWord_7226472 prefixEnd_7226472 3710653572257755628766067 := by
  unfold tailWord_7226472
  simp only [CollatzResearch.WordTrace]
  refine ⟨131785543537866801002184835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175714058050489068002913113 131785543537866801002184835)
  ·
    refine ⟨197678315306800201503277253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131785543537866801002184835 197678315306800201503277253)
    ·
      refine ⟨37064684120025037781864485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197678315306800201503277253 37064684120025037781864485)
      ·
        refine ⟨6949628272504694584099591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37064684120025037781864485 6949628272504694584099591)
        ·
          refine ⟨10424442408757041876149387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6949628272504694584099591 10424442408757041876149387)
          ·
            refine ⟨15636663613135562814224081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10424442408757041876149387 15636663613135562814224081)
            ·
              refine ⟨11727497709851672110668061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15636663613135562814224081 11727497709851672110668061)
              ·
                refine ⟨4397811641194377041500523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11727497709851672110668061 4397811641194377041500523)
                ·
                  refine ⟨6596717461791565562250785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4397811641194377041500523 6596717461791565562250785)
                  ·
                    refine ⟨4947538096343674171688089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6596717461791565562250785 4947538096343674171688089)
                    ·
                      refine ⟨3710653572257755628766067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4947538096343674171688089 3710653572257755628766067)
                      ·
                        rfl

theorem cell23_7226472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_7226472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226472 prefixEnd_7226472 := by exact prefixLift 7226472
  have htrace : WordTrace (prefixWord ++ tailWord_7226472) baseStart_7226472 baseEnd_7226472 := by
    simpa [prefixWord, tailWord_7226472, baseEnd_7226472] using wordTrace_append hprefix tailTrace_7226472
  have hstable : (prefixWord ++ tailWord_7226472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226472).length < 2 ^ (prefixWord ++ tailWord_7226472).sum := by decide
  have hdescent : baseEnd_7226472 < baseStart_7226472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226547 : List Nat := [1, 1, 1, 2, 3, 2, 3, 1, 4, 5]
def baseStart_7226547 : Nat := 118140960795 + 7226547 * 2 ^ 59
def prefixEnd_7226547 : Nat := 4983230072969 + 3 ^ 40 * 7226547 * 2
def baseEnd_7226547 : Nat := 1236897361102280945109407

theorem tailTrace_7226547 : CollatzResearch.WordTrace tailWord_7226547 prefixEnd_7226547 1236897361102280945109407 := by
  unfold tailWord_7226547
  simp only [CollatzResearch.WordTrace]
  refine ⟨263573822550461889813349895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175715881700307926542233263 263573822550461889813349895)
  ·
    refine ⟨395360733825692834720024843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263573822550461889813349895 395360733825692834720024843)
    ·
      refine ⟨593041100738539252080037265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395360733825692834720024843 593041100738539252080037265)
      ·
        refine ⟨444780825553904439060027949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 593041100738539252080037265 444780825553904439060027949)
        ·
          refine ⟨166792809582714164647510481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 444780825553904439060027949 166792809582714164647510481)
          ·
            refine ⟨125094607187035623485632861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166792809582714164647510481 125094607187035623485632861)
            ·
              refine ⟨46910477695138358807112323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125094607187035623485632861 46910477695138358807112323)
              ·
                refine ⟨70365716542707538210668485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46910477695138358807112323 70365716542707538210668485)
                ·
                  refine ⟨13193571851757663414500341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70365716542707538210668485 13193571851757663414500341)
                  ·
                    refine ⟨1236897361102280945109407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13193571851757663414500341 1236897361102280945109407)
                    ·
                      rfl

theorem cell23_7226547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 5].length) (baseStart_7226547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226547 prefixEnd_7226547 := by exact prefixLift 7226547
  have htrace : WordTrace (prefixWord ++ tailWord_7226547) baseStart_7226547 baseEnd_7226547 := by
    simpa [prefixWord, tailWord_7226547, baseEnd_7226547] using wordTrace_append hprefix tailTrace_7226547
  have hstable : (prefixWord ++ tailWord_7226547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226547).length < 2 ^ (prefixWord ++ tailWord_7226547).sum := by decide
  have hdescent : baseEnd_7226547 < baseStart_7226547 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226551 : List Nat := [1, 1, 3, 1, 4, 1, 5, 2, 5]
def baseStart_7226551 : Nat := 118140960795 + 7226551 * 2 ^ 59
def prefixEnd_7226551 : Nat := 4983230072969 + 3 ^ 40 * 7226551 * 2
def baseEnd_7226551 : Nat := 412299348581051202186467

theorem tailTrace_7226551 : CollatzResearch.WordTrace tailWord_7226551 prefixEnd_7226551 412299348581051202186467 := by
  unfold tailWord_7226551
  simp only [CollatzResearch.WordTrace]
  refine ⟨263573968442447398496495507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175715978961631598997663671 263573968442447398496495507)
  ·
    refine ⟨395360952663671097744743261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263573968442447398496495507 395360952663671097744743261)
    ·
      refine ⟨148260357248876661654278723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 395360952663671097744743261 148260357248876661654278723)
      ·
        refine ⟨222390535873314992481418085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148260357248876661654278723 222390535873314992481418085)
        ·
          refine ⟨41698225476246561090265891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222390535873314992481418085 41698225476246561090265891)
          ·
            refine ⟨62547338214369841635398837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41698225476246561090265891 62547338214369841635398837)
            ·
              refine ⟨5863812957597172653318641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62547338214369841635398837 5863812957597172653318641)
              ·
                refine ⟨4397859718197879489988981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5863812957597172653318641 4397859718197879489988981)
                ·
                  refine ⟨412299348581051202186467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4397859718197879489988981 412299348581051202186467)
                  ·
                    rfl

theorem cell23_7226551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 2, 5].length) (baseStart_7226551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226551 prefixEnd_7226551 := by exact prefixLift 7226551
  have htrace : WordTrace (prefixWord ++ tailWord_7226551) baseStart_7226551 baseEnd_7226551 := by
    simpa [prefixWord, tailWord_7226551, baseEnd_7226551] using wordTrace_append hprefix tailTrace_7226551
  have hstable : (prefixWord ++ tailWord_7226551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226551).length < 2 ^ (prefixWord ++ tailWord_7226551).sum := by decide
  have hdescent : baseEnd_7226551 < baseStart_7226551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226554 : List Nat := [3, 1, 1, 1, 2, 2, 1, 3, 2, 5, 2]
def baseStart_7226554 : Nat := 118140960795 + 7226554 * 2 ^ 59
def prefixEnd_7226554 : Nat := 4983230072969 + 3 ^ 40 * 7226554 * 2
def baseEnd_7226554 : Nat := 3710695677671424307940689

theorem tailTrace_7226554 : CollatzResearch.WordTrace tailWord_7226554 prefixEnd_7226554 3710695677671424307940689 := by
  unfold tailWord_7226554
  simp only [CollatzResearch.WordTrace]
  refine ⟨65893519465359132502213679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175716051907624353339236477 65893519465359132502213679)
  ·
    refine ⟨98840279198038698753320519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65893519465359132502213679 98840279198038698753320519)
    ·
      refine ⟨148260418797058048129980779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98840279198038698753320519 148260418797058048129980779)
      ·
        refine ⟨222390628195587072194971169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148260418797058048129980779 222390628195587072194971169)
        ·
          refine ⟨166792971146690304146228377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222390628195587072194971169 166792971146690304146228377)
          ·
            refine ⟨125094728360017728109671283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166792971146690304146228377 125094728360017728109671283)
            ·
              refine ⟨187642092540026592164506925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125094728360017728109671283 187642092540026592164506925)
              ·
                refine ⟨70365784702509972061690097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187642092540026592164506925 70365784702509972061690097)
                ·
                  refine ⟨52774338526882479046267573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70365784702509972061690097 52774338526882479046267573)
                  ·
                    refine ⟨4947594236895232410587585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52774338526882479046267573 4947594236895232410587585)
                    ·
                      refine ⟨3710695677671424307940689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4947594236895232410587585 3710695677671424307940689)
                      ·
                        rfl

theorem cell23_7226554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 2, 5, 2].length) (baseStart_7226554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226554 prefixEnd_7226554 := by exact prefixLift 7226554
  have htrace : WordTrace (prefixWord ++ tailWord_7226554) baseStart_7226554 baseEnd_7226554 := by
    simpa [prefixWord, tailWord_7226554, baseEnd_7226554] using wordTrace_append hprefix tailTrace_7226554
  have hstable : (prefixWord ++ tailWord_7226554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226554).length < 2 ^ (prefixWord ++ tailWord_7226554).sum := by decide
  have hdescent : baseEnd_7226554 < baseStart_7226554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226557 : List Nat := [1, 4, 1, 2, 1, 1, 3, 1, 1, 1, 7]
def baseStart_7226557 : Nat := 118140960795 + 7226557 * 2 ^ 59
def prefixEnd_7226557 : Nat := 4983230072969 + 3 ^ 40 * 7226557 * 2
def baseEnd_7226557 : Nat := 3710697218113387796203175

theorem tailTrace_7226557 : CollatzResearch.WordTrace tailWord_7226557 prefixEnd_7226557 3710697218113387796203175 := by
  unfold tailWord_7226557
  simp only [CollatzResearch.WordTrace]
  refine ⟨263574187280425661521213925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175716124853617107680809283 263574187280425661521213925)
  ·
    refine ⟨49420160115079811535227611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263574187280425661521213925 49420160115079811535227611)
    ·
      refine ⟨74130240172619717302841417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49420160115079811535227611 74130240172619717302841417)
      ·
        refine ⟨55597680129464787977131063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74130240172619717302841417 55597680129464787977131063)
        ·
          refine ⟨83396520194197181965696595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55597680129464787977131063 83396520194197181965696595)
          ·
            refine ⟨125094780291295772948544893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83396520194197181965696595 125094780291295772948544893)
            ·
              refine ⟨46910542609235914855704335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125094780291295772948544893 46910542609235914855704335)
              ·
                refine ⟨70365813913853872283556503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46910542609235914855704335 70365813913853872283556503)
                ·
                  refine ⟨105548720870780808425334755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70365813913853872283556503 105548720870780808425334755)
                  ·
                    refine ⟨158323081306171212638002133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105548720870780808425334755 158323081306171212638002133)
                    ·
                      refine ⟨3710697218113387796203175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 158323081306171212638002133 3710697218113387796203175)
                      ·
                        rfl

theorem cell23_7226557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_7226557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226557 prefixEnd_7226557 := by exact prefixLift 7226557
  have htrace : WordTrace (prefixWord ++ tailWord_7226557) baseStart_7226557 baseEnd_7226557 := by
    simpa [prefixWord, tailWord_7226557, baseEnd_7226557] using wordTrace_append hprefix tailTrace_7226557
  have hstable : (prefixWord ++ tailWord_7226557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226557).length < 2 ^ (prefixWord ++ tailWord_7226557).sum := by decide
  have hdescent : baseEnd_7226557 < baseStart_7226557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226566 : List Nat := [6, 1, 2, 2, 2, 1, 1, 2, 1, 3, 2]
def baseStart_7226566 : Nat := 118140960795 + 7226566 * 2 ^ 59
def prefixEnd_7226566 : Nat := 4983230072969 + 3 ^ 40 * 7226566 * 2
def baseEnd_7226566 : Nat := 3710701839439278260990635

theorem tailTrace_7226566 : CollatzResearch.WordTrace tailWord_7226566 prefixEnd_7226566 3710701839439278260990635 := by
  unfold tailWord_7226566
  simp only [CollatzResearch.WordTrace]
  refine ⟨8236703610543533001821611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 175716343691595370705527701 8236703610543533001821611)
  ·
    refine ⟨12355055415815299502732417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8236703610543533001821611 12355055415815299502732417)
    ·
      refine ⟨9266291561861474627049313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12355055415815299502732417 9266291561861474627049313)
      ·
        refine ⟨6949718671396105970286985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9266291561861474627049313 6949718671396105970286985)
        ·
          refine ⟨5212289003547079477715239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6949718671396105970286985 5212289003547079477715239)
          ·
            refine ⟨7818433505320619216572859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5212289003547079477715239 7818433505320619216572859)
            ·
              refine ⟨11727650257980928824859289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7818433505320619216572859 11727650257980928824859289)
              ·
                refine ⟨8795737693485696618644467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11727650257980928824859289 8795737693485696618644467)
                ·
                  refine ⟨13193606540228544927966701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8795737693485696618644467 13193606540228544927966701)
                  ·
                    refine ⟨4947602452585704347987513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13193606540228544927966701 4947602452585704347987513)
                    ·
                      refine ⟨3710701839439278260990635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4947602452585704347987513 3710701839439278260990635)
                      ·
                        rfl

theorem cell23_7226566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_7226566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226566 prefixEnd_7226566 := by exact prefixLift 7226566
  have htrace : WordTrace (prefixWord ++ tailWord_7226566) baseStart_7226566 baseEnd_7226566 := by
    simpa [prefixWord, tailWord_7226566, baseEnd_7226566] using wordTrace_append hprefix tailTrace_7226566
  have hstable : (prefixWord ++ tailWord_7226566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226566).length < 2 ^ (prefixWord ++ tailWord_7226566).sum := by decide
  have hdescent : baseEnd_7226566 < baseStart_7226566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226567 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 4]
def baseStart_7226567 : Nat := 118140960795 + 7226567 * 2 ^ 59
def prefixEnd_7226567 : Nat := 4983230072969 + 3 ^ 40 * 7226567 * 2
def baseEnd_7226567 : Nat := 3710702352919932757078129

theorem tailTrace_7226567 : CollatzResearch.WordTrace tailWord_7226567 prefixEnd_7226567 3710702352919932757078129 := by
  unfold tailWord_7226567
  simp only [CollatzResearch.WordTrace]
  refine ⟨263574552010389433229077955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175716368006926288819385303 263574552010389433229077955)
  ·
    refine ⟨395361828015584149843616933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263574552010389433229077955 395361828015584149843616933)
    ·
      refine ⟨74130342752922028095678175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 395361828015584149843616933 74130342752922028095678175)
      ·
        refine ⟨111195514129383042143517263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74130342752922028095678175 111195514129383042143517263)
        ·
          refine ⟨166793271194074563215275895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111195514129383042143517263 166793271194074563215275895)
          ·
            refine ⟨250189906791111844822913843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166793271194074563215275895 250189906791111844822913843)
            ·
              refine ⟨375284860186667767234370765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250189906791111844822913843 375284860186667767234370765)
              ·
                refine ⟨140731822570000412712889037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 375284860186667767234370765 140731822570000412712889037)
                ·
                  refine ⟨52774433463750154767333389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140731822570000412712889037 52774433463750154767333389)
                  ·
                    refine ⟨19790412548906308037750021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52774433463750154767333389 19790412548906308037750021)
                    ·
                      refine ⟨3710702352919932757078129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19790412548906308037750021 3710702352919932757078129)
                      ·
                        rfl

theorem cell23_7226567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_7226567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226567 prefixEnd_7226567 := by exact prefixLift 7226567
  have htrace : WordTrace (prefixWord ++ tailWord_7226567) baseStart_7226567 baseEnd_7226567 := by
    simpa [prefixWord, tailWord_7226567, baseEnd_7226567] using wordTrace_append hprefix tailTrace_7226567
  have hstable : (prefixWord ++ tailWord_7226567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226567).length < 2 ^ (prefixWord ++ tailWord_7226567).sum := by decide
  have hdescent : baseEnd_7226567 < baseStart_7226567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226581 : List Nat := [1, 3, 2, 4, 1, 2, 2, 1, 2, 5]
def baseStart_7226581 : Nat := 118140960795 + 7226581 * 2 ^ 59
def prefixEnd_7226581 : Nat := 4983230072969 + 3 ^ 40 * 7226581 * 2
def baseEnd_7226581 : Nat := 1236903180549698567434355

theorem tailTrace_7226581 : CollatzResearch.WordTrace tailWord_7226581 prefixEnd_7226581 1236903180549698567434355 := by
  unfold tailWord_7226581
  simp only [CollatzResearch.WordTrace]
  refine ⟨263575062632338713620087597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175716708421559142413391731 263575062632338713620087597)
  ·
    refine ⟨98840648487127017607532849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263575062632338713620087597 98840648487127017607532849)
    ·
      refine ⟨74130486365345263205649637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98840648487127017607532849 74130486365345263205649637)
      ·
        refine ⟨13899466193502236851059307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74130486365345263205649637 13899466193502236851059307)
        ·
          refine ⟨20849199290253355276588961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13899466193502236851059307 20849199290253355276588961)
          ·
            refine ⟨15636899467690016457441721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20849199290253355276588961 15636899467690016457441721)
            ·
              refine ⟨11727674600767512343081291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15636899467690016457441721 11727674600767512343081291)
              ·
                refine ⟨17591511901151268514621937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11727674600767512343081291 17591511901151268514621937)
                ·
                  refine ⟨13193633925863451385966453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17591511901151268514621937 13193633925863451385966453)
                  ·
                    refine ⟨1236903180549698567434355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13193633925863451385966453 1236903180549698567434355)
                    ·
                      rfl

theorem cell23_7226581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_7226581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226581 prefixEnd_7226581 := by exact prefixLift 7226581
  have htrace : WordTrace (prefixWord ++ tailWord_7226581) baseStart_7226581 baseEnd_7226581 := by
    simpa [prefixWord, tailWord_7226581, baseEnd_7226581] using wordTrace_append hprefix tailTrace_7226581
  have hstable : (prefixWord ++ tailWord_7226581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226581).length < 2 ^ (prefixWord ++ tailWord_7226581).sum := by decide
  have hdescent : baseEnd_7226581 < baseStart_7226581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226614 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4]
def baseStart_7226614 : Nat := 118140960795 + 7226614 * 2 ^ 59
def prefixEnd_7226614 : Nat := 4983230072969 + 3 ^ 40 * 7226614 * 2
def baseEnd_7226614 : Nat := 3710726486510694073190413

theorem tailTrace_7226614 : CollatzResearch.WordTrace tailWord_7226614 prefixEnd_7226614 3710726486510694073190413 := by
  unfold tailWord_7226614
  simp only [CollatzResearch.WordTrace]
  refine ⟨16473516640076197516002431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175717510827479440170692597 16473516640076197516002431)
  ·
    refine ⟨24710274960114296274003647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16473516640076197516002431 24710274960114296274003647)
    ·
      refine ⟨37065412440171444411005471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24710274960114296274003647 37065412440171444411005471)
      ·
        refine ⟨55598118660257166616508207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37065412440171444411005471 55598118660257166616508207)
        ·
          refine ⟨83397177990385749924762311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55598118660257166616508207 83397177990385749924762311)
          ·
            refine ⟨125095766985578624887143467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83397177990385749924762311 125095766985578624887143467)
            ·
              refine ⟨187643650478367937330715201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125095766985578624887143467 187643650478367937330715201)
              ·
                refine ⟨140732737858775952998036401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187643650478367937330715201 140732737858775952998036401)
                ·
                  refine ⟨105549553394081964748527301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140732737858775952998036401 105549553394081964748527301)
                  ·
                    refine ⟨19790541261390368390348869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105549553394081964748527301 19790541261390368390348869)
                    ·
                      refine ⟨3710726486510694073190413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19790541261390368390348869 3710726486510694073190413)
                      ·
                        rfl

theorem cell23_7226614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_7226614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226614 prefixEnd_7226614 := by exact prefixLift 7226614
  have htrace : WordTrace (prefixWord ++ tailWord_7226614) baseStart_7226614 baseEnd_7226614 := by
    simpa [prefixWord, tailWord_7226614, baseEnd_7226614] using wordTrace_append hprefix tailTrace_7226614
  have hstable : (prefixWord ++ tailWord_7226614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226614).length < 2 ^ (prefixWord ++ tailWord_7226614).sum := by decide
  have hdescent : baseEnd_7226614 < baseStart_7226614 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226638 : List Nat := [4, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3]
def baseStart_7226638 : Nat := 118140960795 + 7226638 * 2 ^ 59
def prefixEnd_7226638 : Nat := 4983230072969 + 3 ^ 40 * 7226638 * 2
def baseEnd_7226638 : Nat := 3710738810046401979290303

theorem tailTrace_7226638 : CollatzResearch.WordTrace tailWord_7226638 prefixEnd_7226638 3710738810046401979290303 := by
  unfold tailWord_7226638
  simp only [CollatzResearch.WordTrace]
  refine ⟨32947142699141526544364071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175718094395421474903275045 32947142699141526544364071)
  ·
    refine ⟨49420714048712289816546107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32947142699141526544364071 49420714048712289816546107)
    ·
      refine ⟨74131071073068434724819161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49420714048712289816546107 74131071073068434724819161)
      ·
        refine ⟨55598303304801326043614371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74131071073068434724819161 55598303304801326043614371)
        ·
          refine ⟨83397454957201989065421557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55598303304801326043614371 83397454957201989065421557)
          ·
            refine ⟨7818511402237686474883271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83397454957201989065421557 7818511402237686474883271)
            ·
              refine ⟨11727767103356529712324907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7818511402237686474883271 11727767103356529712324907)
              ·
                refine ⟨17591650655034794568487361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11727767103356529712324907 17591650655034794568487361)
                ·
                  refine ⟨13193737991276095926365521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17591650655034794568487361 13193737991276095926365521)
                  ·
                    refine ⟨9895303493457071944774141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13193737991276095926365521 9895303493457071944774141)
                    ·
                      refine ⟨3710738810046401979290303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9895303493457071944774141 3710738810046401979290303)
                      ·
                        rfl

theorem cell23_7226638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_7226638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226638 prefixEnd_7226638 := by exact prefixLift 7226638
  have htrace : WordTrace (prefixWord ++ tailWord_7226638) baseStart_7226638 baseEnd_7226638 := by
    simpa [prefixWord, tailWord_7226638, baseEnd_7226638] using wordTrace_append hprefix tailTrace_7226638
  have hstable : (prefixWord ++ tailWord_7226638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226638).length < 2 ^ (prefixWord ++ tailWord_7226638).sum := by decide
  have hdescent : baseEnd_7226638 < baseStart_7226638 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226658 : List Nat := [3, 3, 1, 1, 4, 2, 1, 2, 6]
def baseStart_7226658 : Nat := 118140960795 + 7226658 * 2 ^ 59
def prefixEnd_7226658 : Nat := 4983230072969 + 3 ^ 40 * 7226658 * 2
def baseEnd_7226658 : Nat := 412305453295499100115579

theorem tailTrace_7226658 : CollatzResearch.WordTrace tailWord_7226658 prefixEnd_7226658 412305453295499100115579 := by
  unfold tailWord_7226658
  simp only [CollatzResearch.WordTrace]
  refine ⟨65894467763264938942660157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175718580702039837180427085 65894467763264938942660157)
  ·
    refine ⟨24710425411224352103497559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65894467763264938942660157 24710425411224352103497559)
    ·
      refine ⟨37065638116836528155246339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24710425411224352103497559 37065638116836528155246339)
      ·
        refine ⟨55598457175254792232869509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37065638116836528155246339 55598457175254792232869509)
        ·
          refine ⟨10424710720360273543663033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55598457175254792232869509 10424710720360273543663033)
          ·
            refine ⟨7818533040270205157747275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10424710720360273543663033 7818533040270205157747275)
            ·
              refine ⟨11727799560405307736620913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7818533040270205157747275 11727799560405307736620913)
              ·
                refine ⟨8795849670303980802465685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11727799560405307736620913 8795849670303980802465685)
                ·
                  refine ⟨412305453295499100115579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8795849670303980802465685 412305453295499100115579)
                  ·
                    rfl

theorem cell23_7226658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_7226658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226658 prefixEnd_7226658 := by exact prefixLift 7226658
  have htrace : WordTrace (prefixWord ++ tailWord_7226658) baseStart_7226658 baseEnd_7226658 := by
    simpa [prefixWord, tailWord_7226658, baseEnd_7226658] using wordTrace_append hprefix tailTrace_7226658
  have hstable : (prefixWord ++ tailWord_7226658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226658).length < 2 ^ (prefixWord ++ tailWord_7226658).sum := by decide
  have hdescent : baseEnd_7226658 < baseStart_7226658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226704 : List Nat := [2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 4]
def baseStart_7226704 : Nat := 118140960795 + 7226704 * 2 ^ 59
def prefixEnd_7226704 : Nat := 4983230072969 + 3 ^ 40 * 7226704 * 2
def baseEnd_7226704 : Nat := 3710772699769598721064999

theorem tailTrace_7226704 : CollatzResearch.WordTrace tailWord_7226704 prefixEnd_7226704 3710772699769598721064999 := by
  unfold tailWord_7226704
  simp only [CollatzResearch.WordTrace]
  refine ⟨131789774405446552813407583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175719699207262070417876777 131789774405446552813407583)
  ·
    refine ⟨197684661608169829220111375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131789774405446552813407583 197684661608169829220111375)
    ·
      refine ⟨296526992412254743830167063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197684661608169829220111375 296526992412254743830167063)
      ·
        refine ⟨444790488618382115745250595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296526992412254743830167063 444790488618382115745250595)
        ·
          refine ⟨667185732927573173617875893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444790488618382115745250595 667185732927573173617875893)
          ·
            refine ⟨62548662461959985026675865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 667185732927573173617875893 62548662461959985026675865)
            ·
              refine ⟨46911496846469988770006899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62548662461959985026675865 46911496846469988770006899)
              ·
                refine ⟨70367245269704983155010349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46911496846469988770006899 70367245269704983155010349)
                ·
                  refine ⟨26387716976139368683128881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70367245269704983155010349 26387716976139368683128881)
                  ·
                    refine ⟨19790787732104526512346661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26387716976139368683128881 19790787732104526512346661)
                    ·
                      refine ⟨3710772699769598721064999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19790787732104526512346661 3710772699769598721064999)
                      ·
                        rfl

theorem cell23_7226704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 4].length) (baseStart_7226704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226704 prefixEnd_7226704 := by exact prefixLift 7226704
  have htrace : WordTrace (prefixWord ++ tailWord_7226704) baseStart_7226704 baseEnd_7226704 := by
    simpa [prefixWord, tailWord_7226704, baseEnd_7226704] using wordTrace_append hprefix tailTrace_7226704
  have hstable : (prefixWord ++ tailWord_7226704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226704).length < 2 ^ (prefixWord ++ tailWord_7226704).sum := by decide
  have hdescent : baseEnd_7226704 < baseStart_7226704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226711 : List Nat := [1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 5]
def baseStart_7226711 : Nat := 118140960795 + 7226711 * 2 ^ 59
def prefixEnd_7226711 : Nat := 4983230072969 + 3 ^ 40 * 7226711 * 2
def baseEnd_7226711 : Nat := 3710776294134180193677467

theorem tailTrace_7226711 : CollatzResearch.WordTrace tailWord_7226711 prefixEnd_7226711 3710776294134180193677467 := by
  unfold tailWord_7226711
  simp only [CollatzResearch.WordTrace]
  refine ⟨263579804121867745822319987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175719869414578497214879991 263579804121867745822319987)
  ·
    refine ⟨395369706182801618733479981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263579804121867745822319987 395369706182801618733479981)
    ·
      refine ⟨148263639818550607025054993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 395369706182801618733479981 148263639818550607025054993)
      ·
        refine ⟨111197729863912955268791245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148263639818550607025054993 111197729863912955268791245)
        ·
          refine ⟨41699148698967358225796717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111197729863912955268791245 41699148698967358225796717)
          ·
            refine ⟨15637180762112759334673769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41699148698967358225796717 15637180762112759334673769)
            ·
              refine ⟨11727885571584569501005327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15637180762112759334673769 11727885571584569501005327)
              ·
                refine ⟨17591828357376854251507991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11727885571584569501005327 17591828357376854251507991)
                ·
                  refine ⟨26387742536065281377261987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17591828357376854251507991 26387742536065281377261987)
                  ·
                    refine ⟨39581613804097922065892981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26387742536065281377261987 39581613804097922065892981)
                    ·
                      refine ⟨3710776294134180193677467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39581613804097922065892981 3710776294134180193677467)
                      ·
                        rfl

theorem cell23_7226711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_7226711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226711 prefixEnd_7226711 := by exact prefixLift 7226711
  have htrace : WordTrace (prefixWord ++ tailWord_7226711) baseStart_7226711 baseEnd_7226711 := by
    simpa [prefixWord, tailWord_7226711, baseEnd_7226711] using wordTrace_append hprefix tailTrace_7226711
  have hstable : (prefixWord ++ tailWord_7226711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226711).length < 2 ^ (prefixWord ++ tailWord_7226711).sum := by decide
  have hdescent : baseEnd_7226711 < baseStart_7226711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226776 : List Nat := [2, 1, 2, 5, 2, 2, 2, 2, 1, 2, 2]
def baseStart_7226776 : Nat := 118140960795 + 7226776 * 2 ^ 59
def prefixEnd_7226776 : Nat := 4983230072969 + 3 ^ 40 * 7226776 * 2
def baseEnd_7226776 : Nat := 3710809670376722439364669

theorem tailTrace_7226776 : CollatzResearch.WordTrace tailWord_7226776 prefixEnd_7226776 3710809670376722439364669 := by
  unfold tailWord_7226776
  simp only [CollatzResearch.WordTrace]
  refine ⟨131791087433316130961718091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175721449911088174615624121 131791087433316130961718091)
  ·
    refine ⟨197686631149974196442577137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131791087433316130961718091 197686631149974196442577137)
    ·
      refine ⟨148264973362480647331932853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197686631149974196442577137 148264973362480647331932853)
      ·
        refine ⟨13899841252732560687368705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148264973362480647331932853 13899841252732560687368705)
        ·
          refine ⟨10424880939549420515526529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13899841252732560687368705 10424880939549420515526529)
          ·
            refine ⟨7818660704662065386644897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10424880939549420515526529 7818660704662065386644897)
            ·
              refine ⟨5863995528496549039983673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7818660704662065386644897 5863995528496549039983673)
              ·
                refine ⟨4397996646372411779987755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5863995528496549039983673 4397996646372411779987755)
                ·
                  refine ⟨6596994969558617669981633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4397996646372411779987755 6596994969558617669981633)
                  ·
                    refine ⟨4947746227168963252486225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6596994969558617669981633 4947746227168963252486225)
                    ·
                      refine ⟨3710809670376722439364669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4947746227168963252486225 3710809670376722439364669)
                      ·
                        rfl

theorem cell23_7226776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_7226776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226776 prefixEnd_7226776 := by exact prefixLift 7226776
  have htrace : WordTrace (prefixWord ++ tailWord_7226776) baseStart_7226776 baseEnd_7226776 := by
    simpa [prefixWord, tailWord_7226776, baseEnd_7226776] using wordTrace_append hprefix tailTrace_7226776
  have hstable : (prefixWord ++ tailWord_7226776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226776).length < 2 ^ (prefixWord ++ tailWord_7226776).sum := by decide
  have hdescent : baseEnd_7226776 < baseStart_7226776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226781 : List Nat := [1, 4, 2, 1, 3, 1, 1, 1, 2, 3, 4]
def baseStart_7226781 : Nat := 118140960795 + 7226781 * 2 ^ 59
def prefixEnd_7226781 : Nat := 4983230072969 + 3 ^ 40 * 7226781 * 2
def baseEnd_7226781 : Nat := 3710812237779994919802145

theorem tailTrace_7226781 : CollatzResearch.WordTrace tailWord_7226781 prefixEnd_7226781 3710812237779994919802145 := by
  unfold tailWord_7226781
  simp only [CollatzResearch.WordTrace]
  refine ⟨263582357231614147777368197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175721571487742765184912131 263582357231614147777368197)
  ·
    refine ⟨49421691980927652708256537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263582357231614147777368197 49421691980927652708256537)
    ·
      refine ⟨37066268985695739531192403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49421691980927652708256537 37066268985695739531192403)
      ·
        refine ⟨55599403478543609296788605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37066268985695739531192403 55599403478543609296788605)
        ·
          refine ⟨20849776304453853486295727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55599403478543609296788605 20849776304453853486295727)
          ·
            refine ⟨31274664456680780229443591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20849776304453853486295727 31274664456680780229443591)
            ·
              refine ⟨46911996685021170344165387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31274664456680780229443591 46911996685021170344165387)
              ·
                refine ⟨70367995027531755516248081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46911996685021170344165387 70367995027531755516248081)
                ·
                  refine ⟨52775996270648816637186061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70367995027531755516248081 52775996270648816637186061)
                  ·
                    refine ⟨19790998601493306238944773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52775996270648816637186061 19790998601493306238944773)
                    ·
                      refine ⟨3710812237779994919802145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19790998601493306238944773 3710812237779994919802145)
                      ·
                        rfl

theorem cell23_7226781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_7226781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226781 prefixEnd_7226781 := by exact prefixLift 7226781
  have htrace : WordTrace (prefixWord ++ tailWord_7226781) baseStart_7226781 baseEnd_7226781 := by
    simpa [prefixWord, tailWord_7226781, baseEnd_7226781] using wordTrace_append hprefix tailTrace_7226781
  have hstable : (prefixWord ++ tailWord_7226781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226781).length < 2 ^ (prefixWord ++ tailWord_7226781).sum := by decide
  have hdescent : baseEnd_7226781 < baseStart_7226781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226791 : List Nat := [1, 1, 6, 1, 1, 1, 3, 1, 2, 6]
def baseStart_7226791 : Nat := 118140960795 + 7226791 * 2 ^ 59
def prefixEnd_7226791 : Nat := 4983230072969 + 3 ^ 40 * 7226791 * 2
def baseEnd_7226791 : Nat := 1236939124195513293559033

theorem tailTrace_7226791 : CollatzResearch.WordTrace tailWord_7226791 prefixEnd_7226791 1236939124195513293559033 := by
  unfold tailWord_7226791
  simp only [CollatzResearch.WordTrace]
  refine ⟨263582721961577919485232227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175721814641051946323488151 263582721961577919485232227)
  ·
    refine ⟨395374082942366879227848341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263582721961577919485232227 395374082942366879227848341)
    ·
      refine ⟨18533160137923447463805391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 395374082942366879227848341 18533160137923447463805391)
      ·
        refine ⟨27799740206885171195708087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18533160137923447463805391 27799740206885171195708087)
        ·
          refine ⟨41699610310327756793562131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27799740206885171195708087 41699610310327756793562131)
          ·
            refine ⟨62549415465491635190343197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41699610310327756793562131 62549415465491635190343197)
            ·
              refine ⟨23456030799559363196378699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62549415465491635190343197 23456030799559363196378699)
              ·
                refine ⟨35184046199339044794568049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23456030799559363196378699 35184046199339044794568049)
                ·
                  refine ⟨26388034649504283595926037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35184046199339044794568049 26388034649504283595926037)
                  ·
                    refine ⟨1236939124195513293559033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26388034649504283595926037 1236939124195513293559033)
                    ·
                      rfl

theorem cell23_7226791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_7226791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226791 prefixEnd_7226791 := by exact prefixLift 7226791
  have htrace : WordTrace (prefixWord ++ tailWord_7226791) baseStart_7226791 baseEnd_7226791 := by
    simpa [prefixWord, tailWord_7226791, baseEnd_7226791] using wordTrace_append hprefix tailTrace_7226791
  have hstable : (prefixWord ++ tailWord_7226791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226791).length < 2 ^ (prefixWord ++ tailWord_7226791).sum := by decide
  have hdescent : baseEnd_7226791 < baseStart_7226791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226801 : List Nat := [1, 2, 2, 4, 1, 1, 1, 2, 2, 4, 3]
def baseStart_7226801 : Nat := 118140960795 + 7226801 * 2 ^ 59
def prefixEnd_7226801 : Nat := 4983230072969 + 3 ^ 40 * 7226801 * 2
def baseEnd_7226801 : Nat := 3710822507393084841552053

theorem tailTrace_7226801 : CollatzResearch.WordTrace tailWord_7226801 prefixEnd_7226801 3710822507393084841552053 := by
  unfold tailWord_7226801
  simp only [CollatzResearch.WordTrace]
  refine ⟨263583086691541691193096257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175722057794361127462064171 263583086691541691193096257)
  ·
    refine ⟨197687315018656268394822193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263583086691541691193096257 197687315018656268394822193)
    ·
      refine ⟨148265486263992201296116645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197687315018656268394822193 148265486263992201296116645)
      ·
        refine ⟨27799778674498537743021871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148265486263992201296116645 27799778674498537743021871)
        ·
          refine ⟨41699668011747806614532807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27799778674498537743021871 41699668011747806614532807)
          ·
            refine ⟨62549502017621709921799211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41699668011747806614532807 62549502017621709921799211)
            ·
              refine ⟨93824253026432564882698817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62549502017621709921799211 93824253026432564882698817)
              ·
                refine ⟨70368189769824423662024113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93824253026432564882698817 70368189769824423662024113)
                ·
                  refine ⟨52776142327368317746518085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70368189769824423662024113 52776142327368317746518085)
                  ·
                    refine ⟨9895526686381559577472141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52776142327368317746518085 9895526686381559577472141)
                    ·
                      refine ⟨3710822507393084841552053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9895526686381559577472141 3710822507393084841552053)
                      ·
                        rfl

theorem cell23_7226801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_7226801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226801 prefixEnd_7226801 := by exact prefixLift 7226801
  have htrace : WordTrace (prefixWord ++ tailWord_7226801) baseStart_7226801 baseEnd_7226801 := by
    simpa [prefixWord, tailWord_7226801, baseEnd_7226801] using wordTrace_append hprefix tailTrace_7226801
  have hstable : (prefixWord ++ tailWord_7226801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226801).length < 2 ^ (prefixWord ++ tailWord_7226801).sum := by decide
  have hdescent : baseEnd_7226801 < baseStart_7226801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226831 : List Nat := [1, 1, 2, 1, 1, 4, 3, 2, 2, 3, 3]
def baseStart_7226831 : Nat := 118140960795 + 7226831 * 2 ^ 59
def prefixEnd_7226831 : Nat := 4983230072969 + 3 ^ 40 * 7226831 * 2
def baseEnd_7226831 : Nat := 3710837911812719724176915

theorem tailTrace_7226831 : CollatzResearch.WordTrace tailWord_7226831 prefixEnd_7226831 3710837911812719724176915 := by
  unfold tailWord_7226831
  simp only [CollatzResearch.WordTrace]
  refine ⟨263584180881433006316688347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175722787254288670877792231 263584180881433006316688347)
  ·
    refine ⟨395376271322149509475032521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263584180881433006316688347 395376271322149509475032521)
    ·
      refine ⟨296532203491612132106274391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395376271322149509475032521 296532203491612132106274391)
      ·
        refine ⟨444798305237418198159411587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296532203491612132106274391 444798305237418198159411587)
        ·
          refine ⟨667197457856127297239117381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444798305237418198159411587 667197457856127297239117381)
          ·
            refine ⟨125099523348023868232334509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 667197457856127297239117381 125099523348023868232334509)
            ·
              refine ⟨46912321255508950587125441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125099523348023868232334509 46912321255508950587125441)
              ·
                refine ⟨35184240941631712940344081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46912321255508950587125441 35184240941631712940344081)
                ·
                  refine ⟨26388180706223784705258061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35184240941631712940344081 26388180706223784705258061)
                  ·
                    refine ⟨9895567764833919264471773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26388180706223784705258061 9895567764833919264471773)
                    ·
                      refine ⟨3710837911812719724176915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9895567764833919264471773 3710837911812719724176915)
                      ·
                        rfl

theorem cell23_7226831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 3, 3].length) (baseStart_7226831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226831 prefixEnd_7226831 := by exact prefixLift 7226831
  have htrace : WordTrace (prefixWord ++ tailWord_7226831) baseStart_7226831 baseEnd_7226831 := by
    simpa [prefixWord, tailWord_7226831, baseEnd_7226831] using wordTrace_append hprefix tailTrace_7226831
  have hstable : (prefixWord ++ tailWord_7226831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226831).length < 2 ^ (prefixWord ++ tailWord_7226831).sum := by decide
  have hdescent : baseEnd_7226831 < baseStart_7226831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226838 : List Nat := [5, 2, 1, 1, 1, 2, 1, 3, 7]
def baseStart_7226838 : Nat := 118140960795 + 7226838 * 2 ^ 59
def prefixEnd_7226838 : Nat := 4983230072969 + 3 ^ 40 * 7226838 * 2
def baseEnd_7226838 : Nat := 412315722908589021865487

theorem tailTrace_7226838 : CollatzResearch.WordTrace tailWord_7226838 prefixEnd_7226838 412315722908589021865487 := by
  unfold tailWord_7226838
  simp only [CollatzResearch.WordTrace]
  refine ⟨16474027262025477907012073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175722957461605097674795445 16474027262025477907012073)
  ·
    refine ⟨12355520446519108430259055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16474027262025477907012073 12355520446519108430259055)
    ·
      refine ⟨18533280669778662645388583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12355520446519108430259055 18533280669778662645388583)
      ·
        refine ⟨27799921004667993968082875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18533280669778662645388583 27799921004667993968082875)
        ·
          refine ⟨41699881507001990952124313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27799921004667993968082875 41699881507001990952124313)
          ·
            refine ⟨31274911130251493214093235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41699881507001990952124313 31274911130251493214093235)
            ·
              refine ⟨46912366695377239821139853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31274911130251493214093235 46912366695377239821139853)
              ·
                refine ⟨17592137510766464932927445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46912366695377239821139853 17592137510766464932927445)
                ·
                  refine ⟨412315722908589021865487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17592137510766464932927445 412315722908589021865487)
                  ·
                    rfl

theorem cell23_7226838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_7226838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226838 prefixEnd_7226838 := by exact prefixLift 7226838
  have htrace : WordTrace (prefixWord ++ tailWord_7226838) baseStart_7226838 baseEnd_7226838 := by
    simpa [prefixWord, tailWord_7226838, baseEnd_7226838] using wordTrace_append hprefix tailTrace_7226838
  have hstable : (prefixWord ++ tailWord_7226838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226838).length < 2 ^ (prefixWord ++ tailWord_7226838).sum := by decide
  have hdescent : baseEnd_7226838 < baseStart_7226838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226851 : List Nat := [1, 1, 1, 6, 2, 1, 1, 2, 1, 7]
def baseStart_7226851 : Nat := 118140960795 + 7226851 * 2 ^ 59
def prefixEnd_7226851 : Nat := 4983230072969 + 3 ^ 40 * 7226851 * 2
def baseEnd_7226851 : Nat := 1236949393808603215308941

theorem tailTrace_7226851 : CollatzResearch.WordTrace tailWord_7226851 prefixEnd_7226851 1236949393808603215308941 := by
  unfold tailWord_7226851
  simp only [CollatzResearch.WordTrace]
  refine ⟨263584910341360549732416407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175723273560907033154944271 263584910341360549732416407)
  ·
    refine ⟨395377365512040824598624611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263584910341360549732416407 395377365512040824598624611)
    ·
      refine ⟨593066048268061236897936917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395377365512040824598624611 593066048268061236897936917)
      ·
        refine ⟨27799971012565370479590793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 593066048268061236897936917 27799971012565370479590793)
        ·
          refine ⟨20849978259424027859693095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27799971012565370479590793 20849978259424027859693095)
          ·
            refine ⟨31274967389136041789539643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20849978259424027859693095 31274967389136041789539643)
            ·
              refine ⟨46912451083704062684309465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31274967389136041789539643 46912451083704062684309465)
              ·
                refine ⟨35184338312778047013232099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46912451083704062684309465 35184338312778047013232099)
                ·
                  refine ⟨52776507469167070519848149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35184338312778047013232099 52776507469167070519848149)
                  ·
                    refine ⟨1236949393808603215308941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52776507469167070519848149 1236949393808603215308941)
                    ·
                      rfl

theorem cell23_7226851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 7].length) (baseStart_7226851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226851 prefixEnd_7226851 := by exact prefixLift 7226851
  have htrace : WordTrace (prefixWord ++ tailWord_7226851) baseStart_7226851 baseEnd_7226851 := by
    simpa [prefixWord, tailWord_7226851, baseEnd_7226851] using wordTrace_append hprefix tailTrace_7226851
  have hstable : (prefixWord ++ tailWord_7226851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226851).length < 2 ^ (prefixWord ++ tailWord_7226851).sum := by decide
  have hdescent : baseEnd_7226851 < baseStart_7226851 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226888 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 4, 4, 2]
def baseStart_7226888 : Nat := 118140960795 + 7226888 * 2 ^ 59
def prefixEnd_7226888 : Nat := 4983230072969 + 3 ^ 40 * 7226888 * 2
def baseEnd_7226888 : Nat := 3710867180210026001164153

theorem tailTrace_7226888 : CollatzResearch.WordTrace tailWord_7226888 prefixEnd_7226888 3710867180210026001164153 := by
  unfold tailWord_7226888
  simp only [CollatzResearch.WordTrace]
  refine ⟨131793129921113252525756659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175724173228151003367675545 131793129921113252525756659)
  ·
    refine ⟨197689694881669878788634989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131793129921113252525756659 197689694881669878788634989)
    ·
      refine ⟨74133635580626204545738121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197689694881669878788634989 74133635580626204545738121)
      ·
        refine ⟨55600226685469653409303591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74133635580626204545738121 55600226685469653409303591)
        ·
          refine ⟨83400340028204480113955387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55600226685469653409303591 83400340028204480113955387)
          ·
            refine ⟨125100510042306720170933081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83400340028204480113955387 125100510042306720170933081)
            ·
              refine ⟨93825382531730040128199811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125100510042306720170933081 93825382531730040128199811)
              ·
                refine ⟨140738073797595060192299717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93825382531730040128199811 140738073797595060192299717)
                ·
                  refine ⟨26388388837049073786056197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140738073797595060192299717 26388388837049073786056197)
                  ·
                    refine ⟨4947822906946701334885537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26388388837049073786056197 4947822906946701334885537)
                    ·
                      refine ⟨3710867180210026001164153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4947822906946701334885537 3710867180210026001164153)
                      ·
                        rfl

theorem cell23_7226888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_7226888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226888 prefixEnd_7226888 := by exact prefixLift 7226888
  have htrace : WordTrace (prefixWord ++ tailWord_7226888) baseStart_7226888 baseEnd_7226888 := by
    simpa [prefixWord, tailWord_7226888, baseEnd_7226888] using wordTrace_append hprefix tailTrace_7226888
  have hstable : (prefixWord ++ tailWord_7226888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226888).length < 2 ^ (prefixWord ++ tailWord_7226888).sum := by decide
  have hdescent : baseEnd_7226888 < baseStart_7226888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226908 : List Nat := [2, 2, 3, 1, 2, 1, 1, 2, 4, 2, 3]
def baseStart_7226908 : Nat := 118140960795 + 7226908 * 2 ^ 59
def prefixEnd_7226908 : Nat := 4983230072969 + 3 ^ 40 * 7226908 * 2
def baseEnd_7226908 : Nat := 3710877449823115922914061

theorem tailTrace_7226908 : CollatzResearch.WordTrace tailWord_7226908 prefixEnd_7226908 3710877449823115922914061 := by
  unfold tailWord_7226908
  simp only [CollatzResearch.WordTrace]
  refine ⟨131793494651077024233620689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175724659534769365644827585 131793494651077024233620689)
  ·
    refine ⟨98845120988307768175215517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131793494651077024233620689 98845120988307768175215517)
    ·
      refine ⟨37066920370615413065705819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98845120988307768175215517 37066920370615413065705819)
      ·
        refine ⟨55600380555923119598558729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37066920370615413065705819 55600380555923119598558729)
        ·
          refine ⟨41700285416942339698919047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55600380555923119598558729 41700285416942339698919047)
          ·
            refine ⟨62550428125413509548378571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41700285416942339698919047 62550428125413509548378571)
            ·
              refine ⟨93825642188120264322567857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62550428125413509548378571 93825642188120264322567857)
              ·
                refine ⟨70369231641090198241925893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93825642188120264322567857 70369231641090198241925893)
                ·
                  refine ⟨13194230932704412170361105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70369231641090198241925893 13194230932704412170361105)
                  ·
                    refine ⟨9895673199528309127770829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13194230932704412170361105 9895673199528309127770829)
                    ·
                      refine ⟨3710877449823115922914061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9895673199528309127770829 3710877449823115922914061)
                      ·
                        rfl

theorem cell23_7226908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_7226908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226908 prefixEnd_7226908 := by exact prefixLift 7226908
  have htrace : WordTrace (prefixWord ++ tailWord_7226908) baseStart_7226908 baseEnd_7226908 := by
    simpa [prefixWord, tailWord_7226908, baseEnd_7226908] using wordTrace_append hprefix tailTrace_7226908
  have hstable : (prefixWord ++ tailWord_7226908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226908).length < 2 ^ (prefixWord ++ tailWord_7226908).sum := by decide
  have hdescent : baseEnd_7226908 < baseStart_7226908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226972 : List Nat := [2, 2, 4, 1, 2, 2, 1, 2, 3, 1, 3]
def baseStart_7226972 : Nat := 118140960795 + 7226972 * 2 ^ 59
def prefixEnd_7226972 : Nat := 4983230072969 + 3 ^ 40 * 7226972 * 2
def baseEnd_7226972 : Nat := 3710910312585003672513767

theorem tailTrace_7226972 : CollatzResearch.WordTrace tailWord_7226972 prefixEnd_7226972 3710910312585003672513767 := by
  unfold tailWord_7226972
  simp only [CollatzResearch.WordTrace]
  refine ⟨131794661786961093698785585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175726215715948124931714113 131794661786961093698785585)
  ·
    refine ⟨98845996340220820274089189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131794661786961093698785585 98845996340220820274089189)
    ·
      refine ⟨18533624313791403801391723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98845996340220820274089189 18533624313791403801391723)
      ·
        refine ⟨27800436470687105702087585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18533624313791403801391723 27800436470687105702087585)
        ·
          refine ⟨20850327353015329276565689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27800436470687105702087585 20850327353015329276565689)
          ·
            refine ⟨15637745514761496957424267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20850327353015329276565689 15637745514761496957424267)
            ·
              refine ⟨23456618272142245436136401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15637745514761496957424267 23456618272142245436136401)
              ·
                refine ⟨17592463704106684077102301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23456618272142245436136401 17592463704106684077102301)
                ·
                  refine ⟨6597173889040006528913363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17592463704106684077102301 6597173889040006528913363)
                  ·
                    refine ⟨9895760833560009793370045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6597173889040006528913363 9895760833560009793370045)
                    ·
                      refine ⟨3710910312585003672513767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9895760833560009793370045 3710910312585003672513767)
                      ·
                        rfl

theorem cell23_7226972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_7226972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226972 prefixEnd_7226972 := by exact prefixLift 7226972
  have htrace : WordTrace (prefixWord ++ tailWord_7226972) baseStart_7226972 baseEnd_7226972 := by
    simpa [prefixWord, tailWord_7226972, baseEnd_7226972] using wordTrace_append hprefix tailTrace_7226972
  have hstable : (prefixWord ++ tailWord_7226972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226972).length < 2 ^ (prefixWord ++ tailWord_7226972).sum := by decide
  have hdescent : baseEnd_7226972 < baseStart_7226972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226988 : List Nat := [2, 2, 1, 1, 3, 1, 1, 4, 4, 4]
def baseStart_7226988 : Nat := 118140960795 + 7226988 * 2 ^ 59
def prefixEnd_7226988 : Nat := 4983230072969 + 3 ^ 40 * 7226988 * 2
def baseEnd_7226988 : Nat := 1236972842758491869971231

theorem tailTrace_7226988 : CollatzResearch.WordTrace tailWord_7226988 prefixEnd_7226988 1236972842758491869971231 := by
  unfold tailWord_7226988
  simp only [CollatzResearch.WordTrace]
  refine ⟨131794953570932111065076809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175726604761242814753435745 131794953570932111065076809)
  ·
    refine ⟨98846215178199083298807607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131794953570932111065076809 98846215178199083298807607)
    ·
      refine ⟨148269322767298624948211411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98846215178199083298807607 148269322767298624948211411)
      ·
        refine ⟨222403984150947937422317117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148269322767298624948211411 222403984150947937422317117)
        ·
          refine ⟨83401494056605476533368919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222403984150947937422317117 83401494056605476533368919)
          ·
            refine ⟨125102241084908214800053379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83401494056605476533368919 125102241084908214800053379)
            ·
              refine ⟨187653361627362322200080069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125102241084908214800053379 187653361627362322200080069)
              ·
                refine ⟨35185005305130435412515013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187653361627362322200080069 35185005305130435412515013)
                ·
                  refine ⟨6597188494711956639846565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35185005305130435412515013 6597188494711956639846565)
                  ·
                    refine ⟨1236972842758491869971231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6597188494711956639846565 1236972842758491869971231)
                    ·
                      rfl

theorem cell23_7226988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 4].length) (baseStart_7226988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226988 prefixEnd_7226988 := by exact prefixLift 7226988
  have htrace : WordTrace (prefixWord ++ tailWord_7226988) baseStart_7226988 baseEnd_7226988 := by
    simpa [prefixWord, tailWord_7226988, baseEnd_7226988] using wordTrace_append hprefix tailTrace_7226988
  have hstable : (prefixWord ++ tailWord_7226988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226988).length < 2 ^ (prefixWord ++ tailWord_7226988).sum := by decide
  have hdescent : baseEnd_7226988 < baseStart_7226988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226991 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 6]
def baseStart_7226991 : Nat := 118140960795 + 7226991 * 2 ^ 59
def prefixEnd_7226991 : Nat := 4983230072969 + 3 ^ 40 * 7226991 * 2
def baseEnd_7226991 : Nat := 3710920068717439098176179

theorem tailTrace_7226991 : CollatzResearch.WordTrace tailWord_7226991 prefixEnd_7226991 3710920068717439098176179 := by
  unfold tailWord_7226991
  simp only [CollatzResearch.WordTrace]
  refine ⟨263590016560853353642512827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175726677707235569095008551 263590016560853353642512827)
  ·
    refine ⟨395385024841280030463769241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263590016560853353642512827 395385024841280030463769241)
    ·
      refine ⟨296538768630960022847826931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395385024841280030463769241 296538768630960022847826931)
      ·
        refine ⟨444808152946440034271740397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296538768630960022847826931 444808152946440034271740397)
        ·
          refine ⟨166803057354915012851902649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 444808152946440034271740397 166803057354915012851902649)
          ·
            refine ⟨125102293016186259638926987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166803057354915012851902649 125102293016186259638926987)
            ·
              refine ⟨187653439524279389458390481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125102293016186259638926987 187653439524279389458390481)
              ·
                refine ⟨140740079643209542093792861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187653439524279389458390481 140740079643209542093792861)
                ·
                  refine ⟨52777529866203578285172323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140740079643209542093792861 52777529866203578285172323)
                  ·
                    refine ⟨79166294799305367427758485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52777529866203578285172323 79166294799305367427758485)
                    ·
                      refine ⟨3710920068717439098176179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79166294799305367427758485 3710920068717439098176179)
                      ·
                        rfl

theorem cell23_7226991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 6].length) (baseStart_7226991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226991 prefixEnd_7226991 := by exact prefixLift 7226991
  have htrace : WordTrace (prefixWord ++ tailWord_7226991) baseStart_7226991 baseEnd_7226991 := by
    simpa [prefixWord, tailWord_7226991, baseEnd_7226991] using wordTrace_append hprefix tailTrace_7226991
  have hstable : (prefixWord ++ tailWord_7226991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226991).length < 2 ^ (prefixWord ++ tailWord_7226991).sum := by decide
  have hdescent : baseEnd_7226991 < baseStart_7226991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7226992 : List Nat := [2, 1, 1, 1, 6, 3, 2, 1, 1, 5]
def baseStart_7226992 : Nat := 118140960795 + 7226992 * 2 ^ 59
def prefixEnd_7226992 : Nat := 4983230072969 + 3 ^ 40 * 7226992 * 2
def baseEnd_7226992 : Nat := 1236973527399364531421225

theorem tailTrace_7226992 : CollatzResearch.WordTrace tailWord_7226992 prefixEnd_7226992 1236973527399364531421225 := by
  unfold tailWord_7226992
  simp only [CollatzResearch.WordTrace]
  refine ⟨131795026516924865406649615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175726702022566487208866153 131795026516924865406649615)
  ·
    refine ⟨197692539775387298109974423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131795026516924865406649615 197692539775387298109974423)
    ·
      refine ⟨296538809663080947164961635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197692539775387298109974423 296538809663080947164961635)
      ·
        refine ⟨444808214494621420747442453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296538809663080947164961635 444808214494621420747442453)
        ·
          refine ⟨20850385054435379097536365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 444808214494621420747442453 20850385054435379097536365)
          ·
            refine ⟨7818894395413267161576137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20850385054435379097536365 7818894395413267161576137)
            ·
              refine ⟨5864170796559950371182103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7818894395413267161576137 5864170796559950371182103)
              ·
                refine ⟨8796256194839925556773155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5864170796559950371182103 8796256194839925556773155)
                ·
                  refine ⟨13194384292259888335159733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8796256194839925556773155 13194384292259888335159733)
                  ·
                    refine ⟨1236973527399364531421225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13194384292259888335159733 1236973527399364531421225)
                    ·
                      rfl

theorem cell23_7226992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 1, 5].length) (baseStart_7226992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7226992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7226992 prefixEnd_7226992 := by exact prefixLift 7226992
  have htrace : WordTrace (prefixWord ++ tailWord_7226992) baseStart_7226992 baseEnd_7226992 := by
    simpa [prefixWord, tailWord_7226992, baseEnd_7226992] using wordTrace_append hprefix tailTrace_7226992
  have hstable : (prefixWord ++ tailWord_7226992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7226992).length < 2 ^ (prefixWord ++ tailWord_7226992).sum := by decide
  have hdescent : baseEnd_7226992 < baseStart_7226992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7226992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227001 : List Nat := [1, 2, 1, 3, 3, 1, 12]
def baseStart_7227001 : Nat := 118140960795 + 7227001 * 2 ^ 59
def prefixEnd_7227001 : Nat := 4983230072969 + 3 ^ 40 * 7227001 * 2
def baseEnd_7227001 : Nat := 45813891401530667395693

theorem tailTrace_7227001 : CollatzResearch.WordTrace tailWord_7227001 prefixEnd_7227001 45813891401530667395693 := by
  unfold tailWord_7227001
  simp only [CollatzResearch.WordTrace]
  refine ⟨263590381290817125350376857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175726920860544750233584571 263590381290817125350376857)
  ·
    refine ⟨197692785968112844012782643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263590381290817125350376857 197692785968112844012782643)
    ·
      refine ⟨296539178952169266019173965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197692785968112844012782643 296539178952169266019173965)
      ·
        refine ⟨111202192107063474757190237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296539178952169266019173965 111202192107063474757190237)
        ·
          refine ⟨41700822040148803033946339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111202192107063474757190237 41700822040148803033946339)
          ·
            refine ⟨62551233060223204550919509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41700822040148803033946339 62551233060223204550919509)
            ·
              refine ⟨45813891401530667395693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 62551233060223204550919509 45813891401530667395693)
              ·
                rfl

theorem cell23_7227001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 12].length) (baseStart_7227001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227001 prefixEnd_7227001 := by exact prefixLift 7227001
  have htrace : WordTrace (prefixWord ++ tailWord_7227001) baseStart_7227001 baseEnd_7227001 := by
    simpa [prefixWord, tailWord_7227001, baseEnd_7227001] using wordTrace_append hprefix tailTrace_7227001
  have hstable : (prefixWord ++ tailWord_7227001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227001).length < 2 ^ (prefixWord ++ tailWord_7227001).sum := by decide
  have hdescent : baseEnd_7227001 < baseStart_7227001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227005 : List Nat := [1, 4, 1, 1, 4, 2, 1, 1, 4, 4]
def baseStart_7227005 : Nat := 118140960795 + 7227005 * 2 ^ 59
def prefixEnd_7227005 : Nat := 4983230072969 + 3 ^ 40 * 7227005 * 2
def baseEnd_7227005 : Nat := 1236975752482200681133705

theorem tailTrace_7227005 : CollatzResearch.WordTrace tailWord_7227005 prefixEnd_7227005 1236975752482200681133705 := by
  unfold tailWord_7227005
  simp only [CollatzResearch.WordTrace]
  refine ⟨263590527182802634033522469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175727018121868422689014979 263590527182802634033522469)
  ·
    refine ⟨49423223846775493881285463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263590527182802634033522469 49423223846775493881285463)
    ·
      refine ⟨74134835770163240821928195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49423223846775493881285463 74134835770163240821928195)
      ·
        refine ⟨111202253655244861232892293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74134835770163240821928195 111202253655244861232892293)
        ·
          refine ⟨20850422560358411481167305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111202253655244861232892293 20850422560358411481167305)
          ·
            refine ⟨15637816920268808610875479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20850422560358411481167305 15637816920268808610875479)
            ·
              refine ⟨23456725380403212916313219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15637816920268808610875479 23456725380403212916313219)
              ·
                refine ⟨35185088070604819374469829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23456725380403212916313219 35185088070604819374469829)
                ·
                  refine ⟨6597204013238403632713093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35185088070604819374469829 6597204013238403632713093)
                  ·
                    refine ⟨1236975752482200681133705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6597204013238403632713093 1236975752482200681133705)
                    ·
                      rfl

theorem cell23_7227005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_7227005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227005 prefixEnd_7227005 := by exact prefixLift 7227005
  have htrace : WordTrace (prefixWord ++ tailWord_7227005) baseStart_7227005 baseEnd_7227005 := by
    simpa [prefixWord, tailWord_7227005, baseEnd_7227005] using wordTrace_append hprefix tailTrace_7227005
  have hstable : (prefixWord ++ tailWord_7227005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227005).length < 2 ^ (prefixWord ++ tailWord_7227005).sum := by decide
  have hdescent : baseEnd_7227005 < baseStart_7227005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227011 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 7]
def baseStart_7227011 : Nat := 118140960795 + 7227011 * 2 ^ 59
def prefixEnd_7227011 : Nat := 4983230072969 + 3 ^ 40 * 7227011 * 2
def baseEnd_7227011 : Nat := 3710930338330529019926087

theorem tailTrace_7227011 : CollatzResearch.WordTrace tailWord_7227011 prefixEnd_7227011 3710930338330529019926087 := by
  unfold tailWord_7227011
  simp only [CollatzResearch.WordTrace]
  refine ⟨263590746020780897058240887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175727164013853931372160591 263590746020780897058240887)
  ·
    refine ⟨395386119031171345587361331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263590746020780897058240887 395386119031171345587361331)
    ·
      refine ⟨593079178546757018381041997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395386119031171345587361331 593079178546757018381041997)
      ·
        refine ⟨222404691955033881892890749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 593079178546757018381041997 222404691955033881892890749)
        ·
          refine ⟨83401759483137705709834031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222404691955033881892890749 83401759483137705709834031)
          ·
            refine ⟨125102639224706558564751047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83401759483137705709834031 125102639224706558564751047)
            ·
              refine ⟨187653958837059837847126571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125102639224706558564751047 187653958837059837847126571)
              ·
                refine ⟨281480938255589756770689857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187653958837059837847126571 281480938255589756770689857)
                ·
                  refine ⟨211110703691692317578017393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281480938255589756770689857 211110703691692317578017393)
                  ·
                    refine ⟨158333027768769238183513045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 211110703691692317578017393 158333027768769238183513045)
                    ·
                      refine ⟨3710930338330529019926087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 158333027768769238183513045 3710930338330529019926087)
                      ·
                        rfl

theorem cell23_7227011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_7227011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227011 prefixEnd_7227011 := by exact prefixLift 7227011
  have htrace : WordTrace (prefixWord ++ tailWord_7227011) baseStart_7227011 baseEnd_7227011 := by
    simpa [prefixWord, tailWord_7227011, baseEnd_7227011] using wordTrace_append hprefix tailTrace_7227011
  have hstable : (prefixWord ++ tailWord_7227011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227011).length < 2 ^ (prefixWord ++ tailWord_7227011).sum := by decide
  have hdescent : baseEnd_7227011 < baseStart_7227011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227032 : List Nat := [2, 1, 2, 4, 1, 3, 2, 2, 1, 2, 3]
def baseStart_7227032 : Nat := 118140960795 + 7227032 * 2 ^ 59
def prefixEnd_7227032 : Nat := 4983230072969 + 3 ^ 40 * 7227032 * 2
def baseEnd_7227032 : Nat := 3710941121424273437763491

theorem tailTrace_7227032 : CollatzResearch.WordTrace tailWord_7227032 prefixEnd_7227032 3710941121424273437763491 := by
  unfold tailWord_7227032
  simp only [CollatzResearch.WordTrace]
  refine ⟨131795755976852408822377675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175727674635803211763170233 131795755976852408822377675)
  ·
    refine ⟨197693633965278613233566513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131795755976852408822377675 197693633965278613233566513)
    ·
      refine ⟨148270225473958959925174885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197693633965278613233566513 148270225473958959925174885)
      ·
        refine ⟨27800667276367304985970291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148270225473958959925174885 27800667276367304985970291)
        ·
          refine ⟨41701000914550957478955437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27800667276367304985970291 41701000914550957478955437)
          ·
            refine ⟨15637875342956609054608289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41701000914550957478955437 15637875342956609054608289)
            ·
              refine ⟨11728406507217456790956217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15637875342956609054608289 11728406507217456790956217)
              ·
                refine ⟨8796304880413092593217163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11728406507217456790956217 8796304880413092593217163)
                ·
                  refine ⟨13194457320619638889825745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8796304880413092593217163 13194457320619638889825745)
                  ·
                    refine ⟨9895842990464729167369309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13194457320619638889825745 9895842990464729167369309)
                    ·
                      refine ⟨3710941121424273437763491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9895842990464729167369309 3710941121424273437763491)
                      ·
                        rfl

theorem cell23_7227032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_7227032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227032 prefixEnd_7227032 := by exact prefixLift 7227032
  have htrace : WordTrace (prefixWord ++ tailWord_7227032) baseStart_7227032 baseEnd_7227032 := by
    simpa [prefixWord, tailWord_7227032, baseEnd_7227032] using wordTrace_append hprefix tailTrace_7227032
  have hstable : (prefixWord ++ tailWord_7227032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227032).length < 2 ^ (prefixWord ++ tailWord_7227032).sum := by decide
  have hdescent : baseEnd_7227032 < baseStart_7227032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227045 : List Nat := [1, 3, 1, 2, 1, 2, 3, 2, 4, 1, 3]
def baseStart_7227045 : Nat := 118140960795 + 7227045 * 2 ^ 59
def prefixEnd_7227045 : Nat := 4983230072969 + 3 ^ 40 * 7227045 * 2
def baseEnd_7227045 : Nat := 3710947796672781886900931

theorem tailTrace_7227045 : CollatzResearch.WordTrace tailWord_7227045 prefixEnd_7227045 3710947796672781886900931 := by
  unfold tailWord_7227045
  simp only [CollatzResearch.WordTrace]
  refine ⟨263591986102657720864978589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175727990735105147243319059 263591986102657720864978589)
  ·
    refine ⟨98846994788496645324366971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263591986102657720864978589 98846994788496645324366971)
    ·
      refine ⟨148270492182744967986550457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98846994788496645324366971 148270492182744967986550457)
      ·
        refine ⟨111202869137058725989912843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148270492182744967986550457 111202869137058725989912843)
        ·
          refine ⟨166804303705588088984869265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111202869137058725989912843 166804303705588088984869265)
          ·
            refine ⟨125103227779191066738651949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166804303705588088984869265 125103227779191066738651949)
            ·
              refine ⟨46913710417196650026994481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125103227779191066738651949 46913710417196650026994481)
              ·
                refine ⟨35185282812897487520245861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46913710417196650026994481 35185282812897487520245861)
                ·
                  refine ⟨6597240527418278910046099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35185282812897487520245861 6597240527418278910046099)
                  ·
                    refine ⟨9895860791127418365069149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6597240527418278910046099 9895860791127418365069149)
                    ·
                      refine ⟨3710947796672781886900931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9895860791127418365069149 3710947796672781886900931)
                      ·
                        rfl

theorem cell23_7227045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 4, 1, 3].length) (baseStart_7227045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227045 prefixEnd_7227045 := by exact prefixLift 7227045
  have htrace : WordTrace (prefixWord ++ tailWord_7227045) baseStart_7227045 baseEnd_7227045 := by
    simpa [prefixWord, tailWord_7227045, baseEnd_7227045] using wordTrace_append hprefix tailTrace_7227045
  have hstable : (prefixWord ++ tailWord_7227045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227045).length < 2 ^ (prefixWord ++ tailWord_7227045).sum := by decide
  have hdescent : baseEnd_7227045 < baseStart_7227045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227088 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 3]
def baseStart_7227088 : Nat := 118140960795 + 7227088 * 2 ^ 59
def prefixEnd_7227088 : Nat := 4983230072969 + 3 ^ 40 * 7227088 * 2
def baseEnd_7227088 : Nat := 3710969876340925218663233

theorem tailTrace_7227088 : CollatzResearch.WordTrace tailWord_7227088 prefixEnd_7227088 3710969876340925218663233 := by
  unfold tailWord_7227088
  simp only [CollatzResearch.WordTrace]
  refine ⟨131796777220750969604396959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175729036294334626139195945 131796777220750969604396959)
  ·
    refine ⟨197695165831126454406595439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131796777220750969604396959 197695165831126454406595439)
    ·
      refine ⟨296542748746689681609893159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197695165831126454406595439 296542748746689681609893159)
      ·
        refine ⟨444814123120034522414839739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296542748746689681609893159 444814123120034522414839739)
        ·
          refine ⟨667221184680051783622259609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444814123120034522414839739 667221184680051783622259609)
          ·
            refine ⟨500415888510038837716694707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 667221184680051783622259609 500415888510038837716694707)
            ·
              refine ⟨750623832765058256575042061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500415888510038837716694707 750623832765058256575042061)
              ·
                refine ⟨281483937286896846215640773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 750623832765058256575042061 281483937286896846215640773)
                ·
                  refine ⟨52778238241293158665432645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 281483937286896846215640773 52778238241293158665432645)
                  ·
                    refine ⟨9895919670242467249768621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52778238241293158665432645 9895919670242467249768621)
                    ·
                      refine ⟨3710969876340925218663233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9895919670242467249768621 3710969876340925218663233)
                      ·
                        rfl

theorem cell23_7227088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 3].length) (baseStart_7227088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227088 prefixEnd_7227088 := by exact prefixLift 7227088
  have htrace : WordTrace (prefixWord ++ tailWord_7227088) baseStart_7227088 baseEnd_7227088 := by
    simpa [prefixWord, tailWord_7227088, baseEnd_7227088] using wordTrace_append hprefix tailTrace_7227088
  have hstable : (prefixWord ++ tailWord_7227088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227088).length < 2 ^ (prefixWord ++ tailWord_7227088).sum := by decide
  have hdescent : baseEnd_7227088 < baseStart_7227088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227089 : List Nat := [1, 2, 2, 1, 2, 6, 1, 2, 1, 3, 2]
def baseStart_7227089 : Nat := 118140960795 + 7227089 * 2 ^ 59
def prefixEnd_7227089 : Nat := 4983230072969 + 3 ^ 40 * 7227089 * 2
def baseEnd_7227089 : Nat := 3710970389821579714750729

theorem tailTrace_7227089 : CollatzResearch.WordTrace tailWord_7227089 prefixEnd_7227089 3710970389821579714750729 := by
  unfold tailWord_7227089
  simp only [CollatzResearch.WordTrace]
  refine ⟨263593590914498316379580321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175729060609665544253053547 263593590914498316379580321)
  ·
    refine ⟨197695193185873737284685241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263593590914498316379580321 197695193185873737284685241)
    ·
      refine ⟨148271394889405302963513931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197695193185873737284685241 148271394889405302963513931)
      ·
        refine ⟨222407092334107954445270897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148271394889405302963513931 222407092334107954445270897)
        ·
          refine ⟨166805319250580965833953173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222407092334107954445270897 166805319250580965833953173)
          ·
            refine ⟨7818999339870982773466555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 166805319250580965833953173 7818999339870982773466555)
            ·
              refine ⟨11728499009806474160199833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7818999339870982773466555 11728499009806474160199833)
              ·
                refine ⟨8796374257354855620149875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11728499009806474160199833 8796374257354855620149875)
                ·
                  refine ⟨13194561386032283430224813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8796374257354855620149875 13194561386032283430224813)
                  ·
                    refine ⟨4947960519762106286334305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13194561386032283430224813 4947960519762106286334305)
                    ·
                      refine ⟨3710970389821579714750729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4947960519762106286334305 3710970389821579714750729)
                      ·
                        rfl

theorem cell23_7227089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 3, 2].length) (baseStart_7227089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227089 prefixEnd_7227089 := by exact prefixLift 7227089
  have htrace : WordTrace (prefixWord ++ tailWord_7227089) baseStart_7227089 baseEnd_7227089 := by
    simpa [prefixWord, tailWord_7227089, baseEnd_7227089] using wordTrace_append hprefix tailTrace_7227089
  have hstable : (prefixWord ++ tailWord_7227089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227089).length < 2 ^ (prefixWord ++ tailWord_7227089).sum := by decide
  have hdescent : baseEnd_7227089 < baseStart_7227089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227119 : List Nat := [1, 1, 2, 1, 5, 1, 4, 2, 2, 2, 2]
def baseStart_7227119 : Nat := 118140960795 + 7227119 * 2 ^ 59
def prefixEnd_7227119 : Nat := 4983230072969 + 3 ^ 40 * 7227119 * 2
def baseEnd_7227119 : Nat := 3710985794241214597375591

theorem tailTrace_7227119 : CollatzResearch.WordTrace tailWord_7227119 prefixEnd_7227119 3710985794241214597375591 := by
  unfold tailWord_7227119
  simp only [CollatzResearch.WordTrace]
  refine ⟨263594685104389631503172411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175729790069593087668781607 263594685104389631503172411)
  ·
    refine ⟨395392027656584447254758617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263594685104389631503172411 395392027656584447254758617)
    ·
      refine ⟨296544020742438335441068963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395392027656584447254758617 296544020742438335441068963)
      ·
        refine ⟨444816031113657503161603445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296544020742438335441068963 444816031113657503161603445)
        ·
          refine ⟨41701502916905390921400323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 444816031113657503161603445 41701502916905390921400323)
          ·
            refine ⟨62552254375358086382100485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41701502916905390921400323 62552254375358086382100485)
            ·
              refine ⟨11728547695379641196643841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62552254375358086382100485 11728547695379641196643841)
              ·
                refine ⟨8796410771534730897482881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11728547695379641196643841 8796410771534730897482881)
                ·
                  refine ⟨6597308078651048173112161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8796410771534730897482881 6597308078651048173112161)
                  ·
                    refine ⟨4947981058988286129834121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6597308078651048173112161 4947981058988286129834121)
                    ·
                      refine ⟨3710985794241214597375591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4947981058988286129834121 3710985794241214597375591)
                      ·
                        rfl

theorem cell23_7227119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 2, 2, 2].length) (baseStart_7227119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227119 prefixEnd_7227119 := by exact prefixLift 7227119
  have htrace : WordTrace (prefixWord ++ tailWord_7227119) baseStart_7227119 baseEnd_7227119 := by
    simpa [prefixWord, tailWord_7227119, baseEnd_7227119] using wordTrace_append hprefix tailTrace_7227119
  have hstable : (prefixWord ++ tailWord_7227119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227119).length < 2 ^ (prefixWord ++ tailWord_7227119).sum := by decide
  have hdescent : baseEnd_7227119 < baseStart_7227119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227145 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 4, 5, 2]
def baseStart_7227145 : Nat := 118140960795 + 7227145 * 2 ^ 59
def prefixEnd_7227145 : Nat := 4983230072969 + 3 ^ 40 * 7227145 * 2
def baseEnd_7227145 : Nat := 3710999144738231495650471

theorem tailTrace_7227145 : CollatzResearch.WordTrace tailWord_7227145 prefixEnd_7227145 3710999144738231495650471 := by
  unfold tailWord_7227145
  simp only [CollatzResearch.WordTrace]
  refine ⟨263595633402295437943618889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175730422268196958629079259 263595633402295437943618889)
  ·
    refine ⟨197696725051721578457714167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263595633402295437943618889 197696725051721578457714167)
    ·
      refine ⟨296545087577582367686571251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197696725051721578457714167 296545087577582367686571251)
      ·
        refine ⟨444817631366373551529856877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296545087577582367686571251 444817631366373551529856877)
        ·
          refine ⟨166806611762390081823696329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 444817631366373551529856877 166806611762390081823696329)
          ·
            refine ⟨125104958821792561367772247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166806611762390081823696329 125104958821792561367772247)
            ·
              refine ⟨187657438232688842051658371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125104958821792561367772247 187657438232688842051658371)
              ·
                refine ⟨281486157349033263077487557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187657438232688842051658371 281486157349033263077487557)
                ·
                  refine ⟨52778654502943736827028917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 281486157349033263077487557 52778654502943736827028917)
                  ·
                    refine ⟨4947998859650975327533961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52778654502943736827028917 4947998859650975327533961)
                    ·
                      refine ⟨3710999144738231495650471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4947998859650975327533961 3710999144738231495650471)
                      ·
                        rfl

theorem cell23_7227145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 5, 2].length) (baseStart_7227145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227145 prefixEnd_7227145 := by exact prefixLift 7227145
  have htrace : WordTrace (prefixWord ++ tailWord_7227145) baseStart_7227145 baseEnd_7227145 := by
    simpa [prefixWord, tailWord_7227145, baseEnd_7227145] using wordTrace_append hprefix tailTrace_7227145
  have hstable : (prefixWord ++ tailWord_7227145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227145).length < 2 ^ (prefixWord ++ tailWord_7227145).sum := by decide
  have hdescent : baseEnd_7227145 < baseStart_7227145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227148 : List Nat := [2, 2, 1, 2, 2, 1, 2, 2, 1, 1, 7]
def baseStart_7227148 : Nat := 118140960795 + 7227148 * 2 ^ 59
def prefixEnd_7227148 : Nat := 4983230072969 + 3 ^ 40 * 7227148 * 2
def baseEnd_7227148 : Nat := 3711000685180194983912957

theorem tailTrace_7227148 : CollatzResearch.WordTrace tailWord_7227148 prefixEnd_7227148 3711000685180194983912957 := by
  unfold tailWord_7227148
  simp only [CollatzResearch.WordTrace]
  refine ⟨131797871410642284727989049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175730495214189712970652065 131797871410642284727989049)
  ·
    refine ⟨98848403557981713545991787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131797871410642284727989049 98848403557981713545991787)
    ·
      refine ⟨148272605336972570318987681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98848403557981713545991787 148272605336972570318987681)
      ·
        refine ⟨111204454002729427739240761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148272605336972570318987681 111204454002729427739240761)
        ·
          refine ⟨83403340502047070804430571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111204454002729427739240761 83403340502047070804430571)
          ·
            refine ⟨125105010753070606206645857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83403340502047070804430571 125105010753070606206645857)
            ·
              refine ⟨93828758064802954654984393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125105010753070606206645857 93828758064802954654984393)
              ·
                refine ⟨70371568548602215991238295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93828758064802954654984393 70371568548602215991238295)
                ·
                  refine ⟨105557352822903323986857443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70371568548602215991238295 105557352822903323986857443)
                  ·
                    refine ⟨158336029234354985980286165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105557352822903323986857443 158336029234354985980286165)
                    ·
                      refine ⟨3711000685180194983912957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 158336029234354985980286165 3711000685180194983912957)
                      ·
                        rfl

theorem cell23_7227148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_7227148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227148 prefixEnd_7227148 := by exact prefixLift 7227148
  have htrace : WordTrace (prefixWord ++ tailWord_7227148) baseStart_7227148 baseEnd_7227148 := by
    simpa [prefixWord, tailWord_7227148, baseEnd_7227148] using wordTrace_append hprefix tailTrace_7227148
  have hstable : (prefixWord ++ tailWord_7227148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227148).length < 2 ^ (prefixWord ++ tailWord_7227148).sum := by decide
  have hdescent : baseEnd_7227148 < baseStart_7227148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227192 : List Nat := [2, 1, 2, 1, 3, 3, 2, 1, 2, 4, 2]
def baseStart_7227192 : Nat := 118140960795 + 7227192 * 2 ^ 59
def prefixEnd_7227192 : Nat := 4983230072969 + 3 ^ 40 * 7227192 * 2
def baseEnd_7227192 : Nat := 3711023278328992811762755

theorem tailTrace_7227192 : CollatzResearch.WordTrace tailWord_7227192 prefixEnd_7227192 3711023278328992811762755 := by
  unfold tailWord_7227192
  simp only [CollatzResearch.WordTrace]
  refine ⟨131798673816562582485289915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175731565088750109980386553 131798673816562582485289915)
  ·
    refine ⟨197698010724843873727934873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131798673816562582485289915 197698010724843873727934873)
    ·
      refine ⟨148273508043632905295951155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197698010724843873727934873 148273508043632905295951155)
      ·
        refine ⟨222410262065449357943926733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148273508043632905295951155 222410262065449357943926733)
        ·
          refine ⟨83403848274543509228972525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222410262065449357943926733 83403848274543509228972525)
          ·
            refine ⟨31276443102953815960864697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83403848274543509228972525 31276443102953815960864697)
            ·
              refine ⟨23457332327215361970648523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31276443102953815960864697 23457332327215361970648523)
              ·
                refine ⟨35185998490823042955972785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23457332327215361970648523 35185998490823042955972785)
                ·
                  refine ⟨26389498868117282216979589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35185998490823042955972785 26389498868117282216979589)
                  ·
                    refine ⟨4948031037771990415683673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26389498868117282216979589 4948031037771990415683673)
                    ·
                      refine ⟨3711023278328992811762755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4948031037771990415683673 3711023278328992811762755)
                      ·
                        rfl

theorem cell23_7227192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 2, 4, 2].length) (baseStart_7227192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227192 prefixEnd_7227192 := by exact prefixLift 7227192
  have htrace : WordTrace (prefixWord ++ tailWord_7227192) baseStart_7227192 baseEnd_7227192 := by
    simpa [prefixWord, tailWord_7227192, baseEnd_7227192] using wordTrace_append hprefix tailTrace_7227192
  have hstable : (prefixWord ++ tailWord_7227192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227192).length < 2 ^ (prefixWord ++ tailWord_7227192).sum := by decide
  have hdescent : baseEnd_7227192 < baseStart_7227192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227236 : List Nat := [2, 3, 1, 1, 6, 1, 1, 1, 3, 4]
def baseStart_7227236 : Nat := 118140960795 + 7227236 * 2 ^ 59
def prefixEnd_7227236 : Nat := 4983230072969 + 3 ^ 40 * 7227236 * 2
def baseEnd_7227236 : Nat := 1237015290492596879870851

theorem tailTrace_7227236 : CollatzResearch.WordTrace tailWord_7227236 prefixEnd_7227236 1237015290492596879870851 := by
  unfold tailWord_7227236
  simp only [CollatzResearch.WordTrace]
  refine ⟨131799476222482880242590781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175732634963310506990121041 131799476222482880242590781)
  ·
    refine ⟨49424803583431080090971543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131799476222482880242590781 49424803583431080090971543)
    ·
      refine ⟨74137205375146620136457315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49424803583431080090971543 74137205375146620136457315)
      ·
        refine ⟨111205808062719930204685973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74137205375146620136457315 111205808062719930204685973)
        ·
          refine ⟨5212772252939996728344655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 111205808062719930204685973 5212772252939996728344655)
          ·
            refine ⟨7819158379409995092516983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5212772252939996728344655 7819158379409995092516983)
            ·
              refine ⟨11728737569114992638775475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7819158379409995092516983 11728737569114992638775475)
              ·
                refine ⟨17593106353672488958163213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11728737569114992638775475 17593106353672488958163213)
                ·
                  refine ⟨6597414882627183359311205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17593106353672488958163213 6597414882627183359311205)
                  ·
                    refine ⟨1237015290492596879870851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6597414882627183359311205 1237015290492596879870851)
                    ·
                      rfl

theorem cell23_7227236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 3, 4].length) (baseStart_7227236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227236 prefixEnd_7227236 := by exact prefixLift 7227236
  have htrace : WordTrace (prefixWord ++ tailWord_7227236) baseStart_7227236 baseEnd_7227236 := by
    simpa [prefixWord, tailWord_7227236, baseEnd_7227236] using wordTrace_append hprefix tailTrace_7227236
  have hstable : (prefixWord ++ tailWord_7227236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227236).length < 2 ^ (prefixWord ++ tailWord_7227236).sum := by decide
  have hdescent : baseEnd_7227236 < baseStart_7227236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227269 : List Nat := [1, 3, 1, 1, 3, 2, 4, 1, 2, 3, 2]
def baseStart_7227269 : Nat := 118140960795 + 7227269 * 2 ^ 59
def prefixEnd_7227269 : Nat := 4983230072969 + 3 ^ 40 * 7227269 * 2
def baseEnd_7227269 : Nat := 3711062816339389010499901

theorem tailTrace_7227269 : CollatzResearch.WordTrace tailWord_7227269 prefixEnd_7227269 3711062816339389010499901 := by
  unfold tailWord_7227269
  simp only [CollatzResearch.WordTrace]
  refine ⟨263600156053846207121132861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175733437369230804747421907 263600156053846207121132861)
  ·
    refine ⟨98850058520192327670424823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263600156053846207121132861 98850058520192327670424823)
    ·
      refine ⟨148275087780288491505637235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98850058520192327670424823 148275087780288491505637235)
      ·
        refine ⟨222412631670432737258455853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148275087780288491505637235 222412631670432737258455853)
        ·
          refine ⟨83404736876412276471920945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222412631670432737258455853 83404736876412276471920945)
          ·
            refine ⟨62553552657309207353940709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83404736876412276471920945 62553552657309207353940709)
            ·
              refine ⟨11728791123245476378863883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62553552657309207353940709 11728791123245476378863883)
              ·
                refine ⟨17593186684868214568295825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11728791123245476378863883 17593186684868214568295825)
                ·
                  refine ⟨13194890013651160926221869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17593186684868214568295825 13194890013651160926221869)
                  ·
                    refine ⟨4948083755119185347333201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13194890013651160926221869 4948083755119185347333201)
                    ·
                      refine ⟨3711062816339389010499901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4948083755119185347333201 3711062816339389010499901)
                      ·
                        rfl

theorem cell23_7227269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 3, 2].length) (baseStart_7227269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227269 prefixEnd_7227269 := by exact prefixLift 7227269
  have htrace : WordTrace (prefixWord ++ tailWord_7227269) baseStart_7227269 baseEnd_7227269 := by
    simpa [prefixWord, tailWord_7227269, baseEnd_7227269] using wordTrace_append hprefix tailTrace_7227269
  have hstable : (prefixWord ++ tailWord_7227269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227269).length < 2 ^ (prefixWord ++ tailWord_7227269).sum := by decide
  have hdescent : baseEnd_7227269 < baseStart_7227269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227293 : List Nat := [1, 4, 2, 1, 2, 2, 4, 2, 1, 1, 3]
def baseStart_7227293 : Nat := 118140960795 + 7227293 * 2 ^ 59
def prefixEnd_7227293 : Nat := 4983230072969 + 3 ^ 40 * 7227293 * 2
def baseEnd_7227293 : Nat := 3711075139875096916599791

theorem tailTrace_7227293 : CollatzResearch.WordTrace tailWord_7227293 prefixEnd_7227293 3711075139875096916599791 := by
  unfold tailWord_7227293
  simp only [CollatzResearch.WordTrace]
  refine ⟨263601031405759259220006533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175734020937172839480004355 263601031405759259220006533)
  ·
    refine ⟨49425193388579861103751225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263601031405759259220006533 49425193388579861103751225)
    ·
      refine ⟨37068895041434895827813419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49425193388579861103751225 37068895041434895827813419)
      ·
        refine ⟨55603342562152343741720129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37068895041434895827813419 55603342562152343741720129)
        ·
          refine ⟨41702506921614257806290097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55603342562152343741720129 41702506921614257806290097)
          ·
            refine ⟨31276880191210693354717573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41702506921614257806290097 31276880191210693354717573)
            ·
              refine ⟨5864415035852005004009545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31276880191210693354717573 5864415035852005004009545)
              ·
                refine ⟨4398311276889003753007159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5864415035852005004009545 4398311276889003753007159)
                ·
                  refine ⟨6597466915333505629510739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4398311276889003753007159 6597466915333505629510739)
                  ·
                    refine ⟨9896200373000258444266109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6597466915333505629510739 9896200373000258444266109)
                    ·
                      refine ⟨3711075139875096916599791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9896200373000258444266109 3711075139875096916599791)
                      ·
                        rfl

theorem cell23_7227293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_7227293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227293 prefixEnd_7227293 := by exact prefixLift 7227293
  have htrace : WordTrace (prefixWord ++ tailWord_7227293) baseStart_7227293 baseEnd_7227293 := by
    simpa [prefixWord, tailWord_7227293, baseEnd_7227293] using wordTrace_append hprefix tailTrace_7227293
  have hstable : (prefixWord ++ tailWord_7227293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227293).length < 2 ^ (prefixWord ++ tailWord_7227293).sum := by decide
  have hdescent : baseEnd_7227293 < baseStart_7227293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227299 : List Nat := [1, 1, 1, 4, 1, 2, 1, 5, 3, 2, 2]
def baseStart_7227299 : Nat := 118140960795 + 7227299 * 2 ^ 59
def prefixEnd_7227299 : Nat := 4983230072969 + 3 ^ 40 * 7227299 * 2
def baseEnd_7227299 : Nat := 3711078220759023893124763

theorem tailTrace_7227299 : CollatzResearch.WordTrace tailWord_7227299 prefixEnd_7227299 3711078220759023893124763 := by
  unfold tailWord_7227299
  simp only [CollatzResearch.WordTrace]
  refine ⟨263601250243737522244724951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175734166829158348163149967 263601250243737522244724951)
  ·
    refine ⟨395401875365606283367087427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263601250243737522244724951 395401875365606283367087427)
    ·
      refine ⟨593102813048409425050631141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395401875365606283367087427 593102813048409425050631141)
      ·
        refine ⟨111206777446576767196993339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 593102813048409425050631141 111206777446576767196993339)
        ·
          refine ⟨166810166169865150795490009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111206777446576767196993339 166810166169865150795490009)
          ·
            refine ⟨125107624627398863096617507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166810166169865150795490009 125107624627398863096617507)
            ·
              refine ⟨187661436941098294644926261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125107624627398863096617507 187661436941098294644926261)
              ·
                refine ⟨17593259713227965122961837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 187661436941098294644926261 17593259713227965122961837)
                ·
                  refine ⟨6597472392460486921110689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17593259713227965122961837 6597472392460486921110689)
                  ·
                    refine ⟨4948104294345365190833017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6597472392460486921110689 4948104294345365190833017)
                    ·
                      refine ⟨3711078220759023893124763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4948104294345365190833017 3711078220759023893124763)
                      ·
                        rfl

theorem cell23_7227299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 3, 2, 2].length) (baseStart_7227299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227299 prefixEnd_7227299 := by exact prefixLift 7227299
  have htrace : WordTrace (prefixWord ++ tailWord_7227299) baseStart_7227299 baseEnd_7227299 := by
    simpa [prefixWord, tailWord_7227299, baseEnd_7227299] using wordTrace_append hprefix tailTrace_7227299
  have hstable : (prefixWord ++ tailWord_7227299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227299).length < 2 ^ (prefixWord ++ tailWord_7227299).sum := by decide
  have hdescent : baseEnd_7227299 < baseStart_7227299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227310 : List Nat := [4, 1, 5, 1, 1, 1, 1, 2, 3, 1, 3]
def baseStart_7227310 : Nat := 118140960795 + 7227310 * 2 ^ 59
def prefixEnd_7227310 : Nat := 4983230072969 + 3 ^ 40 * 7227310 * 2
def baseEnd_7227310 : Nat := 3711083869046223350087213

theorem tailTrace_7227310 : CollatzResearch.WordTrace tailWord_7227310 prefixEnd_7227310 3711083869046223350087213 := by
  unfold tailWord_7227310
  simp only [CollatzResearch.WordTrace]
  refine ⟨32950206430837208890421923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175734434297798447415583589 32950206430837208890421923)
  ·
    refine ⟨49425309646255813335632885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32950206430837208890421923 49425309646255813335632885)
    ·
      refine ⟨4633622779336482500215583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49425309646255813335632885 4633622779336482500215583)
      ·
        refine ⟨6950434169004723750323375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4633622779336482500215583 6950434169004723750323375)
        ·
          refine ⟨10425651253507085625485063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6950434169004723750323375 10425651253507085625485063)
          ·
            refine ⟨15638476880260628438227595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10425651253507085625485063 15638476880260628438227595)
            ·
              refine ⟨23457715320390942657341393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15638476880260628438227595 23457715320390942657341393)
              ·
                refine ⟨17593286490293206993006045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23457715320390942657341393 17593286490293206993006045)
                ·
                  refine ⟨6597482433859952622377267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17593286490293206993006045 6597482433859952622377267)
                  ·
                    refine ⟨9896223650789928933565901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6597482433859952622377267 9896223650789928933565901)
                    ·
                      refine ⟨3711083869046223350087213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9896223650789928933565901 3711083869046223350087213)
                      ·
                        rfl

theorem cell23_7227310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_7227310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227310 prefixEnd_7227310 := by exact prefixLift 7227310
  have htrace : WordTrace (prefixWord ++ tailWord_7227310) baseStart_7227310 baseEnd_7227310 := by
    simpa [prefixWord, tailWord_7227310, baseEnd_7227310] using wordTrace_append hprefix tailTrace_7227310
  have hstable : (prefixWord ++ tailWord_7227310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227310).length < 2 ^ (prefixWord ++ tailWord_7227310).sum := by decide
  have hdescent : baseEnd_7227310 < baseStart_7227310 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227336 : List Nat := [2, 1, 3, 1, 4, 1, 4, 1, 1, 2, 3]
def baseStart_7227336 : Nat := 118140960795 + 7227336 * 2 ^ 59
def prefixEnd_7227336 : Nat := 4983230072969 + 3 ^ 40 * 7227336 * 2
def baseEnd_7227336 : Nat := 3711097219543240248362093

theorem tailTrace_7227336 : CollatzResearch.WordTrace tailWord_7227336 prefixEnd_7227336 3711097219543240248362093 := by
  unfold tailWord_7227336
  simp only [CollatzResearch.WordTrace]
  refine ⟨131801299872301738781910931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175735066496402318375881241 131801299872301738781910931)
  ·
    refine ⟨197701949808452608172866397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131801299872301738781910931 197701949808452608172866397)
    ·
      refine ⟨74138231178169728064824899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197701949808452608172866397 74138231178169728064824899)
      ·
        refine ⟨111207346767254592097237349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74138231178169728064824899 111207346767254592097237349)
        ·
          refine ⟨20851377518860236018232003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111207346767254592097237349 20851377518860236018232003)
          ·
            refine ⟨31277066278290354027348005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20851377518860236018232003 31277066278290354027348005)
            ·
              refine ⟨5864449927179441380127751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31277066278290354027348005 5864449927179441380127751)
              ·
                refine ⟨8796674890769162070191627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5864449927179441380127751 8796674890769162070191627)
                ·
                  refine ⟨13195012336153743105287441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8796674890769162070191627 13195012336153743105287441)
                  ·
                    refine ⟨9896259252115307328965581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13195012336153743105287441 9896259252115307328965581)
                    ·
                      refine ⟨3711097219543240248362093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9896259252115307328965581 3711097219543240248362093)
                      ·
                        rfl

theorem cell23_7227336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 1, 2, 3].length) (baseStart_7227336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227336 prefixEnd_7227336 := by exact prefixLift 7227336
  have htrace : WordTrace (prefixWord ++ tailWord_7227336) baseStart_7227336 baseEnd_7227336 := by
    simpa [prefixWord, tailWord_7227336, baseEnd_7227336] using wordTrace_append hprefix tailTrace_7227336
  have hstable : (prefixWord ++ tailWord_7227336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227336).length < 2 ^ (prefixWord ++ tailWord_7227336).sum := by decide
  have hdescent : baseEnd_7227336 < baseStart_7227336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227345 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 4, 2, 5]
def baseStart_7227345 : Nat := 118140960795 + 7227345 * 2 ^ 59
def prefixEnd_7227345 : Nat := 4983230072969 + 3 ^ 40 * 7227345 * 2
def baseEnd_7227345 : Nat := 3711101840869130713149551

theorem tailTrace_7227345 : CollatzResearch.WordTrace tailWord_7227345 prefixEnd_7227345 3711101840869130713149551 := by
  unfold tailWord_7227345
  simp only [CollatzResearch.WordTrace]
  refine ⟨263602928001570872100899489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175735285334380581400599659 263602928001570872100899489)
  ·
    refine ⟨197702196001178154075674617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263602928001570872100899489 197702196001178154075674617)
    ·
      refine ⟨148276647000883615556755963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197702196001178154075674617 148276647000883615556755963)
      ·
        refine ⟨222414970501325423335133945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148276647000883615556755963 222414970501325423335133945)
        ·
          refine ⟨166811227875994067501350459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222414970501325423335133945 166811227875994067501350459)
          ·
            refine ⟨250216841813991101252025689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166811227875994067501350459 250216841813991101252025689)
            ·
              refine ⟨187662631360493325939019267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250216841813991101252025689 187662631360493325939019267)
              ·
                refine ⟨281493947040739988908528901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187662631360493325939019267 281493947040739988908528901)
                ·
                  refine ⟨52780115070138747920349169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 281493947040739988908528901 52780115070138747920349169)
                  ·
                    refine ⟨39585086302604060940261877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52780115070138747920349169 39585086302604060940261877)
                    ·
                      refine ⟨3711101840869130713149551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39585086302604060940261877 3711101840869130713149551)
                      ·
                        rfl

theorem cell23_7227345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_7227345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227345 prefixEnd_7227345 := by exact prefixLift 7227345
  have htrace : WordTrace (prefixWord ++ tailWord_7227345) baseStart_7227345 baseEnd_7227345 := by
    simpa [prefixWord, tailWord_7227345, baseEnd_7227345] using wordTrace_append hprefix tailTrace_7227345
  have hstable : (prefixWord ++ tailWord_7227345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227345).length < 2 ^ (prefixWord ++ tailWord_7227345).sum := by decide
  have hdescent : baseEnd_7227345 < baseStart_7227345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227350 : List Nat := [5, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2]
def baseStart_7227350 : Nat := 118140960795 + 7227350 * 2 ^ 59
def prefixEnd_7227350 : Nat := 4983230072969 + 3 ^ 40 * 7227350 * 2
def baseEnd_7227350 : Nat := 3711104408272403193587029

theorem tailTrace_7227350 : CollatzResearch.WordTrace tailWord_7227350 prefixEnd_7227350 3711104408272403193587029 := by
  unfold tailWord_7227350
  simp only [CollatzResearch.WordTrace]
  refine ⟨16475194397909547372176969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175735406911035171969887669 16475194397909547372176969)
  ·
    refine ⟨12356395798432160529132727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16475194397909547372176969 12356395798432160529132727)
    ·
      refine ⟨18534593697648240793699091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12356395798432160529132727 18534593697648240793699091)
      ·
        refine ⟨27801890546472361190548637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18534593697648240793699091 27801890546472361190548637)
        ·
          refine ⟨10425708954927135446455739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27801890546472361190548637 10425708954927135446455739)
          ·
            refine ⟨15638563432390703169683609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10425708954927135446455739 15638563432390703169683609)
            ·
              refine ⟨11728922574293027377262707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15638563432390703169683609 11728922574293027377262707)
              ·
                refine ⟨17593383861439541065894061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11728922574293027377262707 17593383861439541065894061)
                ·
                  refine ⟨6597518948039827899710273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17593383861439541065894061 6597518948039827899710273)
                  ·
                    refine ⟨4948139211029870924782705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6597518948039827899710273 4948139211029870924782705)
                    ·
                      refine ⟨3711104408272403193587029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4948139211029870924782705 3711104408272403193587029)
                      ·
                        rfl

theorem cell23_7227350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_7227350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227350 prefixEnd_7227350 := by exact prefixLift 7227350
  have htrace : WordTrace (prefixWord ++ tailWord_7227350) baseStart_7227350 baseEnd_7227350 := by
    simpa [prefixWord, tailWord_7227350, baseEnd_7227350] using wordTrace_append hprefix tailTrace_7227350
  have hstable : (prefixWord ++ tailWord_7227350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227350).length < 2 ^ (prefixWord ++ tailWord_7227350).sum := by decide
  have hdescent : baseEnd_7227350 < baseStart_7227350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227373 : List Nat := [1, 5, 1, 4, 2, 1, 2, 7]
def baseStart_7227373 : Nat := 118140960795 + 7227373 * 2 ^ 59
def prefixEnd_7227373 : Nat := 4983230072969 + 3 ^ 40 * 7227373 * 2
def baseEnd_7227373 : Nat := 137448748826942837170349

theorem tailTrace_7227373 : CollatzResearch.WordTrace tailWord_7227373 prefixEnd_7227373 137448748826942837170349 := by
  unfold tailWord_7227373
  simp only [CollatzResearch.WordTrace]
  refine ⟨263603949245469432882918773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175735966163646288588612515 263603949245469432882918773)
  ·
    refine ⟨24712870241762759332773635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 263603949245469432882918773 24712870241762759332773635)
    ·
      refine ⟨37069305362644138999160453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24712870241762759332773635 37069305362644138999160453)
      ·
        refine ⟨6950494755495776062342585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37069305362644138999160453 6950494755495776062342585)
        ·
          refine ⟨5212871066621832046756939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6950494755495776062342585 5212871066621832046756939)
          ·
            refine ⟨7819306599932748070135409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5212871066621832046756939 7819306599932748070135409)
            ·
              refine ⟨5864479949949561052601557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7819306599932748070135409 5864479949949561052601557)
              ·
                refine ⟨137448748826942837170349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5864479949949561052601557 137448748826942837170349)
                ·
                  rfl

theorem cell23_7227373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 7].length) (baseStart_7227373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227373 prefixEnd_7227373 := by exact prefixLift 7227373
  have htrace : WordTrace (prefixWord ++ tailWord_7227373) baseStart_7227373 baseEnd_7227373 := by
    simpa [prefixWord, tailWord_7227373, baseEnd_7227373] using wordTrace_append hprefix tailTrace_7227373
  have hstable : (prefixWord ++ tailWord_7227373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227373).length < 2 ^ (prefixWord ++ tailWord_7227373).sum := by decide
  have hdescent : baseEnd_7227373 < baseStart_7227373 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227389 : List Nat := [1, 4, 1, 1, 1, 2, 2, 4, 1, 4, 2]
def baseStart_7227389 : Nat := 118140960795 + 7227389 * 2 ^ 59
def prefixEnd_7227389 : Nat := 4983230072969 + 3 ^ 40 * 7227389 * 2
def baseEnd_7227389 : Nat := 3711124434017928540999349

theorem tailTrace_7227389 : CollatzResearch.WordTrace tailWord_7227389 prefixEnd_7227389 3711124434017928540999349 := by
  unfold tailWord_7227389
  simp only [CollatzResearch.WordTrace]
  refine ⟨263604532813411467615501221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175736355208940978410334147 263604532813411467615501221)
  ·
    refine ⟨49425849902514650177906479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263604532813411467615501221 49425849902514650177906479)
    ·
      refine ⟨74138774853771975266859719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49425849902514650177906479 74138774853771975266859719)
      ·
        refine ⟨111208162280657962900289579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74138774853771975266859719 111208162280657962900289579)
        ·
          refine ⟨166812243420986944350434369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111208162280657962900289579 166812243420986944350434369)
          ·
            refine ⟨125109182565740208262825777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166812243420986944350434369 125109182565740208262825777)
            ·
              refine ⟨93831886924305156197119333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125109182565740208262825777 93831886924305156197119333)
              ·
                refine ⟨17593478798307216786959875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93831886924305156197119333 17593478798307216786959875)
                ·
                  refine ⟨26390218197460825180439813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17593478798307216786959875 26390218197460825180439813)
                  ·
                    refine ⟨4948165912023904721332465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26390218197460825180439813 4948165912023904721332465)
                    ·
                      refine ⟨3711124434017928540999349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4948165912023904721332465 3711124434017928540999349)
                      ·
                        rfl

theorem cell23_7227389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 4, 2].length) (baseStart_7227389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227389 prefixEnd_7227389 := by exact prefixLift 7227389
  have htrace : WordTrace (prefixWord ++ tailWord_7227389) baseStart_7227389 baseEnd_7227389 := by
    simpa [prefixWord, tailWord_7227389, baseEnd_7227389] using wordTrace_append hprefix tailTrace_7227389
  have hstable : (prefixWord ++ tailWord_7227389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227389).length < 2 ^ (prefixWord ++ tailWord_7227389).sum := by decide
  have hdescent : baseEnd_7227389 < baseStart_7227389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227395 : List Nat := [1, 1, 1, 3, 2, 1, 1, 4, 9]
def baseStart_7227395 : Nat := 118140960795 + 7227395 * 2 ^ 59
def prefixEnd_7227395 : Nat := 4983230072969 + 3 ^ 40 * 7227395 * 2
def baseEnd_7227395 : Nat := 412347501655761724169369

theorem tailTrace_7227395 : CollatzResearch.WordTrace tailWord_7227395 prefixEnd_7227395 412347501655761724169369 := by
  unfold tailWord_7227395
  simp only [CollatzResearch.WordTrace]
  refine ⟨263604751651389730640219639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175736501100926487093479759 263604751651389730640219639)
  ·
    refine ⟨395407127477084595960329459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263604751651389730640219639 395407127477084595960329459)
    ·
      refine ⟨593110691215626893940494189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395407127477084595960329459 593110691215626893940494189)
      ·
        refine ⟨222416509205860085227685321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 593110691215626893940494189 222416509205860085227685321)
        ·
          refine ⟨166812381904395063920763991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222416509205860085227685321 166812381904395063920763991)
          ·
            refine ⟨250218572856592595881145987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166812381904395063920763991 250218572856592595881145987)
            ·
              refine ⟨375327859284888893821718981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250218572856592595881145987 375327859284888893821718981)
              ·
                refine ⟨70373973615916667591572309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 375327859284888893821718981 70373973615916667591572309)
                ·
                  refine ⟨412347501655761724169369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 70373973615916667591572309 412347501655761724169369)
                  ·
                    rfl

theorem cell23_7227395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 9].length) (baseStart_7227395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227395 prefixEnd_7227395 := by exact prefixLift 7227395
  have htrace : WordTrace (prefixWord ++ tailWord_7227395) baseStart_7227395 baseEnd_7227395 := by
    simpa [prefixWord, tailWord_7227395, baseEnd_7227395] using wordTrace_append hprefix tailTrace_7227395
  have hstable : (prefixWord ++ tailWord_7227395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227395).length < 2 ^ (prefixWord ++ tailWord_7227395).sum := by decide
  have hdescent : baseEnd_7227395 < baseStart_7227395 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227406 : List Nat := [4, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2]
def baseStart_7227406 : Nat := 118140960795 + 7227406 * 2 ^ 59
def prefixEnd_7227406 : Nat := 4983230072969 + 3 ^ 40 * 7227406 * 2
def baseEnd_7227406 : Nat := 3711133163189054974486771

theorem tailTrace_7227406 : CollatzResearch.WordTrace tailWord_7227406 prefixEnd_7227406 3711133163189054974486771 := by
  unfold tailWord_7227406
  simp only [CollatzResearch.WordTrace]
  refine ⟨32950644106793734939858759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175736768569566586345913381 32950644106793734939858759)
  ·
    refine ⟨49425966160190602409788139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32950644106793734939858759 49425966160190602409788139)
    ·
      refine ⟨74138949240285903614682209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49425966160190602409788139 74138949240285903614682209)
      ·
        refine ⟨55604211930214427711011657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74138949240285903614682209 55604211930214427711011657)
        ·
          refine ⟨41703158947660820783258743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55604211930214427711011657 41703158947660820783258743)
          ·
            refine ⟨62554738421491231174888115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41703158947660820783258743 62554738421491231174888115)
            ·
              refine ⟨93832107632236846762332173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62554738421491231174888115 93832107632236846762332173)
              ·
                refine ⟨35187040362088817535874565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93832107632236846762332173 35187040362088817535874565)
                ·
                  refine ⟨6597570067891653287976481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35187040362088817535874565 6597570067891653287976481)
                  ·
                    refine ⟨4948177550918739965982361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6597570067891653287976481 4948177550918739965982361)
                    ·
                      refine ⟨3711133163189054974486771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4948177550918739965982361 3711133163189054974486771)
                      ·
                        rfl

theorem cell23_7227406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_7227406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227406 prefixEnd_7227406 := by exact prefixLift 7227406
  have htrace : WordTrace (prefixWord ++ tailWord_7227406) baseStart_7227406 baseEnd_7227406 := by
    simpa [prefixWord, tailWord_7227406, baseEnd_7227406] using wordTrace_append hprefix tailTrace_7227406
  have hstable : (prefixWord ++ tailWord_7227406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227406).length < 2 ^ (prefixWord ++ tailWord_7227406).sum := by decide
  have hdescent : baseEnd_7227406 < baseStart_7227406 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227446 : List Nat := [5, 1, 2, 1, 1, 1, 2, 5, 5]
def baseStart_7227446 : Nat := 118140960795 + 7227446 * 2 ^ 59
def prefixEnd_7227446 : Nat := 4983230072969 + 3 ^ 40 * 7227446 * 2
def baseEnd_7227446 : Nat := 412350411379470535331843

theorem tailTrace_7227446 : CollatzResearch.WordTrace tailWord_7227446 prefixEnd_7227446 412350411379470535331843 := by
  unfold tailWord_7227446
  simp only [CollatzResearch.WordTrace]
  refine ⟨16475413235887810396895387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175737741182803310900217461 16475413235887810396895387)
  ·
    refine ⟨24713119853831715595343081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16475413235887810396895387 24713119853831715595343081)
    ·
      refine ⟨18534839890373786696507311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24713119853831715595343081 18534839890373786696507311)
      ·
        refine ⟨27802259835560680044760967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18534839890373786696507311 27802259835560680044760967)
        ·
          refine ⟨41703389753341020067141451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27802259835560680044760967 41703389753341020067141451)
          ·
            refine ⟨62555084630011530100712177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41703389753341020067141451 62555084630011530100712177)
            ·
              refine ⟨46916313472508647575534133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62555084630011530100712177 46916313472508647575534133)
              ·
                refine ⟨4398404388047685710206325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46916313472508647575534133 4398404388047685710206325)
                ·
                  refine ⟨412350411379470535331843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4398404388047685710206325 412350411379470535331843)
                  ·
                    rfl

theorem cell23_7227446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_7227446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227446 prefixEnd_7227446 := by exact prefixLift 7227446
  have htrace : WordTrace (prefixWord ++ tailWord_7227446) baseStart_7227446 baseEnd_7227446 := by
    simpa [prefixWord, tailWord_7227446, baseEnd_7227446] using wordTrace_append hprefix tailTrace_7227446
  have hstable : (prefixWord ++ tailWord_7227446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227446).length < 2 ^ (prefixWord ++ tailWord_7227446).sum := by decide
  have hdescent : baseEnd_7227446 < baseStart_7227446 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227452 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 3, 2, 5]
def baseStart_7227452 : Nat := 118140960795 + 7227452 * 2 ^ 59
def prefixEnd_7227452 : Nat := 4983230072969 + 3 ^ 40 * 7227452 * 2
def baseEnd_7227452 : Nat := 3711156783299161794511559

theorem tailTrace_7227452 : CollatzResearch.WordTrace tailWord_7227452 prefixEnd_7227452 3711156783299161794511559 := by
  unfold tailWord_7227452
  simp only [CollatzResearch.WordTrace]
  refine ⟨131803415306091614687522305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175737887074788819583363073 131803415306091614687522305)
  ·
    refine ⟨98852561479568711015641729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131803415306091614687522305 98852561479568711015641729)
    ·
      refine ⟨74139421109676533261731297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98852561479568711015641729 74139421109676533261731297)
      ·
        refine ⟨55604565832257399946298473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74139421109676533261731297 55604565832257399946298473)
        ·
          refine ⟨41703424374193049959723855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55604565832257399946298473 41703424374193049959723855)
          ·
            refine ⟨62555136561289574939585783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41703424374193049959723855 62555136561289574939585783)
            ·
              refine ⟨93832704841934362409378675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62555136561289574939585783 93832704841934362409378675)
              ·
                refine ⟨140749057262901543614068013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93832704841934362409378675 140749057262901543614068013)
                ·
                  refine ⟨52780896473588078855275505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140749057262901543614068013 52780896473588078855275505)
                  ·
                    refine ⟨39585672355191059141456629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52780896473588078855275505 39585672355191059141456629)
                    ·
                      refine ⟨3711156783299161794511559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39585672355191059141456629 3711156783299161794511559)
                      ·
                        rfl

theorem cell23_7227452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_7227452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227452 prefixEnd_7227452 := by exact prefixLift 7227452
  have htrace : WordTrace (prefixWord ++ tailWord_7227452) baseStart_7227452 baseEnd_7227452 := by
    simpa [prefixWord, tailWord_7227452, baseEnd_7227452] using wordTrace_append hprefix tailTrace_7227452
  have hstable : (prefixWord ++ tailWord_7227452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227452).length < 2 ^ (prefixWord ++ tailWord_7227452).sum := by decide
  have hdescent : baseEnd_7227452 < baseStart_7227452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227469 : List Nat := [1, 6, 1, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_7227469 : Nat := 118140960795 + 7227469 * 2 ^ 59
def prefixEnd_7227469 : Nat := 4983230072969 + 3 ^ 40 * 7227469 * 2
def baseEnd_7227469 : Nat := 3711165512470288227998981

theorem tailTrace_7227469 : CollatzResearch.WordTrace tailWord_7227469 prefixEnd_7227469 3711165512470288227998981 := by
  unfold tailWord_7227469
  simp only [CollatzResearch.WordTrace]
  refine ⟨263607450653121641278413461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175738300435414427518942307 263607450653121641278413461)
  ·
    refine ⟨12356599249365076934925631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 263607450653121641278413461 12356599249365076934925631)
    ·
      refine ⟨18534898874047615402388447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12356599249365076934925631 18534898874047615402388447)
      ·
        refine ⟨27802348311071423103582671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18534898874047615402388447 27802348311071423103582671)
        ·
          refine ⟨41703522466607134655374007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27802348311071423103582671 41703522466607134655374007)
          ·
            refine ⟨62555283699910701983061011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41703522466607134655374007 62555283699910701983061011)
            ·
              refine ⟨93832925549866052974591517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62555283699910701983061011 93832925549866052974591517)
              ·
                refine ⟨35187347081199769865471819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93832925549866052974591517 35187347081199769865471819)
                ·
                  refine ⟨52781020621799654798207729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35187347081199769865471819 52781020621799654798207729)
                  ·
                    refine ⟨39585765466349741098655797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52781020621799654798207729 39585765466349741098655797)
                    ·
                      refine ⟨3711165512470288227998981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39585765466349741098655797 3711165512470288227998981)
                      ·
                        rfl

theorem cell23_7227469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_7227469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227469 prefixEnd_7227469 := by exact prefixLift 7227469
  have htrace : WordTrace (prefixWord ++ tailWord_7227469) baseStart_7227469 baseEnd_7227469 := by
    simpa [prefixWord, tailWord_7227469, baseEnd_7227469] using wordTrace_append hprefix tailTrace_7227469
  have hstable : (prefixWord ++ tailWord_7227469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227469).length < 2 ^ (prefixWord ++ tailWord_7227469).sum := by decide
  have hdescent : baseEnd_7227469 < baseStart_7227469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227479 : List Nat := [1, 1, 3, 2, 2, 1, 3, 1, 1, 6, 2]
def baseStart_7227479 : Nat := 118140960795 + 7227479 * 2 ^ 59
def prefixEnd_7227479 : Nat := 4983230072969 + 3 ^ 40 * 7227479 * 2
def baseEnd_7227479 : Nat := 3711170647276833188873935

theorem tailTrace_7227479 : CollatzResearch.WordTrace tailWord_7227479 prefixEnd_7227479 3711170647276833188873935 := by
  unfold tailWord_7227479
  simp only [CollatzResearch.WordTrace]
  refine ⟨263607815383085412986277491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175738543588723608657518327 263607815383085412986277491)
  ·
    refine ⟨395411723074628119479416237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263607815383085412986277491 395411723074628119479416237)
    ·
      refine ⟨148279396152985544804781089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 395411723074628119479416237 148279396152985544804781089)
      ·
        refine ⟨111209547114739158603585817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148279396152985544804781089 111209547114739158603585817)
        ·
          refine ⟨83407160336054368952689363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111209547114739158603585817 83407160336054368952689363)
          ·
            refine ⟨125110740504081553429034045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83407160336054368952689363 125110740504081553429034045)
            ·
              refine ⟨46916527689030582535887767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125110740504081553429034045 46916527689030582535887767)
              ·
                refine ⟨70374791533545873803831651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46916527689030582535887767 70374791533545873803831651)
                ·
                  refine ⟨105562187300318810705747477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70374791533545873803831651 105562187300318810705747477)
                  ·
                    refine ⟨4948227529702444251831913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 105562187300318810705747477 4948227529702444251831913)
                    ·
                      refine ⟨3711170647276833188873935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4948227529702444251831913 3711170647276833188873935)
                      ·
                        rfl

theorem cell23_7227479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 6, 2].length) (baseStart_7227479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227479 prefixEnd_7227479 := by exact prefixLift 7227479
  have htrace : WordTrace (prefixWord ++ tailWord_7227479) baseStart_7227479 baseEnd_7227479 := by
    simpa [prefixWord, tailWord_7227479, baseEnd_7227479] using wordTrace_append hprefix tailTrace_7227479
  have hstable : (prefixWord ++ tailWord_7227479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227479).length < 2 ^ (prefixWord ++ tailWord_7227479).sum := by decide
  have hdescent : baseEnd_7227479 < baseStart_7227479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227579 : List Nat := [1, 1, 1, 1, 1, 2, 5, 3, 4, 4]
def baseStart_7227579 : Nat := 118140960795 + 7227579 * 2 ^ 59
def prefixEnd_7227579 : Nat := 4983230072969 + 3 ^ 40 * 7227579 * 2
def baseEnd_7227579 : Nat := 1237073998447427599207825

theorem tailTrace_7227579 : CollatzResearch.WordTrace tailWord_7227579 prefixEnd_7227579 1237073998447427599207825 := by
  unfold tailWord_7227579
  simp only [CollatzResearch.WordTrace]
  refine ⟨263611462682723130064917791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175740975121815420043278527 263611462682723130064917791)
  ·
    refine ⟨395417194024084695097376687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263611462682723130064917791 395417194024084695097376687)
    ·
      refine ⟨593125791036127042646065031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395417194024084695097376687 593125791036127042646065031)
      ·
        refine ⟨889688686554190563969097547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593125791036127042646065031 889688686554190563969097547)
        ·
          refine ⟨1334533029831285845953646321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 889688686554190563969097547 1334533029831285845953646321)
          ·
            refine ⟨1000899772373464384465234741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1334533029831285845953646321 1000899772373464384465234741)
            ·
              refine ⟨93834353660012286043615757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1000899772373464384465234741 93834353660012286043615757)
              ·
                refine ⟨35187882622504607266355909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93834353660012286043615757 35187882622504607266355909)
                ·
                  refine ⟨6597727991719613862441733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35187882622504607266355909 6597727991719613862441733)
                  ·
                    refine ⟨1237073998447427599207825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6597727991719613862441733 1237073998447427599207825)
                    ·
                      rfl

theorem cell23_7227579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 4, 4].length) (baseStart_7227579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227579 prefixEnd_7227579 := by exact prefixLift 7227579
  have htrace : WordTrace (prefixWord ++ tailWord_7227579) baseStart_7227579 baseEnd_7227579 := by
    simpa [prefixWord, tailWord_7227579, baseEnd_7227579] using wordTrace_append hprefix tailTrace_7227579
  have hstable : (prefixWord ++ tailWord_7227579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227579).length < 2 ^ (prefixWord ++ tailWord_7227579).sum := by decide
  have hdescent : baseEnd_7227579 < baseStart_7227579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227580 : List Nat := [2, 2, 2, 3, 3, 2, 1, 1, 3, 1, 3]
def baseStart_7227580 : Nat := 118140960795 + 7227580 * 2 ^ 59
def prefixEnd_7227580 : Nat := 4983230072969 + 3 ^ 40 * 7227580 * 2
def baseEnd_7227580 : Nat := 3711222508822937293710971

theorem tailTrace_7227580 : CollatzResearch.WordTrace tailWord_7227580 prefixEnd_7227580 3711222508822937293710971 := by
  unfold tailWord_7227580
  simp only [CollatzResearch.WordTrace]
  refine ⟨131805749577859753617852097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175740999437146338157136129 131805749577859753617852097)
  ·
    refine ⟨98854312183394815213389073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131805749577859753617852097 98854312183394815213389073)
    ·
      refine ⟨74140734137546111410041805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98854312183394815213389073 74140734137546111410041805)
      ·
        refine ⟨27802775301579791778765677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74140734137546111410041805 27802775301579791778765677)
        ·
          refine ⟨10426040738092421917037129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27802775301579791778765677 10426040738092421917037129)
          ·
            refine ⟨7819530553569316437777847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10426040738092421917037129 7819530553569316437777847)
            ·
              refine ⟨11729295830353974656666771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7819530553569316437777847 11729295830353974656666771)
              ·
                refine ⟨17593943745530961985000157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11729295830353974656666771 17593943745530961985000157)
                ·
                  refine ⟨6597728904574110744375059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17593943745530961985000157 6597728904574110744375059)
                  ·
                    refine ⟨9896593356861166116562589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6597728904574110744375059 9896593356861166116562589)
                    ·
                      refine ⟨3711222508822937293710971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9896593356861166116562589 3711222508822937293710971)
                      ·
                        rfl

theorem cell23_7227580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_7227580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227580 prefixEnd_7227580 := by exact prefixLift 7227580
  have htrace : WordTrace (prefixWord ++ tailWord_7227580) baseStart_7227580 baseEnd_7227580 := by
    simpa [prefixWord, tailWord_7227580, baseEnd_7227580] using wordTrace_append hprefix tailTrace_7227580
  have hstable : (prefixWord ++ tailWord_7227580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227580).length < 2 ^ (prefixWord ++ tailWord_7227580).sum := by decide
  have hdescent : baseEnd_7227580 < baseStart_7227580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227589 : List Nat := [1, 3, 1, 1, 1, 1, 6, 2, 1, 1, 5]
def baseStart_7227589 : Nat := 118140960795 + 7227589 * 2 ^ 59
def prefixEnd_7227589 : Nat := 4983230072969 + 3 ^ 40 * 7227589 * 2
def baseEnd_7227589 : Nat := 3711227130148827758498429

theorem tailTrace_7227589 : CollatzResearch.WordTrace tailWord_7227589 prefixEnd_7227589 3711227130148827758498429 := by
  unfold tailWord_7227589
  simp only [CollatzResearch.WordTrace]
  refine ⟨263611827412686901772781821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175741218275124601181854547 263611827412686901772781821)
  ·
    refine ⟨98854435279757588164793183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263611827412686901772781821 98854435279757588164793183)
    ·
      refine ⟨148281652919636382247189775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98854435279757588164793183 148281652919636382247189775)
      ·
        refine ⟨222422479379454573370784663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148281652919636382247189775 222422479379454573370784663)
        ·
          refine ⟨333633719069181860056176995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222422479379454573370784663 333633719069181860056176995)
          ·
            refine ⟨500450578603772790084265493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333633719069181860056176995 500450578603772790084265493)
            ·
              refine ⟨23458620872051849535199945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 500450578603772790084265493 23458620872051849535199945)
              ·
                refine ⟨17593965654038887151399959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23458620872051849535199945 17593965654038887151399959)
                ·
                  refine ⟨26390948481058330727099939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17593965654038887151399959 26390948481058330727099939)
                  ·
                    refine ⟨39586422721587496090649909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26390948481058330727099939 39586422721587496090649909)
                    ·
                      refine ⟨3711227130148827758498429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39586422721587496090649909 3711227130148827758498429)
                      ·
                        rfl

theorem cell23_7227589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 1, 5].length) (baseStart_7227589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227589 prefixEnd_7227589 := by exact prefixLift 7227589
  have htrace : WordTrace (prefixWord ++ tailWord_7227589) baseStart_7227589 baseEnd_7227589 := by
    simpa [prefixWord, tailWord_7227589, baseEnd_7227589] using wordTrace_append hprefix tailTrace_7227589
  have hstable : (prefixWord ++ tailWord_7227589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227589).length < 2 ^ (prefixWord ++ tailWord_7227589).sum := by decide
  have hdescent : baseEnd_7227589 < baseStart_7227589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227599 : List Nat := [1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 4]
def baseStart_7227599 : Nat := 118140960795 + 7227599 * 2 ^ 59
def prefixEnd_7227599 : Nat := 4983230072969 + 3 ^ 40 * 7227599 * 2
def baseEnd_7227599 : Nat := 3711232264955372719373383

theorem tailTrace_7227599 : CollatzResearch.WordTrace tailWord_7227599 prefixEnd_7227599 3711232264955372719373383 := by
  unfold tailWord_7227599
  simp only [CollatzResearch.WordTrace]
  refine ⟨263612192142650673480645851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175741461428433782320430567 263612192142650673480645851)
  ·
    refine ⟨395418288213976010220968777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263612192142650673480645851 395418288213976010220968777)
    ·
      refine ⟨296563716160482007665726583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395418288213976010220968777 296563716160482007665726583)
      ·
        refine ⟨444845574240723011498589875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296563716160482007665726583 444845574240723011498589875)
        ·
          refine ⟨667268361361084517247884813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444845574240723011498589875 667268361361084517247884813)
          ·
            refine ⟨250225635510406693967956805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 667268361361084517247884813 250225635510406693967956805)
            ·
              refine ⟨46917306658201255118991901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 250225635510406693967956805 46917306658201255118991901)
              ·
                refine ⟨17593989996825470669621963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46917306658201255118991901 17593989996825470669621963)
                ·
                  refine ⟨26390984995238206004432945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17593989996825470669621963 26390984995238206004432945)
                  ·
                    refine ⟨19793238746428654503324709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26390984995238206004432945 19793238746428654503324709)
                    ·
                      refine ⟨3711232264955372719373383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19793238746428654503324709 3711232264955372719373383)
                      ·
                        rfl

theorem cell23_7227599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 4].length) (baseStart_7227599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227599 prefixEnd_7227599 := by exact prefixLift 7227599
  have htrace : WordTrace (prefixWord ++ tailWord_7227599) baseStart_7227599 baseEnd_7227599 := by
    simpa [prefixWord, tailWord_7227599, baseEnd_7227599] using wordTrace_append hprefix tailTrace_7227599
  have hstable : (prefixWord ++ tailWord_7227599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227599).length < 2 ^ (prefixWord ++ tailWord_7227599).sum := by decide
  have hdescent : baseEnd_7227599 < baseStart_7227599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227620 : List Nat := [2, 3, 1, 1, 1, 2, 1, 7, 1, 2, 2]
def baseStart_7227620 : Nat := 118140960795 + 7227620 * 2 ^ 59
def prefixEnd_7227620 : Nat := 4983230072969 + 3 ^ 40 * 7227620 * 2
def baseEnd_7227620 : Nat := 3711243048049117137210787

theorem tailTrace_7227620 : CollatzResearch.WordTrace tailWord_7227620 prefixEnd_7227620 3711243048049117137210787 := by
  unfold tailWord_7227620
  simp only [CollatzResearch.WordTrace]
  refine ⟨131806479037787297033580157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175741972050383062711440209 131806479037787297033580157)
  ·
    refine ⟨49427429639170236387592559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131806479037787297033580157 49427429639170236387592559)
    ·
      refine ⟨74141144458755354581388839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49427429639170236387592559 74141144458755354581388839)
      ·
        refine ⟨111211716688133031872083259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74141144458755354581388839 111211716688133031872083259)
        ·
          refine ⟨166817575032199547808124889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111211716688133031872083259 166817575032199547808124889)
          ·
            refine ⟨125113181274149660856093667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166817575032199547808124889 125113181274149660856093667)
            ·
              refine ⟨187669771911224491284140501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125113181274149660856093667 187669771911224491284140501)
              ·
                refine ⟨4398510279169324014472043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 187669771911224491284140501 4398510279169324014472043)
                ·
                  refine ⟨6597765418753986021708065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4398510279169324014472043 6597765418753986021708065)
                  ·
                    refine ⟨4948324064065489516281049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6597765418753986021708065 4948324064065489516281049)
                    ·
                      refine ⟨3711243048049117137210787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4948324064065489516281049 3711243048049117137210787)
                      ·
                        rfl

theorem cell23_7227620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 7, 1, 2, 2].length) (baseStart_7227620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227620 prefixEnd_7227620 := by exact prefixLift 7227620
  have htrace : WordTrace (prefixWord ++ tailWord_7227620) baseStart_7227620 baseEnd_7227620 := by
    simpa [prefixWord, tailWord_7227620, baseEnd_7227620] using wordTrace_append hprefix tailTrace_7227620
  have hstable : (prefixWord ++ tailWord_7227620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227620).length < 2 ^ (prefixWord ++ tailWord_7227620).sum := by decide
  have hdescent : baseEnd_7227620 < baseStart_7227620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227623 : List Nat := [1, 1, 5, 3, 1, 3, 1, 1, 1, 1, 5]
def baseStart_7227623 : Nat := 118140960795 + 7227623 * 2 ^ 59
def prefixEnd_7227623 : Nat := 4983230072969 + 3 ^ 40 * 7227623 * 2
def baseEnd_7227623 : Nat := 3711244588491080625473273

theorem tailTrace_7227623 : CollatzResearch.WordTrace tailWord_7227623 prefixEnd_7227623 3711244588491080625473273 := by
  unfold tailWord_7227623
  simp only [CollatzResearch.WordTrace]
  refine ⟨263613067494563725579519523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175742044996375817053013015 263613067494563725579519523)
  ·
    refine ⟨395419601241845588369279285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263613067494563725579519523 395419601241845588369279285)
    ·
      refine ⟨37070587616423023909619933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 395419601241845588369279285 37070587616423023909619933)
      ·
        refine ⟨13901470356158633966107475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37070587616423023909619933 13901470356158633966107475)
        ·
          refine ⟨20852205534237950949161213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13901470356158633966107475 20852205534237950949161213)
          ·
            refine ⟨7819577075339231605935455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20852205534237950949161213 7819577075339231605935455)
            ·
              refine ⟨11729365613008847408903183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7819577075339231605935455 11729365613008847408903183)
              ·
                refine ⟨17594048419513271113354775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11729365613008847408903183 17594048419513271113354775)
                ·
                  refine ⟨26391072629269906670032163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17594048419513271113354775 26391072629269906670032163)
                  ·
                    refine ⟨39586608943904860005048245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26391072629269906670032163 39586608943904860005048245)
                    ·
                      refine ⟨3711244588491080625473273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39586608943904860005048245 3711244588491080625473273)
                      ·
                        rfl

theorem cell23_7227623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_7227623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227623 prefixEnd_7227623 := by exact prefixLift 7227623
  have htrace : WordTrace (prefixWord ++ tailWord_7227623) baseStart_7227623 baseEnd_7227623 := by
    simpa [prefixWord, tailWord_7227623, baseEnd_7227623] using wordTrace_append hprefix tailTrace_7227623
  have hstable : (prefixWord ++ tailWord_7227623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227623).length < 2 ^ (prefixWord ++ tailWord_7227623).sum := by decide
  have hdescent : baseEnd_7227623 < baseStart_7227623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227659 : List Nat := [1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 4]
def baseStart_7227659 : Nat := 118140960795 + 7227659 * 2 ^ 59
def prefixEnd_7227659 : Nat := 4983230072969 + 3 ^ 40 * 7227659 * 2
def baseEnd_7227659 : Nat := 3711263073794642484623107

theorem tailTrace_7227659 : CollatzResearch.WordTrace tailWord_7227659 prefixEnd_7227659 3711263073794642484623107 := by
  unfold tailWord_7227659
  simp only [CollatzResearch.WordTrace]
  refine ⟨263614380522433303727830031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175742920348288869151886687 263614380522433303727830031)
  ·
    refine ⟨395421570783649955591745047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263614380522433303727830031 395421570783649955591745047)
    ·
      refine ⟨593132356175474933387617571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395421570783649955591745047 593132356175474933387617571)
      ·
        refine ⟨889698534263212400081426357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593132356175474933387617571 889698534263212400081426357)
        ·
          refine ⟨83409237587176162507633721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 889698534263212400081426357 83409237587176162507633721)
          ·
            refine ⟨62556928190382121880725291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83409237587176162507633721 62556928190382121880725291)
            ·
              refine ⟨93835392285573182821087937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62556928190382121880725291 93835392285573182821087937)
              ·
                refine ⟨70376544214179887115815953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93835392285573182821087937 70376544214179887115815953)
                ·
                  refine ⟨52782408160634915336861965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70376544214179887115815953 52782408160634915336861965)
                  ·
                    refine ⟨19793403060238093251323237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52782408160634915336861965 19793403060238093251323237)
                    ·
                      refine ⟨3711263073794642484623107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19793403060238093251323237 3711263073794642484623107)
                      ·
                        rfl

theorem cell23_7227659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 4].length) (baseStart_7227659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227659 prefixEnd_7227659 := by exact prefixLift 7227659
  have htrace : WordTrace (prefixWord ++ tailWord_7227659) baseStart_7227659 baseEnd_7227659 := by
    simpa [prefixWord, tailWord_7227659, baseEnd_7227659] using wordTrace_append hprefix tailTrace_7227659
  have hstable : (prefixWord ++ tailWord_7227659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227659).length < 2 ^ (prefixWord ++ tailWord_7227659).sum := by decide
  have hdescent : baseEnd_7227659 < baseStart_7227659 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227680 : List Nat := [2, 1, 1, 5, 2, 2, 1, 3, 1, 3, 2]
def baseStart_7227680 : Nat := 118140960795 + 7227680 * 2 ^ 59
def prefixEnd_7227680 : Nat := 4983230072969 + 3 ^ 40 * 7227680 * 2
def baseEnd_7227680 : Nat := 3711273856888386902460511

theorem tailTrace_7227680 : CollatzResearch.WordTrace tailWord_7227680 prefixEnd_7227680 3711273856888386902460511 := by
  unfold tailWord_7227680
  simp only [CollatzResearch.WordTrace]
  refine ⟨131807573227678612157172247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175743430970238149542896329 131807573227678612157172247)
  ·
    refine ⟨197711359841517918235758371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131807573227678612157172247 197711359841517918235758371)
    ·
      refine ⟨296567039762276877353637557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197711359841517918235758371 296567039762276877353637557)
      ·
        refine ⟨27803159977713457251903521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 296567039762276877353637557 27803159977713457251903521)
        ·
          refine ⟨20852369983285092938927641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27803159977713457251903521 20852369983285092938927641)
          ·
            refine ⟨15639277487463819704195731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20852369983285092938927641 15639277487463819704195731)
            ·
              refine ⟨23458916231195729556293597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15639277487463819704195731 23458916231195729556293597)
              ·
                refine ⟨8797093586698398583610099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23458916231195729556293597 8797093586698398583610099)
                ·
                  refine ⟨13195640380047597875415149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8797093586698398583610099 13195640380047597875415149)
                  ·
                    refine ⟨4948365142517849203280681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13195640380047597875415149 4948365142517849203280681)
                    ·
                      refine ⟨3711273856888386902460511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4948365142517849203280681 3711273856888386902460511)
                      ·
                        rfl

theorem cell23_7227680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_7227680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227680 prefixEnd_7227680 := by exact prefixLift 7227680
  have htrace : WordTrace (prefixWord ++ tailWord_7227680) baseStart_7227680 baseEnd_7227680 := by
    simpa [prefixWord, tailWord_7227680, baseEnd_7227680] using wordTrace_append hprefix tailTrace_7227680
  have hstable : (prefixWord ++ tailWord_7227680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227680).length < 2 ^ (prefixWord ++ tailWord_7227680).sum := by decide
  have hdescent : baseEnd_7227680 < baseStart_7227680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227706 : List Nat := [3, 1, 1, 1, 4, 2, 2, 1, 2, 2, 4]
def baseStart_7227706 : Nat := 118140960795 + 7227706 * 2 ^ 59
def prefixEnd_7227706 : Nat := 4983230072969 + 3 ^ 40 * 7227706 * 2
def baseEnd_7227706 : Nat := 3711287207385403800735391

theorem tailTrace_7227706 : CollatzResearch.WordTrace tailWord_7227706 prefixEnd_7227706 3711287207385403800735391 := by
  unfold tailWord_7227706
  simp only [CollatzResearch.WordTrace]
  refine ⟨65904023688315757688697743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175744063168842020503193981 65904023688315757688697743)
  ·
    refine ⟨98856035532473636533046615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65904023688315757688697743 98856035532473636533046615)
    ·
      refine ⟨148284053298710454799569923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98856035532473636533046615 148284053298710454799569923)
      ·
        refine ⟨222426079948065682199354885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148284053298710454799569923 222426079948065682199354885)
        ·
          refine ⟨41704889990262315412379041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222426079948065682199354885 41704889990262315412379041)
          ·
            refine ⟨31278667492696736559284281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41704889990262315412379041 31278667492696736559284281)
            ·
              refine ⟨23459000619522552419463211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31278667492696736559284281 23459000619522552419463211)
              ·
                refine ⟨35188500929283828629194817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23459000619522552419463211 35188500929283828629194817)
                ·
                  refine ⟨26391375696962871471896113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35188500929283828629194817 26391375696962871471896113)
                  ·
                    refine ⟨19793531772722153603922085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26391375696962871471896113 19793531772722153603922085)
                    ·
                      refine ⟨3711287207385403800735391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19793531772722153603922085 3711287207385403800735391)
                      ·
                        rfl

theorem cell23_7227706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_7227706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227706 prefixEnd_7227706 := by exact prefixLift 7227706
  have htrace : WordTrace (prefixWord ++ tailWord_7227706) baseStart_7227706 baseEnd_7227706 := by
    simpa [prefixWord, tailWord_7227706, baseEnd_7227706] using wordTrace_append hprefix tailTrace_7227706
  have hstable : (prefixWord ++ tailWord_7227706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227706).length < 2 ^ (prefixWord ++ tailWord_7227706).sum := by decide
  have hdescent : baseEnd_7227706 < baseStart_7227706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227710 : List Nat := [4, 2, 1, 2, 1, 2, 3, 1, 1, 4, 2]
def baseStart_7227710 : Nat := 118140960795 + 7227710 * 2 ^ 59
def prefixEnd_7227710 : Nat := 4983230072969 + 3 ^ 40 * 7227710 * 2
def baseEnd_7227710 : Nat := 3711289261308021785085373

theorem tailTrace_7227710 : CollatzResearch.WordTrace tailWord_7227710 prefixEnd_7227710 3711289261308021785085373 := by
  unfold tailWord_7227710
  simp only [CollatzResearch.WordTrace]
  refine ⟨32952030080656067429742073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175744160430165692958624389 32952030080656067429742073)
  ·
    refine ⟨24714022560492050572306555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32952030080656067429742073 24714022560492050572306555)
    ·
      refine ⟨37071033840738075858459833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24714022560492050572306555 37071033840738075858459833)
      ·
        refine ⟨27803275380553556893844875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37071033840738075858459833 27803275380553556893844875)
        ·
          refine ⟨41704913070830335340767313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27803275380553556893844875 41704913070830335340767313)
          ·
            refine ⟨31278684803122751505575485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41704913070830335340767313 31278684803122751505575485)
            ·
              refine ⟨11729506801171031814590807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31278684803122751505575485 11729506801171031814590807)
              ·
                refine ⟨17594260201756547721886211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11729506801171031814590807 17594260201756547721886211)
                ·
                  refine ⟨26391390302634821582829317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17594260201756547721886211 26391390302634821582829317)
                  ·
                    refine ⟨4948385681744029046780497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26391390302634821582829317 4948385681744029046780497)
                    ·
                      refine ⟨3711289261308021785085373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4948385681744029046780497 3711289261308021785085373)
                      ·
                        rfl

theorem cell23_7227710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_7227710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227710 prefixEnd_7227710 := by exact prefixLift 7227710
  have htrace : WordTrace (prefixWord ++ tailWord_7227710) baseStart_7227710 baseEnd_7227710 := by
    simpa [prefixWord, tailWord_7227710, baseEnd_7227710] using wordTrace_append hprefix tailTrace_7227710
  have hstable : (prefixWord ++ tailWord_7227710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227710).length < 2 ^ (prefixWord ++ tailWord_7227710).sum := by decide
  have hdescent : baseEnd_7227710 < baseStart_7227710 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227726 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3]
def baseStart_7227726 : Nat := 118140960795 + 7227726 * 2 ^ 59
def prefixEnd_7227726 : Nat := 4983230072969 + 3 ^ 40 * 7227726 * 2
def baseEnd_7227726 : Nat := 3711297476998493722485299

theorem tailTrace_7227726 : CollatzResearch.WordTrace tailWord_7227726 prefixEnd_7227726 3711297476998493722485299 := by
  unfold tailWord_7227726
  simp only [CollatzResearch.WordTrace]
  refine ⟨32952103026648821771314879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175744549475460382780346021 32952103026648821771314879)
  ·
    refine ⟨49428154539973232656972319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32952103026648821771314879 49428154539973232656972319)
    ·
      refine ⟨74142231809959848985458479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49428154539973232656972319 74142231809959848985458479)
      ·
        refine ⟨111213347714939773478187719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74142231809959848985458479 111213347714939773478187719)
        ·
          refine ⟨166820021572409660217281579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111213347714939773478187719 166820021572409660217281579)
          ·
            refine ⟨250230032358614490325922369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166820021572409660217281579 250230032358614490325922369)
            ·
              refine ⟨187672524268960867744441777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250230032358614490325922369 187672524268960867744441777)
              ·
                refine ⟨140754393201720650808331333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187672524268960867744441777 140754393201720650808331333)
                ·
                  refine ⟨26391448725322622026562125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140754393201720650808331333 26391448725322622026562125)
                  ·
                    refine ⟨9896793271995983259960797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26391448725322622026562125 9896793271995983259960797)
                    ·
                      refine ⟨3711297476998493722485299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9896793271995983259960797 3711297476998493722485299)
                      ·
                        rfl

theorem cell23_7227726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_7227726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227726 prefixEnd_7227726 := by exact prefixLift 7227726
  have htrace : WordTrace (prefixWord ++ tailWord_7227726) baseStart_7227726 baseEnd_7227726 := by
    simpa [prefixWord, tailWord_7227726, baseEnd_7227726] using wordTrace_append hprefix tailTrace_7227726
  have hstable : (prefixWord ++ tailWord_7227726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227726).length < 2 ^ (prefixWord ++ tailWord_7227726).sum := by decide
  have hdescent : baseEnd_7227726 < baseStart_7227726 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227759 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 2, 8]
def baseStart_7227759 : Nat := 118140960795 + 7227759 * 2 ^ 59
def prefixEnd_7227759 : Nat := 4983230072969 + 3 ^ 40 * 7227759 * 2
def baseEnd_7227759 : Nat := 1237104807286697364457549

theorem tailTrace_7227759 : CollatzResearch.WordTrace tailWord_7227759 prefixEnd_7227759 1237104807286697364457549 := by
  unfold tailWord_7227759
  simp only [CollatzResearch.WordTrace]
  refine ⟨263618027822071020806470331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175745351881380680537646887 263618027822071020806470331)
  ·
    refine ⟨395427041733106531209705497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263618027822071020806470331 395427041733106531209705497)
    ·
      refine ⟨296570281299829898407279123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395427041733106531209705497 296570281299829898407279123)
      ·
        refine ⟨444855421949744847610918685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296570281299829898407279123 444855421949744847610918685)
        ·
          refine ⟨166820783231154317854094507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 444855421949744847610918685 166820783231154317854094507)
          ·
            refine ⟨250231174846731476781141761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166820783231154317854094507 250231174846731476781141761)
            ·
              refine ⟨187673381135048607585856321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250231174846731476781141761 187673381135048607585856321)
              ·
                refine ⟨140755035851286455689392241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187673381135048607585856321 140755035851286455689392241)
                ·
                  refine ⟨105566276888464841767044181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140755035851286455689392241 105566276888464841767044181)
                  ·
                    refine ⟨1237104807286697364457549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105566276888464841767044181 1237104807286697364457549)
                    ·
                      rfl

theorem cell23_7227759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 8].length) (baseStart_7227759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227759 prefixEnd_7227759 := by exact prefixLift 7227759
  have htrace : WordTrace (prefixWord ++ tailWord_7227759) baseStart_7227759 baseEnd_7227759 := by
    simpa [prefixWord, tailWord_7227759, baseEnd_7227759] using wordTrace_append hprefix tailTrace_7227759
  have hstable : (prefixWord ++ tailWord_7227759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227759).length < 2 ^ (prefixWord ++ tailWord_7227759).sum := by decide
  have hdescent : baseEnd_7227759 < baseStart_7227759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227783 : List Nat := [1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 4]
def baseStart_7227783 : Nat := 118140960795 + 7227783 * 2 ^ 59
def prefixEnd_7227783 : Nat := 4983230072969 + 3 ^ 40 * 7227783 * 2
def baseEnd_7227783 : Nat := 3711326745395799999472537

theorem tailTrace_7227783 : CollatzResearch.WordTrace tailWord_7227783 prefixEnd_7227783 3711326745395799999472537 := by
  unfold tailWord_7227783
  simp only [CollatzResearch.WordTrace]
  refine ⟨263618903173984072905344003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175745935449322715270229335 263618903173984072905344003)
  ·
    refine ⟨395428354760976109358016005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263618903173984072905344003 395428354760976109358016005)
    ·
      refine ⟨74142816517683020504628001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 395428354760976109358016005 74142816517683020504628001)
      ·
        refine ⟨55607112388262265378471001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74142816517683020504628001 55607112388262265378471001)
        ·
          refine ⟨41705334291196699033853251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55607112388262265378471001 41705334291196699033853251)
          ·
            refine ⟨62558001436795048550779877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41705334291196699033853251 62558001436795048550779877)
            ·
              refine ⟨11729625269399071603271227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62558001436795048550779877 11729625269399071603271227)
              ·
                refine ⟨17594437904098607404906841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11729625269399071603271227 17594437904098607404906841)
                ·
                  refine ⟨13195828428073955553680131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17594437904098607404906841 13195828428073955553680131)
                  ·
                    refine ⟨19793742642110933330520197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13195828428073955553680131 19793742642110933330520197)
                    ·
                      refine ⟨3711326745395799999472537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19793742642110933330520197 3711326745395799999472537)
                      ·
                        rfl

theorem cell23_7227783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_7227783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227783 prefixEnd_7227783 := by exact prefixLift 7227783
  have htrace : WordTrace (prefixWord ++ tailWord_7227783) baseStart_7227783 baseEnd_7227783 := by
    simpa [prefixWord, tailWord_7227783, baseEnd_7227783] using wordTrace_append hprefix tailTrace_7227783
  have hstable : (prefixWord ++ tailWord_7227783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227783).length < 2 ^ (prefixWord ++ tailWord_7227783).sum := by decide
  have hdescent : baseEnd_7227783 < baseStart_7227783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227844 : List Nat := [2, 3, 3, 2, 2, 1, 2, 3, 1, 4]
def baseStart_7227844 : Nat := 118140960795 + 7227844 * 2 ^ 59
def prefixEnd_7227844 : Nat := 4983230072969 + 3 ^ 40 * 7227844 * 2
def baseEnd_7227844 : Nat := 1237119355905241420269919

theorem tailTrace_7227844 : CollatzResearch.WordTrace tailWord_7227844 prefixEnd_7227844 1237119355905241420269919 := by
  unfold tailWord_7227844
  simp only [CollatzResearch.WordTrace]
  refine ⟨131810564013381540161657293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175747418684508720215543057 131810564013381540161657293)
  ·
    refine ⟨49428961505018077560621485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131810564013381540161657293 49428961505018077560621485)
    ·
      refine ⟨18535860564381779085233057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49428961505018077560621485 18535860564381779085233057)
      ·
        refine ⟨13901895423286334313924793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18535860564381779085233057 13901895423286334313924793)
        ·
          refine ⟨10426421567464750735443595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13901895423286334313924793 10426421567464750735443595)
          ·
            refine ⟨15639632351197126103165393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10426421567464750735443595 15639632351197126103165393)
            ·
              refine ⟨11729724263397844577374045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15639632351197126103165393 11729724263397844577374045)
              ·
                refine ⟨4398646598774191716515267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11729724263397844577374045 4398646598774191716515267)
                ·
                  refine ⟨6597969898161287574772901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4398646598774191716515267 6597969898161287574772901)
                  ·
                    refine ⟨1237119355905241420269919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6597969898161287574772901 1237119355905241420269919)
                    ·
                      rfl

theorem cell23_7227844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_7227844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227844 prefixEnd_7227844 := by exact prefixLift 7227844
  have htrace : WordTrace (prefixWord ++ tailWord_7227844) baseStart_7227844 baseEnd_7227844 := by
    simpa [prefixWord, tailWord_7227844, baseEnd_7227844] using wordTrace_append hprefix tailTrace_7227844
  have hstable : (prefixWord ++ tailWord_7227844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227844).length < 2 ^ (prefixWord ++ tailWord_7227844).sum := by decide
  have hdescent : baseEnd_7227844 < baseStart_7227844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227874 : List Nat := [3, 3, 3, 2, 1, 1, 3, 1, 6]
def baseStart_7227874 : Nat := 118140960795 + 7227874 * 2 ^ 59
def prefixEnd_7227874 : Nat := 4983230072969 + 3 ^ 40 * 7227874 * 2
def baseEnd_7227874 : Nat := 412374830237262127048291

theorem tailTrace_7227874 : CollatzResearch.WordTrace tailWord_7227874 prefixEnd_7227874 412374830237262127048291 := by
  unfold tailWord_7227874
  simp only [CollatzResearch.WordTrace]
  refine ⟨65905555554163598861726669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175748148144436263631271117 65905555554163598861726669)
  ·
    refine ⟨24714583332811349573147501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65905555554163598861726669 24714583332811349573147501)
    ·
      refine ⟨9267968749804256089930313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24714583332811349573147501 9267968749804256089930313)
      ·
        refine ⟨6950976562353192067447735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9267968749804256089930313 6950976562353192067447735)
        ·
          refine ⟨10426464843529788101171603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6950976562353192067447735 10426464843529788101171603)
          ·
            refine ⟨15639697265294682151757405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10426464843529788101171603 15639697265294682151757405)
            ·
              refine ⟨5864886474485505806909027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15639697265294682151757405 5864886474485505806909027)
              ·
                refine ⟨8797329711728258710363541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5864886474485505806909027 8797329711728258710363541)
                ·
                  refine ⟨412374830237262127048291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8797329711728258710363541 412374830237262127048291)
                  ·
                    rfl

theorem cell23_7227874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_7227874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227874 prefixEnd_7227874 := by exact prefixLift 7227874
  have htrace : WordTrace (prefixWord ++ tailWord_7227874) baseStart_7227874 baseEnd_7227874 := by
    simpa [prefixWord, tailWord_7227874, baseEnd_7227874] using wordTrace_append hprefix tailTrace_7227874
  have hstable : (prefixWord ++ tailWord_7227874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227874).length < 2 ^ (prefixWord ++ tailWord_7227874).sum := by decide
  have hdescent : baseEnd_7227874 < baseStart_7227874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227896 : List Nat := [2, 1, 2, 1, 1, 4, 3, 9]
def baseStart_7227896 : Nat := 118140960795 + 7227896 * 2 ^ 59
def prefixEnd_7227896 : Nat := 4983230072969 + 3 ^ 40 * 7227896 * 2
def baseEnd_7227896 : Nat := 137458695137398446568871

theorem tailTrace_7227896 : CollatzResearch.WordTrace tailWord_7227896 prefixEnd_7227896 137458695137398446568871 := by
  unfold tailWord_7227896
  simp only [CollatzResearch.WordTrace]
  refine ⟨131811512311287346602103771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175748683081716462136138361 131811512311287346602103771)
  ·
    refine ⟨197717268466931019903155657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131811512311287346602103771 197717268466931019903155657)
    ·
      refine ⟨148287951350198264927366743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197717268466931019903155657 148287951350198264927366743)
      ·
        refine ⟨222431927025297397391050115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148287951350198264927366743 222431927025297397391050115)
        ·
          refine ⟨333647890537946096086575173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222431927025297397391050115 333647890537946096086575173)
          ·
            refine ⟨62558979475864893016232845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 333647890537946096086575173 62558979475864893016232845)
            ·
              refine ⟨23459617303449334881087317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62558979475864893016232845 23459617303449334881087317)
              ·
                refine ⟨137458695137398446568871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23459617303449334881087317 137458695137398446568871)
                ·
                  rfl

theorem cell23_7227896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 9].length) (baseStart_7227896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227896 prefixEnd_7227896 := by exact prefixLift 7227896
  have htrace : WordTrace (prefixWord ++ tailWord_7227896) baseStart_7227896 baseEnd_7227896 := by
    simpa [prefixWord, tailWord_7227896, baseEnd_7227896] using wordTrace_append hprefix tailTrace_7227896
  have hstable : (prefixWord ++ tailWord_7227896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227896).length < 2 ^ (prefixWord ++ tailWord_7227896).sum := by decide
  have hdescent : baseEnd_7227896 < baseStart_7227896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227944 : List Nat := [2, 1, 5, 2, 1, 3, 1, 2, 1, 2, 3]
def baseStart_7227944 : Nat := 118140960795 + 7227944 * 2 ^ 59
def prefixEnd_7227944 : Nat := 4983230072969 + 3 ^ 40 * 7227944 * 2
def baseEnd_7227944 : Nat := 3711409415781173869559297

theorem tailTrace_7227944 : CollatzResearch.WordTrace tailWord_7227944 prefixEnd_7227944 3711409415781173869559297 := by
  unfold tailWord_7227944
  simp only [CollatzResearch.WordTrace]
  refine ⟨131812387663200398700977443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175749850217600531601303257 131812387663200398700977443)
  ·
    refine ⟨197718581494800598051466165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131812387663200398700977443 197718581494800598051466165)
    ·
      refine ⟨18536117015137556067324953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 197718581494800598051466165 18536117015137556067324953)
      ·
        refine ⟨13902087761353167050493715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18536117015137556067324953 13902087761353167050493715)
        ·
          refine ⟨20853131642029750575740573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13902087761353167050493715 20853131642029750575740573)
          ·
            refine ⟨7819924365761156465902715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20853131642029750575740573 7819924365761156465902715)
            ·
              refine ⟨11729886548641734698854073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7819924365761156465902715 11729886548641734698854073)
              ·
                refine ⟨8797414911481301024140555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11729886548641734698854073 8797414911481301024140555)
                ·
                  refine ⟨13196122367221951536210833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8797414911481301024140555 13196122367221951536210833)
                  ·
                    refine ⟨9897091775416463652158125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13196122367221951536210833 9897091775416463652158125)
                    ·
                      refine ⟨3711409415781173869559297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9897091775416463652158125 3711409415781173869559297)
                      ·
                        rfl

theorem cell23_7227944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_7227944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227944 prefixEnd_7227944 := by exact prefixLift 7227944
  have htrace : WordTrace (prefixWord ++ tailWord_7227944) baseStart_7227944 baseEnd_7227944 := by
    simpa [prefixWord, tailWord_7227944, baseEnd_7227944] using wordTrace_append hprefix tailTrace_7227944
  have hstable : (prefixWord ++ tailWord_7227944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227944).length < 2 ^ (prefixWord ++ tailWord_7227944).sum := by decide
  have hdescent : baseEnd_7227944 < baseStart_7227944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227980 : List Nat := [2, 2, 1, 3, 1, 2, 1, 2, 3, 4, 2]
def baseStart_7227980 : Nat := 118140960795 + 7227980 * 2 ^ 59
def prefixEnd_7227980 : Nat := 4983230072969 + 3 ^ 40 * 7227980 * 2
def baseEnd_7227980 : Nat := 3711427901084735728709131

theorem tailTrace_7227980 : CollatzResearch.WordTrace tailWord_7227980 prefixEnd_7227980 3711427901084735728709131 := by
  unfold tailWord_7227980
  simp only [CollatzResearch.WordTrace]
  refine ⟨131813044177135187775132697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175750725569513583700176929 131813044177135187775132697)
  ·
    refine ⟨98859783132851390831349523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131813044177135187775132697 98859783132851390831349523)
    ·
      refine ⟨148289674699277086247024285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98859783132851390831349523 148289674699277086247024285)
      ·
        refine ⟨55608628012228907342634107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148289674699277086247024285 55608628012228907342634107)
        ·
          refine ⟨83412942018343361013951161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55608628012228907342634107 83412942018343361013951161)
          ·
            refine ⟨62559706513757520760463371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83412942018343361013951161 62559706513757520760463371)
            ·
              refine ⟨93839559770636281140695057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62559706513757520760463371 93839559770636281140695057)
              ·
                refine ⟨70379669827977210855521293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93839559770636281140695057 70379669827977210855521293)
                ·
                  refine ⟨26392376185491454070820485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70379669827977210855521293 26392376185491454070820485)
                  ·
                    refine ⟨4948570534779647638278841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26392376185491454070820485 4948570534779647638278841)
                    ·
                      refine ⟨3711427901084735728709131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4948570534779647638278841 3711427901084735728709131)
                      ·
                        rfl

theorem cell23_7227980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_7227980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227980 prefixEnd_7227980 := by exact prefixLift 7227980
  have htrace : WordTrace (prefixWord ++ tailWord_7227980) baseStart_7227980 baseEnd_7227980 := by
    simpa [prefixWord, tailWord_7227980, baseEnd_7227980] using wordTrace_append hprefix tailTrace_7227980
  have hstable : (prefixWord ++ tailWord_7227980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227980).length < 2 ^ (prefixWord ++ tailWord_7227980).sum := by decide
  have hdescent : baseEnd_7227980 < baseStart_7227980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7227983 : List Nat := [1, 1, 2, 1, 1, 2, 5, 1, 2, 4, 3]
def baseStart_7227983 : Nat := 118140960795 + 7227983 * 2 ^ 59
def prefixEnd_7227983 : Nat := 4983230072969 + 3 ^ 40 * 7227983 * 2
def baseEnd_7227983 : Nat := 3711429441526699216971617

theorem tailTrace_7227983 : CollatzResearch.WordTrace tailWord_7227983 prefixEnd_7227983 3711429441526699216971617 := by
  unfold tailWord_7227983
  simp only [CollatzResearch.WordTrace]
  refine ⟨263626197773259507062624603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175750798515506338041749735 263626197773259507062624603)
  ·
    refine ⟨395439296659889260593936905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263626197773259507062624603 395439296659889260593936905)
    ·
      refine ⟨296579472494916945445452679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395439296659889260593936905 296579472494916945445452679)
      ·
        refine ⟨444869208742375418168179019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296579472494916945445452679 444869208742375418168179019)
        ·
          refine ⟨667303813113563127252268529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444869208742375418168179019 667303813113563127252268529)
          ·
            refine ⟨500477859835172345439201397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 667303813113563127252268529 500477859835172345439201397)
            ·
              refine ⟨46919799359547407384925131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 500477859835172345439201397 46919799359547407384925131)
              ·
                refine ⟨70379699039321111077387697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46919799359547407384925131 70379699039321111077387697)
                ·
                  refine ⟨52784774279490833308040773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70379699039321111077387697 52784774279490833308040773)
                  ·
                    refine ⟨9897145177404531245257645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52784774279490833308040773 9897145177404531245257645)
                    ·
                      refine ⟨3711429441526699216971617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9897145177404531245257645 3711429441526699216971617)
                      ·
                        rfl

theorem cell23_7227983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 4, 3].length) (baseStart_7227983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7227983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7227983 prefixEnd_7227983 := by exact prefixLift 7227983
  have htrace : WordTrace (prefixWord ++ tailWord_7227983) baseStart_7227983 baseEnd_7227983 := by
    simpa [prefixWord, tailWord_7227983, baseEnd_7227983] using wordTrace_append hprefix tailTrace_7227983
  have hstable : (prefixWord ++ tailWord_7227983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7227983).length < 2 ^ (prefixWord ++ tailWord_7227983).sum := by decide
  have hdescent : baseEnd_7227983 < baseStart_7227983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7227983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228003 : List Nat := [1, 1, 1, 5, 1, 2, 3, 2, 7]
def baseStart_7228003 : Nat := 118140960795 + 7228003 * 2 ^ 59
def prefixEnd_7228003 : Nat := 4983230072969 + 3 ^ 40 * 7228003 * 2
def baseEnd_7228003 : Nat := 412382190126643237635725

theorem tailTrace_7228003 : CollatzResearch.WordTrace tailWord_7228003 prefixEnd_7228003 412382190126643237635725 := by
  unfold tailWord_7228003
  simp only [CollatzResearch.WordTrace]
  refine ⟨263626927233187050478352663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175751284822124700318901775 263626927233187050478352663)
  ·
    refine ⟨395440390849780575717528995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263626927233187050478352663 395440390849780575717528995)
    ·
      refine ⟨593160586274670863576293493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395440390849780575717528995 593160586274670863576293493)
      ·
        refine ⟨55608804963250393460277515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 593160586274670863576293493 55608804963250393460277515)
        ·
          refine ⟨83413207444875590190416273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55608804963250393460277515 83413207444875590190416273)
          ·
            refine ⟨62559905583656692642812205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83413207444875590190416273 62559905583656692642812205)
            ·
              refine ⟨23459964593871259741054577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62559905583656692642812205 23459964593871259741054577)
              ·
                refine ⟨17594973445403444805790933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23459964593871259741054577 17594973445403444805790933)
                ·
                  refine ⟨412382190126643237635725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17594973445403444805790933 412382190126643237635725)
                  ·
                    rfl

theorem cell23_7228003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 7].length) (baseStart_7228003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228003 prefixEnd_7228003 := by exact prefixLift 7228003
  have htrace : WordTrace (prefixWord ++ tailWord_7228003) baseStart_7228003 baseEnd_7228003 := by
    simpa [prefixWord, tailWord_7228003, baseEnd_7228003] using wordTrace_append hprefix tailTrace_7228003
  have hstable : (prefixWord ++ tailWord_7228003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228003).length < 2 ^ (prefixWord ++ tailWord_7228003).sum := by decide
  have hdescent : baseEnd_7228003 < baseStart_7228003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228018 : List Nat := [3, 2, 1, 2, 5, 1, 2, 1, 1, 3, 2]
def baseStart_7228018 : Nat := 118140960795 + 7228018 * 2 ^ 59
def prefixEnd_7228018 : Nat := 4983230072969 + 3 ^ 40 * 7228018 * 2
def baseEnd_7228018 : Nat := 3711447413349606580033957

theorem tailTrace_7228018 : CollatzResearch.WordTrace tailWord_7228018 prefixEnd_7228018 3711447413349606580033957 := by
  unfold tailWord_7228018
  simp only [CollatzResearch.WordTrace]
  refine ⟨65906868582033177010037177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175751649552088472026765805 65906868582033177010037177)
  ·
    refine ⟨49430151436524882757527883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65906868582033177010037177 49430151436524882757527883)
    ·
      refine ⟨74145227154787324136291825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49430151436524882757527883 74145227154787324136291825)
      ·
        refine ⟨55608920366090493102218869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74145227154787324136291825 55608920366090493102218869)
        ·
          refine ⟨5213336284320983728333019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55608920366090493102218869 5213336284320983728333019)
          ·
            refine ⟨7820004426481475592499529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5213336284320983728333019 7820004426481475592499529)
            ·
              refine ⟨5865003319861106694374647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7820004426481475592499529 5865003319861106694374647)
              ·
                refine ⟨8797504979791660041561971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5865003319861106694374647 8797504979791660041561971)
                ·
                  refine ⟨13196257469687490062342957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8797504979791660041561971 13196257469687490062342957)
                  ·
                    refine ⟨4948596551132808773378609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13196257469687490062342957 4948596551132808773378609)
                    ·
                      refine ⟨3711447413349606580033957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4948596551132808773378609 3711447413349606580033957)
                      ·
                        rfl

theorem cell23_7228018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_7228018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228018 prefixEnd_7228018 := by exact prefixLift 7228018
  have htrace : WordTrace (prefixWord ++ tailWord_7228018) baseStart_7228018 baseEnd_7228018 := by
    simpa [prefixWord, tailWord_7228018, baseEnd_7228018] using wordTrace_append hprefix tailTrace_7228018
  have hstable : (prefixWord ++ tailWord_7228018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228018).length < 2 ^ (prefixWord ++ tailWord_7228018).sum := by decide
  have hdescent : baseEnd_7228018 < baseStart_7228018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228050 : List Nat := [3, 2, 3, 1, 2, 1, 1, 2, 1, 7]
def baseStart_7228050 : Nat := 118140960795 + 7228050 * 2 ^ 59
def prefixEnd_7228050 : Nat := 4983230072969 + 3 ^ 40 * 7228050 * 2
def baseEnd_7228050 : Nat := 1237154614910183484944603

theorem tailTrace_7228050 : CollatzResearch.WordTrace tailWord_7228050 prefixEnd_7228050 1237154614910183484944603 := by
  unfold tailWord_7228050
  simp only [CollatzResearch.WordTrace]
  refine ⟨65907160366004194376328401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175752427642677851670209069 65907160366004194376328401)
  ·
    refine ⟨49430370274503145782246301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65907160366004194376328401 49430370274503145782246301)
    ·
      refine ⟨18536388852938679668342363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49430370274503145782246301 18536388852938679668342363)
      ·
        refine ⟨27804583279408019502513545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18536388852938679668342363 27804583279408019502513545)
        ·
          refine ⟨20853437459556014626885159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27804583279408019502513545 20853437459556014626885159)
          ·
            refine ⟨31280156189334021940327739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20853437459556014626885159 31280156189334021940327739)
            ·
              refine ⟨46920234284001032910491609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31280156189334021940327739 46920234284001032910491609)
              ·
                refine ⟨35190175713000774682868707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46920234284001032910491609 35190175713000774682868707)
                ·
                  refine ⟨52785263569501162024303061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35190175713000774682868707 52785263569501162024303061)
                  ·
                    refine ⟨1237154614910183484944603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52785263569501162024303061 1237154614910183484944603)
                    ·
                      rfl

theorem cell23_7228050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_7228050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228050 prefixEnd_7228050 := by exact prefixLift 7228050
  have htrace : WordTrace (prefixWord ++ tailWord_7228050) baseStart_7228050 baseEnd_7228050 := by
    simpa [prefixWord, tailWord_7228050, baseEnd_7228050] using wordTrace_append hprefix tailTrace_7228050
  have hstable : (prefixWord ++ tailWord_7228050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228050).length < 2 ^ (prefixWord ++ tailWord_7228050).sum := by decide
  have hdescent : baseEnd_7228050 < baseStart_7228050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228071 : List Nat := [1, 1, 6, 3, 1, 2, 1, 3, 5]
def baseStart_7228071 : Nat := 118140960795 + 7228071 * 2 ^ 59
def prefixEnd_7228071 : Nat := 4983230072969 + 3 ^ 40 * 7228071 * 2
def baseEnd_7228071 : Nat := 412386069758254985852357

theorem tailTrace_7228071 : CollatzResearch.WordTrace tailWord_7228071 prefixEnd_7228071 412386069758254985852357 := by
  unfold tailWord_7228071
  simp only [CollatzResearch.WordTrace]
  refine ⟨263629407396940698091828067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175752938264627132061218711 263629407396940698091828067)
  ·
    refine ⟨395444111095411047137742101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263629407396940698091828067 395444111095411047137742101)
    ·
      refine ⟨18536442707597392834581661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 395444111095411047137742101 18536442707597392834581661)
      ·
        refine ⟨6951166015349022312968123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18536442707597392834581661 6951166015349022312968123)
        ·
          refine ⟨10426749023023533469452185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6951166015349022312968123 10426749023023533469452185)
          ·
            refine ⟨7820061767267650102089139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10426749023023533469452185 7820061767267650102089139)
            ·
              refine ⟨11730092650901475153133709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7820061767267650102089139 11730092650901475153133709)
              ·
                refine ⟨4398784744088053182425141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11730092650901475153133709 4398784744088053182425141)
                ·
                  refine ⟨412386069758254985852357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4398784744088053182425141 412386069758254985852357)
                  ·
                    rfl

theorem cell23_7228071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 3, 5].length) (baseStart_7228071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228071 prefixEnd_7228071 := by exact prefixLift 7228071
  have htrace : WordTrace (prefixWord ++ tailWord_7228071) baseStart_7228071 baseEnd_7228071 := by
    simpa [prefixWord, tailWord_7228071, baseEnd_7228071] using wordTrace_append hprefix tailTrace_7228071
  have hstable : (prefixWord ++ tailWord_7228071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228071).length < 2 ^ (prefixWord ++ tailWord_7228071).sum := by decide
  have hdescent : baseEnd_7228071 < baseStart_7228071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228087 : List Nat := [1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 4]
def baseStart_7228087 : Nat := 118140960795 + 7228087 * 2 ^ 59
def prefixEnd_7228087 : Nat := 4983230072969 + 3 ^ 40 * 7228087 * 2
def baseEnd_7228087 : Nat := 3711482843514766810071139

theorem tailTrace_7228087 : CollatzResearch.WordTrace tailWord_7228087 prefixEnd_7228087 3711482843514766810071139 := by
  unfold tailWord_7228087
  simp only [CollatzResearch.WordTrace]
  refine ⟨263629990964882732824410515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175753327309921821882940343 263629990964882732824410515)
  ·
    refine ⟨395444986447324099236615773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263629990964882732824410515 395444986447324099236615773)
    ·
      refine ⟨148291869917746537213730915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 395444986447324099236615773 148291869917746537213730915)
      ·
        refine ⟨222437804876619805820596373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148291869917746537213730915 222437804876619805820596373)
        ·
          refine ⟨10426772103591553397840455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 222437804876619805820596373 10426772103591553397840455)
          ·
            refine ⟨15640158155387330096760683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10426772103591553397840455 15640158155387330096760683)
            ·
              refine ⟨23460237233080995145141025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15640158155387330096760683 23460237233080995145141025)
              ·
                refine ⟨17595177924810746358855769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23460237233080995145141025 17595177924810746358855769)
                ·
                  refine ⟨13196383443608059769141827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17595177924810746358855769 13196383443608059769141827)
                  ·
                    refine ⟨19794575165412089653712741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13196383443608059769141827 19794575165412089653712741)
                    ·
                      refine ⟨3711482843514766810071139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19794575165412089653712741 3711482843514766810071139)
                      ·
                        rfl

theorem cell23_7228087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 4].length) (baseStart_7228087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228087 prefixEnd_7228087 := by exact prefixLift 7228087
  have htrace : WordTrace (prefixWord ++ tailWord_7228087) baseStart_7228087 baseEnd_7228087 := by
    simpa [prefixWord, tailWord_7228087, baseEnd_7228087] using wordTrace_append hprefix tailTrace_7228087
  have hstable : (prefixWord ++ tailWord_7228087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228087).length < 2 ^ (prefixWord ++ tailWord_7228087).sum := by decide
  have hdescent : baseEnd_7228087 < baseStart_7228087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228124 : List Nat := [2, 2, 5, 1, 1, 1, 1, 3, 2, 2, 3]
def baseStart_7228124 : Nat := 118140960795 + 7228124 * 2 ^ 59
def prefixEnd_7228124 : Nat := 4983230072969 + 3 ^ 40 * 7228124 * 2
def baseEnd_7228124 : Nat := 3711501842298983165308469

theorem tailTrace_7228124 : CollatzResearch.WordTrace tailWord_7228124 prefixEnd_7228124 3711501842298983165308469 := by
  unfold tailWord_7228124
  simp only [CollatzResearch.WordTrace]
  refine ⟨131815670232874344071753713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175754226977165792095671617 131815670232874344071753713)
  ·
    refine ⟨98861752674655758053815285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131815670232874344071753713 98861752674655758053815285)
    ·
      refine ⟨9268289313248977317545183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98861752674655758053815285 9268289313248977317545183)
      ·
        refine ⟨13902433969873465976317775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9268289313248977317545183 13902433969873465976317775)
        ·
          refine ⟨20853650954810198964476663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13902433969873465976317775 20853650954810198964476663)
          ·
            refine ⟨31280476432215298446714995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20853650954810198964476663 31280476432215298446714995)
            ·
              refine ⟨46920714648322947670072493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31280476432215298446714995 46920714648322947670072493)
              ·
                refine ⟨17595267993121105376277185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46920714648322947670072493 17595267993121105376277185)
                ·
                  refine ⟨13196450994840829032207889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17595267993121105376277185 13196450994840829032207889)
                  ·
                    refine ⟨9897338246130621774155917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13196450994840829032207889 9897338246130621774155917)
                    ·
                      refine ⟨3711501842298983165308469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9897338246130621774155917 3711501842298983165308469)
                      ·
                        rfl

theorem cell23_7228124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_7228124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228124 prefixEnd_7228124 := by exact prefixLift 7228124
  have htrace : WordTrace (prefixWord ++ tailWord_7228124) baseStart_7228124 baseEnd_7228124 := by
    simpa [prefixWord, tailWord_7228124, baseEnd_7228124] using wordTrace_append hprefix tailTrace_7228124
  have hstable : (prefixWord ++ tailWord_7228124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228124).length < 2 ^ (prefixWord ++ tailWord_7228124).sum := by decide
  have hdescent : baseEnd_7228124 < baseStart_7228124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228194 : List Nat := [3, 3, 1, 1, 2, 3, 1, 3, 1, 1, 4]
def baseStart_7228194 : Nat := 118140960795 + 7228194 * 2 ^ 59
def prefixEnd_7228194 : Nat := 4983230072969 + 3 ^ 40 * 7228194 * 2
def baseEnd_7228194 : Nat := 3711537785944797891433147

theorem tailTrace_7228194 : CollatzResearch.WordTrace tailWord_7228194 prefixEnd_7228194 3711537785944797891433147 := by
  unfold tailWord_7228194
  simp only [CollatzResearch.WordTrace]
  refine ⟨65908473393873772524638909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175755929050330060065703757 65908473393873772524638909)
  ·
    refine ⟨24715677522702664696739591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65908473393873772524638909 24715677522702664696739591)
    ·
      refine ⟨37073516284053997045109387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24715677522702664696739591 37073516284053997045109387)
      ·
        refine ⟨55610274426080995567664081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37073516284053997045109387 55610274426080995567664081)
        ·
          refine ⟨41707705819560746675748061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55610274426080995567664081 41707705819560746675748061)
          ·
            refine ⟨15640389682335280003405523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41707705819560746675748061 15640389682335280003405523)
            ·
              refine ⟨23460584523502920005108285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15640389682335280003405523 23460584523502920005108285)
              ·
                refine ⟨8797719196313595001915607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23460584523502920005108285 8797719196313595001915607)
                ·
                  refine ⟨13196578794470392502873411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8797719196313595001915607 13196578794470392502873411)
                  ·
                    refine ⟨19794868191705588754310117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13196578794470392502873411 19794868191705588754310117)
                    ·
                      refine ⟨3711537785944797891433147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19794868191705588754310117 3711537785944797891433147)
                      ·
                        rfl

theorem cell23_7228194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_7228194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228194 prefixEnd_7228194 := by exact prefixLift 7228194
  have htrace : WordTrace (prefixWord ++ tailWord_7228194) baseStart_7228194 baseEnd_7228194 := by
    simpa [prefixWord, tailWord_7228194, baseEnd_7228194] using wordTrace_append hprefix tailTrace_7228194
  have hstable : (prefixWord ++ tailWord_7228194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228194).length < 2 ^ (prefixWord ++ tailWord_7228194).sum := by decide
  have hdescent : baseEnd_7228194 < baseStart_7228194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228200 : List Nat := [2, 1, 5, 1, 1, 1, 12]
def baseStart_7228200 : Nat := 118140960795 + 7228200 * 2 ^ 59
def prefixEnd_7228200 : Nat := 4983230072969 + 3 ^ 40 * 7228200 * 2
def baseEnd_7228200 : Nat := 45821492183070677382199

theorem tailTrace_7228200 : CollatzResearch.WordTrace tailWord_7228200 prefixEnd_7228200 45821492183070677382199 := by
  unfold tailWord_7228200
  simp only [CollatzResearch.WordTrace]
  refine ⟨131817056206736676561637027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175756074942315568748849369 131817056206736676561637027)
  ·
    refine ⟨197725584310105014842455541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131817056206736676561637027 197725584310105014842455541)
    ·
      refine ⟨18536773529072345141480207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 197725584310105014842455541 18536773529072345141480207)
      ·
        refine ⟨27805160293608517712220311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18536773529072345141480207 27805160293608517712220311)
        ·
          refine ⟨41707740440412776568330467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27805160293608517712220311 41707740440412776568330467)
          ·
            refine ⟨62561610660619164852495701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41707740440412776568330467 62561610660619164852495701)
            ·
              refine ⟨45821492183070677382199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 62561610660619164852495701 45821492183070677382199)
              ·
                rfl

theorem cell23_7228200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 12].length) (baseStart_7228200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228200 prefixEnd_7228200 := by exact prefixLift 7228200
  have htrace : WordTrace (prefixWord ++ tailWord_7228200) baseStart_7228200 baseEnd_7228200 := by
    simpa [prefixWord, tailWord_7228200, baseEnd_7228200] using wordTrace_append hprefix tailTrace_7228200
  have hstable : (prefixWord ++ tailWord_7228200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228200).length < 2 ^ (prefixWord ++ tailWord_7228200).sum := by decide
  have hdescent : baseEnd_7228200 < baseStart_7228200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228211 : List Nat := [1, 1, 1, 2, 6, 2, 2, 1, 3, 2, 2]
def baseStart_7228211 : Nat := 118140960795 + 7228211 * 2 ^ 59
def prefixEnd_7228211 : Nat := 4983230072969 + 3 ^ 40 * 7228211 * 2
def baseEnd_7228211 : Nat := 3711546515115924324920569

theorem tailTrace_7228211 : CollatzResearch.WordTrace tailWord_7228211 prefixEnd_7228211 3711546515115924324920569 := by
  unfold tailWord_7228211
  simp only [CollatzResearch.WordTrace]
  refine ⟨263634513616433502001924487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175756342410955668001282991 263634513616433502001924487)
  ·
    refine ⟨395451770424650253002886731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263634513616433502001924487 395451770424650253002886731)
    ·
      refine ⟨593177655636975379504330097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395451770424650253002886731 593177655636975379504330097)
      ·
        refine ⟨444883241727731534628247573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 593177655636975379504330097 444883241727731534628247573)
        ·
          refine ⟨20853901955987415685699105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 444883241727731534628247573 20853901955987415685699105)
          ·
            refine ⟨15640426466990561764274329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20853901955987415685699105 15640426466990561764274329)
            ·
              refine ⟨11730319850242921323205747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15640426466990561764274329 11730319850242921323205747)
              ·
                refine ⟨17595479775364381984808621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11730319850242921323205747 17595479775364381984808621)
                ·
                  refine ⟨6598304915761643244303233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17595479775364381984808621 6598304915761643244303233)
                  ·
                    refine ⟨4948728686821232433227425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6598304915761643244303233 4948728686821232433227425)
                    ·
                      refine ⟨3711546515115924324920569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4948728686821232433227425 3711546515115924324920569)
                      ·
                        rfl

theorem cell23_7228211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 3, 2, 2].length) (baseStart_7228211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228211 prefixEnd_7228211 := by exact prefixLift 7228211
  have htrace : WordTrace (prefixWord ++ tailWord_7228211) baseStart_7228211 baseEnd_7228211 := by
    simpa [prefixWord, tailWord_7228211, baseEnd_7228211] using wordTrace_append hprefix tailTrace_7228211
  have hstable : (prefixWord ++ tailWord_7228211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228211).length < 2 ^ (prefixWord ++ tailWord_7228211).sum := by decide
  have hdescent : baseEnd_7228211 < baseStart_7228211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228221 : List Nat := [1, 4, 1, 4, 3, 1, 1, 1, 1, 6]
def baseStart_7228221 : Nat := 118140960795 + 7228221 * 2 ^ 59
def prefixEnd_7228221 : Nat := 4983230072969 + 3 ^ 40 * 7228221 * 2
def baseEnd_7228221 : Nat := 1237183883307489761931841

theorem tailTrace_7228221 : CollatzResearch.WordTrace tailWord_7228221 prefixEnd_7228221 1237183883307489761931841 := by
  unfold tailWord_7228221
  simp only [CollatzResearch.WordTrace]
  refine ⟨263634878346397273709788517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175756585564264849139859011 263634878346397273709788517)
  ·
    refine ⟨49431539689949488820585347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263634878346397273709788517 49431539689949488820585347)
    ·
      refine ⟨74147309534924233230878021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49431539689949488820585347 74147309534924233230878021)
      ·
        refine ⟨13902620537798293730789629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74147309534924233230878021 13902620537798293730789629)
        ·
          refine ⟨5213482701674360149046111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13902620537798293730789629 5213482701674360149046111)
          ·
            refine ⟨7820224052511540223569167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5213482701674360149046111 7820224052511540223569167)
            ·
              refine ⟨11730336078767310335353751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7820224052511540223569167 11730336078767310335353751)
              ·
                refine ⟨17595504118150965503030627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11730336078767310335353751 17595504118150965503030627)
                ·
                  refine ⟨26393256177226448254545941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17595504118150965503030627 26393256177226448254545941)
                  ·
                    refine ⟨1237183883307489761931841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26393256177226448254545941 1237183883307489761931841)
                    ·
                      rfl

theorem cell23_7228221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 1, 6].length) (baseStart_7228221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228221 prefixEnd_7228221 := by exact prefixLift 7228221
  have htrace : WordTrace (prefixWord ++ tailWord_7228221) baseStart_7228221 baseEnd_7228221 := by
    simpa [prefixWord, tailWord_7228221, baseEnd_7228221] using wordTrace_append hprefix tailTrace_7228221
  have hstable : (prefixWord ++ tailWord_7228221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228221).length < 2 ^ (prefixWord ++ tailWord_7228221).sum := by decide
  have hdescent : baseEnd_7228221 < baseStart_7228221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228228 : List Nat := [2, 3, 4, 2, 1, 1, 2, 2, 1, 1, 4]
def baseStart_7228228 : Nat := 118140960795 + 7228228 * 2 ^ 59
def prefixEnd_7228228 : Nat := 4983230072969 + 3 ^ 40 * 7228228 * 2
def baseEnd_7228228 : Nat := 3711555244287050758407991

theorem tailTrace_7228228 : CollatzResearch.WordTrace tailWord_7228228 prefixEnd_7228228 3711555244287050758407991 := by
  unfold tailWord_7228228
  simp only [CollatzResearch.WordTrace]
  refine ⟨131817566828685956952646669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175756755771581275936862225 131817566828685956952646669)
  ·
    refine ⟨49431587560757233857242501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131817566828685956952646669 49431587560757233857242501)
    ·
      refine ⟨9268422667641981348232969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49431587560757233857242501 9268422667641981348232969)
      ·
        refine ⟨6951317000731486011174727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9268422667641981348232969 6951317000731486011174727)
        ·
          refine ⟨10426975501097229016762091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6951317000731486011174727 10426975501097229016762091)
          ·
            refine ⟨15640463251645843525143137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10426975501097229016762091 15640463251645843525143137)
            ·
              refine ⟨11730347438734382643857353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15640463251645843525143137 11730347438734382643857353)
              ·
                refine ⟨8797760579050786982893015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11730347438734382643857353 8797760579050786982893015)
                ·
                  refine ⟨13196640868576180474339523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8797760579050786982893015 13196640868576180474339523)
                  ·
                    refine ⟨19794961302864270711509285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13196640868576180474339523 19794961302864270711509285)
                    ·
                      refine ⟨3711555244287050758407991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19794961302864270711509285 3711555244287050758407991)
                      ·
                        rfl

theorem cell23_7228228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_7228228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228228 prefixEnd_7228228 := by exact prefixLift 7228228
  have htrace : WordTrace (prefixWord ++ tailWord_7228228) baseStart_7228228 baseEnd_7228228 := by
    simpa [prefixWord, tailWord_7228228, baseEnd_7228228] using wordTrace_append hprefix tailTrace_7228228
  have hstable : (prefixWord ++ tailWord_7228228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228228).length < 2 ^ (prefixWord ++ tailWord_7228228).sum := by decide
  have hdescent : baseEnd_7228228 < baseStart_7228228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228240 : List Nat := [2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 5]
def baseStart_7228240 : Nat := 118140960795 + 7228240 * 2 ^ 59
def prefixEnd_7228240 : Nat := 4983230072969 + 3 ^ 40 * 7228240 * 2
def baseEnd_7228240 : Nat := 3711561406054904711457935

theorem tailTrace_7228240 : CollatzResearch.WordTrace tailWord_7228240 prefixEnd_7228240 3711561406054904711457935 := by
  unfold tailWord_7228240
  simp only [CollatzResearch.WordTrace]
  refine ⟨131817785666664219977365087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175757047555552293303153449 131817785666664219977365087)
  ·
    refine ⟨197726678499996329966047631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131817785666664219977365087 197726678499996329966047631)
    ·
      refine ⟨296590017749994494949071447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197726678499996329966047631 296590017749994494949071447)
      ·
        refine ⟨444885026624991742423607171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296590017749994494949071447 444885026624991742423607171)
        ·
          refine ⟨667327539937487613635410757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444885026624991742423607171 667327539937487613635410757)
          ·
            refine ⟨125123913738278927556639517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 667327539937487613635410757 125123913738278927556639517)
            ·
              refine ⟨46921467651854597833739819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125123913738278927556639517 46921467651854597833739819)
              ·
                refine ⟨70382201477781896750609729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46921467651854597833739819 70382201477781896750609729)
                ·
                  refine ⟨52786651108336422562957297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70382201477781896750609729 52786651108336422562957297)
                  ·
                    refine ⟨39589988331252316922217973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52786651108336422562957297 39589988331252316922217973)
                    ·
                      refine ⟨3711561406054904711457935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39589988331252316922217973 3711561406054904711457935)
                      ·
                        rfl

theorem cell23_7228240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 5].length) (baseStart_7228240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228240 prefixEnd_7228240 := by exact prefixLift 7228240
  have htrace : WordTrace (prefixWord ++ tailWord_7228240) baseStart_7228240 baseEnd_7228240 := by
    simpa [prefixWord, tailWord_7228240, baseEnd_7228240] using wordTrace_append hprefix tailTrace_7228240
  have hstable : (prefixWord ++ tailWord_7228240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228240).length < 2 ^ (prefixWord ++ tailWord_7228240).sum := by decide
  have hdescent : baseEnd_7228240 < baseStart_7228240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228278 : List Nat := [5, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3]
def baseStart_7228278 : Nat := 118140960795 + 7228278 * 2 ^ 59
def prefixEnd_7228278 : Nat := 4983230072969 + 3 ^ 40 * 7228278 * 2
def baseEnd_7228278 : Nat := 3711580918319775562782761

theorem tailTrace_7228278 : CollatzResearch.WordTrace tailWord_7228278 prefixEnd_7228278 3711580918319775562782761 := by
  unfold tailWord_7228278
  simp only [CollatzResearch.WordTrace]
  refine ⟨16477309831699423277788343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175757971538127181629742325 16477309831699423277788343)
  ·
    refine ⟨24715964747549134916682515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16477309831699423277788343 24715964747549134916682515)
    ·
      refine ⟨37073947121323702375023773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24715964747549134916682515 37073947121323702375023773)
      ·
        refine ⟨13902730170496388390633915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37073947121323702375023773 13902730170496388390633915)
        ·
          refine ⟨20854095255744582585950873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13902730170496388390633915 20854095255744582585950873)
          ·
            refine ⟨15640571441808436939463155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20854095255744582585950873 15640571441808436939463155)
            ·
              refine ⟨23460857162712655409194733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15640571441808436939463155 23460857162712655409194733)
              ·
                refine ⟨8797821436017245778448025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23460857162712655409194733 8797821436017245778448025)
                ·
                  refine ⟨6598366077012934333836019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8797821436017245778448025 6598366077012934333836019)
                  ·
                    refine ⟨9897549115519401500754029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6598366077012934333836019 9897549115519401500754029)
                    ·
                      refine ⟨3711580918319775562782761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9897549115519401500754029 3711580918319775562782761)
                      ·
                        rfl

theorem cell23_7228278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_7228278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228278 prefixEnd_7228278 := by exact prefixLift 7228278
  have htrace : WordTrace (prefixWord ++ tailWord_7228278) baseStart_7228278 baseEnd_7228278 := by
    simpa [prefixWord, tailWord_7228278, baseEnd_7228278] using wordTrace_append hprefix tailTrace_7228278
  have hstable : (prefixWord ++ tailWord_7228278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228278).length < 2 ^ (prefixWord ++ tailWord_7228278).sum := by decide
  have hdescent : baseEnd_7228278 < baseStart_7228278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228324 : List Nat := [2, 3, 1, 2, 1, 2, 3, 4, 5]
def baseStart_7228324 : Nat := 118140960795 + 7228324 * 2 ^ 59
def prefixEnd_7228324 : Nat := 4983230072969 + 3 ^ 40 * 7228324 * 2
def baseEnd_7228324 : Nat := 412400504269986931423061

theorem tailTrace_7228324 : CollatzResearch.WordTrace tailWord_7228324 prefixEnd_7228324 412400504269986931423061 := by
  unfold tailWord_7228324
  simp only [CollatzResearch.WordTrace]
  refine ⟨131819317532512061150394013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175759090043349414867192017 131819317532512061150394013)
  ·
    refine ⟨49432244074692022931397755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131819317532512061150394013 49432244074692022931397755)
    ·
      refine ⟨74148366112038034397096633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49432244074692022931397755 74148366112038034397096633)
      ·
        refine ⟨55611274584028525797822475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74148366112038034397096633 55611274584028525797822475)
        ·
          refine ⟨83416911876042788696733713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55611274584028525797822475 83416911876042788696733713)
          ·
            refine ⟨62562683907032091522550285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83416911876042788696733713 62562683907032091522550285)
            ·
              refine ⟨23461006465137034320956357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62562683907032091522550285 23461006465137034320956357)
              ·
                refine ⟨4398938712213193935179317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23461006465137034320956357 4398938712213193935179317)
                ·
                  refine ⟨412400504269986931423061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4398938712213193935179317 412400504269986931423061)
                  ·
                    rfl

theorem cell23_7228324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 4, 5].length) (baseStart_7228324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228324 prefixEnd_7228324 := by exact prefixLift 7228324
  have htrace : WordTrace (prefixWord ++ tailWord_7228324) baseStart_7228324 baseEnd_7228324 := by
    simpa [prefixWord, tailWord_7228324, baseEnd_7228324] using wordTrace_append hprefix tailTrace_7228324
  have hstable : (prefixWord ++ tailWord_7228324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228324).length < 2 ^ (prefixWord ++ tailWord_7228324).sum := by decide
  have hdescent : baseEnd_7228324 < baseStart_7228324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228387 : List Nat := [1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 6]
def baseStart_7228387 : Nat := 118140960795 + 7228387 * 2 ^ 59
def prefixEnd_7228387 : Nat := 4983230072969 + 3 ^ 40 * 7228387 * 2
def baseEnd_7228387 : Nat := 3711636887711115636319759

theorem tailTrace_7228387 : CollatzResearch.WordTrace tailWord_7228387 prefixEnd_7228387 3711636887711115636319759 := by
  unfold tailWord_7228387
  simp only [CollatzResearch.WordTrace]
  refine ⟨263640932863795884060331415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175760621909197256040220943 263640932863795884060331415)
  ·
    refine ⟨395461399295693826090497123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263640932863795884060331415 395461399295693826090497123)
    ·
      refine ⟨593192098943540739135745685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395461399295693826090497123 593192098943540739135745685)
      ·
        refine ⟨27805879637978472146988079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 593192098943540739135745685 27805879637978472146988079)
        ·
          refine ⟨41708819456967708220482119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27805879637978472146988079 41708819456967708220482119)
          ·
            refine ⟨62563229185451562330723179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41708819456967708220482119 62563229185451562330723179)
            ·
              refine ⟨93844843778177343496084769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62563229185451562330723179 93844843778177343496084769)
              ·
                refine ⟨70383632833633007622063577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93844843778177343496084769 70383632833633007622063577)
                ·
                  refine ⟨52787724625224755716547683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70383632833633007622063577 52787724625224755716547683)
                  ·
                    refine ⟨79181586937837133574821525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52787724625224755716547683 79181586937837133574821525)
                    ·
                      refine ⟨3711636887711115636319759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79181586937837133574821525 3711636887711115636319759)
                      ·
                        rfl

theorem cell23_7228387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_7228387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228387 prefixEnd_7228387 := by exact prefixLift 7228387
  have htrace : WordTrace (prefixWord ++ tailWord_7228387) baseStart_7228387 baseEnd_7228387 := by
    simpa [prefixWord, tailWord_7228387, baseEnd_7228387] using wordTrace_append hprefix tailTrace_7228387
  have hstable : (prefixWord ++ tailWord_7228387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228387).length < 2 ^ (prefixWord ++ tailWord_7228387).sum := by decide
  have hdescent : baseEnd_7228387 < baseStart_7228387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228391 : List Nat := [1, 1, 5, 2, 2, 1, 2, 1, 2, 4, 2]
def baseStart_7228391 : Nat := 118140960795 + 7228391 * 2 ^ 59
def prefixEnd_7228391 : Nat := 4983230072969 + 3 ^ 40 * 7228391 * 2
def baseEnd_7228391 : Nat := 3711638941633733620669741

theorem tailTrace_7228391 : CollatzResearch.WordTrace tailWord_7228391 prefixEnd_7228391 3711638941633733620669741 := by
  unfold tailWord_7228391
  simp only [CollatzResearch.WordTrace]
  refine ⟨263641078755781392743477027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175760719170520928495651351 263641078755781392743477027)
  ·
    refine ⟨395461618133672089115215541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263641078755781392743477027 395461618133672089115215541)
    ·
      refine ⟨37074526700031758354551457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 395461618133672089115215541 37074526700031758354551457)
      ·
        refine ⟨27805895025023818765913593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37074526700031758354551457 27805895025023818765913593)
        ·
          refine ⟨20854421268767864074435195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27805895025023818765913593 20854421268767864074435195)
          ·
            refine ⟨31281631903151796111652793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20854421268767864074435195 31281631903151796111652793)
            ·
              refine ⟨23461223927363847083739595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31281631903151796111652793 23461223927363847083739595)
              ·
                refine ⟨35191835891045770625609393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23461223927363847083739595 35191835891045770625609393)
                ·
                  refine ⟨26393876918284327969207045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35191835891045770625609393 26393876918284327969207045)
                  ·
                    refine ⟨4948851922178311494226321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26393876918284327969207045 4948851922178311494226321)
                    ·
                      refine ⟨3711638941633733620669741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4948851922178311494226321 3711638941633733620669741)
                      ·
                        rfl

theorem cell23_7228391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_7228391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228391 prefixEnd_7228391 := by exact prefixLift 7228391
  have htrace : WordTrace (prefixWord ++ tailWord_7228391) baseStart_7228391 baseEnd_7228391 := by
    simpa [prefixWord, tailWord_7228391, baseEnd_7228391] using wordTrace_append hprefix tailTrace_7228391
  have hstable : (prefixWord ++ tailWord_7228391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228391).length < 2 ^ (prefixWord ++ tailWord_7228391).sum := by decide
  have hdescent : baseEnd_7228391 < baseStart_7228391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228394 : List Nat := [3, 1, 3, 1, 2, 2, 1, 2, 1, 4, 3]
def baseStart_7228394 : Nat := 118140960795 + 7228394 * 2 ^ 59
def prefixEnd_7228394 : Nat := 4983230072969 + 3 ^ 40 * 7228394 * 2
def baseEnd_7228394 : Nat := 3711640482075697108932227

theorem tailTrace_7228394 : CollatzResearch.WordTrace tailWord_7228394 prefixEnd_7228394 3711640482075697108932227 := by
  unfold tailWord_7228394
  simp only [CollatzResearch.WordTrace]
  refine ⟨65910297043692631063959059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175760792116513682837224157 65910297043692631063959059)
  ·
    refine ⟨98865445565538946595938589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65910297043692631063959059 98865445565538946595938589)
    ·
      refine ⟨37074542087077104973476971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98865445565538946595938589 37074542087077104973476971)
      ·
        refine ⟨55611813130615657460215457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37074542087077104973476971 55611813130615657460215457)
        ·
          refine ⟨41708859847961743095161593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55611813130615657460215457 41708859847961743095161593)
          ·
            refine ⟨31281644885971307321371195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41708859847961743095161593 31281644885971307321371195)
            ·
              refine ⟨46922467328956960982056793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31281644885971307321371195 46922467328956960982056793)
              ·
                refine ⟨35191850496717720736542595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46922467328956960982056793 35191850496717720736542595)
                ·
                  refine ⟨52787775745076581104813893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35191850496717720736542595 52787775745076581104813893)
                  ·
                    refine ⟨9897707952201858957152605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52787775745076581104813893 9897707952201858957152605)
                    ·
                      refine ⟨3711640482075697108932227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9897707952201858957152605 3711640482075697108932227)
                      ·
                        rfl

theorem cell23_7228394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_7228394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228394 prefixEnd_7228394 := by exact prefixLift 7228394
  have htrace : WordTrace (prefixWord ++ tailWord_7228394) baseStart_7228394 baseEnd_7228394 := by
    simpa [prefixWord, tailWord_7228394, baseEnd_7228394] using wordTrace_append hprefix tailTrace_7228394
  have hstable : (prefixWord ++ tailWord_7228394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228394).length < 2 ^ (prefixWord ++ tailWord_7228394).sum := by decide
  have hdescent : baseEnd_7228394 < baseStart_7228394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228441 : List Nat := [1, 2, 1, 2, 1, 1, 7, 1, 3, 1, 3]
def baseStart_7228441 : Nat := 118140960795 + 7228441 * 2 ^ 59
def prefixEnd_7228441 : Nat := 4983230072969 + 3 ^ 40 * 7228441 * 2
def baseEnd_7228441 : Nat := 3711664615666458425044511

theorem tailTrace_7228441 : CollatzResearch.WordTrace tailWord_7228441 prefixEnd_7228441 3711664615666458425044511 := by
  unfold tailWord_7228441
  simp only [CollatzResearch.WordTrace]
  refine ⟨263642902405600251282797177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175761934937066834188531451 263642902405600251282797177)
  ·
    refine ⟨197732176804200188462097883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263642902405600251282797177 197732176804200188462097883)
    ·
      refine ⟨296598265206300282693146825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197732176804200188462097883 296598265206300282693146825)
      ·
        refine ⟨222448698904725212019860119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296598265206300282693146825 222448698904725212019860119)
        ·
          refine ⟨333673048357087818029790179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222448698904725212019860119 333673048357087818029790179)
          ·
            refine ⟨500509572535631727044685269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333673048357087818029790179 500509572535631727044685269)
            ·
              refine ⟨11730693106303868602609811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 500509572535631727044685269 11730693106303868602609811)
              ·
                refine ⟨17596039659455802903914717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11730693106303868602609811 17596039659455802903914717)
                ·
                  refine ⟨6598514872295926088968019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17596039659455802903914717 6598514872295926088968019)
                  ·
                    refine ⟨9897772308443889133452029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6598514872295926088968019 9897772308443889133452029)
                    ·
                      refine ⟨3711664615666458425044511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9897772308443889133452029 3711664615666458425044511)
                      ·
                        rfl

theorem cell23_7228441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 3, 1, 3].length) (baseStart_7228441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228441 prefixEnd_7228441 := by exact prefixLift 7228441
  have htrace : WordTrace (prefixWord ++ tailWord_7228441) baseStart_7228441 baseEnd_7228441 := by
    simpa [prefixWord, tailWord_7228441, baseEnd_7228441] using wordTrace_append hprefix tailTrace_7228441
  have hstable : (prefixWord ++ tailWord_7228441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228441).length < 2 ^ (prefixWord ++ tailWord_7228441).sum := by decide
  have hdescent : baseEnd_7228441 < baseStart_7228441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228464 : List Nat := [2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 4]
def baseStart_7228464 : Nat := 118140960795 + 7228464 * 2 ^ 59
def prefixEnd_7228464 : Nat := 4983230072969 + 3 ^ 40 * 7228464 * 2
def baseEnd_7228464 : Nat := 3711676425721511835056905

theorem tailTrace_7228464 : CollatzResearch.WordTrace tailWord_7228464 prefixEnd_7228464 3711676425721511835056905 := by
  unfold tailWord_7228464
  simp only [CollatzResearch.WordTrace]
  refine ⟨131821870642258463105442223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175762494189677950807256297 131821870642258463105442223)
  ·
    refine ⟨197732805963387694658163335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131821870642258463105442223 197732805963387694658163335)
    ·
      refine ⟨296599208945081541987245003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197732805963387694658163335 296599208945081541987245003)
      ·
        refine ⟨444898813417622312980867505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296599208945081541987245003 444898813417622312980867505)
        ·
          refine ⟨333674110063216734735650629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444898813417622312980867505 333674110063216734735650629)
          ·
            refine ⟨62563895636853137762934493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 333674110063216734735650629 62563895636853137762934493)
            ·
              refine ⟨23461460863819926661100435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62563895636853137762934493 23461460863819926661100435)
              ·
                refine ⟨35192191295729889991650653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23461460863819926661100435 35192191295729889991650653)
                ·
                  refine ⟨13197071735898708746868995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35192191295729889991650653 13197071735898708746868995)
                  ·
                    refine ⟨19795607603848063120303493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13197071735898708746868995 19795607603848063120303493)
                    ·
                      refine ⟨3711676425721511835056905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19795607603848063120303493 3711676425721511835056905)
                      ·
                        rfl

theorem cell23_7228464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 4].length) (baseStart_7228464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228464 prefixEnd_7228464 := by exact prefixLift 7228464
  have htrace : WordTrace (prefixWord ++ tailWord_7228464) baseStart_7228464 baseEnd_7228464 := by
    simpa [prefixWord, tailWord_7228464, baseEnd_7228464] using wordTrace_append hprefix tailTrace_7228464
  have hstable : (prefixWord ++ tailWord_7228464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228464).length < 2 ^ (prefixWord ++ tailWord_7228464).sum := by decide
  have hdescent : baseEnd_7228464 < baseStart_7228464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228474 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 6, 4]
def baseStart_7228474 : Nat := 118140960795 + 7228474 * 2 ^ 59
def prefixEnd_7228474 : Nat := 4983230072969 + 3 ^ 40 * 7228474 * 2
def baseEnd_7228474 : Nat := 1237227186842685598643953

theorem tailTrace_7228474 : CollatzResearch.WordTrace tailWord_7228474 prefixEnd_7228474 1237227186842685598643953 := by
  unfold tailWord_7228474
  simp only [CollatzResearch.WordTrace]
  refine ⟨65911026503620174479687119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175762737342987131945832317 65911026503620174479687119)
  ·
    refine ⟨98866539755430261719530679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65911026503620174479687119 98866539755430261719530679)
    ·
      refine ⟨148299809633145392579296019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98866539755430261719530679 148299809633145392579296019)
      ·
        refine ⟨222449714449718088868944029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148299809633145392579296019 222449714449718088868944029)
        ·
          refine ⟨83418642918644283325854011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222449714449718088868944029 83418642918644283325854011)
          ·
            refine ⟨125127964377966424988781017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83418642918644283325854011 125127964377966424988781017)
            ·
              refine ⟨93845973283474818741585763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125127964377966424988781017 93845973283474818741585763)
              ·
                refine ⟨140768959925212228112378645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93845973283474818741585763 140768959925212228112378645)
                ·
                  refine ⟨6598544996494323192767749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 140768959925212228112378645 6598544996494323192767749)
                  ·
                    refine ⟨1237227186842685598643953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6598544996494323192767749 1237227186842685598643953)
                    ·
                      rfl

theorem cell23_7228474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 6, 4].length) (baseStart_7228474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228474 prefixEnd_7228474 := by exact prefixLift 7228474
  have htrace : WordTrace (prefixWord ++ tailWord_7228474) baseStart_7228474 baseEnd_7228474 := by
    simpa [prefixWord, tailWord_7228474, baseEnd_7228474] using wordTrace_append hprefix tailTrace_7228474
  have hstable : (prefixWord ++ tailWord_7228474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228474).length < 2 ^ (prefixWord ++ tailWord_7228474).sum := by decide
  have hdescent : baseEnd_7228474 < baseStart_7228474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228487 : List Nat := [1, 1, 4, 1, 3, 13]
def baseStart_7228487 : Nat := 118140960795 + 7228487 * 2 ^ 59
def prefixEnd_7228487 : Nat := 4983230072969 + 3 ^ 40 * 7228487 * 2
def baseEnd_7228487 : Nat := 15274437184265700596993

theorem tailTrace_7228487 : CollatzResearch.WordTrace tailWord_7228487 prefixEnd_7228487 15274437184265700596993 := by
  unfold tailWord_7228487
  simp only [CollatzResearch.WordTrace]
  refine ⟨263644580163433601138971715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175763053442289067425981143 263644580163433601138971715)
  ·
    refine ⟨395466870245150401708457573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263644580163433601138971715 395466870245150401708457573)
    ·
      refine ⟨74150038170965700320335795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 395466870245150401708457573 74150038170965700320335795)
      ·
        refine ⟨111225057256448550480503693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74150038170965700320335795 111225057256448550480503693)
        ·
          refine ⟨41709396471168206430188885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111225057256448550480503693 41709396471168206430188885)
          ·
            refine ⟨15274437184265700596993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 41709396471168206430188885 15274437184265700596993)
            ·
              rfl

theorem cell23_7228487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 13].length) (baseStart_7228487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228487 prefixEnd_7228487 := by exact prefixLift 7228487
  have htrace : WordTrace (prefixWord ++ tailWord_7228487) baseStart_7228487 baseEnd_7228487 := by
    simpa [prefixWord, tailWord_7228487, baseEnd_7228487] using wordTrace_append hprefix tailTrace_7228487
  have hstable : (prefixWord ++ tailWord_7228487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228487).length < 2 ^ (prefixWord ++ tailWord_7228487).sum := by decide
  have hdescent : baseEnd_7228487 < baseStart_7228487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228494 : List Nat := [4, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4]
def baseStart_7228494 : Nat := 118140960795 + 7228494 * 2 ^ 59
def prefixEnd_7228494 : Nat := 4983230072969 + 3 ^ 40 * 7228494 * 2
def baseEnd_7228494 : Nat := 3711691830141146717681767

theorem tailTrace_7228494 : CollatzResearch.WordTrace tailWord_7228494 prefixEnd_7228494 3711691830141146717681767 := by
  unfold tailWord_7228494
  simp only [CollatzResearch.WordTrace]
  refine ⟨32955604434301030166809567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175763223649605494222984357 32955604434301030166809567)
  ·
    refine ⟨49433406651451545250214351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32955604434301030166809567 49433406651451545250214351)
    ·
      refine ⟨74150109977177317875321527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49433406651451545250214351 74150109977177317875321527)
      ·
        refine ⟨111225164965765976812982291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74150109977177317875321527 111225164965765976812982291)
        ·
          refine ⟨166837747448648965219473437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111225164965765976812982291 166837747448648965219473437)
          ·
            refine ⟨62564155293243361957302539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166837747448648965219473437 62564155293243361957302539)
            ·
              refine ⟨93846232939865042935953809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62564155293243361957302539 93846232939865042935953809)
              ·
                refine ⟨70384674704898782201965357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93846232939865042935953809 70384674704898782201965357)
                ·
                  refine ⟨26394253014337043325737009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70384674704898782201965357 26394253014337043325737009)
                  ·
                    refine ⟨19795689760752782494302757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26394253014337043325737009 19795689760752782494302757)
                    ·
                      refine ⟨3711691830141146717681767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19795689760752782494302757 3711691830141146717681767)
                      ·
                        rfl

theorem cell23_7228494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_7228494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228494 prefixEnd_7228494 := by exact prefixLift 7228494
  have htrace : WordTrace (prefixWord ++ tailWord_7228494) baseStart_7228494 baseEnd_7228494 := by
    simpa [prefixWord, tailWord_7228494, baseEnd_7228494] using wordTrace_append hprefix tailTrace_7228494
  have hstable : (prefixWord ++ tailWord_7228494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228494).length < 2 ^ (prefixWord ++ tailWord_7228494).sum := by decide
  have hdescent : baseEnd_7228494 < baseStart_7228494 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228542 : List Nat := [4, 2, 4, 1, 1, 1, 1, 1, 4, 4]
def baseStart_7228542 : Nat := 118140960795 + 7228542 * 2 ^ 59
def prefixEnd_7228542 : Nat := 4983230072969 + 3 ^ 40 * 7228542 * 2
def baseEnd_7228542 : Nat := 1237238825737520843293849

theorem tailTrace_7228542 : CollatzResearch.WordTrace tailWord_7228542 prefixEnd_7228542 1237238825737520843293849 := by
  unfold tailWord_7228542
  simp only [CollatzResearch.WordTrace]
  refine ⟨32955823272279293191527985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175764390785489563688149253 32955823272279293191527985)
  ·
    refine ⟨24716867454209469893645989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32955823272279293191527985 24716867454209469893645989)
    ·
      refine ⟨4634412647664275605058623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24716867454209469893645989 4634412647664275605058623)
      ·
        refine ⟨6951618971496413407587935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4634412647664275605058623 6951618971496413407587935)
        ·
          refine ⟨10427428457244620111381903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6951618971496413407587935 10427428457244620111381903)
          ·
            refine ⟨15641142685866930167072855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10427428457244620111381903 15641142685866930167072855)
            ·
              refine ⟨23461714028800395250609283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15641142685866930167072855 23461714028800395250609283)
              ·
                refine ⟨35192571043200592875913925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23461714028800395250609283 35192571043200592875913925)
                ·
                  refine ⟨6598607070600111164233861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35192571043200592875913925 6598607070600111164233861)
                  ·
                    refine ⟨1237238825737520843293849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6598607070600111164233861 1237238825737520843293849)
                    ·
                      rfl

theorem cell23_7228542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_7228542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228542 prefixEnd_7228542 := by exact prefixLift 7228542
  have htrace : WordTrace (prefixWord ++ tailWord_7228542) baseStart_7228542 baseEnd_7228542 := by
    simpa [prefixWord, tailWord_7228542, baseEnd_7228542] using wordTrace_append hprefix tailTrace_7228542
  have hstable : (prefixWord ++ tailWord_7228542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228542).length < 2 ^ (prefixWord ++ tailWord_7228542).sum := by decide
  have hdescent : baseEnd_7228542 < baseStart_7228542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228548 : List Nat := [2, 3, 2, 1, 2, 3, 1, 1, 4, 1, 3]
def baseStart_7228548 : Nat := 118140960795 + 7228548 * 2 ^ 59
def prefixEnd_7228548 : Nat := 4983230072969 + 3 ^ 40 * 7228548 * 2
def baseEnd_7228548 : Nat := 3711719558096489506406519

theorem tailTrace_7228548 : CollatzResearch.WordTrace tailWord_7228548 prefixEnd_7228548 3711719558096489506406519 := by
  unfold tailWord_7228548
  simp only [CollatzResearch.WordTrace]
  refine ⟨131823402508106304278471149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175764536677475072371294865 131823402508106304278471149)
  ·
    refine ⟨49433775940539864104426681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131823402508106304278471149 49433775940539864104426681)
    ·
      refine ⟨37075331955404898078320011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49433775940539864104426681 37075331955404898078320011)
      ·
        refine ⟨55612997933107347117480017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37075331955404898078320011 55612997933107347117480017)
        ·
          refine ⟨41709748449830510338110013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55612997933107347117480017 41709748449830510338110013)
          ·
            refine ⟨15641155668686441376791255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41709748449830510338110013 15641155668686441376791255)
            ·
              refine ⟨23461733503029662065186883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15641155668686441376791255 23461733503029662065186883)
              ·
                refine ⟨35192600254544493097780325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23461733503029662065186883 35192600254544493097780325)
                ·
                  refine ⟨6598612547727092455833811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35192600254544493097780325 6598612547727092455833811)
                  ·
                    refine ⟨9897918821590638683750717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6598612547727092455833811 9897918821590638683750717)
                    ·
                      refine ⟨3711719558096489506406519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9897918821590638683750717 3711719558096489506406519)
                      ·
                        rfl

theorem cell23_7228548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_7228548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228548 prefixEnd_7228548 := by exact prefixLift 7228548
  have htrace : WordTrace (prefixWord ++ tailWord_7228548) baseStart_7228548 baseEnd_7228548 := by
    simpa [prefixWord, tailWord_7228548, baseEnd_7228548] using wordTrace_append hprefix tailTrace_7228548
  have hstable : (prefixWord ++ tailWord_7228548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228548).length < 2 ^ (prefixWord ++ tailWord_7228548).sum := by decide
  have hdescent : baseEnd_7228548 < baseStart_7228548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228622 : List Nat := [4, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2]
def baseStart_7228622 : Nat := 118140960795 + 7228622 * 2 ^ 59
def prefixEnd_7228622 : Nat := 4983230072969 + 3 ^ 40 * 7228622 * 2
def baseEnd_7228622 : Nat := 3711757555664922216881179

theorem tailTrace_7228622 : CollatzResearch.WordTrace tailWord_7228622 prefixEnd_7228622 3711757555664922216881179 := by
  unfold tailWord_7228622
  simp only [CollatzResearch.WordTrace]
  refine ⟨32956188002243064899392015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175766336011963012796757413 32956188002243064899392015)
  ·
    refine ⟨49434282003364597349088023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32956188002243064899392015 49434282003364597349088023)
    ·
      refine ⟨74151423005046896023632035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49434282003364597349088023 74151423005046896023632035)
      ·
        refine ⟨111227134507570344035448053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74151423005046896023632035 111227134507570344035448053)
        ·
          refine ⟨10427543860084719753323255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111227134507570344035448053 10427543860084719753323255)
          ·
            refine ⟨15641315790127079629984883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10427543860084719753323255 15641315790127079629984883)
            ·
              refine ⟨23461973685190619444977325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15641315790127079629984883 23461973685190619444977325)
              ·
                refine ⟨8798240131946482291866497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23461973685190619444977325 8798240131946482291866497)
                ·
                  refine ⟨6598680098959861718899873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8798240131946482291866497 6598680098959861718899873)
                  ·
                    refine ⟨4949010074219896289174905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6598680098959861718899873 4949010074219896289174905)
                    ·
                      refine ⟨3711757555664922216881179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4949010074219896289174905 3711757555664922216881179)
                      ·
                        rfl

theorem cell23_7228622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2].length) (baseStart_7228622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228622 prefixEnd_7228622 := by exact prefixLift 7228622
  have htrace : WordTrace (prefixWord ++ tailWord_7228622) baseStart_7228622 baseEnd_7228622 := by
    simpa [prefixWord, tailWord_7228622, baseEnd_7228622] using wordTrace_append hprefix tailTrace_7228622
  have hstable : (prefixWord ++ tailWord_7228622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228622).length < 2 ^ (prefixWord ++ tailWord_7228622).sum := by decide
  have hdescent : baseEnd_7228622 < baseStart_7228622 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228634 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 7]
def baseStart_7228634 : Nat := 118140960795 + 7228634 * 2 ^ 59
def prefixEnd_7228634 : Nat := 4983230072969 + 3 ^ 40 * 7228634 * 2
def baseEnd_7228634 : Nat := 3711763717432776169931123

theorem tailTrace_7228634 : CollatzResearch.WordTrace tailWord_7228634 prefixEnd_7228634 3711763717432776169931123 := by
  unfold tailWord_7228634
  simp only [CollatzResearch.WordTrace]
  refine ⟨65912485423475261311143239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175766627795934030163048637 65912485423475261311143239)
  ·
    refine ⟨98868728135212891966714859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65912485423475261311143239 98868728135212891966714859)
    ·
      refine ⟨148303092202819337950072289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98868728135212891966714859 148303092202819337950072289)
      ·
        refine ⟨111227319152114503462554217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148303092202819337950072289 111227319152114503462554217)
        ·
          refine ⟨83420489364085877596915663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111227319152114503462554217 83420489364085877596915663)
          ·
            refine ⟨125130734046128816395373495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83420489364085877596915663 125130734046128816395373495)
            ·
              refine ⟨187696101069193224593060243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125130734046128816395373495 187696101069193224593060243)
              ·
                refine ⟨281544151603789836889590365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187696101069193224593060243 281544151603789836889590365)
                ·
                  refine ⟨105579056851421188833596387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 281544151603789836889590365 105579056851421188833596387)
                  ·
                    refine ⟨158368585277131783250394581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105579056851421188833596387 158368585277131783250394581)
                    ·
                      refine ⟨3711763717432776169931123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 158368585277131783250394581 3711763717432776169931123)
                      ·
                        rfl

theorem cell23_7228634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_7228634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228634 prefixEnd_7228634 := by exact prefixLift 7228634
  have htrace : WordTrace (prefixWord ++ tailWord_7228634) baseStart_7228634 baseEnd_7228634 := by
    simpa [prefixWord, tailWord_7228634, baseEnd_7228634] using wordTrace_append hprefix tailTrace_7228634
  have hstable : (prefixWord ++ tailWord_7228634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228634).length < 2 ^ (prefixWord ++ tailWord_7228634).sum := by decide
  have hdescent : baseEnd_7228634 < baseStart_7228634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228641 : List Nat := [1, 2, 3, 1, 3, 2, 1, 3, 2, 5]
def baseStart_7228641 : Nat := 118140960795 + 7228641 * 2 ^ 59
def prefixEnd_7228641 : Nat := 4983230072969 + 3 ^ 40 * 7228641 * 2
def baseEnd_7228641 : Nat := 1237255770599119214181197

theorem tailTrace_7228641 : CollatzResearch.WordTrace tailWord_7228641 prefixEnd_7228641 1237255770599119214181197 := by
  unfold tailWord_7228641
  simp only [CollatzResearch.WordTrace]
  refine ⟨263650197004875685440077777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175766798003250456960051851 263650197004875685440077777)
  ·
    refine ⟨197737647753656764080058333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263650197004875685440077777 197737647753656764080058333)
    ·
      refine ⟨74151617907621286530021875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197737647753656764080058333 74151617907621286530021875)
      ·
        refine ⟨111227426861431929795032813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74151617907621286530021875 111227426861431929795032813)
        ·
          refine ⟨41710285073036973673137305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111227426861431929795032813 41710285073036973673137305)
          ·
            refine ⟨31282713804777730254852979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41710285073036973673137305 31282713804777730254852979)
            ·
              refine ⟨46924070707166595382279469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31282713804777730254852979 46924070707166595382279469)
              ·
                refine ⟨17596526515187473268354801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46924070707166595382279469 17596526515187473268354801)
                ·
                  refine ⟨13197394886390604951266101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17596526515187473268354801 13197394886390604951266101)
                  ·
                    refine ⟨1237255770599119214181197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13197394886390604951266101 1237255770599119214181197)
                    ·
                      rfl

theorem cell23_7228641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_7228641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228641 prefixEnd_7228641 := by exact prefixLift 7228641
  have htrace : WordTrace (prefixWord ++ tailWord_7228641) baseStart_7228641 baseEnd_7228641 := by
    simpa [prefixWord, tailWord_7228641, baseEnd_7228641] using wordTrace_append hprefix tailTrace_7228641
  have hstable : (prefixWord ++ tailWord_7228641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228641).length < 2 ^ (prefixWord ++ tailWord_7228641).sum := by decide
  have hdescent : baseEnd_7228641 < baseStart_7228641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228681 : List Nat := [1, 2, 1, 1, 3, 3, 2, 2, 1, 4, 3]
def baseStart_7228681 : Nat := 118140960795 + 7228681 * 2 ^ 59
def prefixEnd_7228681 : Nat := 4983230072969 + 3 ^ 40 * 7228681 * 2
def baseEnd_7228681 : Nat := 3711787851023537486043407

theorem tailTrace_7228681 : CollatzResearch.WordTrace tailWord_7228681 prefixEnd_7228681 3711787851023537486043407 := by
  unfold tailWord_7228681
  simp only [CollatzResearch.WordTrace]
  refine ⟨263651655924730772271533897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175767770616487181514355931 263651655924730772271533897)
  ·
    refine ⟨197738741943548079203650423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263651655924730772271533897 197738741943548079203650423)
    ·
      refine ⟨296608112915322118805475635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197738741943548079203650423 296608112915322118805475635)
      ·
        refine ⟨444912169372983178208213453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296608112915322118805475635 444912169372983178208213453)
        ·
          refine ⟨166842063514868691828080045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 444912169372983178208213453 166842063514868691828080045)
          ·
            refine ⟨62565773818075759435530017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166842063514868691828080045 62565773818075759435530017)
            ·
              refine ⟨46924330363556819576647513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62565773818075759435530017 46924330363556819576647513)
              ·
                refine ⟨35193247772667614682485635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46924330363556819576647513 35193247772667614682485635)
                ·
                  refine ⟨52789871659001422023728453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35193247772667614682485635 52789871659001422023728453)
                  ·
                    refine ⟨9898100936062766629449085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52789871659001422023728453 9898100936062766629449085)
                    ·
                      refine ⟨3711787851023537486043407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9898100936062766629449085 3711787851023537486043407)
                      ·
                        rfl

theorem cell23_7228681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 4, 3].length) (baseStart_7228681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228681 prefixEnd_7228681 := by exact prefixLift 7228681
  have htrace : WordTrace (prefixWord ++ tailWord_7228681) baseStart_7228681 baseEnd_7228681 := by
    simpa [prefixWord, tailWord_7228681, baseEnd_7228681] using wordTrace_append hprefix tailTrace_7228681
  have hstable : (prefixWord ++ tailWord_7228681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228681).length < 2 ^ (prefixWord ++ tailWord_7228681).sum := by decide
  have hdescent : baseEnd_7228681 < baseStart_7228681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228698 : List Nat := [3, 1, 1, 3, 3, 2, 1, 1, 1, 4, 3]
def baseStart_7228698 : Nat := 118140960795 + 7228698 * 2 ^ 59
def prefixEnd_7228698 : Nat := 4983230072969 + 3 ^ 40 * 7228698 * 2
def baseEnd_7228698 : Nat := 3711796580194663919530829

theorem tailTrace_7228698 : CollatzResearch.WordTrace tailWord_7228698 prefixEnd_7228698 3711796580194663919530829 := by
  unfold tailWord_7228698
  simp only [CollatzResearch.WordTrace]
  refine ⟨65913068991417296043725687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175768183977112789449935165 65913068991417296043725687)
  ·
    refine ⟨98869603487125944065588531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65913068991417296043725687 98869603487125944065588531)
    ·
      refine ⟨148304405230688916098382797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98869603487125944065588531 148304405230688916098382797)
      ·
        refine ⟨55614151961508343536893549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148304405230688916098382797 55614151961508343536893549)
        ·
          refine ⟨20855306985565628826335081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55614151961508343536893549 20855306985565628826335081)
          ·
            refine ⟨15641480239174221619751311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20855306985565628826335081 15641480239174221619751311)
            ·
              refine ⟨23462220358761332429626967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15641480239174221619751311 23462220358761332429626967)
              ·
                refine ⟨35193330538141998644440451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23462220358761332429626967 35193330538141998644440451)
                ·
                  refine ⟨52789995807212997966660677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35193330538141998644440451 52789995807212997966660677)
                  ·
                    refine ⟨9898124213852437118748877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52789995807212997966660677 9898124213852437118748877)
                    ·
                      refine ⟨3711796580194663919530829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9898124213852437118748877 3711796580194663919530829)
                      ·
                        rfl

theorem cell23_7228698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_7228698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228698 prefixEnd_7228698 := by exact prefixLift 7228698
  have htrace : WordTrace (prefixWord ++ tailWord_7228698) baseStart_7228698 baseEnd_7228698 := by
    simpa [prefixWord, tailWord_7228698, baseEnd_7228698] using wordTrace_append hprefix tailTrace_7228698
  have hstable : (prefixWord ++ tailWord_7228698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228698).length < 2 ^ (prefixWord ++ tailWord_7228698).sum := by decide
  have hdescent : baseEnd_7228698 < baseStart_7228698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228721 : List Nat := [1, 2, 2, 3, 3, 1, 1, 1, 1, 2, 6]
def baseStart_7228721 : Nat := 118140960795 + 7228721 * 2 ^ 59
def prefixEnd_7228721 : Nat := 4983230072969 + 3 ^ 40 * 7228721 * 2
def baseEnd_7228721 : Nat := 3711808390249717329543223

theorem tailTrace_7228721 : CollatzResearch.WordTrace tailWord_7228721 prefixEnd_7228721 3711808390249717329543223 := by
  unfold tailWord_7228721
  simp only [CollatzResearch.WordTrace]
  refine ⟨263653114844585859102990017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175768743229723906068660011 263653114844585859102990017)
  ·
    refine ⟨197739836133439394327242513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263653114844585859102990017 197739836133439394327242513)
    ·
      refine ⟨148304877100079545745431885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197739836133439394327242513 148304877100079545745431885)
      ·
        refine ⟨55614328912529829654536957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148304877100079545745431885 55614328912529829654536957)
        ·
          refine ⟨20855373342198686120451359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55614328912529829654536957 20855373342198686120451359)
          ·
            refine ⟨31283060013298029180677039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20855373342198686120451359 31283060013298029180677039)
            ·
              refine ⟨46924590019947043771015559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31283060013298029180677039 46924590019947043771015559)
              ·
                refine ⟨70386885029920565656523339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46924590019947043771015559 70386885029920565656523339)
                ·
                  refine ⟨105580327544880848484785009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70386885029920565656523339 105580327544880848484785009)
                  ·
                    refine ⟨79185245658660636363588757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105580327544880848484785009 79185245658660636363588757)
                    ·
                      refine ⟨3711808390249717329543223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79185245658660636363588757 3711808390249717329543223)
                      ·
                        rfl

theorem cell23_7228721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_7228721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228721 prefixEnd_7228721 := by exact prefixLift 7228721
  have htrace : WordTrace (prefixWord ++ tailWord_7228721) baseStart_7228721 baseEnd_7228721 := by
    simpa [prefixWord, tailWord_7228721, baseEnd_7228721] using wordTrace_append hprefix tailTrace_7228721
  have hstable : (prefixWord ++ tailWord_7228721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228721).length < 2 ^ (prefixWord ++ tailWord_7228721).sum := by decide
  have hdescent : baseEnd_7228721 < baseStart_7228721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228748 : List Nat := [2, 2, 1, 3, 2, 2, 1, 4, 1, 5]
def baseStart_7228748 : Nat := 118140960795 + 7228748 * 2 ^ 59
def prefixEnd_7228748 : Nat := 4983230072969 + 3 ^ 40 * 7228748 * 2
def baseEnd_7228748 : Nat := 1237274084742462907968533

theorem tailTrace_7228748 : CollatzResearch.WordTrace tailWord_7228748 prefixEnd_7228748 1237274084742462907968533 := by
  unfold tailWord_7228748
  simp only [CollatzResearch.WordTrace]
  refine ⟨131827049807744021357111449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175769399743658695142815265 131827049807744021357111449)
  ·
    refine ⟨98870287355808016017833587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131827049807744021357111449 98870287355808016017833587)
    ·
      refine ⟨148305431033712024026750381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98870287355808016017833587 148305431033712024026750381)
      ·
        refine ⟨55614536637642009010031393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148305431033712024026750381 55614536637642009010031393)
        ·
          refine ⟨41710902478231506757523545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55614536637642009010031393 41710902478231506757523545)
          ·
            refine ⟨31283176858673630068142659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41710902478231506757523545 31283176858673630068142659)
            ·
              refine ⟨46924765288010445102213989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31283176858673630068142659 46924765288010445102213989)
              ·
                refine ⟨8798393491501958456665123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46924765288010445102213989 8798393491501958456665123)
                ·
                  refine ⟨13197590237252937684997685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8798393491501958456665123 13197590237252937684997685)
                  ·
                    refine ⟨1237274084742462907968533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13197590237252937684997685 1237274084742462907968533)
                    ·
                      rfl

theorem cell23_7228748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 1, 5].length) (baseStart_7228748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228748 prefixEnd_7228748 := by exact prefixLift 7228748
  have htrace : WordTrace (prefixWord ++ tailWord_7228748) baseStart_7228748 baseEnd_7228748 := by
    simpa [prefixWord, tailWord_7228748, baseEnd_7228748] using wordTrace_append hprefix tailTrace_7228748
  have hstable : (prefixWord ++ tailWord_7228748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228748).length < 2 ^ (prefixWord ++ tailWord_7228748).sum := by decide
  have hdescent : baseEnd_7228748 < baseStart_7228748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228751 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 4]
def baseStart_7228751 : Nat := 118140960795 + 7228751 * 2 ^ 59
def prefixEnd_7228751 : Nat := 4983230072969 + 3 ^ 40 * 7228751 * 2
def baseEnd_7228751 : Nat := 3711823794669352212168085

theorem tailTrace_7228751 : CollatzResearch.WordTrace tailWord_7228751 prefixEnd_7228751 3711823794669352212168085 := by
  unfold tailWord_7228751
  simp only [CollatzResearch.WordTrace]
  refine ⟨263654209034477174226582107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175769472689651449484388071 263654209034477174226582107)
  ·
    refine ⟨395481313551715761339873161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263654209034477174226582107 395481313551715761339873161)
    ·
      refine ⟨296610985163786821004904871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395481313551715761339873161 296610985163786821004904871)
      ·
        refine ⟨444916477745680231507357307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296610985163786821004904871 444916477745680231507357307)
        ·
          refine ⟨667374716618520347261035961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444916477745680231507357307 667374716618520347261035961)
          ·
            refine ⟨500531037463890260445776971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 667374716618520347261035961 500531037463890260445776971)
            ·
              refine ⟨750796556195835390668665457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500531037463890260445776971 750796556195835390668665457)
              ·
                refine ⟨563097417146876543001499093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 750796556195835390668665457 563097417146876543001499093)
                ·
                  refine ⟨13197595714379918976597635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 563097417146876543001499093 13197595714379918976597635)
                  ·
                    refine ⟨19796393571569878464896453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13197595714379918976597635 19796393571569878464896453)
                    ·
                      refine ⟨3711823794669352212168085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19796393571569878464896453 3711823794669352212168085)
                      ·
                        rfl

theorem cell23_7228751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 4].length) (baseStart_7228751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228751 prefixEnd_7228751 := by exact prefixLift 7228751
  have htrace : WordTrace (prefixWord ++ tailWord_7228751) baseStart_7228751 baseEnd_7228751 := by
    simpa [prefixWord, tailWord_7228751, baseEnd_7228751] using wordTrace_append hprefix tailTrace_7228751
  have hstable : (prefixWord ++ tailWord_7228751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228751).length < 2 ^ (prefixWord ++ tailWord_7228751).sum := by decide
  have hdescent : baseEnd_7228751 < baseStart_7228751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228761 : List Nat := [1, 2, 1, 2, 2, 2, 2, 4, 1, 6]
def baseStart_7228761 : Nat := 118140960795 + 7228761 * 2 ^ 59
def prefixEnd_7228761 : Nat := 4983230072969 + 3 ^ 40 * 7228761 * 2
def baseEnd_7228761 : Nat := 1237276309825299057681013

theorem tailTrace_7228761 : CollatzResearch.WordTrace tailWord_7228761 prefixEnd_7228761 1237276309825299057681013 := by
  unfold tailWord_7228761
  simp only [CollatzResearch.WordTrace]
  refine ⟨263654573764440945934446137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175769715842960630622964091 263654573764440945934446137)
  ·
    refine ⟨197740930323330709450834603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263654573764440945934446137 197740930323330709450834603)
    ·
      refine ⟨296611395484996064176251905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197740930323330709450834603 296611395484996064176251905)
      ·
        refine ⟨222458546613747048132188929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296611395484996064176251905 222458546613747048132188929)
        ·
          refine ⟨166843909960310286099141697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222458546613747048132188929 166843909960310286099141697)
          ·
            refine ⟨125132932470232714574356273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166843909960310286099141697 125132932470232714574356273)
            ·
              refine ⟨93849699352674535930767205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125132932470232714574356273 93849699352674535930767205)
              ·
                refine ⟨17596818628626475487018851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93849699352674535930767205 17596818628626475487018851)
                ·
                  refine ⟨26395227942939713230528277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17596818628626475487018851 26395227942939713230528277)
                  ·
                    refine ⟨1237276309825299057681013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26395227942939713230528277 1237276309825299057681013)
                    ·
                      rfl

theorem cell23_7228761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 6].length) (baseStart_7228761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228761 prefixEnd_7228761 := by exact prefixLift 7228761
  have htrace : WordTrace (prefixWord ++ tailWord_7228761) baseStart_7228761 baseEnd_7228761 := by
    simpa [prefixWord, tailWord_7228761, baseEnd_7228761] using wordTrace_append hprefix tailTrace_7228761
  have hstable : (prefixWord ++ tailWord_7228761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228761).length < 2 ^ (prefixWord ++ tailWord_7228761).sum := by decide
  have hdescent : baseEnd_7228761 < baseStart_7228761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228762 : List Nat := [3, 1, 1, 2, 1, 2, 5, 3, 1, 1, 3]
def baseStart_7228762 : Nat := 118140960795 + 7228762 * 2 ^ 59
def prefixEnd_7228762 : Nat := 4983230072969 + 3 ^ 40 * 7228762 * 2
def baseEnd_7228762 : Nat := 3711829442956551669130535

theorem tailTrace_7228762 : CollatzResearch.WordTrace tailWord_7228762 prefixEnd_7228762 3711829442956551669130535 := by
  unfold tailWord_7228762
  simp only [CollatzResearch.WordTrace]
  refine ⟨65913652559359330776308135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175769740158291548736821693 65913652559359330776308135)
  ·
    refine ⟨98870478839038996164462203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65913652559359330776308135 98870478839038996164462203)
    ·
      refine ⟨148305718258558494246693305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98870478839038996164462203 148305718258558494246693305)
      ·
        refine ⟨111229288693918870685019979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148305718258558494246693305 111229288693918870685019979)
        ·
          refine ⟨166843933040878306027529969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111229288693918870685019979 166843933040878306027529969)
          ·
            refine ⟨125132949780658729520647477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166843933040878306027529969 125132949780658729520647477)
            ·
              refine ⟨11731214041936755892560701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125132949780658729520647477 11731214041936755892560701)
              ·
                refine ⟨4399205265726283459710263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11731214041936755892560701 4399205265726283459710263)
                ·
                  refine ⟨6598807898589425189565395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4399205265726283459710263 6598807898589425189565395)
                  ·
                    refine ⟨9898211847884137784348093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6598807898589425189565395 9898211847884137784348093)
                    ·
                      refine ⟨3711829442956551669130535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9898211847884137784348093 3711829442956551669130535)
                      ·
                        rfl

theorem cell23_7228762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 3, 1, 1, 3].length) (baseStart_7228762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228762 prefixEnd_7228762 := by exact prefixLift 7228762
  have htrace : WordTrace (prefixWord ++ tailWord_7228762) baseStart_7228762 baseEnd_7228762 := by
    simpa [prefixWord, tailWord_7228762, baseEnd_7228762] using wordTrace_append hprefix tailTrace_7228762
  have hstable : (prefixWord ++ tailWord_7228762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228762).length < 2 ^ (prefixWord ++ tailWord_7228762).sum := by decide
  have hdescent : baseEnd_7228762 < baseStart_7228762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228791 : List Nat := [1, 1, 3, 1, 1, 2, 6, 8]
def baseStart_7228791 : Nat := 118140960795 + 7228791 * 2 ^ 59
def prefixEnd_7228791 : Nat := 4983230072969 + 3 ^ 40 * 7228791 * 2
def baseEnd_7228791 : Nat := 137475716070204890950663

theorem tailTrace_7228791 : CollatzResearch.WordTrace tailWord_7228791 prefixEnd_7228791 137475716070204890950663 := by
  unfold tailWord_7228791
  simp only [CollatzResearch.WordTrace]
  refine ⟨263655667954332261058038227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175770445302888174038692151 263655667954332261058038227)
  ·
    refine ⟨395483501931498391587057341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263655667954332261058038227 395483501931498391587057341)
    ·
      refine ⟨148306313224311896845146503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 395483501931498391587057341 148306313224311896845146503)
      ·
        refine ⟨222459469836467845267719755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148306313224311896845146503 222459469836467845267719755)
        ·
          refine ⟨333689204754701767901579633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222459469836467845267719755 333689204754701767901579633)
          ·
            refine ⟨250266903566026325926184725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333689204754701767901579633 250266903566026325926184725)
            ·
              refine ⟨11731261104657484027789909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 250266903566026325926184725 11731261104657484027789909)
              ·
                refine ⟨137475716070204890950663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11731261104657484027789909 137475716070204890950663)
                ·
                  rfl

theorem cell23_7228791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 8].length) (baseStart_7228791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228791 prefixEnd_7228791 := by exact prefixLift 7228791
  have htrace : WordTrace (prefixWord ++ tailWord_7228791) baseStart_7228791 baseEnd_7228791 := by
    simpa [prefixWord, tailWord_7228791, baseEnd_7228791] using wordTrace_append hprefix tailTrace_7228791
  have hstable : (prefixWord ++ tailWord_7228791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228791).length < 2 ^ (prefixWord ++ tailWord_7228791).sum := by decide
  have hdescent : baseEnd_7228791 < baseStart_7228791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228802 : List Nat := [3, 4, 2, 1, 1, 2, 1, 1, 3, 1, 4]
def baseStart_7228802 : Nat := 118140960795 + 7228802 * 2 ^ 59
def prefixEnd_7228802 : Nat := 4983230072969 + 3 ^ 40 * 7228802 * 2
def baseEnd_7228802 : Nat := 3711849982182731512630351

theorem tailTrace_7228802 : CollatzResearch.WordTrace tailWord_7228802 prefixEnd_7228802 3711849982182731512630351 := by
  unfold tailWord_7228802
  simp only [CollatzResearch.WordTrace]
  refine ⟨65914017289323102484172165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175770712771528273291125773 65914017289323102484172165)
  ·
    refine ⟨12358878241748081715782281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65914017289323102484172165 12358878241748081715782281)
    ·
      refine ⟨9269158681311061286836711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12358878241748081715782281 9269158681311061286836711)
      ·
        refine ⟨13903738021966591930255067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9269158681311061286836711 13903738021966591930255067)
        ·
          refine ⟨20855607032949887895382601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13903738021966591930255067 20855607032949887895382601)
          ·
            refine ⟨15641705274712415921536951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20855607032949887895382601 15641705274712415921536951)
            ·
              refine ⟨23462557912068623882305427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15641705274712415921536951 23462557912068623882305427)
              ·
                refine ⟨35193836868102935823458141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23462557912068623882305427 35193836868102935823458141)
                ·
                  refine ⟨13197688825538600933796803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35193836868102935823458141 13197688825538600933796803)
                  ·
                    refine ⟨19796533238307901400695205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13197688825538600933796803 19796533238307901400695205)
                    ·
                      refine ⟨3711849982182731512630351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19796533238307901400695205 3711849982182731512630351)
                      ·
                        rfl

theorem cell23_7228802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_7228802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228802 prefixEnd_7228802 := by exact prefixLift 7228802
  have htrace : WordTrace (prefixWord ++ tailWord_7228802) baseStart_7228802 baseEnd_7228802 := by
    simpa [prefixWord, tailWord_7228802, baseEnd_7228802] using wordTrace_append hprefix tailTrace_7228802
  have hstable : (prefixWord ++ tailWord_7228802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228802).length < 2 ^ (prefixWord ++ tailWord_7228802).sum := by decide
  have hdescent : baseEnd_7228802 < baseStart_7228802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228805 : List Nat := [1, 3, 1, 1, 3, 1, 5, 2, 1, 2, 3]
def baseStart_7228805 : Nat := 118140960795 + 7228805 * 2 ^ 59
def prefixEnd_7228805 : Nat := 4983230072969 + 3 ^ 40 * 7228805 * 2
def baseEnd_7228805 : Nat := 3711851522624695000892837

theorem tailTrace_7228805 : CollatzResearch.WordTrace tailWord_7228805 prefixEnd_7228805 3711851522624695000892837 := by
  unfold tailWord_7228805
  simp only [CollatzResearch.WordTrace]
  refine ⟨263656178576281541449047869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175770785717521027632698579 263656178576281541449047869)
  ·
    refine ⟨98871066966105578043392951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263656178576281541449047869 98871066966105578043392951)
    ·
      refine ⟨148306600449158367065089427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98871066966105578043392951 148306600449158367065089427)
      ·
        refine ⟨222459900673737550597634141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148306600449158367065089427 222459900673737550597634141)
        ·
          refine ⟨83422462752651581474112803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222459900673737550597634141 83422462752651581474112803)
          ·
            refine ⟨125133694128977372211169205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83422462752651581474112803 125133694128977372211169205)
            ·
              refine ⟨11731283824591628644797113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125133694128977372211169205 11731283824591628644797113)
              ·
                refine ⟨8798462868443721483597835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11731283824591628644797113 8798462868443721483597835)
                ·
                  refine ⟨13197694302665582225396753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8798462868443721483597835 13197694302665582225396753)
                  ·
                    refine ⟨9898270726999186669047565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13197694302665582225396753 9898270726999186669047565)
                    ·
                      refine ⟨3711851522624695000892837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9898270726999186669047565 3711851522624695000892837)
                      ·
                        rfl

theorem cell23_7228805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 2, 3].length) (baseStart_7228805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228805 prefixEnd_7228805 := by exact prefixLift 7228805
  have htrace : WordTrace (prefixWord ++ tailWord_7228805) baseStart_7228805 baseEnd_7228805 := by
    simpa [prefixWord, tailWord_7228805, baseEnd_7228805] using wordTrace_append hprefix tailTrace_7228805
  have hstable : (prefixWord ++ tailWord_7228805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228805).length < 2 ^ (prefixWord ++ tailWord_7228805).sum := by decide
  have hdescent : baseEnd_7228805 < baseStart_7228805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228830 : List Nat := [4, 3, 1, 2, 3, 1, 2, 2, 1, 1, 3]
def baseStart_7228830 : Nat := 118140960795 + 7228830 * 2 ^ 59
def prefixEnd_7228830 : Nat := 4983230072969 + 3 ^ 40 * 7228830 * 2
def baseEnd_7228830 : Nat := 3711864359641057403080223

theorem tailTrace_7228830 : CollatzResearch.WordTrace tailWord_7228830 prefixEnd_7228830 3711864359641057403080223 := by
  unfold tailWord_7228830
  simp only [CollatzResearch.WordTrace]
  refine ⟨32957136300148871339838493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175771393600793980479138629 32957136300148871339838493)
  ·
    refine ⟨12358926112555826752439435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32957136300148871339838493 12358926112555826752439435)
    ·
      refine ⟨18538389168833740128659153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12358926112555826752439435 18538389168833740128659153)
      ·
        refine ⟨13903791876625305096494365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18538389168833740128659153 13903791876625305096494365)
        ·
          refine ⟨5213921953734489411185387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13903791876625305096494365 5213921953734489411185387)
          ·
            refine ⟨7820882930601734116778081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5213921953734489411185387 7820882930601734116778081)
            ·
              refine ⟨5865662197951300587583561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7820882930601734116778081 5865662197951300587583561)
              ·
                refine ⟨4399246648463475440687671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5865662197951300587583561 4399246648463475440687671)
                ·
                  refine ⟨6598869972695213161031507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4399246648463475440687671 6598869972695213161031507)
                  ·
                    refine ⟨9898304959042819741547261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6598869972695213161031507 9898304959042819741547261)
                    ·
                      refine ⟨3711864359641057403080223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9898304959042819741547261 3711864359641057403080223)
                      ·
                        rfl

theorem cell23_7228830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_7228830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228830 prefixEnd_7228830 := by exact prefixLift 7228830
  have htrace : WordTrace (prefixWord ++ tailWord_7228830) baseStart_7228830 baseEnd_7228830 := by
    simpa [prefixWord, tailWord_7228830, baseEnd_7228830] using wordTrace_append hprefix tailTrace_7228830
  have hstable : (prefixWord ++ tailWord_7228830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228830).length < 2 ^ (prefixWord ++ tailWord_7228830).sum := by decide
  have hdescent : baseEnd_7228830 < baseStart_7228830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228862 : List Nat := [4, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2]
def baseStart_7228862 : Nat := 118140960795 + 7228862 * 2 ^ 59
def prefixEnd_7228862 : Nat := 4983230072969 + 3 ^ 40 * 7228862 * 2
def baseEnd_7228862 : Nat := 3711880791022001277880075

theorem tailTrace_7228862 : CollatzResearch.WordTrace tailWord_7228862 prefixEnd_7228862 3711880791022001277880075 := by
  unfold tailWord_7228862
  simp only [CollatzResearch.WordTrace]
  refine ⟨32957282192134380022984105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175772171691383360122581893 32957282192134380022984105)
  ·
    refine ⟨24717961644100785017238079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32957282192134380022984105 24717961644100785017238079)
    ·
      refine ⟨37076942466151177525857119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24717961644100785017238079 37076942466151177525857119)
      ·
        refine ⟨55615413699226766288785679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37076942466151177525857119 55615413699226766288785679)
        ·
          refine ⟨83423120548840149433178519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55615413699226766288785679 83423120548840149433178519)
          ·
            refine ⟨125134680823260224149767779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83423120548840149433178519 125134680823260224149767779)
            ·
              refine ⟨187702021234890336224651669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125134680823260224149767779 187702021234890336224651669)
              ·
                refine ⟨8798532245385484510530547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 187702021234890336224651669 8798532245385484510530547)
                ·
                  refine ⟨13197798368078226765795821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8798532245385484510530547 13197798368078226765795821)
                  ·
                    refine ⟨4949174388029335037173433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13197798368078226765795821 4949174388029335037173433)
                    ·
                      refine ⟨3711880791022001277880075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4949174388029335037173433 3711880791022001277880075)
                      ·
                        rfl

theorem cell23_7228862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_7228862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228862 prefixEnd_7228862 := by exact prefixLift 7228862
  have htrace : WordTrace (prefixWord ++ tailWord_7228862) baseStart_7228862 baseEnd_7228862 := by
    simpa [prefixWord, tailWord_7228862, baseEnd_7228862] using wordTrace_append hprefix tailTrace_7228862
  have hstable : (prefixWord ++ tailWord_7228862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228862).length < 2 ^ (prefixWord ++ tailWord_7228862).sum := by decide
  have hdescent : baseEnd_7228862 < baseStart_7228862 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228875 : List Nat := [1, 1, 1, 1, 3, 3, 4, 2, 1, 4, 2]
def baseStart_7228875 : Nat := 118140960795 + 7228875 * 2 ^ 59
def prefixEnd_7228875 : Nat := 4983230072969 + 3 ^ 40 * 7228875 * 2
def baseEnd_7228875 : Nat := 3711887466270509727017515

theorem tailTrace_7228875 : CollatzResearch.WordTrace tailWord_7228875 prefixEnd_7228875 3711887466270509727017515 := by
  unfold tailWord_7228875
  simp only [CollatzResearch.WordTrace]
  refine ⟨263658731686027943404096079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175772487790685295602730719 263658731686027943404096079)
  ·
    refine ⟨395488097529041915106144119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263658731686027943404096079 395488097529041915106144119)
    ·
      refine ⟨593232146293562872659216179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395488097529041915106144119 593232146293562872659216179)
      ·
        refine ⟨889848219440344308988824269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593232146293562872659216179 889848219440344308988824269)
        ·
          refine ⟨333693082290129115870809101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 889848219440344308988824269 333693082290129115870809101)
          ·
            refine ⟨125134905858798418451553413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 333693082290129115870809101 125134905858798418451553413)
            ·
              refine ⟨23462794848524703459666265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125134905858798418451553413 23462794848524703459666265)
              ·
                refine ⟨17597096136393527594749699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23462794848524703459666265 17597096136393527594749699)
                ·
                  refine ⟨26395644204590291392124549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17597096136393527594749699 26395644204590291392124549)
                  ·
                    refine ⟨4949183288360679636023353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26395644204590291392124549 4949183288360679636023353)
                    ·
                      refine ⟨3711887466270509727017515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4949183288360679636023353 3711887466270509727017515)
                      ·
                        rfl

theorem cell23_7228875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 4, 2].length) (baseStart_7228875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228875 prefixEnd_7228875 := by exact prefixLift 7228875
  have htrace : WordTrace (prefixWord ++ tailWord_7228875) baseStart_7228875 baseEnd_7228875 := by
    simpa [prefixWord, tailWord_7228875, baseEnd_7228875] using wordTrace_append hprefix tailTrace_7228875
  have hstable : (prefixWord ++ tailWord_7228875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228875).length < 2 ^ (prefixWord ++ tailWord_7228875).sum := by decide
  have hdescent : baseEnd_7228875 < baseStart_7228875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228878 : List Nat := [4, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5]
def baseStart_7228878 : Nat := 118140960795 + 7228878 * 2 ^ 59
def prefixEnd_7228878 : Nat := 4983230072969 + 3 ^ 40 * 7228878 * 2
def baseEnd_7228878 : Nat := 3711889006712473215280001

theorem tailTrace_7228878 : CollatzResearch.WordTrace tailWord_7228878 prefixEnd_7228878 3711889006712473215280001 := by
  unfold tailWord_7228878
  simp only [CollatzResearch.WordTrace]
  refine ⟨32957355138127134364556911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175772560736678049944303525 32957355138127134364556911)
  ·
    refine ⟨49436032707190701546835367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32957355138127134364556911 49436032707190701546835367)
    ·
      refine ⟨74154049060786052320253051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49436032707190701546835367 74154049060786052320253051)
      ·
        refine ⟨111231073591179078480379577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74154049060786052320253051 111231073591179078480379577)
        ·
          refine ⟨83423305193384308860284683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111231073591179078480379577 83423305193384308860284683)
          ·
            refine ⟨125134957790076463290427025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83423305193384308860284683 125134957790076463290427025)
            ·
              refine ⟨93851218342557347467820269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125134957790076463290427025 93851218342557347467820269)
              ·
                refine ⟨35194206878459005300432601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93851218342557347467820269 35194206878459005300432601)
                ·
                  refine ⟨26395655158844253975324451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35194206878459005300432601 26395655158844253975324451)
                  ·
                    refine ⟨39593482738266380962986677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26395655158844253975324451 39593482738266380962986677)
                    ·
                      refine ⟨3711889006712473215280001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39593482738266380962986677 3711889006712473215280001)
                      ·
                        rfl

theorem cell23_7228878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_7228878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228878 prefixEnd_7228878 := by exact prefixLift 7228878
  have htrace : WordTrace (prefixWord ++ tailWord_7228878) baseStart_7228878 baseEnd_7228878 := by
    simpa [prefixWord, tailWord_7228878, baseEnd_7228878] using wordTrace_append hprefix tailTrace_7228878
  have hstable : (prefixWord ++ tailWord_7228878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228878).length < 2 ^ (prefixWord ++ tailWord_7228878).sum := by decide
  have hdescent : baseEnd_7228878 < baseStart_7228878 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228886 : List Nat := [5, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3]
def baseStart_7228886 : Nat := 118140960795 + 7228886 * 2 ^ 59
def prefixEnd_7228886 : Nat := 4983230072969 + 3 ^ 40 * 7228886 * 2
def baseEnd_7228886 : Nat := 3711893114557709183979965

theorem tailTrace_7228886 : CollatzResearch.WordTrace tailWord_7228886 prefixEnd_7228886 3711893114557709183979965 := by
  unfold tailWord_7228886
  simp only [CollatzResearch.WordTrace]
  refine ⟨16478695805561755767671657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175772755259325394855164341 16478695805561755767671657)
  ·
    refine ⟨12359021854171316825753743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16478695805561755767671657 12359021854171316825753743)
    ·
      refine ⟨18538532781256975238630615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12359021854171316825753743 18538532781256975238630615)
      ·
        refine ⟨27807799171885462857945923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18538532781256975238630615 27807799171885462857945923)
        ·
          refine ⟨41711698757828194286918885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27807799171885462857945923 41711698757828194286918885)
          ·
            refine ⟨7820943517092786428797291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41711698757828194286918885 7820943517092786428797291)
            ·
              refine ⟨11731415275639179643195937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7820943517092786428797291 11731415275639179643195937)
              ·
                refine ⟨8798561456729384732396953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11731415275639179643195937 8798561456729384732396953)
                ·
                  refine ⟨6598921092547038549297715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8798561456729384732396953 6598921092547038549297715)
                  ·
                    refine ⟨9898381638820557823946573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6598921092547038549297715 9898381638820557823946573)
                    ·
                      refine ⟨3711893114557709183979965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9898381638820557823946573 3711893114557709183979965)
                      ·
                        rfl

theorem cell23_7228886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_7228886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228886 prefixEnd_7228886 := by exact prefixLift 7228886
  have htrace : WordTrace (prefixWord ++ tailWord_7228886) baseStart_7228886 baseEnd_7228886 := by
    simpa [prefixWord, tailWord_7228886, baseEnd_7228886] using wordTrace_append hprefix tailTrace_7228886
  have hstable : (prefixWord ++ tailWord_7228886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228886).length < 2 ^ (prefixWord ++ tailWord_7228886).sum := by decide
  have hdescent : baseEnd_7228886 < baseStart_7228886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228888 : List Nat := [2, 1, 2, 2, 2, 1, 3, 2, 2, 2, 4]
def baseStart_7228888 : Nat := 118140960795 + 7228888 * 2 ^ 59
def prefixEnd_7228888 : Nat := 4983230072969 + 3 ^ 40 * 7228888 * 2
def baseEnd_7228888 : Nat := 3711894141519018176154955

theorem tailTrace_7228888 : CollatzResearch.WordTrace tailWord_7228888 prefixEnd_7228888 3711894141519018176154955 := by
  unfold tailWord_7228888
  simp only [CollatzResearch.WordTrace]
  refine ⟨131829602917490423312159659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175772803889987231082879545 131829602917490423312159659)
  ·
    refine ⟨197744404376235634968239489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131829602917490423312159659 197744404376235634968239489)
    ·
      refine ⟨148308303282176726226179617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197744404376235634968239489 148308303282176726226179617)
      ·
        refine ⟨111231227461632544669634713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148308303282176726226179617 111231227461632544669634713)
        ·
          refine ⟨83423420596224408502226035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111231227461632544669634713 83423420596224408502226035)
          ·
            refine ⟨125135130894336612753339053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83423420596224408502226035 125135130894336612753339053)
            ·
              refine ⟨46925674085376229782502145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125135130894336612753339053 46925674085376229782502145)
              ·
                refine ⟨35194255564032172336876609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46925674085376229782502145 35194255564032172336876609)
                ·
                  refine ⟨26395691673024129252657457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35194255564032172336876609 26395691673024129252657457)
                  ·
                    refine ⟨19796768754768096939493093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26395691673024129252657457 19796768754768096939493093)
                    ·
                      refine ⟨3711894141519018176154955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19796768754768096939493093 3711894141519018176154955)
                      ·
                        rfl

theorem cell23_7228888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_7228888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228888 prefixEnd_7228888 := by exact prefixLift 7228888
  have htrace : WordTrace (prefixWord ++ tailWord_7228888) baseStart_7228888 baseEnd_7228888 := by
    simpa [prefixWord, tailWord_7228888, baseEnd_7228888] using wordTrace_append hprefix tailTrace_7228888
  have hstable : (prefixWord ++ tailWord_7228888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228888).length < 2 ^ (prefixWord ++ tailWord_7228888).sum := by decide
  have hdescent : baseEnd_7228888 < baseStart_7228888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228891 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 7]
def baseStart_7228891 : Nat := 118140960795 + 7228891 * 2 ^ 59
def prefixEnd_7228891 : Nat := 4983230072969 + 3 ^ 40 * 7228891 * 2
def baseEnd_7228891 : Nat := 3711895681960981664417441

theorem tailTrace_7228891 : CollatzResearch.WordTrace tailWord_7228891 prefixEnd_7228891 3711895681960981664417441 := by
  unfold tailWord_7228891
  simp only [CollatzResearch.WordTrace]
  refine ⟨263659315253969978136678527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175772876835979985424452351 263659315253969978136678527)
  ·
    refine ⟨395488972880954967205017791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263659315253969978136678527 395488972880954967205017791)
    ·
      refine ⟨593233459321432450807526687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395488972880954967205017791 593233459321432450807526687)
      ·
        refine ⟨889850188982148676211290031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593233459321432450807526687 889850188982148676211290031)
        ·
          refine ⟨1334775283473223014316935047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 889850188982148676211290031 1334775283473223014316935047)
          ·
            refine ⟨2002162925209834521475402571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1334775283473223014316935047 2002162925209834521475402571)
            ·
              refine ⟨3003244387814751782213103857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2002162925209834521475402571 3003244387814751782213103857)
              ·
                refine ⟨2252433290861063836659827893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3003244387814751782213103857 2252433290861063836659827893)
                ·
                  refine ⟨211165621018224734686858865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2252433290861063836659827893 211165621018224734686858865)
                  ·
                    refine ⟨158374215763668551015144149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 211165621018224734686858865 158374215763668551015144149)
                    ·
                      refine ⟨3711895681960981664417441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 158374215763668551015144149 3711895681960981664417441)
                      ·
                        rfl

theorem cell23_7228891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 7].length) (baseStart_7228891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228891 prefixEnd_7228891 := by exact prefixLift 7228891
  have htrace : WordTrace (prefixWord ++ tailWord_7228891) baseStart_7228891 baseEnd_7228891 := by
    simpa [prefixWord, tailWord_7228891, baseEnd_7228891] using wordTrace_append hprefix tailTrace_7228891
  have hstable : (prefixWord ++ tailWord_7228891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228891).length < 2 ^ (prefixWord ++ tailWord_7228891).sum := by decide
  have hdescent : baseEnd_7228891 < baseStart_7228891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228908 : List Nat := [2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 3]
def baseStart_7228908 : Nat := 118140960795 + 7228908 * 2 ^ 59
def prefixEnd_7228908 : Nat := 4983230072969 + 3 ^ 40 * 7228908 * 2
def baseEnd_7228908 : Nat := 3711904411132108097904863

theorem tailTrace_7228908 : CollatzResearch.WordTrace tailWord_7228908 prefixEnd_7228908 3711904411132108097904863 := by
  unfold tailWord_7228908
  simp only [CollatzResearch.WordTrace]
  refine ⟨131829967647454195020023689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175773290196605593360031585 131829967647454195020023689)
  ·
    refine ⟨98872475735590646265017767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131829967647454195020023689 98872475735590646265017767)
    ·
      refine ⟨148308713603385969397526651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98872475735590646265017767 148308713603385969397526651)
      ·
        refine ⟨222463070405078954096289977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148308713603385969397526651 222463070405078954096289977)
        ·
          refine ⟨166847302803809215572217483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222463070405078954096289977 166847302803809215572217483)
          ·
            refine ⟨250270954205713823358326225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166847302803809215572217483 250270954205713823358326225)
            ·
              refine ⟨187703215654285367518744669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250270954205713823358326225 187703215654285367518744669)
              ·
                refine ⟨70388705870357012819529251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187703215654285367518744669 70388705870357012819529251)
                ·
                  refine ⟨105583058805535519229293877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70388705870357012819529251 105583058805535519229293877)
                  ·
                    refine ⟨9898411763018954927746301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105583058805535519229293877 9898411763018954927746301)
                    ·
                      refine ⟨3711904411132108097904863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9898411763018954927746301 3711904411132108097904863)
                      ·
                        rfl

theorem cell23_7228908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 3].length) (baseStart_7228908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228908 prefixEnd_7228908 := by exact prefixLift 7228908
  have htrace : WordTrace (prefixWord ++ tailWord_7228908) baseStart_7228908 baseEnd_7228908 := by
    simpa [prefixWord, tailWord_7228908, baseEnd_7228908] using wordTrace_append hprefix tailTrace_7228908
  have hstable : (prefixWord ++ tailWord_7228908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228908).length < 2 ^ (prefixWord ++ tailWord_7228908).sum := by decide
  have hdescent : baseEnd_7228908 < baseStart_7228908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228965 : List Nat := [1, 3, 1, 2, 2, 1, 1, 3, 1, 6, 2]
def baseStart_7228965 : Nat := 118140960795 + 7228965 * 2 ^ 59
def prefixEnd_7228965 : Nat := 4983230072969 + 3 ^ 40 * 7228965 * 2
def baseEnd_7228965 : Nat := 3711933679529414374892101

theorem tailTrace_7228965 : CollatzResearch.WordTrace tailWord_7228965 prefixEnd_7228965 3711933679529414374892101 := by
  unfold tailWord_7228965
  simp only [CollatzResearch.WordTrace]
  refine ⟨263662014255701888774872349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175774676170467925849914899 263662014255701888774872349)
  ·
    refine ⟨98873255345888208290577131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263662014255701888774872349 98873255345888208290577131)
    ·
      refine ⟨148309883018832312435865697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98873255345888208290577131 148309883018832312435865697)
      ·
        refine ⟨111232412264124234326899273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148309883018832312435865697 111232412264124234326899273)
        ·
          refine ⟨83424309198093175745174455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111232412264124234326899273 83424309198093175745174455)
          ·
            refine ⟨125136463797139763617761683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83424309198093175745174455 125136463797139763617761683)
            ·
              refine ⟨187704695695709645426642525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125136463797139763617761683 187704695695709645426642525)
              ·
                refine ⟨70389260885891117034990947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187704695695709645426642525 70389260885891117034990947)
                ·
                  refine ⟨105583891328836675552486421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70389260885891117034990947 105583891328836675552486421)
                  ·
                    refine ⟨4949244906039219166522801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 105583891328836675552486421 4949244906039219166522801)
                    ·
                      refine ⟨3711933679529414374892101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4949244906039219166522801 3711933679529414374892101)
                      ·
                        rfl

theorem cell23_7228965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 6, 2].length) (baseStart_7228965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228965 prefixEnd_7228965 := by exact prefixLift 7228965
  have htrace : WordTrace (prefixWord ++ tailWord_7228965) baseStart_7228965 baseEnd_7228965 := by
    simpa [prefixWord, tailWord_7228965, baseEnd_7228965] using wordTrace_append hprefix tailTrace_7228965
  have hstable : (prefixWord ++ tailWord_7228965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228965).length < 2 ^ (prefixWord ++ tailWord_7228965).sum := by decide
  have hdescent : baseEnd_7228965 < baseStart_7228965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228978 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6]
def baseStart_7228978 : Nat := 118140960795 + 7228978 * 2 ^ 59
def prefixEnd_7228978 : Nat := 4983230072969 + 3 ^ 40 * 7228978 * 2
def baseEnd_7228978 : Nat := 3711940354777922824029541

theorem tailTrace_7228978 : CollatzResearch.WordTrace tailWord_7228978 prefixEnd_7228978 3711940354777922824029541 := by
  unfold tailWord_7228978
  simp only [CollatzResearch.WordTrace]
  refine ⟨65915622101163697998773897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175774992269769861330063725 65915622101163697998773897)
  ·
    refine ⟨49436716575872773499080423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65915622101163697998773897 49436716575872773499080423)
    ·
      refine ⟨74155074863809160248620635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49436716575872773499080423 74155074863809160248620635)
      ·
        refine ⟨111232612295713740372930953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74155074863809160248620635 111232612295713740372930953)
        ·
          refine ⟨83424459221785305279698215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111232612295713740372930953 83424459221785305279698215)
          ·
            refine ⟨125136688832677957919547323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83424459221785305279698215 125136688832677957919547323)
            ·
              refine ⟨187705033249016936879320985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125136688832677957919547323 187705033249016936879320985)
              ·
                refine ⟨140778774936762702659490739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187705033249016936879320985 140778774936762702659490739)
                ·
                  refine ⟨211168162405144053989236109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 140778774936762702659490739 211168162405144053989236109)
                  ·
                    refine ⟨79188060901929020245963541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 211168162405144053989236109 79188060901929020245963541)
                    ·
                      refine ⟨3711940354777922824029541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79188060901929020245963541 3711940354777922824029541)
                      ·
                        rfl

theorem cell23_7228978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_7228978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228978 prefixEnd_7228978 := by exact prefixLift 7228978
  have htrace : WordTrace (prefixWord ++ tailWord_7228978) baseStart_7228978 baseEnd_7228978 := by
    simpa [prefixWord, tailWord_7228978, baseEnd_7228978] using wordTrace_append hprefix tailTrace_7228978
  have hstable : (prefixWord ++ tailWord_7228978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228978).length < 2 ^ (prefixWord ++ tailWord_7228978).sum := by decide
  have hdescent : baseEnd_7228978 < baseStart_7228978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228992 : List Nat := [2, 1, 1, 2, 2, 2, 1, 7, 1, 4]
def baseStart_7228992 : Nat := 118140960795 + 7228992 * 2 ^ 59
def prefixEnd_7228992 : Nat := 4983230072969 + 3 ^ 40 * 7228992 * 2
def baseEnd_7228992 : Nat := 1237315847835695256418159

theorem tailTrace_7228992 : CollatzResearch.WordTrace tailWord_7228992 prefixEnd_7228992 1237315847835695256418159 := by
  unfold tailWord_7228992
  simp only [CollatzResearch.WordTrace]
  refine ⟨131831499513302036193052615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175775332684402714924070153 131831499513302036193052615)
  ·
    refine ⟨197747249269953054289578923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131831499513302036193052615 197747249269953054289578923)
    ·
      refine ⟨296620873904929581434368385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197747249269953054289578923 296620873904929581434368385)
      ·
        refine ⟨222465655428697186075776289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296620873904929581434368385 222465655428697186075776289)
        ·
          refine ⟨166849241571522889556832217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222465655428697186075776289 166849241571522889556832217)
          ·
            refine ⟨125136931178642167167624163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166849241571522889556832217 125136931178642167167624163)
            ·
              refine ⟨187705396767963250751436245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125136931178642167167624163 187705396767963250751436245)
              ·
                refine ⟨4399345236749138689486787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 187705396767963250751436245 4399345236749138689486787)
                ·
                  refine ⟨6599017855123708034230181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4399345236749138689486787 6599017855123708034230181)
                  ·
                    refine ⟨1237315847835695256418159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6599017855123708034230181 1237315847835695256418159)
                    ·
                      rfl

theorem cell23_7228992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 7, 1, 4].length) (baseStart_7228992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7228992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7228992 prefixEnd_7228992 := by exact prefixLift 7228992
  have htrace : WordTrace (prefixWord ++ tailWord_7228992) baseStart_7228992 baseEnd_7228992 := by
    simpa [prefixWord, tailWord_7228992, baseEnd_7228992] using wordTrace_append hprefix tailTrace_7228992
  have hstable : (prefixWord ++ tailWord_7228992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228992).length < 2 ^ (prefixWord ++ tailWord_7228992).sum := by decide
  have hdescent : baseEnd_7228992 < baseStart_7228992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
