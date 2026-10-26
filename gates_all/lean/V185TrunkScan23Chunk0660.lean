import V185TrunkScan23Chunk0659

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3901829 : List Nat := [1, 3, 1, 1, 3, 1, 1, 6, 2, 4]
def baseStart_3901829 : Nat := 118140960795 + 3901829 * 2 ^ 59
def prefixEnd_3901829 : Nat := 4983230072969 + 3 ^ 40 * 3901829 * 2
def baseEnd_3901829 : Nat := 667837902883973269931107

theorem tailTrace_3901829 : CollatzResearch.WordTrace tailWord_3901829 prefixEnd_3901829 667837902883973269931107 := by
  unfold tailWord_3901829
  simp only [CollatzResearch.WordTrace]
  refine ⟨142311394981347387185140541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94874263320898258123427027 142311394981347387185140541)
  ·
    refine ⟨53366773118005270194427703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142311394981347387185140541 53366773118005270194427703)
    ·
      refine ⟨80050159677007905291641555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53366773118005270194427703 80050159677007905291641555)
      ·
        refine ⟨120075239515511857937462333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80050159677007905291641555 120075239515511857937462333)
        ·
          refine ⟨45028214818316946726548375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120075239515511857937462333 45028214818316946726548375)
          ·
            refine ⟨67542322227475420089822563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45028214818316946726548375 67542322227475420089822563)
            ·
              refine ⟨101313483341213130134733845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67542322227475420089822563 101313483341213130134733845)
              ·
                refine ⟨4749069531619365475065649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101313483341213130134733845 4749069531619365475065649)
                ·
                  refine ⟨3561802148714524106299237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4749069531619365475065649 3561802148714524106299237)
                  ·
                    refine ⟨667837902883973269931107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3561802148714524106299237 667837902883973269931107)
                    ·
                      rfl

theorem cell23_3901829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 2, 4].length) (baseStart_3901829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901829 prefixEnd_3901829 := by exact prefixLift 3901829
  have htrace : WordTrace (prefixWord ++ tailWord_3901829) baseStart_3901829 baseEnd_3901829 := by
    simpa [prefixWord, tailWord_3901829, baseEnd_3901829] using wordTrace_append hprefix tailTrace_3901829
  have hstable : (prefixWord ++ tailWord_3901829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901829).length < 2 ^ (prefixWord ++ tailWord_3901829).sum := by decide
  have hdescent : baseEnd_3901829 < baseStart_3901829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901832 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 3, 1, 6]
def baseStart_3901832 : Nat := 118140960795 + 3901832 * 2 ^ 59
def prefixEnd_3901832 : Nat := 4983230072969 + 3 ^ 40 * 3901832 * 2
def baseEnd_3901832 : Nat := 2003515249093883298055807

theorem tailTrace_3901832 : CollatzResearch.WordTrace tailWord_3901832 prefixEnd_3901832 2003515249093883298055807 := by
  unfold tailWord_3901832
  simp only [CollatzResearch.WordTrace]
  refine ⟨71155752200168259348749875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94874336266891012464999833 71155752200168259348749875)
  ·
    refine ⟨106733628300252389023124813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71155752200168259348749875 106733628300252389023124813)
    ·
      refine ⟨40025110612594645883671805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106733628300252389023124813 40025110612594645883671805)
      ·
        refine ⟨15009416479722992206376927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40025110612594645883671805 15009416479722992206376927)
        ·
          refine ⟨22514124719584488309565391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15009416479722992206376927 22514124719584488309565391)
          ·
            refine ⟨33771187079376732464348087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22514124719584488309565391 33771187079376732464348087)
            ·
              refine ⟨50656780619065098696522131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33771187079376732464348087 50656780619065098696522131)
              ·
                refine ⟨75985170928597648044783197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50656780619065098696522131 75985170928597648044783197)
                ·
                  refine ⟨28494439098224118016793699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75985170928597648044783197 28494439098224118016793699)
                  ·
                    refine ⟨42741658647336177025190549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28494439098224118016793699 42741658647336177025190549)
                    ·
                      refine ⟨2003515249093883298055807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42741658647336177025190549 2003515249093883298055807)
                      ·
                        rfl

theorem cell23_3901832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_3901832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901832 prefixEnd_3901832 := by exact prefixLift 3901832
  have htrace : WordTrace (prefixWord ++ tailWord_3901832) baseStart_3901832 baseEnd_3901832 := by
    simpa [prefixWord, tailWord_3901832, baseEnd_3901832] using wordTrace_append hprefix tailTrace_3901832
  have hstable : (prefixWord ++ tailWord_3901832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901832).length < 2 ^ (prefixWord ++ tailWord_3901832).sum := by decide
  have hdescent : baseEnd_3901832 < baseStart_3901832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901853 : List Nat := [1, 4, 2, 1, 4, 2, 1, 2, 1, 1, 4]
def baseStart_3901853 : Nat := 118140960795 + 3901853 * 2 ^ 59
def prefixEnd_3901853 : Nat := 4983230072969 + 3 ^ 40 * 3901853 * 2
def baseEnd_3901853 : Nat := 2003526032187627715893211

theorem tailTrace_3901853 : CollatzResearch.WordTrace tailWord_3901853 prefixEnd_3901853 2003526032187627715893211 := by
  unfold tailWord_3901853
  simp only [CollatzResearch.WordTrace]
  refine ⟨142312270333260439284014213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94874846888840292856009475 142312270333260439284014213)
  ·
    refine ⟨26683550687486332365752665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142312270333260439284014213 26683550687486332365752665)
    ·
      refine ⟨20012663015614749274314499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26683550687486332365752665 20012663015614749274314499)
      ·
        refine ⟨30018994523422123911471749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20012663015614749274314499 30018994523422123911471749)
        ·
          refine ⟨5628561473141648233400953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30018994523422123911471749 5628561473141648233400953)
          ·
            refine ⟨4221421104856236175050715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5628561473141648233400953 4221421104856236175050715)
            ·
              refine ⟨6332131657284354262576073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4221421104856236175050715 6332131657284354262576073)
              ·
                refine ⟨4749098742963265696932055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6332131657284354262576073 4749098742963265696932055)
                ·
                  refine ⟨7123648114444898545398083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4749098742963265696932055 7123648114444898545398083)
                  ·
                    refine ⟨10685472171667347818097125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7123648114444898545398083 10685472171667347818097125)
                    ·
                      refine ⟨2003526032187627715893211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10685472171667347818097125 2003526032187627715893211)
                      ·
                        rfl

theorem cell23_3901853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_3901853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901853 prefixEnd_3901853 := by exact prefixLift 3901853
  have htrace : WordTrace (prefixWord ++ tailWord_3901853) baseStart_3901853 baseEnd_3901853 := by
    simpa [prefixWord, tailWord_3901853, baseEnd_3901853] using wordTrace_append hprefix tailTrace_3901853
  have hstable : (prefixWord ++ tailWord_3901853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901853).length < 2 ^ (prefixWord ++ tailWord_3901853).sum := by decide
  have hdescent : baseEnd_3901853 < baseStart_3901853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901856 : List Nat := [2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 3]
def baseStart_3901856 : Nat := 118140960795 + 3901856 * 2 ^ 59
def prefixEnd_3901856 : Nat := 4983230072969 + 3 ^ 40 * 3901856 * 2
def baseEnd_3901856 : Nat := 2003527572629591204155697

theorem tailTrace_3901856 : CollatzResearch.WordTrace tailWord_3901856 prefixEnd_3901856 2003527572629591204155697 := by
  unfold tailWord_3901856
  simp only [CollatzResearch.WordTrace]
  refine ⟨71156189876124785398186711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94874919834833047197582281 71156189876124785398186711)
  ·
    refine ⟨106734284814187178097280067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71156189876124785398186711 106734284814187178097280067)
    ·
      refine ⟨160101427221280767145920101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106734284814187178097280067 160101427221280767145920101)
      ·
        refine ⟨30019017603990143839860019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160101427221280767145920101 30019017603990143839860019)
        ·
          refine ⟨45028526405985215759790029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30019017603990143839860019 45028526405985215759790029)
          ·
            refine ⟨16885697402244455909921261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45028526405985215759790029 16885697402244455909921261)
            ·
              refine ⟨6332136525841670966220473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16885697402244455909921261 6332136525841670966220473)
              ·
                refine ⟨4749102394381253224665355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6332136525841670966220473 4749102394381253224665355)
                ·
                  refine ⟨7123653591571879836998033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4749102394381253224665355 7123653591571879836998033)
                  ·
                    refine ⟨5342740193678909877748525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7123653591571879836998033 5342740193678909877748525)
                    ·
                      refine ⟨2003527572629591204155697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5342740193678909877748525 2003527572629591204155697)
                      ·
                        rfl

theorem cell23_3901856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_3901856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901856 prefixEnd_3901856 := by exact prefixLift 3901856
  have htrace : WordTrace (prefixWord ++ tailWord_3901856) baseStart_3901856 baseEnd_3901856 := by
    simpa [prefixWord, tailWord_3901856, baseEnd_3901856] using wordTrace_append hprefix tailTrace_3901856
  have hstable : (prefixWord ++ tailWord_3901856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901856).length < 2 ^ (prefixWord ++ tailWord_3901856).sum := by decide
  have hdescent : baseEnd_3901856 < baseStart_3901856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901873 : List Nat := [1, 2, 2, 4, 1, 3, 3, 1, 1, 2, 3]
def baseStart_3901873 : Nat := 118140960795 + 3901873 * 2 ^ 59
def prefixEnd_3901873 : Nat := 4983230072969 + 3 ^ 40 * 3901873 * 2
def baseEnd_3901873 : Nat := 2003536301800717637643119

theorem tailTrace_3901873 : CollatzResearch.WordTrace tailWord_3901873 prefixEnd_3901873 2003536301800717637643119 := by
  unfold tailWord_3901873
  simp only [CollatzResearch.WordTrace]
  refine ⟨142312999793187982699742273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94875333195458655133161515 142312999793187982699742273)
  ·
    refine ⟨106734749844890987024806705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142312999793187982699742273 106734749844890987024806705)
    ·
      refine ⟨80051062383668240268605029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106734749844890987024806705 80051062383668240268605029)
      ·
        refine ⟨15009574196937795050363443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80051062383668240268605029 15009574196937795050363443)
        ·
          refine ⟨22514361295406692575545165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15009574196937795050363443 22514361295406692575545165)
          ·
            refine ⟨8442885485777509715829437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22514361295406692575545165 8442885485777509715829437)
            ·
              refine ⟨3166082057166566143436039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8442885485777509715829437 3166082057166566143436039)
              ·
                refine ⟨4749123085749849215154059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3166082057166566143436039 4749123085749849215154059)
                ·
                  refine ⟨7123684628624773822731089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4749123085749849215154059 7123684628624773822731089)
                  ·
                    refine ⟨5342763471468580367048317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7123684628624773822731089 5342763471468580367048317)
                    ·
                      refine ⟨2003536301800717637643119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5342763471468580367048317 2003536301800717637643119)
                      ·
                        rfl

theorem cell23_3901873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_3901873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901873 prefixEnd_3901873 := by exact prefixLift 3901873
  have htrace : WordTrace (prefixWord ++ tailWord_3901873) baseStart_3901873 baseEnd_3901873 := by
    simpa [prefixWord, tailWord_3901873, baseEnd_3901873] using wordTrace_append hprefix tailTrace_3901873
  have hstable : (prefixWord ++ tailWord_3901873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901873).length < 2 ^ (prefixWord ++ tailWord_3901873).sum := by decide
  have hdescent : baseEnd_3901873 < baseStart_3901873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901876 : List Nat := [2, 5, 2, 2, 1, 11]
def baseStart_3901876 : Nat := 118140960795 + 3901876 * 2 ^ 59
def prefixEnd_3901876 : Nat := 4983230072969 + 3 ^ 40 * 3901876 * 2
def baseEnd_3901876 : Nat := 8245011696471938789735

theorem tailTrace_3901876 : CollatzResearch.WordTrace tailWord_3901876 prefixEnd_3901876 8245011696471938789735 := by
  unfold tailWord_3901876
  simp only [CollatzResearch.WordTrace]
  refine ⟨71156554606088557106050741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94875406141451409474734321 71156554606088557106050741)
  ·
    refine ⟨6670926994320802228692257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71156554606088557106050741 6670926994320802228692257)
    ·
      refine ⟨5003195245740601671519193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6670926994320802228692257 5003195245740601671519193)
      ·
        refine ⟨3752396434305451253639395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5003195245740601671519193 3752396434305451253639395)
        ·
          refine ⟨5628594651458176880459093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3752396434305451253639395 5628594651458176880459093)
          ·
            refine ⟨8245011696471938789735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5628594651458176880459093 8245011696471938789735)
            ·
              rfl

theorem cell23_3901876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 11].length) (baseStart_3901876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901876 prefixEnd_3901876 := by exact prefixLift 3901876
  have htrace : WordTrace (prefixWord ++ tailWord_3901876) baseStart_3901876 baseEnd_3901876 := by
    simpa [prefixWord, tailWord_3901876, baseEnd_3901876] using wordTrace_append hprefix tailTrace_3901876
  have hstable : (prefixWord ++ tailWord_3901876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901876).length < 2 ^ (prefixWord ++ tailWord_3901876).sum := by decide
  have hdescent : baseEnd_3901876 < baseStart_3901876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901882 : List Nat := [3, 1, 1, 1, 2, 1, 1, 4, 2, 2, 5]
def baseStart_3901882 : Nat := 118140960795 + 3901882 * 2 ^ 59
def prefixEnd_3901882 : Nat := 4983230072969 + 3 ^ 40 * 3901882 * 2
def baseEnd_3901882 : Nat := 2003540923126608102430577

theorem tailTrace_3901882 : CollatzResearch.WordTrace tailWord_3901882 prefixEnd_3901882 2003540923126608102430577 := by
  unfold tailWord_3901882
  simp only [CollatzResearch.WordTrace]
  refine ⟨35578332012538844309204975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94875552033436918157879933 35578332012538844309204975)
  ·
    refine ⟨53367498018808266463807463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35578332012538844309204975 53367498018808266463807463)
    ·
      refine ⟨80051247028212399695711195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53367498018808266463807463 80051247028212399695711195)
      ·
        refine ⟨120076870542318599543566793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80051247028212399695711195 120076870542318599543566793)
        ·
          refine ⟨90057652906738949657675095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120076870542318599543566793 90057652906738949657675095)
          ·
            refine ⟨135086479360108424486512643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90057652906738949657675095 135086479360108424486512643)
            ·
              refine ⟨202629719040162636729768965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135086479360108424486512643 202629719040162636729768965)
              ·
                refine ⟨37993072320030494386831681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 202629719040162636729768965 37993072320030494386831681)
                ·
                  refine ⟨28494804240022870790123761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37993072320030494386831681 28494804240022870790123761)
                  ·
                    refine ⟨21371103180017153092592821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28494804240022870790123761 21371103180017153092592821)
                    ·
                      refine ⟨2003540923126608102430577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21371103180017153092592821 2003540923126608102430577)
                      ·
                        rfl

theorem cell23_3901882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_3901882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901882 prefixEnd_3901882 := by exact prefixLift 3901882
  have htrace : WordTrace (prefixWord ++ tailWord_3901882) baseStart_3901882 baseEnd_3901882 := by
    simpa [prefixWord, tailWord_3901882, baseEnd_3901882] using wordTrace_append hprefix tailTrace_3901882
  have hstable : (prefixWord ++ tailWord_3901882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901882).length < 2 ^ (prefixWord ++ tailWord_3901882).sum := by decide
  have hdescent : baseEnd_3901882 < baseStart_3901882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901886 : List Nat := [4, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3]
def baseStart_3901886 : Nat := 118140960795 + 3901886 * 2 ^ 59
def prefixEnd_3901886 : Nat := 4983230072969 + 3 ^ 40 * 3901886 * 2
def baseEnd_3901886 : Nat := 2003542977049226086780559

theorem tailTrace_3901886 : CollatzResearch.WordTrace tailWord_3901886 prefixEnd_3901886 2003542977049226086780559 := by
  unfold tailWord_3901886
  simp only [CollatzResearch.WordTrace]
  refine ⟨17789184242767610739995689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94875649294760590613310341 17789184242767610739995689)
  ·
    refine ⟨13341888182075708054996767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17789184242767610739995689 13341888182075708054996767)
    ·
      refine ⟨20012832273113562082495151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13341888182075708054996767 20012832273113562082495151)
      ·
        refine ⟨30019248409670343123742727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20012832273113562082495151 30019248409670343123742727)
        ·
          refine ⟨45028872614505514685614091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30019248409670343123742727 45028872614505514685614091)
          ·
            refine ⟨67543308921758272028421137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45028872614505514685614091 67543308921758272028421137)
            ·
              refine ⟨50657481691318704021315853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67543308921758272028421137 50657481691318704021315853)
              ·
                refine ⟨18996555634244514007993445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50657481691318704021315853 18996555634244514007993445)
                ·
                  refine ⟨3561854181420846376498771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18996555634244514007993445 3561854181420846376498771)
                  ·
                    refine ⟨5342781272131269564748157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3561854181420846376498771 5342781272131269564748157)
                    ·
                      refine ⟨2003542977049226086780559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5342781272131269564748157 2003542977049226086780559)
                      ·
                        rfl

theorem cell23_3901886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_3901886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901886 prefixEnd_3901886 := by exact prefixLift 3901886
  have htrace : WordTrace (prefixWord ++ tailWord_3901886) baseStart_3901886 baseEnd_3901886 := by
    simpa [prefixWord, tailWord_3901886, baseEnd_3901886] using wordTrace_append hprefix tailTrace_3901886
  have hstable : (prefixWord ++ tailWord_3901886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901886).length < 2 ^ (prefixWord ++ tailWord_3901886).sum := by decide
  have hdescent : baseEnd_3901886 < baseStart_3901886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901896 : List Nat := [2, 1, 3, 1, 3, 2, 1, 2, 3, 3, 2]
def baseStart_3901896 : Nat := 118140960795 + 3901896 * 2 ^ 59
def prefixEnd_3901896 : Nat := 4983230072969 + 3 ^ 40 * 3901896 * 2
def baseEnd_3901896 : Nat := 2003548111855771047655513

theorem tailTrace_3901896 : CollatzResearch.WordTrace tailWord_3901896 prefixEnd_3901896 2003548111855771047655513 := by
  unfold tailWord_3901896
  simp only [CollatzResearch.WordTrace]
  refine ⟨71156919336052328813914771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94875892448069771751886361 71156919336052328813914771)
  ·
    refine ⟨106735379004078493220872157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71156919336052328813914771 106735379004078493220872157)
    ·
      refine ⟨40025767126529434957827059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106735379004078493220872157 40025767126529434957827059)
      ·
        refine ⟨60038650689794152436740589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40025767126529434957827059 60038650689794152436740589)
        ·
          refine ⟨22514494008672807163777721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60038650689794152436740589 22514494008672807163777721)
          ·
            refine ⟨16885870506504605372833291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22514494008672807163777721 16885870506504605372833291)
            ·
              refine ⟨25328805759756908059249937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16885870506504605372833291 25328805759756908059249937)
              ·
                refine ⟨18996604319817681044437453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25328805759756908059249937 18996604319817681044437453)
                ·
                  refine ⟨7123726619931630391664045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18996604319817681044437453 7123726619931630391664045)
                  ·
                    refine ⟨2671397482474361396874017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7123726619931630391664045 2671397482474361396874017)
                    ·
                      refine ⟨2003548111855771047655513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2671397482474361396874017 2003548111855771047655513)
                      ·
                        rfl

theorem cell23_3901896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 3, 3, 2].length) (baseStart_3901896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901896 prefixEnd_3901896 := by exact prefixLift 3901896
  have htrace : WordTrace (prefixWord ++ tailWord_3901896) baseStart_3901896 baseEnd_3901896 := by
    simpa [prefixWord, tailWord_3901896, baseEnd_3901896] using wordTrace_append hprefix tailTrace_3901896
  have hstable : (prefixWord ++ tailWord_3901896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901896).length < 2 ^ (prefixWord ++ tailWord_3901896).sum := by decide
  have hdescent : baseEnd_3901896 < baseStart_3901896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901930 : List Nat := [3, 1, 3, 1, 3, 1, 4, 1, 1, 3, 2]
def baseStart_3901930 : Nat := 118140960795 + 3901930 * 2 ^ 59
def prefixEnd_3901930 : Nat := 4983230072969 + 3 ^ 40 * 3901930 * 2
def baseEnd_3901930 : Nat := 2003565570198023914630357

theorem tailTrace_3901930 : CollatzResearch.WordTrace tailWord_3901930 prefixEnd_3901930 2003565570198023914630357 := by
  unfold tailWord_3901930
  simp only [CollatzResearch.WordTrace]
  refine ⟨35578769688495370358641811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94876719169320987623044829 35578769688495370358641811)
  ·
    refine ⟨53368154532743055537962717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35578769688495370358641811 53368154532743055537962717)
    ·
      refine ⟨20013057949778645826736019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53368154532743055537962717 20013057949778645826736019)
      ·
        refine ⟨30019586924667968740104029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20013057949778645826736019 30019586924667968740104029)
        ·
          refine ⟨11257345096750488277539011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30019586924667968740104029 11257345096750488277539011)
          ·
            refine ⟨16886017645125732416308517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11257345096750488277539011 16886017645125732416308517)
            ·
              refine ⟨3166128308461074828057847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16886017645125732416308517 3166128308461074828057847)
              ·
                refine ⟨4749192462691612242086771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3166128308461074828057847 4749192462691612242086771)
                ·
                  refine ⟨7123788694037418363130157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4749192462691612242086771 7123788694037418363130157)
                  ·
                    refine ⟨2671420760264031886173809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7123788694037418363130157 2671420760264031886173809)
                    ·
                      refine ⟨2003565570198023914630357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2671420760264031886173809 2003565570198023914630357)
                      ·
                        rfl

theorem cell23_3901930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_3901930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901930 prefixEnd_3901930 := by exact prefixLift 3901930
  have htrace : WordTrace (prefixWord ++ tailWord_3901930) baseStart_3901930 baseEnd_3901930 := by
    simpa [prefixWord, tailWord_3901930, baseEnd_3901930] using wordTrace_append hprefix tailTrace_3901930
  have hstable : (prefixWord ++ tailWord_3901930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901930).length < 2 ^ (prefixWord ++ tailWord_3901930).sum := by decide
  have hdescent : baseEnd_3901930 < baseStart_3901930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901932 : List Nat := [2, 2, 1, 1, 2, 1, 3, 2, 9]
def baseStart_3901932 : Nat := 118140960795 + 3901932 * 2 ^ 59
def prefixEnd_3901932 : Nat := 4983230072969 + 3 ^ 40 * 3901932 * 2
def baseEnd_3901932 : Nat := 222618510795481434089483

theorem tailTrace_3901932 : CollatzResearch.WordTrace tailWord_3901932 prefixEnd_3901932 222618510795481434089483 := by
  unfold tailWord_3901932
  simp only [CollatzResearch.WordTrace]
  refine ⟨71157575849987117888070025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94876767799982823850760033 71157575849987117888070025)
  ·
    refine ⟨53368181887490338416052519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71157575849987117888070025 53368181887490338416052519)
    ·
      refine ⟨80052272831235507624078779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53368181887490338416052519 80052272831235507624078779)
      ·
        refine ⟨120078409246853261436118169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80052272831235507624078779 120078409246853261436118169)
        ·
          refine ⟨90058806935139946077088627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120078409246853261436118169 90058806935139946077088627)
          ·
            refine ⟨135088210402709919115632941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90058806935139946077088627 135088210402709919115632941)
            ·
              refine ⟨50658078901016219668362353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135088210402709919115632941 50658078901016219668362353)
              ·
                refine ⟨37993559175762164751271765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50658078901016219668362353 37993559175762164751271765)
                ·
                  refine ⟨222618510795481434089483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 37993559175762164751271765 222618510795481434089483)
                  ·
                    rfl

theorem cell23_3901932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 9].length) (baseStart_3901932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901932 prefixEnd_3901932 := by exact prefixLift 3901932
  have htrace : WordTrace (prefixWord ++ tailWord_3901932) baseStart_3901932 baseEnd_3901932 := by
    simpa [prefixWord, tailWord_3901932, baseEnd_3901932] using wordTrace_append hprefix tailTrace_3901932
  have hstable : (prefixWord ++ tailWord_3901932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901932).length < 2 ^ (prefixWord ++ tailWord_3901932).sum := by decide
  have hdescent : baseEnd_3901932 < baseStart_3901932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901949 : List Nat := [1, 4, 1, 1, 1, 3, 4, 1, 7]
def baseStart_3901949 : Nat := 118140960795 + 3901949 * 2 ^ 59
def prefixEnd_3901949 : Nat := 4983230072969 + 3 ^ 40 * 3901949 * 2
def baseEnd_3901949 : Nat := 222619480703384371143641

theorem tailTrace_3901949 : CollatzResearch.WordTrace tailWord_3901949 prefixEnd_3901949 222619480703384371143641 := by
  unfold tailWord_3901949
  simp only [CollatzResearch.WordTrace]
  refine ⟨142315771740912647679508901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94877181160608431786339267 142315771740912647679508901)
  ·
    refine ⟨26684207201421121439907919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142315771740912647679508901 26684207201421121439907919)
    ·
      refine ⟨40026310802131682159861879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26684207201421121439907919 40026310802131682159861879)
      ·
        refine ⟨60039466203197523239792819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40026310802131682159861879 60039466203197523239792819)
        ·
          refine ⟨90059199304796284859689229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60039466203197523239792819 90059199304796284859689229)
          ·
            refine ⟨33772199739298606822383461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90059199304796284859689229 33772199739298606822383461)
            ·
              refine ⟨6332287451118488779196899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33772199739298606822383461 6332287451118488779196899)
              ·
                refine ⟨9498431176677733168795349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6332287451118488779196899 9498431176677733168795349)
                ·
                  refine ⟨222619480703384371143641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9498431176677733168795349 222619480703384371143641)
                  ·
                    rfl

theorem cell23_3901949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 7].length) (baseStart_3901949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901949 prefixEnd_3901949 := by exact prefixLift 3901949
  have htrace : WordTrace (prefixWord ++ tailWord_3901949) baseStart_3901949 baseEnd_3901949 := by
    simpa [prefixWord, tailWord_3901949, baseEnd_3901949] using wordTrace_append hprefix tailTrace_3901949
  have hstable : (prefixWord ++ tailWord_3901949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901949).length < 2 ^ (prefixWord ++ tailWord_3901949).sum := by decide
  have hdescent : baseEnd_3901949 < baseStart_3901949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901956 : List Nat := [2, 3, 2, 3, 1, 1, 2, 1, 2, 2, 4]
def baseStart_3901956 : Nat := 118140960795 + 3901956 * 2 ^ 59
def prefixEnd_3901956 : Nat := 4983230072969 + 3 ^ 40 * 3901956 * 2
def baseEnd_3901956 : Nat := 2003578920695040812905237

theorem tailTrace_3901956 : CollatzResearch.WordTrace tailWord_3901956 prefixEnd_3901956 2003578920695040812905237 := by
  unfold tailWord_3901956
  simp only [CollatzResearch.WordTrace]
  refine ⟨71158013525943643937506861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94877351367924858583342481 71158013525943643937506861)
  ·
    refine ⟨26684255072228866476565073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71158013525943643937506861 26684255072228866476565073)
    ·
      refine ⟨20013191304171649857423805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26684255072228866476565073 20013191304171649857423805)
      ·
        refine ⟨7504946739064368696533927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20013191304171649857423805 7504946739064368696533927)
        ·
          refine ⟨11257420108596553044800891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7504946739064368696533927 11257420108596553044800891)
          ·
            refine ⟨16886130162894829567201337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11257420108596553044800891 16886130162894829567201337)
            ·
              refine ⟨12664597622171122175401003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16886130162894829567201337 12664597622171122175401003)
              ·
                refine ⟨18996896433256683263101505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12664597622171122175401003 18996896433256683263101505)
                ·
                  refine ⟨14247672324942512447326129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18996896433256683263101505 14247672324942512447326129)
                  ·
                    refine ⟨10685754243706884335494597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14247672324942512447326129 10685754243706884335494597)
                    ·
                      refine ⟨2003578920695040812905237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10685754243706884335494597 2003578920695040812905237)
                      ·
                        rfl

theorem cell23_3901956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_3901956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901956 prefixEnd_3901956 := by exact prefixLift 3901956
  have htrace : WordTrace (prefixWord ++ tailWord_3901956) baseStart_3901956 baseEnd_3901956 := by
    simpa [prefixWord, tailWord_3901956, baseEnd_3901956] using wordTrace_append hprefix tailTrace_3901956
  have hstable : (prefixWord ++ tailWord_3901956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901956).length < 2 ^ (prefixWord ++ tailWord_3901956).sum := by decide
  have hdescent : baseEnd_3901956 < baseStart_3901956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3901986 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 1, 7, 2]
def baseStart_3901986 : Nat := 118140960795 + 3901986 * 2 ^ 59
def prefixEnd_3901986 : Nat := 4983230072969 + 3 ^ 40 * 3901986 * 2
def baseEnd_3901986 : Nat := 2003594325114675695530099

theorem tailTrace_3901986 : CollatzResearch.WordTrace tailWord_3901986 prefixEnd_3901986 2003594325114675695530099 := by
  unfold tailWord_3901986
  simp only [CollatzResearch.WordTrace]
  refine ⟨35579280310444650749651453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94878080827852401999070541 35579280310444650749651453)
  ·
    refine ⟨13342230116416744031119295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35579280310444650749651453 13342230116416744031119295)
    ·
      refine ⟨20013345174625116046678943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13342230116416744031119295 20013345174625116046678943)
      ·
        refine ⟨30020017761937674070018415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20013345174625116046678943 30020017761937674070018415)
        ·
          refine ⟨45030026642906511105027623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30020017761937674070018415 45030026642906511105027623)
          ·
            refine ⟨67545039964359766657541435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45030026642906511105027623 67545039964359766657541435)
            ·
              refine ⟨101317559946539649986312153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67545039964359766657541435 101317559946539649986312153)
              ·
                refine ⟨75988169959904737489734115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101317559946539649986312153 75988169959904737489734115)
                ·
                  refine ⟨113982254939857106234601173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75988169959904737489734115 113982254939857106234601173)
                  ·
                    refine ⟨2671459100152900927373465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 113982254939857106234601173 2671459100152900927373465)
                    ·
                      refine ⟨2003594325114675695530099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2671459100152900927373465 2003594325114675695530099)
                      ·
                        rfl

theorem cell23_3901986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_3901986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3901986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3901986 prefixEnd_3901986 := by exact prefixLift 3901986
  have htrace : WordTrace (prefixWord ++ tailWord_3901986) baseStart_3901986 baseEnd_3901986 := by
    simpa [prefixWord, tailWord_3901986, baseEnd_3901986] using wordTrace_append hprefix tailTrace_3901986
  have hstable : (prefixWord ++ tailWord_3901986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3901986).length < 2 ^ (prefixWord ++ tailWord_3901986).sum := by decide
  have hdescent : baseEnd_3901986 < baseStart_3901986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3901986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902006 : List Nat := [5, 1, 2, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_3902006 : Nat := 118140960795 + 3902006 * 2 ^ 59
def prefixEnd_3902006 : Nat := 4983230072969 + 3 ^ 40 * 3902006 * 2
def baseEnd_3902006 : Nat := 2003604594727765617280007

theorem tailTrace_3902006 : CollatzResearch.WordTrace tailWord_3902006 prefixEnd_3902006 2003604594727765617280007 := by
  unfold tailWord_3902006
  simp only [CollatzResearch.WordTrace]
  refine ⟨8894865668856634150895867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94878567134470764276222581 8894865668856634150895867)
  ·
    refine ⟨13342298503284951226343801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8894865668856634150895867 13342298503284951226343801)
    ·
      refine ⟨10006723877463713419757851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13342298503284951226343801 10006723877463713419757851)
      ·
        refine ⟨15010085816195570129636777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10006723877463713419757851 15010085816195570129636777)
        ·
          refine ⟨11257564362146677597227583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15010085816195570129636777 11257564362146677597227583)
          ·
            refine ⟨16886346543220016395841375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11257564362146677597227583 16886346543220016395841375)
            ·
              refine ⟨25329519814830024593762063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16886346543220016395841375 25329519814830024593762063)
              ·
                refine ⟨37994279722245036890643095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25329519814830024593762063 37994279722245036890643095)
                ·
                  refine ⟨56991419583367555335964643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37994279722245036890643095 56991419583367555335964643)
                  ·
                    refine ⟨85487129375051333003946965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56991419583367555335964643 85487129375051333003946965)
                    ·
                      refine ⟨2003604594727765617280007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 85487129375051333003946965 2003604594727765617280007)
                      ·
                        rfl

theorem cell23_3902006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_3902006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902006 prefixEnd_3902006 := by exact prefixLift 3902006
  have htrace : WordTrace (prefixWord ++ tailWord_3902006) baseStart_3902006 baseEnd_3902006 := by
    simpa [prefixWord, tailWord_3902006, baseEnd_3902006] using wordTrace_append hprefix tailTrace_3902006
  have hstable : (prefixWord ++ tailWord_3902006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902006).length < 2 ^ (prefixWord ++ tailWord_3902006).sum := by decide
  have hdescent : baseEnd_3902006 < baseStart_3902006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902016 : List Nat := [2, 1, 1, 2, 2, 2, 2, 3, 2, 4, 2]
def baseStart_3902016 : Nat := 118140960795 + 3902016 * 2 ^ 59
def prefixEnd_3902016 : Nat := 4983230072969 + 3 ^ 40 * 3902016 * 2
def baseEnd_3902016 : Nat := 2003609729534310578154961

theorem tailTrace_3902016 : CollatzResearch.WordTrace tailWord_3902016 prefixEnd_3902016 2003609729534310578154961 := by
  unfold tailWord_3902016
  simp only [CollatzResearch.WordTrace]
  refine ⟨71159107715834959061098951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94878810287779945414798601 71159107715834959061098951)
  ·
    refine ⟨106738661573752438591648427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71159107715834959061098951 106738661573752438591648427)
    ·
      refine ⟨160107992360628657887472641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106738661573752438591648427 160107992360628657887472641)
      ·
        refine ⟨120080994270471493415604481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160107992360628657887472641 120080994270471493415604481)
        ·
          refine ⟨90060745702853620061703361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120080994270471493415604481 90060745702853620061703361)
          ·
            refine ⟨67545559277140215046277521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90060745702853620061703361 67545559277140215046277521)
            ·
              refine ⟨50659169457855161284708141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67545559277140215046277521 50659169457855161284708141)
              ·
                refine ⟨18997188546695685481765553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50659169457855161284708141 18997188546695685481765553)
                ·
                  refine ⟨14247891410021764111324165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18997188546695685481765553 14247891410021764111324165)
                  ·
                    refine ⟨2671479639379080770873281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14247891410021764111324165 2671479639379080770873281)
                    ·
                      refine ⟨2003609729534310578154961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2671479639379080770873281 2003609729534310578154961)
                      ·
                        rfl

theorem cell23_3902016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 2, 4, 2].length) (baseStart_3902016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902016 prefixEnd_3902016 := by exact prefixLift 3902016
  have htrace : WordTrace (prefixWord ++ tailWord_3902016) baseStart_3902016 baseEnd_3902016 := by
    simpa [prefixWord, tailWord_3902016, baseEnd_3902016] using wordTrace_append hprefix tailTrace_3902016
  have hstable : (prefixWord ++ tailWord_3902016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902016).length < 2 ^ (prefixWord ++ tailWord_3902016).sum := by decide
  have hdescent : baseEnd_3902016 < baseStart_3902016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902019 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 3, 4, 3]
def baseStart_3902019 : Nat := 118140960795 + 3902019 * 2 ^ 59
def prefixEnd_3902019 : Nat := 4983230072969 + 3 ^ 40 * 3902019 * 2
def baseEnd_3902019 : Nat := 2003611269976274066417447

theorem tailTrace_3902019 : CollatzResearch.WordTrace tailWord_3902019 prefixEnd_3902019 2003611269976274066417447 := by
  unfold tailWord_3902019
  simp only [CollatzResearch.WordTrace]
  refine ⟨142318324850659049634557111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94878883233772699756371407 142318324850659049634557111)
  ·
    refine ⟨213477487275988574451835667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142318324850659049634557111 213477487275988574451835667)
    ·
      refine ⟨320216230913982861677753501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213477487275988574451835667 320216230913982861677753501)
      ·
        refine ⟨120081086592743573129157563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320216230913982861677753501 120081086592743573129157563)
        ·
          refine ⟨180121629889115359693736345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120081086592743573129157563 180121629889115359693736345)
          ·
            refine ⟨135091222416836519770302259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180121629889115359693736345 135091222416836519770302259)
            ·
              refine ⟨202636833625254779655453389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135091222416836519770302259 202636833625254779655453389)
              ·
                refine ⟨75988812609470542370795021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202636833625254779655453389 75988812609470542370795021)
                ·
                  refine ⟨28495804728551453389048133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75988812609470542370795021 28495804728551453389048133)
                  ·
                    refine ⟨5342963386603397510446525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28495804728551453389048133 5342963386603397510446525)
                    ·
                      refine ⟨2003611269976274066417447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5342963386603397510446525 2003611269976274066417447)
                      ·
                        rfl

theorem cell23_3902019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 4, 3].length) (baseStart_3902019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902019 prefixEnd_3902019 := by exact prefixLift 3902019
  have htrace : WordTrace (prefixWord ++ tailWord_3902019) baseStart_3902019 baseEnd_3902019 := by
    simpa [prefixWord, tailWord_3902019, baseEnd_3902019] using wordTrace_append hprefix tailTrace_3902019
  have hstable : (prefixWord ++ tailWord_3902019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902019).length < 2 ^ (prefixWord ++ tailWord_3902019).sum := by decide
  have hdescent : baseEnd_3902019 < baseStart_3902019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902060 : List Nat := [2, 2, 1, 1, 3, 1, 6, 2, 1, 4]
def baseStart_3902060 : Nat := 118140960795 + 3902060 * 2 ^ 59
def prefixEnd_3902060 : Nat := 4983230072969 + 3 ^ 40 * 3902060 * 2
def baseEnd_3902060 : Nat := 667877440894369468668253

theorem tailTrace_3902060 : CollatzResearch.WordTrace tailWord_3902060 prefixEnd_3902060 667877440894369468668253 := by
  unfold tailWord_3902060
  simp only [CollatzResearch.WordTrace]
  refine ⟨71159910121755256818399817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94879880162340342424533089 71159910121755256818399817)
  ·
    refine ⟨53369932591316442613799863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71159910121755256818399817 53369932591316442613799863)
    ·
      refine ⟨80054898886974663920699795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53369932591316442613799863 80054898886974663920699795)
      ·
        refine ⟨120082348330461995881049693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80054898886974663920699795 120082348330461995881049693)
        ·
          refine ⟨45030880623923248455393635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120082348330461995881049693 45030880623923248455393635)
          ·
            refine ⟨67546320935884872683090453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45030880623923248455393635 67546320935884872683090453)
            ·
              refine ⟨3166233793869603407019865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67546320935884872683090453 3166233793869603407019865)
              ·
                refine ⟨2374675345402202555264899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3166233793869603407019865 2374675345402202555264899)
                ·
                  refine ⟨3562013018103303832897349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2374675345402202555264899 3562013018103303832897349)
                  ·
                    refine ⟨667877440894369468668253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3562013018103303832897349 667877440894369468668253)
                    ·
                      rfl

theorem cell23_3902060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 2, 1, 4].length) (baseStart_3902060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902060 prefixEnd_3902060 := by exact prefixLift 3902060
  have htrace : WordTrace (prefixWord ++ tailWord_3902060) baseStart_3902060 baseEnd_3902060 := by
    simpa [prefixWord, tailWord_3902060, baseEnd_3902060] using wordTrace_append hprefix tailTrace_3902060
  have hstable : (prefixWord ++ tailWord_3902060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902060).length < 2 ^ (prefixWord ++ tailWord_3902060).sum := by decide
  have hdescent : baseEnd_3902060 < baseStart_3902060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902110 : List Nat := [4, 3, 1, 1, 1, 1, 2, 1, 4, 3, 2]
def baseStart_3902110 : Nat := 118140960795 + 3902110 * 2 ^ 59
def prefixEnd_3902110 : Nat := 4983230072969 + 3 ^ 40 * 3902110 * 2
def baseEnd_3902110 : Nat := 2003657996715833210379529

theorem tailTrace_3902110 : CollatzResearch.WordTrace tailWord_3902110 prefixEnd_3902110 2003657996715833210379529 := by
  unfold tailWord_3902110
  simp only [CollatzResearch.WordTrace]
  refine ⟨17790205486666171522014973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94881095928886248117413189 17790205486666171522014973)
  ·
    refine ⟨6671327057499814320755615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17790205486666171522014973 6671327057499814320755615)
    ·
      refine ⟨10006990586249721481133423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6671327057499814320755615 10006990586249721481133423)
      ·
        refine ⟨15010485879374582221700135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10006990586249721481133423 15010485879374582221700135)
        ·
          refine ⟨22515728819061873332550203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15010485879374582221700135 22515728819061873332550203)
          ·
            refine ⟨33773593228592809998825305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22515728819061873332550203 33773593228592809998825305)
            ·
              refine ⟨25330194921444607499118979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33773593228592809998825305 25330194921444607499118979)
              ·
                refine ⟨37995292382166911248678469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25330194921444607499118979 37995292382166911248678469)
                ·
                  refine ⟨7124117321656295859127213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37995292382166911248678469 7124117321656295859127213)
                  ·
                    refine ⟨2671543995621110947172705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7124117321656295859127213 2671543995621110947172705)
                    ·
                      refine ⟨2003657996715833210379529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2671543995621110947172705 2003657996715833210379529)
                      ·
                        rfl

theorem cell23_3902110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_3902110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902110 prefixEnd_3902110 := by exact prefixLift 3902110
  have htrace : WordTrace (prefixWord ++ tailWord_3902110) baseStart_3902110 baseEnd_3902110 := by
    simpa [prefixWord, tailWord_3902110, baseEnd_3902110] using wordTrace_append hprefix tailTrace_3902110
  have hstable : (prefixWord ++ tailWord_3902110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902110).length < 2 ^ (prefixWord ++ tailWord_3902110).sum := by decide
  have hdescent : baseEnd_3902110 < baseStart_3902110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902133 : List Nat := [1, 3, 3, 3, 1, 1, 3, 1, 1, 6]
def baseStart_3902133 : Nat := 118140960795 + 3902133 * 2 ^ 59
def prefixEnd_3902133 : Nat := 4983230072969 + 3 ^ 40 * 3902133 * 2
def baseEnd_3902133 : Nat := 667889935590295540130641

theorem tailTrace_3902133 : CollatzResearch.WordTrace tailWord_3902133 prefixEnd_3902133 667889935590295540130641 := by
  unfold tailWord_3902133
  simp only [CollatzResearch.WordTrace]
  refine ⟨142322482772246047104207053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94881655181497364736138035 142322482772246047104207053)
  ·
    refine ⟨53370931039592267664077645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142322482772246047104207053 53370931039592267664077645)
    ·
      refine ⟨20014099139847100374029117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53370931039592267664077645 20014099139847100374029117)
      ·
        refine ⟨7505287177442662640260919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20014099139847100374029117 7505287177442662640260919)
        ·
          refine ⟨11257930766163993960391379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7505287177442662640260919 11257930766163993960391379)
          ·
            refine ⟨16886896149245990940587069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11257930766163993960391379 16886896149245990940587069)
            ·
              refine ⟨6332586055967246602720151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16886896149245990940587069 6332586055967246602720151)
              ·
                refine ⟨9498879083950869904080227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6332586055967246602720151 9498879083950869904080227)
                ·
                  refine ⟨14248318625926304856120341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9498879083950869904080227 14248318625926304856120341)
                  ·
                    refine ⟨667889935590295540130641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14248318625926304856120341 667889935590295540130641)
                    ·
                      rfl

theorem cell23_3902133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_3902133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902133 prefixEnd_3902133 := by exact prefixLift 3902133
  have htrace : WordTrace (prefixWord ++ tailWord_3902133) baseStart_3902133 baseEnd_3902133 := by
    simpa [prefixWord, tailWord_3902133, baseEnd_3902133] using wordTrace_append hprefix tailTrace_3902133
  have hstable : (prefixWord ++ tailWord_3902133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902133).length < 2 ^ (prefixWord ++ tailWord_3902133).sum := by decide
  have hdescent : baseEnd_3902133 < baseStart_3902133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902140 : List Nat := [2, 2, 2, 3, 1, 1, 1, 4, 3, 2, 2]
def baseStart_3902140 : Nat := 118140960795 + 3902140 * 2 ^ 59
def prefixEnd_3902140 : Nat := 4983230072969 + 3 ^ 40 * 3902140 * 2
def baseEnd_3902140 : Nat := 2003673401135468093004391

theorem tailTrace_3902140 : CollatzResearch.WordTrace tailWord_3902140 prefixEnd_3902140 2003673401135468093004391 := by
  unfold tailWord_3902140
  simp only [CollatzResearch.WordTrace]
  refine ⟨71161369041610343649855937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94881825388813791533141249 71161369041610343649855937)
  ·
    refine ⟨53371026781207757737391953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71161369041610343649855937 53371026781207757737391953)
    ·
      refine ⟨40028270085905818303043965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53371026781207757737391953 40028270085905818303043965)
      ·
        refine ⟨15010601282214681863641487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40028270085905818303043965 15010601282214681863641487)
        ·
          refine ⟨22515901923322022795462231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15010601282214681863641487 22515901923322022795462231)
          ·
            refine ⟨33773852884983034193193347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22515901923322022795462231 33773852884983034193193347)
            ·
              refine ⟨50660779327474551289790021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33773852884983034193193347 50660779327474551289790021)
              ·
                refine ⟨9498896123901478366835629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50660779327474551289790021 9498896123901478366835629)
                ·
                  refine ⟨3562086046463054387563361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9498896123901478366835629 3562086046463054387563361)
                  ·
                    refine ⟨2671564534847290790672521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3562086046463054387563361 2671564534847290790672521)
                    ·
                      refine ⟨2003673401135468093004391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2671564534847290790672521 2003673401135468093004391)
                      ·
                        rfl

theorem cell23_3902140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_3902140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902140 prefixEnd_3902140 := by exact prefixLift 3902140
  have htrace : WordTrace (prefixWord ++ tailWord_3902140) baseStart_3902140 baseEnd_3902140 := by
    simpa [prefixWord, tailWord_3902140, baseEnd_3902140] using wordTrace_append hprefix tailTrace_3902140
  have hstable : (prefixWord ++ tailWord_3902140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902140).length < 2 ^ (prefixWord ++ tailWord_3902140).sum := by decide
  have hdescent : baseEnd_3902140 < baseStart_3902140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902143 : List Nat := [1, 1, 2, 2, 2, 4, 1, 4, 1, 2, 3]
def baseStart_3902143 : Nat := 118140960795 + 3902143 * 2 ^ 59
def prefixEnd_3902143 : Nat := 4983230072969 + 3 ^ 40 * 3902143 * 2
def baseEnd_3902143 : Nat := 2003674941577431581266877

theorem tailTrace_3902143 : CollatzResearch.WordTrace tailWord_3902143 prefixEnd_3902143 2003674941577431581266877 := by
  unfold tailWord_3902143
  simp only [CollatzResearch.WordTrace]
  refine ⟨142322847502209818812071083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94881898334806545874714055 142322847502209818812071083)
  ·
    refine ⟨213484271253314728218106625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142322847502209818812071083 213484271253314728218106625)
    ·
      refine ⟨160113203439986046163579969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213484271253314728218106625 160113203439986046163579969)
      ·
        refine ⟨120084902579989534622684977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160113203439986046163579969 120084902579989534622684977)
        ·
          refine ⟨90063676934992150967013733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120084902579989534622684977 90063676934992150967013733)
          ·
            refine ⟨16886939425311028306315075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90063676934992150967013733 16886939425311028306315075)
            ·
              refine ⟨25330409137966542459472613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16886939425311028306315075 25330409137966542459472613)
              ·
                refine ⟨4749451713368726711151115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25330409137966542459472613 4749451713368726711151115)
                ·
                  refine ⟨7124177570053090066726673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4749451713368726711151115 7124177570053090066726673)
                  ·
                    refine ⟨5343133177539817550045005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7124177570053090066726673 5343133177539817550045005)
                    ·
                      refine ⟨2003674941577431581266877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5343133177539817550045005 2003674941577431581266877)
                      ·
                        rfl

theorem cell23_3902143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 2, 3].length) (baseStart_3902143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902143 prefixEnd_3902143 := by exact prefixLift 3902143
  have htrace : WordTrace (prefixWord ++ tailWord_3902143) baseStart_3902143 baseEnd_3902143 := by
    simpa [prefixWord, tailWord_3902143, baseEnd_3902143] using wordTrace_append hprefix tailTrace_3902143
  have hstable : (prefixWord ++ tailWord_3902143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902143).length < 2 ^ (prefixWord ++ tailWord_3902143).sum := by decide
  have hdescent : baseEnd_3902143 < baseStart_3902143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902159 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 3, 9]
def baseStart_3902159 : Nat := 118140960795 + 3902159 * 2 ^ 59
def prefixEnd_3902159 : Nat := 4983230072969 + 3 ^ 40 * 3902159 * 2
def baseEnd_3902159 : Nat := 667894385755967839555601

theorem tailTrace_3902159 : CollatzResearch.WordTrace tailWord_3902159 prefixEnd_3902159 667894385755967839555601 := by
  unfold tailWord_3902159
  simp only [CollatzResearch.WordTrace]
  refine ⟨142323431070151853544653531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94882287380101235696435687 142323431070151853544653531)
  ·
    refine ⟨213485146605227780316980297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142323431070151853544653531 213485146605227780316980297)
    ·
      refine ⟨160113859953920835237735223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213485146605227780316980297 160113859953920835237735223)
      ·
        refine ⟨240170789930881252856602835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160113859953920835237735223 240170789930881252856602835)
        ·
          refine ⟨360256184896321879284904253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240170789930881252856602835 360256184896321879284904253)
          ·
            refine ⟨135096069336120704731839095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360256184896321879284904253 135096069336120704731839095)
            ·
              refine ⟨202644104004181057097758643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135096069336120704731839095 202644104004181057097758643)
              ·
                refine ⟨303966156006271585646637965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202644104004181057097758643 303966156006271585646637965)
                ·
                  refine ⟨113987308502351844617489237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 303966156006271585646637965 113987308502351844617489237)
                  ·
                    refine ⟨667894385755967839555601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 113987308502351844617489237 667894385755967839555601)
                    ·
                      rfl

theorem cell23_3902159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 9].length) (baseStart_3902159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902159 prefixEnd_3902159 := by exact prefixLift 3902159
  have htrace : WordTrace (prefixWord ++ tailWord_3902159) baseStart_3902159 baseEnd_3902159 := by
    simpa [prefixWord, tailWord_3902159, baseEnd_3902159] using wordTrace_append hprefix tailTrace_3902159
  have hstable : (prefixWord ++ tailWord_3902159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902159).length < 2 ^ (prefixWord ++ tailWord_3902159).sum := by decide
  have hdescent : baseEnd_3902159 < baseStart_3902159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902184 : List Nat := [2, 1, 4, 1, 5, 1, 2, 1, 2, 4]
def baseStart_3902184 : Nat := 118140960795 + 3902184 * 2 ^ 59
def prefixEnd_3902184 : Nat := 4983230072969 + 3 ^ 40 * 3902184 * 2
def baseEnd_3902184 : Nat := 667898664761421973618063

theorem tailTrace_3902184 : CollatzResearch.WordTrace tailWord_3902184 prefixEnd_3902184 667898664761421973618063 := by
  unfold tailWord_3902184
  simp only [CollatzResearch.WordTrace]
  refine ⟨71162171447530641407156803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94882895263374188542875737 71162171447530641407156803)
  ·
    refine ⟨106743257171295962110735205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71162171447530641407156803 106743257171295962110735205)
    ·
      refine ⟨20014360719617992895762851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106743257171295962110735205 20014360719617992895762851)
      ·
        refine ⟨30021541079426989343644277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20014360719617992895762851 30021541079426989343644277)
        ·
          refine ⟨2814519476196280250966651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30021541079426989343644277 2814519476196280250966651)
          ·
            refine ⟨4221779214294420376449977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2814519476196280250966651 4221779214294420376449977)
            ·
              refine ⟨3166334410720815282337483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4221779214294420376449977 3166334410720815282337483)
              ·
                refine ⟨4749501616081222923506225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3166334410720815282337483 4749501616081222923506225)
                ·
                  refine ⟨3562126212060917192629669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4749501616081222923506225 3562126212060917192629669)
                  ·
                    refine ⟨667898664761421973618063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3562126212060917192629669 667898664761421973618063)
                    ·
                      rfl

theorem cell23_3902184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_3902184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902184 prefixEnd_3902184 := by exact prefixLift 3902184
  have htrace : WordTrace (prefixWord ++ tailWord_3902184) baseStart_3902184 baseEnd_3902184 := by
    simpa [prefixWord, tailWord_3902184, baseEnd_3902184] using wordTrace_append hprefix tailTrace_3902184
  have hstable : (prefixWord ++ tailWord_3902184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902184).length < 2 ^ (prefixWord ++ tailWord_3902184).sum := by decide
  have hdescent : baseEnd_3902184 < baseStart_3902184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902323 : List Nat := [1, 1, 1, 2, 2, 1, 6, 1, 1, 4, 3]
def baseStart_3902323 : Nat := 118140960795 + 3902323 * 2 ^ 59
def prefixEnd_3902323 : Nat := 4983230072969 + 3 ^ 40 * 3902323 * 2
def baseEnd_3902323 : Nat := 2003767368095240877016049

theorem tailTrace_3902323 : CollatzResearch.WordTrace tailWord_3902323 prefixEnd_3902323 2003767368095240877016049 := by
  unfold tailWord_3902323
  simp only [CollatzResearch.WordTrace]
  refine ⟨142329412641557709553623623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94886275094371806369082415 142329412641557709553623623)
  ·
    refine ⟨213494118962336564330435435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142329412641557709553623623 213494118962336564330435435)
    ·
      refine ⟨320241178443504846495653153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213494118962336564330435435 320241178443504846495653153)
      ·
        refine ⟨240180883832628634871739865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320241178443504846495653153 240180883832628634871739865)
        ·
          refine ⟨180135662874471476153804899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240180883832628634871739865 180135662874471476153804899)
          ·
            refine ⟨270203494311707214230707349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180135662874471476153804899 270203494311707214230707349)
            ·
              refine ⟨12665788795861275667064407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 270203494311707214230707349 12665788795861275667064407)
              ·
                refine ⟨18998683193791913500596611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12665788795861275667064407 18998683193791913500596611)
                ·
                  refine ⟨28498024790687870250894917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18998683193791913500596611 28498024790687870250894917)
                  ·
                    refine ⟨5343379648253975672042797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28498024790687870250894917 5343379648253975672042797)
                    ·
                      refine ⟨2003767368095240877016049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5343379648253975672042797 2003767368095240877016049)
                      ·
                        rfl

theorem cell23_3902323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 4, 3].length) (baseStart_3902323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902323 prefixEnd_3902323 := by exact prefixLift 3902323
  have htrace : WordTrace (prefixWord ++ tailWord_3902323) baseStart_3902323 baseEnd_3902323 := by
    simpa [prefixWord, tailWord_3902323, baseEnd_3902323] using wordTrace_append hprefix tailTrace_3902323
  have hstable : (prefixWord ++ tailWord_3902323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902323).length < 2 ^ (prefixWord ++ tailWord_3902323).sum := by decide
  have hdescent : baseEnd_3902323 < baseStart_3902323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902343 : List Nat := [1, 1, 4, 2, 3, 1, 2, 1, 8]
def baseStart_3902343 : Nat := 118140960795 + 3902343 * 2 ^ 59
def prefixEnd_3902343 : Nat := 4983230072969 + 3 ^ 40 * 3902343 * 2
def baseEnd_3902343 : Nat := 222641959745370088751773

theorem tailTrace_3902343 : CollatzResearch.WordTrace tailWord_3902343 prefixEnd_3902343 222641959745370088751773 := by
  unfold tailWord_3902343
  simp only [CollatzResearch.WordTrace]
  refine ⟨142330142101485252969351683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94886761400990168646234455 142330142101485252969351683)
  ·
    refine ⟨213495213152227879454027525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142330142101485252969351683 213495213152227879454027525)
    ·
      refine ⟨40030352466042727397630161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213495213152227879454027525 40030352466042727397630161)
      ·
        refine ⟨30022764349532045548222621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40030352466042727397630161 30022764349532045548222621)
        ·
          refine ⟨11258536631074517080583483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30022764349532045548222621 11258536631074517080583483)
          ·
            refine ⟨16887804946611775620875225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11258536631074517080583483 16887804946611775620875225)
            ·
              refine ⟨12665853709958831715656419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16887804946611775620875225 12665853709958831715656419)
              ·
                refine ⟨18998780564938247573484629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12665853709958831715656419 18998780564938247573484629)
                ·
                  refine ⟨222641959745370088751773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18998780564938247573484629 222641959745370088751773)
                  ·
                    rfl

theorem cell23_3902343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 8].length) (baseStart_3902343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902343 prefixEnd_3902343 := by exact prefixLift 3902343
  have htrace : WordTrace (prefixWord ++ tailWord_3902343) baseStart_3902343 baseEnd_3902343 := by
    simpa [prefixWord, tailWord_3902343, baseEnd_3902343] using wordTrace_append hprefix tailTrace_3902343
  have hstable : (prefixWord ++ tailWord_3902343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902343).length < 2 ^ (prefixWord ++ tailWord_3902343).sum := by decide
  have hdescent : baseEnd_3902343 < baseStart_3902343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902380 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 6, 3, 2]
def baseStart_3902380 : Nat := 118140960795 + 3902380 * 2 ^ 59
def prefixEnd_3902380 : Nat := 4983230072969 + 3 ^ 40 * 3902380 * 2
def baseEnd_3902380 : Nat := 2003796636492547154003287

theorem tailTrace_3902380 : CollatzResearch.WordTrace tailWord_3902380 prefixEnd_3902380 2003796636492547154003287 := by
  unfold tailWord_3902380
  simp only [CollatzResearch.WordTrace]
  refine ⟨71165745801175604144224297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94887661068234138858965729 71165745801175604144224297)
  ·
    refine ⟨53374309350881703108168223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71165745801175604144224297 53374309350881703108168223)
    ·
      refine ⟨80061464026322554662252335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53374309350881703108168223 80061464026322554662252335)
      ·
        refine ⟨120092196039483831993378503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80061464026322554662252335 120092196039483831993378503)
        ·
          refine ⟨180138294059225747990067755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120092196039483831993378503 180138294059225747990067755)
          ·
            refine ⟨270207441088838621985101633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180138294059225747990067755 270207441088838621985101633)
            ·
              refine ⟨202655580816628966488826225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270207441088838621985101633 202655580816628966488826225)
              ·
                refine ⟨151991685612471724866619669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202655580816628966488826225 151991685612471724866619669)
                ·
                  refine ⟨7124610263084612103122797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 151991685612471724866619669 7124610263084612103122797)
                  ·
                    refine ⟨2671728848656729538671049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7124610263084612103122797 2671728848656729538671049)
                    ·
                      refine ⟨2003796636492547154003287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2671728848656729538671049 2003796636492547154003287)
                      ·
                        rfl

theorem cell23_3902380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 3, 2].length) (baseStart_3902380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902380 prefixEnd_3902380 := by exact prefixLift 3902380
  have htrace : WordTrace (prefixWord ++ tailWord_3902380) baseStart_3902380 baseEnd_3902380 := by
    simpa [prefixWord, tailWord_3902380, baseEnd_3902380] using wordTrace_append hprefix tailTrace_3902380
  have hstable : (prefixWord ++ tailWord_3902380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902380).length < 2 ^ (prefixWord ++ tailWord_3902380).sum := by decide
  have hdescent : baseEnd_3902380 < baseStart_3902380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902410 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 2, 6, 2]
def baseStart_3902410 : Nat := 118140960795 + 3902410 * 2 ^ 59
def prefixEnd_3902410 : Nat := 4983230072969 + 3 ^ 40 * 3902410 * 2
def baseEnd_3902410 : Nat := 2003812040912182036628149

theorem tailTrace_3902410 : CollatzResearch.WordTrace tailWord_3902410 prefixEnd_3902410 2003812040912182036628149 := by
  unfold tailWord_3902410
  simp only [CollatzResearch.WordTrace]
  refine ⟨35583146448060630853010171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94888390528161682274693789 35583146448060630853010171)
  ·
    refine ⟨53374719672090946279515257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35583146448060630853010171 53374719672090946279515257)
    ·
      refine ⟨40031039754068209709636443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53374719672090946279515257 40031039754068209709636443)
      ·
        refine ⟨60046559631102314564454665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40031039754068209709636443 60046559631102314564454665)
        ·
          refine ⟨45034919723326735923340999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60046559631102314564454665 45034919723326735923340999)
          ·
            refine ⟨67552379584990103885011499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45034919723326735923340999 67552379584990103885011499)
            ·
              refine ⟨101328569377485155827517249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67552379584990103885011499 101328569377485155827517249)
              ·
                refine ⟨75996427033113866870637937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101328569377485155827517249 75996427033113866870637937)
                ·
                  refine ⟨56997320274835400152978453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75996427033113866870637937 56997320274835400152978453)
                  ·
                    refine ⟨2671749387882909382170865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 56997320274835400152978453 2671749387882909382170865)
                    ·
                      refine ⟨2003812040912182036628149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2671749387882909382170865 2003812040912182036628149)
                      ·
                        rfl

theorem cell23_3902410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 2, 6, 2].length) (baseStart_3902410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902410 prefixEnd_3902410 := by exact prefixLift 3902410
  have htrace : WordTrace (prefixWord ++ tailWord_3902410) baseStart_3902410 baseEnd_3902410 := by
    simpa [prefixWord, tailWord_3902410, baseEnd_3902410] using wordTrace_append hprefix tailTrace_3902410
  have hstable : (prefixWord ++ tailWord_3902410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902410).length < 2 ^ (prefixWord ++ tailWord_3902410).sum := by decide
  have hdescent : baseEnd_3902410 < baseStart_3902410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902420 : List Nat := [2, 4, 1, 2, 1, 2, 1, 3, 1, 6]
def baseStart_3902420 : Nat := 118140960795 + 3902420 * 2 ^ 59
def prefixEnd_3902420 : Nat := 4983230072969 + 3 ^ 40 * 3902420 * 2
def baseEnd_3902420 : Nat := 667939058572908999167701

theorem tailTrace_3902420 : CollatzResearch.WordTrace tailWord_3902420 prefixEnd_3902420 667939058572908999167701 := by
  unfold tailWord_3902420
  simp only [CollatzResearch.WordTrace]
  refine ⟨71166475261103147559952357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94888633681470863413269809 71166475261103147559952357)
  ·
    refine ⟨13343714111456840167491067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71166475261103147559952357 13343714111456840167491067)
    ·
      refine ⟨20015571167185260251236601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13343714111456840167491067 20015571167185260251236601)
      ·
        refine ⟨15011678375388945188427451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20015571167185260251236601 15011678375388945188427451)
        ·
          refine ⟨22517517563083417782641177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15011678375388945188427451 22517517563083417782641177)
          ·
            refine ⟨16888138172312563336980883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22517517563083417782641177 16888138172312563336980883)
            ·
              refine ⟨25332207258468845005471325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16888138172312563336980883 25332207258468845005471325)
              ·
                refine ⟨9499577721925816877051747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25332207258468845005471325 9499577721925816877051747)
                ·
                  refine ⟨14249366582888725315577621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9499577721925816877051747 14249366582888725315577621)
                  ·
                    refine ⟨667939058572908999167701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14249366582888725315577621 667939058572908999167701)
                    ·
                      rfl

theorem cell23_3902420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_3902420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902420 prefixEnd_3902420 := by exact prefixLift 3902420
  have htrace : WordTrace (prefixWord ++ tailWord_3902420) baseStart_3902420 baseEnd_3902420 := by
    simpa [prefixWord, tailWord_3902420, baseEnd_3902420] using wordTrace_append hprefix tailTrace_3902420
  have hstable : (prefixWord ++ tailWord_3902420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902420).length < 2 ^ (prefixWord ++ tailWord_3902420).sum := by decide
  have hdescent : baseEnd_3902420 < baseStart_3902420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902431 : List Nat := [1, 1, 2, 3, 6, 1, 1, 1, 2, 3, 2]
def baseStart_3902431 : Nat := 118140960795 + 3902431 * 2 ^ 59
def prefixEnd_3902431 : Nat := 4983230072969 + 3 ^ 40 * 3902431 * 2
def baseEnd_3902431 : Nat := 2003822824005926454465553

theorem tailTrace_3902431 : CollatzResearch.WordTrace tailWord_3902431 prefixEnd_3902431 2003822824005926454465553 := by
  unfold tailWord_3902431
  simp only [CollatzResearch.WordTrace]
  refine ⟨142333351725166443998555147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94888901150110962665703431 142333351725166443998555147)
  ·
    refine ⟨213500027587749665997832721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142333351725166443998555147 213500027587749665997832721)
    ·
      refine ⟨160125020690812249498374541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213500027587749665997832721 160125020690812249498374541)
      ·
        refine ⟨60046882759054593561890453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160125020690812249498374541 60046882759054593561890453)
        ·
          refine ⟨2814697629330684073213615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 60046882759054593561890453 2814697629330684073213615)
          ·
            refine ⟨4222046443996026109820423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2814697629330684073213615 4222046443996026109820423)
            ·
              refine ⟨6333069665994039164730635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4222046443996026109820423 6333069665994039164730635)
              ·
                refine ⟨9499604498991058747095953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6333069665994039164730635 9499604498991058747095953)
                ·
                  refine ⟨7124703374243294060321965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9499604498991058747095953 7124703374243294060321965)
                  ·
                    refine ⟨2671763765341235272620737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7124703374243294060321965 2671763765341235272620737)
                    ·
                      refine ⟨2003822824005926454465553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2671763765341235272620737 2003822824005926454465553)
                      ·
                        rfl

theorem cell23_3902431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 2, 3, 2].length) (baseStart_3902431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902431 prefixEnd_3902431 := by exact prefixLift 3902431
  have htrace : WordTrace (prefixWord ++ tailWord_3902431) baseStart_3902431 baseEnd_3902431 := by
    simpa [prefixWord, tailWord_3902431, baseEnd_3902431] using wordTrace_append hprefix tailTrace_3902431
  have hstable : (prefixWord ++ tailWord_3902431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902431).length < 2 ^ (prefixWord ++ tailWord_3902431).sum := by decide
  have hdescent : baseEnd_3902431 < baseStart_3902431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902440 : List Nat := [2, 1, 4, 1, 1, 1, 4, 2, 1, 2, 4]
def baseStart_3902440 : Nat := 118140960795 + 3902440 * 2 ^ 59
def prefixEnd_3902440 : Nat := 4983230072969 + 3 ^ 40 * 3902440 * 2
def baseEnd_3902440 : Nat := 2003827445331816919253011

theorem tailTrace_3902440 : CollatzResearch.WordTrace tailWord_3902440 prefixEnd_3902440 2003827445331816919253011 := by
  unfold tailWord_3902440
  simp only [CollatzResearch.WordTrace]
  refine ⟨71166839991066919267816387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94889119988089225690421849 71166839991066919267816387)
  ·
    refine ⟨106750259986600378901724581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71166839991066919267816387 106750259986600378901724581)
    ·
      refine ⟨20015673747487571044073359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106750259986600378901724581 20015673747487571044073359)
      ·
        refine ⟨30023510621231356566110039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20015673747487571044073359 30023510621231356566110039)
        ·
          refine ⟨45035265931847034849165059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30023510621231356566110039 45035265931847034849165059)
          ·
            refine ⟨67552898897770552273747589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45035265931847034849165059 67552898897770552273747589)
            ·
              refine ⟨12666168543331978551327673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67552898897770552273747589 12666168543331978551327673)
              ·
                refine ⟨9499626407498983913495755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12666168543331978551327673 9499626407498983913495755)
                ·
                  refine ⟨14249439611248475870243633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9499626407498983913495755 14249439611248475870243633)
                  ·
                    refine ⟨10687079708436356902682725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14249439611248475870243633 10687079708436356902682725)
                    ·
                      refine ⟨2003827445331816919253011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10687079708436356902682725 2003827445331816919253011)
                      ·
                        rfl

theorem cell23_3902440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_3902440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902440 prefixEnd_3902440 := by exact prefixLift 3902440
  have htrace : WordTrace (prefixWord ++ tailWord_3902440) baseStart_3902440 baseEnd_3902440 := by
    simpa [prefixWord, tailWord_3902440, baseEnd_3902440] using wordTrace_append hprefix tailTrace_3902440
  have hstable : (prefixWord ++ tailWord_3902440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902440).length < 2 ^ (prefixWord ++ tailWord_3902440).sum := by decide
  have hdescent : baseEnd_3902440 < baseStart_3902440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902447 : List Nat := [1, 1, 2, 1, 4, 4, 1, 3, 1, 2, 3]
def baseStart_3902447 : Nat := 118140960795 + 3902447 * 2 ^ 59
def prefixEnd_3902447 : Nat := 4983230072969 + 3 ^ 40 * 3902447 * 2
def baseEnd_3902447 : Nat := 2003831039696398391865479

theorem tailTrace_3902447 : CollatzResearch.WordTrace tailWord_3902447 prefixEnd_3902447 2003831039696398391865479 := by
  unfold tailWord_3902447
  simp only [CollatzResearch.WordTrace]
  refine ⟨142333935293108478731137595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94889290195405652487425063 142333935293108478731137595)
  ·
    refine ⟨213500902939662718096706393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142333935293108478731137595 213500902939662718096706393)
    ·
      refine ⟨160125677204747038572529795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213500902939662718096706393 160125677204747038572529795)
      ·
        refine ⟨240188515807120557858794693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160125677204747038572529795 240188515807120557858794693)
        ·
          refine ⟨45035346713835104598524005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 240188515807120557858794693 45035346713835104598524005)
          ·
            refine ⟨8444127508844082112223251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45035346713835104598524005 8444127508844082112223251)
            ·
              refine ⟨12666191263266123168334877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8444127508844082112223251 12666191263266123168334877)
              ·
                refine ⟨4749821723724796188125579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12666191263266123168334877 4749821723724796188125579)
                ·
                  refine ⟨7124732585587194282188369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4749821723724796188125579 7124732585587194282188369)
                  ·
                    refine ⟨5343549439190395711641277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7124732585587194282188369 5343549439190395711641277)
                    ·
                      refine ⟨2003831039696398391865479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5343549439190395711641277 2003831039696398391865479)
                      ·
                        rfl

theorem cell23_3902447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 2, 3].length) (baseStart_3902447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902447 prefixEnd_3902447 := by exact prefixLift 3902447
  have htrace : WordTrace (prefixWord ++ tailWord_3902447) baseStart_3902447 baseEnd_3902447 := by
    simpa [prefixWord, tailWord_3902447, baseEnd_3902447] using wordTrace_append hprefix tailTrace_3902447
  have hstable : (prefixWord ++ tailWord_3902447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902447).length < 2 ^ (prefixWord ++ tailWord_3902447).sum := by decide
  have hdescent : baseEnd_3902447 < baseStart_3902447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902454 : List Nat := [5, 1, 1, 1, 3, 1, 3, 2, 2, 4]
def baseStart_3902454 : Nat := 118140960795 + 3902454 * 2 ^ 59
def prefixEnd_3902454 : Nat := 4983230072969 + 3 ^ 40 * 3902454 * 2
def baseEnd_3902454 : Nat := 667944878020326621492649

theorem tailTrace_3902454 : CollatzResearch.WordTrace tailWord_3902454 prefixEnd_3902454 667944878020326621492649 := by
  unfold tailWord_3902454
  simp only [CollatzResearch.WordTrace]
  refine ⟨8895886912755194932915151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94889460402722079284428277 8895886912755194932915151)
  ·
    refine ⟨13343830369132792399372727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8895886912755194932915151 13343830369132792399372727)
    ·
      refine ⟨20015745553699188599059091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13343830369132792399372727 20015745553699188599059091)
      ·
        refine ⟨30023618330548782898588637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20015745553699188599059091 30023618330548782898588637)
        ·
          refine ⟨11258856873955793586970739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30023618330548782898588637 11258856873955793586970739)
          ·
            refine ⟨16888285310933690380456109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11258856873955793586970739 16888285310933690380456109)
            ·
              refine ⟨6333106991600133892671041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16888285310933690380456109 6333106991600133892671041)
              ·
                refine ⟨4749830243700100419503281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6333106991600133892671041 4749830243700100419503281)
                ·
                  refine ⟨3562372682775075314627461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4749830243700100419503281 3562372682775075314627461)
                  ·
                    refine ⟨667944878020326621492649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3562372682775075314627461 667944878020326621492649)
                    ·
                      rfl

theorem cell23_3902454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_3902454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902454 prefixEnd_3902454 := by exact prefixLift 3902454
  have htrace : WordTrace (prefixWord ++ tailWord_3902454) baseStart_3902454 baseEnd_3902454 := by
    simpa [prefixWord, tailWord_3902454, baseEnd_3902454] using wordTrace_append hprefix tailTrace_3902454
  have hstable : (prefixWord ++ tailWord_3902454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902454).length < 2 ^ (prefixWord ++ tailWord_3902454).sum := by decide
  have hdescent : baseEnd_3902454 < baseStart_3902454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902473 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 4, 2, 5]
def baseStart_3902473 : Nat := 118140960795 + 3902473 * 2 ^ 59
def prefixEnd_3902473 : Nat := 4983230072969 + 3 ^ 40 * 3902473 * 2
def baseEnd_3902473 : Nat := 2003844390193415290140359

theorem tailTrace_3902473 : CollatzResearch.WordTrace tailWord_3902473 prefixEnd_3902473 2003844390193415290140359 := by
  unfold tailWord_3902473
  simp only [CollatzResearch.WordTrace]
  refine ⟨142334883591014285171584073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94889922394009523447722715 142334883591014285171584073)
  ·
    refine ⟨106751162693260713878688055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142334883591014285171584073 106751162693260713878688055)
    ·
      refine ⟨160126744039891070818032083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106751162693260713878688055 160126744039891070818032083)
      ·
        refine ⟨240190116059836606227048125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160126744039891070818032083 240190116059836606227048125)
        ·
          refine ⟨90071293522438727335143047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240190116059836606227048125 90071293522438727335143047)
          ·
            refine ⟨135106940283658091002714571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90071293522438727335143047 135106940283658091002714571)
            ·
              refine ⟨202660410425487136504071857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135106940283658091002714571 202660410425487136504071857)
              ·
                refine ⟨151995307819115352378053893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202660410425487136504071857 151995307819115352378053893)
                ·
                  refine ⟨28499120216084128570885105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151995307819115352378053893 28499120216084128570885105)
                  ·
                    refine ⟨21374340162063096428163829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28499120216084128570885105 21374340162063096428163829)
                    ·
                      refine ⟨2003844390193415290140359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21374340162063096428163829 2003844390193415290140359)
                      ·
                        rfl

theorem cell23_3902473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 2, 5].length) (baseStart_3902473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902473 prefixEnd_3902473 := by exact prefixLift 3902473
  have htrace : WordTrace (prefixWord ++ tailWord_3902473) baseStart_3902473 baseEnd_3902473 := by
    simpa [prefixWord, tailWord_3902473, baseEnd_3902473] using wordTrace_append hprefix tailTrace_3902473
  have hstable : (prefixWord ++ tailWord_3902473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902473).length < 2 ^ (prefixWord ++ tailWord_3902473).sum := by decide
  have hdescent : baseEnd_3902473 < baseStart_3902473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902574 : List Nat := [4, 1, 2, 2, 1, 3, 1, 4, 5]
def baseStart_3902574 : Nat := 118140960795 + 3902574 * 2 ^ 59
def prefixEnd_3902574 : Nat := 4983230072969 + 3 ^ 40 * 3902574 * 2
def baseEnd_3902574 : Nat := 222655139082168821664155

theorem tailTrace_3902574 : CollatzResearch.WordTrace tailWord_3902574 prefixEnd_3902574 222655139082168821664155 := by
  unfold tailWord_3902574
  simp only [CollatzResearch.WordTrace]
  refine ⟨17792320920456047427626347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94892378242432252947340517 17792320920456047427626347)
  ·
    refine ⟨26688481380684071141439521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17792320920456047427626347 26688481380684071141439521)
    ·
      refine ⟨20016361035513053356079641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26688481380684071141439521 20016361035513053356079641)
      ·
        refine ⟨15012270776634790017059731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20016361035513053356079641 15012270776634790017059731)
        ·
          refine ⟨22518406164952185025589597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15012270776634790017059731 22518406164952185025589597)
          ·
            refine ⟨8444402311857069384596099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22518406164952185025589597 8444402311857069384596099)
            ·
              refine ⟨12666603467785604076894149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8444402311857069384596099 12666603467785604076894149)
              ·
                refine ⟨2374988150209800764417653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12666603467785604076894149 2374988150209800764417653)
                ·
                  refine ⟨222655139082168821664155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2374988150209800764417653 222655139082168821664155)
                  ·
                    rfl

theorem cell23_3902574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 4, 5].length) (baseStart_3902574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902574 prefixEnd_3902574 := by exact prefixLift 3902574
  have htrace : WordTrace (prefixWord ++ tailWord_3902574) baseStart_3902574 baseEnd_3902574 := by
    simpa [prefixWord, tailWord_3902574, baseEnd_3902574] using wordTrace_append hprefix tailTrace_3902574
  have hstable : (prefixWord ++ tailWord_3902574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902574).length < 2 ^ (prefixWord ++ tailWord_3902574).sum := by decide
  have hdescent : baseEnd_3902574 < baseStart_3902574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902627 : List Nat := [1, 1, 1, 4, 1, 1, 1, 6, 2, 2, 3]
def baseStart_3902627 : Nat := 118140960795 + 3902627 * 2 ^ 59
def prefixEnd_3902627 : Nat := 4983230072969 + 3 ^ 40 * 3902627 * 2
def baseEnd_3902627 : Nat := 2003923466214207687614651

theorem tailTrace_3902627 : CollatzResearch.WordTrace tailWord_3902627 prefixEnd_3902627 2003923466214207687614651 := by
  unfold tailWord_3902627
  simp only [CollatzResearch.WordTrace]
  refine ⟨142340500432456369472690135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94893666954970912981793423 142340500432456369472690135)
  ·
    refine ⟨213510750648684554209035203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142340500432456369472690135 213510750648684554209035203)
    ·
      refine ⟨320266125973026831313552805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213510750648684554209035203 320266125973026831313552805)
      ·
        refine ⟨60049898619942530871291151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 320266125973026831313552805 60049898619942530871291151)
        ·
          refine ⟨90074847929913796306936727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60049898619942530871291151 90074847929913796306936727)
          ·
            refine ⟨135112271894870694460405091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90074847929913796306936727 135112271894870694460405091)
            ·
              refine ⟨202668407842306041690607637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135112271894870694460405091 202668407842306041690607637)
              ·
                refine ⟨9500081617608095704247233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 202668407842306041690607637 9500081617608095704247233)
                ·
                  refine ⟨7125061213206071778185425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9500081617608095704247233 7125061213206071778185425)
                  ·
                    refine ⟨5343795909904553833639069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7125061213206071778185425 5343795909904553833639069)
                    ·
                      refine ⟨2003923466214207687614651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5343795909904553833639069 2003923466214207687614651)
                      ·
                        rfl

theorem cell23_3902627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_3902627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902627 prefixEnd_3902627 := by exact prefixLift 3902627
  have htrace : WordTrace (prefixWord ++ tailWord_3902627) baseStart_3902627 baseEnd_3902627 := by
    simpa [prefixWord, tailWord_3902627, baseEnd_3902627] using wordTrace_append hprefix tailTrace_3902627
  have hstable : (prefixWord ++ tailWord_3902627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902627).length < 2 ^ (prefixWord ++ tailWord_3902627).sum := by decide
  have hdescent : baseEnd_3902627 < baseStart_3902627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902650 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 3, 2, 6]
def baseStart_3902650 : Nat := 118140960795 + 3902650 * 2 ^ 59
def prefixEnd_3902650 : Nat := 4983230072969 + 3 ^ 40 * 3902650 * 2
def baseEnd_3902650 : Nat := 2003935276269261097627045

theorem tailTrace_3902650 : CollatzResearch.WordTrace tailWord_3902650 prefixEnd_3902650 2003935276269261097627045 := by
  unfold tailWord_3902650
  simp only [CollatzResearch.WordTrace]
  refine ⟨35585334827843261100194351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94894226207582029600518269 35585334827843261100194351)
  ·
    refine ⟨53378002241764891650291527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35585334827843261100194351 53378002241764891650291527)
    ·
      refine ⟨80067003362647337475437291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53378002241764891650291527 80067003362647337475437291)
      ·
        refine ⟨120100505043971006213155937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80067003362647337475437291 120100505043971006213155937)
        ·
          refine ⟨90075378782978254659866953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120100505043971006213155937 90075378782978254659866953)
          ·
            refine ⟨67556534087233690994900215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90075378782978254659866953 67556534087233690994900215)
            ·
              refine ⟨101334801130850536492350323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67556534087233690994900215 101334801130850536492350323)
              ·
                refine ⟨152002201696275804738525485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101334801130850536492350323 152002201696275804738525485)
                ·
                  refine ⟨57000825636103426776947057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152002201696275804738525485 57000825636103426776947057)
                  ·
                    refine ⟨42750619227077570082710293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57000825636103426776947057 42750619227077570082710293)
                    ·
                      refine ⟨2003935276269261097627045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42750619227077570082710293 2003935276269261097627045)
                      ·
                        rfl

theorem cell23_3902650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_3902650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902650 prefixEnd_3902650 := by exact prefixLift 3902650
  have htrace : WordTrace (prefixWord ++ tailWord_3902650) baseStart_3902650 baseEnd_3902650 := by
    simpa [prefixWord, tailWord_3902650, baseEnd_3902650] using wordTrace_append hprefix tailTrace_3902650
  have hstable : (prefixWord ++ tailWord_3902650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902650).length < 2 ^ (prefixWord ++ tailWord_3902650).sum := by decide
  have hdescent : baseEnd_3902650 < baseStart_3902650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902678 : List Nat := [5, 2, 1, 2, 2, 1, 1, 2, 2, 2, 3]
def baseStart_3902678 : Nat := 118140960795 + 3902678 * 2 ^ 59
def prefixEnd_3902678 : Nat := 4983230072969 + 3 ^ 40 * 3902678 * 2
def baseEnd_3902678 : Nat := 2003949653727586988076917

theorem tailTrace_3902678 : CollatzResearch.WordTrace tailWord_3902678 prefixEnd_3902678 2003949653727586988076917 := by
  unfold tailWord_3902678
  simp only [CollatzResearch.WordTrace]
  refine ⟨8896397534704475323924793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94894907036847736788531125 8896397534704475323924793)
  ·
    refine ⟨6672298151028356492943595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8896397534704475323924793 6672298151028356492943595)
    ·
      refine ⟨10008447226542534739415393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6672298151028356492943595 10008447226542534739415393)
      ·
        refine ⟨7506335419906901054561545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10008447226542534739415393 7506335419906901054561545)
        ·
          refine ⟨5629751564930175790921159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7506335419906901054561545 5629751564930175790921159)
          ·
            refine ⟨8444627347395263686381739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5629751564930175790921159 8444627347395263686381739)
            ·
              refine ⟨12666941021092895529572609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8444627347395263686381739 12666941021092895529572609)
              ·
                refine ⟨9500205765819671647179457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12666941021092895529572609 9500205765819671647179457)
                ·
                  refine ⟨7125154324364753735384593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9500205765819671647179457 7125154324364753735384593)
                  ·
                    refine ⟨5343865743273565301538445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7125154324364753735384593 5343865743273565301538445)
                    ·
                      refine ⟨2003949653727586988076917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5343865743273565301538445 2003949653727586988076917)
                      ·
                        rfl

theorem cell23_3902678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_3902678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902678 prefixEnd_3902678 := by exact prefixLift 3902678
  have htrace : WordTrace (prefixWord ++ tailWord_3902678) baseStart_3902678 baseEnd_3902678 := by
    simpa [prefixWord, tailWord_3902678, baseEnd_3902678] using wordTrace_append hprefix tailTrace_3902678
  have hstable : (prefixWord ++ tailWord_3902678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902678).length < 2 ^ (prefixWord ++ tailWord_3902678).sum := by decide
  have hdescent : baseEnd_3902678 < baseStart_3902678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902685 : List Nat := [1, 4, 3, 2, 2, 1, 3, 2, 1, 4]
def baseStart_3902685 : Nat := 118140960795 + 3902685 * 2 ^ 59
def prefixEnd_3902685 : Nat := 4983230072969 + 3 ^ 40 * 3902685 * 2
def baseEnd_3902685 : Nat := 667984416030722820229795

theorem tailTrace_3902685 : CollatzResearch.WordTrace tailWord_3902685 prefixEnd_3902685 667984416030722820229795 := by
  unfold tailWord_3902685
  simp only [CollatzResearch.WordTrace]
  refine ⟨142342615866246245378301509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94895077244164163585534339 142342615866246245378301509)
  ·
    refine ⟨26689240474921171008431533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142342615866246245378301509 26689240474921171008431533)
    ·
      refine ⟨10008465178095439128161825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26689240474921171008431533 10008465178095439128161825)
      ·
        refine ⟨7506348883571579346121369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10008465178095439128161825 7506348883571579346121369)
        ·
          refine ⟨5629761662678684509591027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7506348883571579346121369 5629761662678684509591027)
          ·
            refine ⟨8444642494018026764386541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5629761662678684509591027 8444642494018026764386541)
            ·
              refine ⟨3166740935256760036644953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8444642494018026764386541 3166740935256760036644953)
              ·
                refine ⟨2375055701442570027483715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3166740935256760036644953 2375055701442570027483715)
                ·
                  refine ⟨3562583552163855041225573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2375055701442570027483715 3562583552163855041225573)
                  ·
                    refine ⟨667984416030722820229795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3562583552163855041225573 667984416030722820229795)
                    ·
                      rfl

theorem cell23_3902685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_3902685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902685 prefixEnd_3902685 := by exact prefixLift 3902685
  have htrace : WordTrace (prefixWord ++ tailWord_3902685) baseStart_3902685 baseEnd_3902685 := by
    simpa [prefixWord, tailWord_3902685, baseEnd_3902685] using wordTrace_append hprefix tailTrace_3902685
  have hstable : (prefixWord ++ tailWord_3902685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902685).length < 2 ^ (prefixWord ++ tailWord_3902685).sum := by decide
  have hdescent : baseEnd_3902685 < baseStart_3902685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902718 : List Nat := [4, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2]
def baseStart_3902718 : Nat := 118140960795 + 3902718 * 2 ^ 59
def prefixEnd_3902718 : Nat := 4983230072969 + 3 ^ 40 * 3902718 * 2
def baseEnd_3902718 : Nat := 2003970192953766831576733

theorem tailTrace_3902718 : CollatzResearch.WordTrace tailWord_3902718 prefixEnd_3902718 2003970192953766831576733 := by
  unfold tailWord_3902718
  simp only [CollatzResearch.WordTrace]
  refine ⟨17792977434390836501781601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94895879650084461342835205 17792977434390836501781601)
  ·
    refine ⟨13344733075793127376336201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17792977434390836501781601 13344733075793127376336201)
    ·
      refine ⟨10008549806844845532252151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13344733075793127376336201 10008549806844845532252151)
      ·
        refine ⟨15012824710267268298378227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10008549806844845532252151 15012824710267268298378227)
        ·
          refine ⟨22519237065400902447567341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15012824710267268298378227 22519237065400902447567341)
          ·
            refine ⟨8444713899525338417837753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22519237065400902447567341 8444713899525338417837753)
            ·
              refine ⟨6333535424644003813378315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8444713899525338417837753 6333535424644003813378315)
              ·
                refine ⟨9500303136966005720067473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6333535424644003813378315 9500303136966005720067473)
                ·
                  refine ⟨7125227352724504290050605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9500303136966005720067473 7125227352724504290050605)
                  ·
                    refine ⟨2671960257271689108768977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7125227352724504290050605 2671960257271689108768977)
                    ·
                      refine ⟨2003970192953766831576733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2671960257271689108768977 2003970192953766831576733)
                      ·
                        rfl

theorem cell23_3902718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_3902718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902718 prefixEnd_3902718 := by exact prefixLift 3902718
  have htrace : WordTrace (prefixWord ++ tailWord_3902718) baseStart_3902718 baseEnd_3902718 := by
    simpa [prefixWord, tailWord_3902718, baseEnd_3902718] using wordTrace_append hprefix tailTrace_3902718
  have hstable : (prefixWord ++ tailWord_3902718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902718).length < 2 ^ (prefixWord ++ tailWord_3902718).sum := by decide
  have hdescent : baseEnd_3902718 < baseStart_3902718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902724 : List Nat := [2, 3, 2, 2, 2, 2, 1, 2, 1, 6]
def baseStart_3902724 : Nat := 118140960795 + 3902724 * 2 ^ 59
def prefixEnd_3902724 : Nat := 4983230072969 + 3 ^ 40 * 3902724 * 2
def baseEnd_3902724 : Nat := 667991091279231269367235

theorem tailTrace_3902724 : CollatzResearch.WordTrace tailWord_3902724 prefixEnd_3902724 667991091279231269367235 := by
  unfold tailWord_3902724
  simp only [CollatzResearch.WordTrace]
  refine ⟨71172019156552477519485613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94896025542069970025980817 71172019156552477519485613)
  ·
    refine ⟨26689507183707179069807105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71172019156552477519485613 26689507183707179069807105)
    ·
      refine ⟨20017130387780384302355329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26689507183707179069807105 20017130387780384302355329)
      ·
        refine ⟨15012847790835288226766497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20017130387780384302355329 15012847790835288226766497)
        ·
          refine ⟨11259635843126466170074873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15012847790835288226766497 11259635843126466170074873)
          ·
            refine ⟨8444726882344849627556155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11259635843126466170074873 8444726882344849627556155)
            ·
              refine ⟨12667090323517274441334233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8444726882344849627556155 12667090323517274441334233)
              ·
                refine ⟨9500317742637955831000675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12667090323517274441334233 9500317742637955831000675)
                ·
                  refine ⟨14250476613956933746501013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9500317742637955831000675 14250476613956933746501013)
                  ·
                    refine ⟨667991091279231269367235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14250476613956933746501013 667991091279231269367235)
                    ·
                      rfl

theorem cell23_3902724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_3902724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902724 prefixEnd_3902724 := by exact prefixLift 3902724
  have htrace : WordTrace (prefixWord ++ tailWord_3902724) baseStart_3902724 baseEnd_3902724 := by
    simpa [prefixWord, tailWord_3902724, baseEnd_3902724] using wordTrace_append hprefix tailTrace_3902724
  have hstable : (prefixWord ++ tailWord_3902724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902724).length < 2 ^ (prefixWord ++ tailWord_3902724).sum := by decide
  have hdescent : baseEnd_3902724 < baseStart_3902724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902731 : List Nat := [1, 1, 1, 1, 5, 4, 3, 1, 1, 1, 4]
def baseStart_3902731 : Nat := 118140960795 + 3902731 * 2 ^ 59
def prefixEnd_3902731 : Nat := 4983230072969 + 3 ^ 40 * 3902731 * 2
def baseEnd_3902731 : Nat := 2003976868202275280714173

theorem tailTrace_3902731 : CollatzResearch.WordTrace tailWord_3902731 prefixEnd_3902731 2003976868202275280714173 := by
  unfold tailWord_3902731
  simp only [CollatzResearch.WordTrace]
  refine ⟨142344293624079595234476047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94896195749386396822984031 142344293624079595234476047)
  ·
    refine ⟨213516440436119392851714071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142344293624079595234476047 213516440436119392851714071)
    ·
      refine ⟨320274660654179089277571107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213516440436119392851714071 320274660654179089277571107)
      ·
        refine ⟨480411990981268633916356661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320274660654179089277571107 480411990981268633916356661)
        ·
          refine ⟨45038624154493934429658437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 480411990981268633916356661 45038624154493934429658437)
          ·
            refine ⟨8444742028967612705560957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45038624154493934429658437 8444742028967612705560957)
            ·
              refine ⟨3166778260862854764585359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8444742028967612705560957 3166778260862854764585359)
              ·
                refine ⟨4750167391294282146878039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3166778260862854764585359 4750167391294282146878039)
                ·
                  refine ⟨7125251086941423220317059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4750167391294282146878039 7125251086941423220317059)
                  ·
                    refine ⟨10687876630412134830475589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7125251086941423220317059 10687876630412134830475589)
                    ·
                      refine ⟨2003976868202275280714173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10687876630412134830475589 2003976868202275280714173)
                      ·
                        rfl

theorem cell23_3902731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 1, 1, 4].length) (baseStart_3902731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902731 prefixEnd_3902731 := by exact prefixLift 3902731
  have htrace : WordTrace (prefixWord ++ tailWord_3902731) baseStart_3902731 baseEnd_3902731 := by
    simpa [prefixWord, tailWord_3902731, baseEnd_3902731] using wordTrace_append hprefix tailTrace_3902731
  have hstable : (prefixWord ++ tailWord_3902731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902731).length < 2 ^ (prefixWord ++ tailWord_3902731).sum := by decide
  have hdescent : baseEnd_3902731 < baseStart_3902731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902734 : List Nat := [4, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5]
def baseStart_3902734 : Nat := 118140960795 + 3902734 * 2 ^ 59
def prefixEnd_3902734 : Nat := 4983230072969 + 3 ^ 40 * 3902734 * 2
def baseEnd_3902734 : Nat := 2003978408644238768976659

theorem tailTrace_3902734 : CollatzResearch.WordTrace tailWord_3902734 prefixEnd_3902734 2003978408644238768976659 := by
  unfold tailWord_3902734
  simp only [CollatzResearch.WordTrace]
  refine ⟨17793050380383590843354407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94896268695379151164556837 17793050380383590843354407)
  ·
    refine ⟨26689575570575386265031611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17793050380383590843354407 26689575570575386265031611)
    ·
      refine ⟨40034363355863079397547417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26689575570575386265031611 40034363355863079397547417)
      ·
        refine ⟨30025772516897309548160563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40034363355863079397547417 30025772516897309548160563)
        ·
          refine ⟨45038658775345964322240845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30025772516897309548160563 45038658775345964322240845)
          ·
            refine ⟨16889497040754736620840317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45038658775345964322240845 16889497040754736620840317)
            ·
              refine ⟨6333561390283026232815119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16889497040754736620840317 6333561390283026232815119)
              ·
                refine ⟨9500342085424539349222679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6333561390283026232815119 9500342085424539349222679)
                ·
                  refine ⟨14250513128136809023834019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9500342085424539349222679 14250513128136809023834019)
                  ·
                    refine ⟨21375769692205213535751029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14250513128136809023834019 21375769692205213535751029)
                    ·
                      refine ⟨2003978408644238768976659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21375769692205213535751029 2003978408644238768976659)
                      ·
                        rfl

theorem cell23_3902734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_3902734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902734 prefixEnd_3902734 := by exact prefixLift 3902734
  have htrace : WordTrace (prefixWord ++ tailWord_3902734) baseStart_3902734 baseEnd_3902734 := by
    simpa [prefixWord, tailWord_3902734, baseEnd_3902734] using wordTrace_append hprefix tailTrace_3902734
  have hstable : (prefixWord ++ tailWord_3902734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902734).length < 2 ^ (prefixWord ++ tailWord_3902734).sum := by decide
  have hdescent : baseEnd_3902734 < baseStart_3902734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902747 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 5, 3, 3]
def baseStart_3902747 : Nat := 118140960795 + 3902747 * 2 ^ 59
def prefixEnd_3902747 : Nat := 4983230072969 + 3 ^ 40 * 3902747 * 2
def baseEnd_3902747 : Nat := 2003985083892747218114099

theorem tailTrace_3902747 : CollatzResearch.WordTrace tailWord_3902747 prefixEnd_3902747 2003985083892747218114099 := by
  unfold tailWord_3902747
  simp only [CollatzResearch.WordTrace]
  refine ⟨142344877192021629967058495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94896584794681086644705663 142344877192021629967058495)
  ·
    refine ⟨213517315788032444950587743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142344877192021629967058495 213517315788032444950587743)
    ·
      refine ⟨320275973682048667425881615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213517315788032444950587743 320275973682048667425881615)
      ·
        refine ⟨480413960523073001138822423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320275973682048667425881615 480413960523073001138822423)
        ·
          refine ⟨720620940784609501708233635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480413960523073001138822423 720620940784609501708233635)
          ·
            refine ⟨1080931411176914252562350453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 720620940784609501708233635 1080931411176914252562350453)
            ·
              refine ⟨101337319797835711177720355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1080931411176914252562350453 101337319797835711177720355)
              ·
                refine ⟨152005979696753566766580533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101337319797835711177720355 152005979696753566766580533)
                ·
                  refine ⟨14250560596570646884366925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 152005979696753566766580533 14250560596570646884366925)
                  ·
                    refine ⟨5343960223713992581637597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14250560596570646884366925 5343960223713992581637597)
                    ·
                      refine ⟨2003985083892747218114099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5343960223713992581637597 2003985083892747218114099)
                      ·
                        rfl

theorem cell23_3902747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 3, 3].length) (baseStart_3902747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902747 prefixEnd_3902747 := by exact prefixLift 3902747
  have htrace : WordTrace (prefixWord ++ tailWord_3902747) baseStart_3902747 baseEnd_3902747 := by
    simpa [prefixWord, tailWord_3902747, baseEnd_3902747] using wordTrace_append hprefix tailTrace_3902747
  have hstable : (prefixWord ++ tailWord_3902747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902747).length < 2 ^ (prefixWord ++ tailWord_3902747).sum := by decide
  have hdescent : baseEnd_3902747 < baseStart_3902747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902764 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 3]
def baseStart_3902764 : Nat := 118140960795 + 3902764 * 2 ^ 59
def prefixEnd_3902764 : Nat := 4983230072969 + 3 ^ 40 * 3902764 * 2
def baseEnd_3902764 : Nat := 2003993813063873651601521

theorem tailTrace_3902764 : CollatzResearch.WordTrace tailWord_3902764 prefixEnd_3902764 2003993813063873651601521 := by
  unfold tailWord_3902764
  simp only [CollatzResearch.WordTrace]
  refine ⟨71172748616480020935213673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94896998155306694580284897 71172748616480020935213673)
  ·
    refine ⟨53379561462360015701410255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71172748616480020935213673 53379561462360015701410255)
    ·
      refine ⟨80069342193540023552115383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53379561462360015701410255 80069342193540023552115383)
      ·
        refine ⟨120104013290310035328173075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80069342193540023552115383 120104013290310035328173075)
        ·
          refine ⟨180156019935465052992259613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120104013290310035328173075 180156019935465052992259613)
          ·
            refine ⟨67558507475799394872097355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180156019935465052992259613 67558507475799394872097355)
            ·
              refine ⟨101337761213699092308146033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67558507475799394872097355 101337761213699092308146033)
              ·
                refine ⟨76003320910274319231109525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101337761213699092308146033 76003320910274319231109525)
                ·
                  refine ⟨3562655667669108713958259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 76003320910274319231109525 3562655667669108713958259)
                  ·
                    refine ⟨5343983501503663070937389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3562655667669108713958259 5343983501503663070937389)
                    ·
                      refine ⟨2003993813063873651601521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5343983501503663070937389 2003993813063873651601521)
                      ·
                        rfl

theorem cell23_3902764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 3].length) (baseStart_3902764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902764 prefixEnd_3902764 := by exact prefixLift 3902764
  have htrace : WordTrace (prefixWord ++ tailWord_3902764) baseStart_3902764 baseEnd_3902764 := by
    simpa [prefixWord, tailWord_3902764, baseEnd_3902764] using wordTrace_append hprefix tailTrace_3902764
  have hstable : (prefixWord ++ tailWord_3902764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902764).length < 2 ^ (prefixWord ++ tailWord_3902764).sum := by decide
  have hdescent : baseEnd_3902764 < baseStart_3902764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902765 : List Nat := [1, 5, 3, 1, 1, 2, 1, 2, 3, 2, 2]
def baseStart_3902765 : Nat := 118140960795 + 3902765 * 2 ^ 59
def prefixEnd_3902765 : Nat := 4983230072969 + 3 ^ 40 * 3902765 * 2
def baseEnd_3902765 : Nat := 2003994326544528147689017

theorem tailTrace_3902765 : CollatzResearch.WordTrace tailWord_3902765 prefixEnd_3902765 2003994326544528147689017 := by
  unfold tailWord_3902765
  simp only [CollatzResearch.WordTrace]
  refine ⟨142345533705956419041213749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94897022470637612694142499 142345533705956419041213749)
  ·
    refine ⟨13344893784933414285113789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142345533705956419041213749 13344893784933414285113789)
    ·
      refine ⟨5004335169350030356917671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13344893784933414285113789 5004335169350030356917671)
      ·
        refine ⟨7506502754025045535376507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5004335169350030356917671 7506502754025045535376507)
        ·
          refine ⟨11259754131037568303064761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7506502754025045535376507 11259754131037568303064761)
          ·
            refine ⟨8444815598278176227298571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11259754131037568303064761 8444815598278176227298571)
            ·
              refine ⟨12667223397417264340947857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8444815598278176227298571 12667223397417264340947857)
              ·
                refine ⟨9500417548062948255710893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12667223397417264340947857 9500417548062948255710893)
                ·
                  refine ⟨3562656580523605595891585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9500417548062948255710893 3562656580523605595891585)
                  ·
                    refine ⟨2671992435392704196918689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3562656580523605595891585 2671992435392704196918689)
                    ·
                      refine ⟨2003994326544528147689017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2671992435392704196918689 2003994326544528147689017)
                      ·
                        rfl

theorem cell23_3902765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_3902765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902765 prefixEnd_3902765 := by exact prefixLift 3902765
  have htrace : WordTrace (prefixWord ++ tailWord_3902765) baseStart_3902765 baseEnd_3902765 := by
    simpa [prefixWord, tailWord_3902765, baseEnd_3902765] using wordTrace_append hprefix tailTrace_3902765
  have hstable : (prefixWord ++ tailWord_3902765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902765).length < 2 ^ (prefixWord ++ tailWord_3902765).sum := by decide
  have hdescent : baseEnd_3902765 < baseStart_3902765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902785 : List Nat := [1, 2, 5, 2, 1, 3, 2, 1, 1, 2, 3]
def baseStart_3902785 : Nat := 118140960795 + 3902785 * 2 ^ 59
def prefixEnd_3902785 : Nat := 4983230072969 + 3 ^ 40 * 3902785 * 2
def baseEnd_3902785 : Nat := 2004004596157618069438925

theorem tailTrace_3902785 : CollatzResearch.WordTrace tailWord_3902785 prefixEnd_3902785 2004004596157618069438925 := by
  unfold tailWord_3902785
  simp only [CollatzResearch.WordTrace]
  refine ⟨142346263165883962456941809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94897508777255974971294539 142346263165883962456941809)
  ·
    refine ⟨106759697374412971842706357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142346263165883962456941809 106759697374412971842706357)
    ·
      refine ⟨10008721628851216110253721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106759697374412971842706357 10008721628851216110253721)
      ·
        refine ⟨7506541221638412082690291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10008721628851216110253721 7506541221638412082690291)
        ·
          refine ⟨11259811832457618124035437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7506541221638412082690291 11259811832457618124035437)
          ·
            refine ⟨4222429437171606796513289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11259811832457618124035437 4222429437171606796513289)
            ·
              refine ⟨3166822077878705097384967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4222429437171606796513289 3166822077878705097384967)
              ·
                refine ⟨4750233116818057646077451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3166822077878705097384967 4750233116818057646077451)
                ·
                  refine ⟨7125349675227086469116177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4750233116818057646077451 7125349675227086469116177)
                  ·
                    refine ⟨5344012256420314851837133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7125349675227086469116177 5344012256420314851837133)
                    ·
                      refine ⟨2004004596157618069438925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5344012256420314851837133 2004004596157618069438925)
                      ·
                        rfl

theorem cell23_3902785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_3902785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902785 prefixEnd_3902785 := by exact prefixLift 3902785
  have htrace : WordTrace (prefixWord ++ tailWord_3902785) baseStart_3902785 baseEnd_3902785 := by
    simpa [prefixWord, tailWord_3902785, baseEnd_3902785] using wordTrace_append hprefix tailTrace_3902785
  have hstable : (prefixWord ++ tailWord_3902785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902785).length < 2 ^ (prefixWord ++ tailWord_3902785).sum := by decide
  have hdescent : baseEnd_3902785 < baseStart_3902785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902874 : List Nat := [3, 1, 1, 4, 1, 1, 1, 2, 4, 5]
def baseStart_3902874 : Nat := 118140960795 + 3902874 * 2 ^ 59
def prefixEnd_3902874 : Nat := 4983230072969 + 3 ^ 40 * 3902874 * 2
def baseEnd_3902874 : Nat := 668016765311956073742005

theorem tailTrace_3902874 : CollatzResearch.WordTrace tailWord_3902874 prefixEnd_3902874 668016765311956073742005 := by
  unfold tailWord_3902874
  simp only [CollatzResearch.WordTrace]
  refine ⟨35587377315640382664232919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94899672841707687104621117 35587377315640382664232919)
  ·
    refine ⟨53381065973460573996349379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35587377315640382664232919 53381065973460573996349379)
    ·
      refine ⟨80071598960190860994524069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53381065973460573996349379 80071598960190860994524069)
      ·
        refine ⟨15013424805035786436473263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80071598960190860994524069 15013424805035786436473263)
        ·
          refine ⟨22520137207553679654709895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15013424805035786436473263 22520137207553679654709895)
          ·
            refine ⟨33780205811330519482064843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22520137207553679654709895 33780205811330519482064843)
            ·
              refine ⟨50670308716995779223097265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33780205811330519482064843 50670308716995779223097265)
              ·
                refine ⟨38002731537746834417322949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50670308716995779223097265 38002731537746834417322949)
                ·
                  refine ⟨7125512163327531453248053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38002731537746834417322949 7125512163327531453248053)
                  ·
                    refine ⟨668016765311956073742005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7125512163327531453248053 668016765311956073742005)
                    ·
                      rfl

theorem cell23_3902874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 4, 5].length) (baseStart_3902874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902874 prefixEnd_3902874 := by exact prefixLift 3902874
  have htrace : WordTrace (prefixWord ++ tailWord_3902874) baseStart_3902874 baseEnd_3902874 := by
    simpa [prefixWord, tailWord_3902874, baseEnd_3902874] using wordTrace_append hprefix tailTrace_3902874
  have hstable : (prefixWord ++ tailWord_3902874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902874).length < 2 ^ (prefixWord ++ tailWord_3902874).sum := by decide
  have hdescent : baseEnd_3902874 < baseStart_3902874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3902944 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 3]
def baseStart_3902944 : Nat := 118140960795 + 3902944 * 2 ^ 59
def prefixEnd_3902944 : Nat := 4983230072969 + 3 ^ 40 * 3902944 * 2
def baseEnd_3902944 : Nat := 2004086239581682947350693

theorem tailTrace_3902944 : CollatzResearch.WordTrace tailWord_3902944 prefixEnd_3902944 2004086239581682947350693 := by
  unfold tailWord_3902944
  simp only [CollatzResearch.WordTrace]
  refine ⟨71176031186153966305989943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94901374914871955074653257 71176031186153966305989943)
  ·
    refine ⟨106764046779230949458984915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71176031186153966305989943 106764046779230949458984915)
    ·
      refine ⟨160146070168846424188477373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106764046779230949458984915 160146070168846424188477373)
      ·
        refine ⟨60054776313317409070679015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160146070168846424188477373 60054776313317409070679015)
        ·
          refine ⟨90082164469976113606018523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60054776313317409070679015 90082164469976113606018523)
          ·
            refine ⟨135123246704964170409027785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90082164469976113606018523 135123246704964170409027785)
            ·
              refine ⟨101342435028723127806770839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135123246704964170409027785 101342435028723127806770839)
              ·
                refine ⟨152013652543084691710156259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101342435028723127806770839 152013652543084691710156259)
                ·
                  refine ⟨228020478814627037565234389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152013652543084691710156259 228020478814627037565234389)
                  ·
                    refine ⟨5344229972217821192935181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 228020478814627037565234389 5344229972217821192935181)
                    ·
                      refine ⟨2004086239581682947350693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5344229972217821192935181 2004086239581682947350693)
                      ·
                        rfl

theorem cell23_3902944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_3902944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3902944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3902944 prefixEnd_3902944 := by exact prefixLift 3902944
  have htrace : WordTrace (prefixWord ++ tailWord_3902944) baseStart_3902944 baseEnd_3902944 := by
    simpa [prefixWord, tailWord_3902944, baseEnd_3902944] using wordTrace_append hprefix tailTrace_3902944
  have hstable : (prefixWord ++ tailWord_3902944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3902944).length < 2 ^ (prefixWord ++ tailWord_3902944).sum := by decide
  have hdescent : baseEnd_3902944 < baseStart_3902944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3902944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903018 : List Nat := [3, 1, 4, 1, 1, 1, 1, 5, 1, 1, 4]
def baseStart_3903018 : Nat := 118140960795 + 3903018 * 2 ^ 59
def prefixEnd_3903018 : Nat := 4983230072969 + 3 ^ 40 * 3903018 * 2
def baseEnd_3903018 : Nat := 2004124237150115657825353

theorem tailTrace_3903018 : CollatzResearch.WordTrace tailWord_3903018 prefixEnd_3903018 2004124237150115657825353 := by
  unfold tailWord_3903018
  simp only [CollatzResearch.WordTrace]
  refine ⟨35588690343509960812543427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94903174249359895500115805 35588690343509960812543427)
  ·
    refine ⟨53383035515264941218815141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35588690343509960812543427 53383035515264941218815141)
    ·
      refine ⟨10009319159112176478527839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53383035515264941218815141 10009319159112176478527839)
      ·
        refine ⟨15013978738668264717791759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10009319159112176478527839 15013978738668264717791759)
        ·
          refine ⟨22520968108002397076687639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15013978738668264717791759 22520968108002397076687639)
          ·
            refine ⟨33781452162003595615031459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22520968108002397076687639 33781452162003595615031459)
            ·
              refine ⟨50672178243005393422547189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33781452162003595615031459 50672178243005393422547189)
              ·
                refine ⟨4750516710281755633363799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50672178243005393422547189 4750516710281755633363799)
                ·
                  refine ⟨7125775065422633450045699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4750516710281755633363799 7125775065422633450045699)
                  ·
                    refine ⟨10688662598133950175068549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7125775065422633450045699 10688662598133950175068549)
                    ·
                      refine ⟨2004124237150115657825353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10688662598133950175068549 2004124237150115657825353)
                      ·
                        rfl

theorem cell23_3903018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_3903018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903018 prefixEnd_3903018 := by exact prefixLift 3903018
  have htrace : WordTrace (prefixWord ++ tailWord_3903018) baseStart_3903018 baseEnd_3903018 := by
    simpa [prefixWord, tailWord_3903018, baseEnd_3903018] using wordTrace_append hprefix tailTrace_3903018
  have hstable : (prefixWord ++ tailWord_3903018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903018).length < 2 ^ (prefixWord ++ tailWord_3903018).sum := by decide
  have hdescent : baseEnd_3903018 < baseStart_3903018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903041 : List Nat := [1, 2, 5, 1, 1, 1, 4, 8]
def baseStart_3903041 : Nat := 118140960795 + 3903041 * 2 ^ 59
def prefixEnd_3903041 : Nat := 4983230072969 + 3 ^ 40 * 3903041 * 2
def baseEnd_3903041 : Nat := 74227261007598854364361

theorem tailTrace_3903041 : CollatzResearch.WordTrace tailWord_3903041 prefixEnd_3903041 74227261007598854364361 := by
  unfold tailWord_3903041
  simp only [CollatzResearch.WordTrace]
  refine ⟨142355600252956518178260977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94903733501971012118840651 142355600252956518178260977)
  ·
    refine ⟨106766700189717388633695733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142355600252956518178260977 106766700189717388633695733)
    ·
      refine ⟨10009378142786005184408975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106766700189717388633695733 10009378142786005184408975)
      ·
        refine ⟨15014067214179007776613463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10009378142786005184408975 15014067214179007776613463)
        ·
          refine ⟨22521100821268511664920195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15014067214179007776613463 22521100821268511664920195)
          ·
            refine ⟨33781651231902767497380293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22521100821268511664920195 33781651231902767497380293)
            ·
              refine ⟨6334059605981768905758805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33781651231902767497380293 6334059605981768905758805)
              ·
                refine ⟨74227261007598854364361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6334059605981768905758805 74227261007598854364361)
                ·
                  rfl

theorem cell23_3903041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 8].length) (baseStart_3903041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903041 prefixEnd_3903041 := by exact prefixLift 3903041
  have htrace : WordTrace (prefixWord ++ tailWord_3903041) baseStart_3903041 baseEnd_3903041 := by
    simpa [prefixWord, tailWord_3903041, baseEnd_3903041] using wordTrace_append hprefix tailTrace_3903041
  have hstable : (prefixWord ++ tailWord_3903041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903041).length < 2 ^ (prefixWord ++ tailWord_3903041).sum := by decide
  have hdescent : baseEnd_3903041 < baseStart_3903041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903051 : List Nat := [1, 1, 1, 1, 3, 1, 3, 5, 1, 3, 3]
def baseStart_3903051 : Nat := 118140960795 + 3903051 * 2 ^ 59
def prefixEnd_3903051 : Nat := 4983230072969 + 3 ^ 40 * 3903051 * 2
def baseEnd_3903051 : Nat := 2004141182011714028712701

theorem tailTrace_3903051 : CollatzResearch.WordTrace tailWord_3903051 prefixEnd_3903051 2004141182011714028712701 := by
  unfold tailWord_3903051
  simp only [CollatzResearch.WordTrace]
  refine ⟨142355964982920289886125007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94903976655280193257416671 142355964982920289886125007)
  ·
    refine ⟨213533947474380434829187511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142355964982920289886125007 213533947474380434829187511)
    ·
      refine ⟨320300921211570652243781267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213533947474380434829187511 320300921211570652243781267)
      ·
        refine ⟨480451381817355978365671901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320300921211570652243781267 480451381817355978365671901)
        ·
          refine ⟨180169268181508491887126963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 480451381817355978365671901 180169268181508491887126963)
          ·
            refine ⟨270253902272262737830690445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180169268181508491887126963 270253902272262737830690445)
            ·
              refine ⟨101345213352098526686508917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270253902272262737830690445 101345213352098526686508917)
              ·
                refine ⟨9501113751759236876860211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101345213352098526686508917 9501113751759236876860211)
                ·
                  refine ⟨14251670627638855315290317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9501113751759236876860211 14251670627638855315290317)
                  ·
                    refine ⟨5344376485364570743233869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14251670627638855315290317 5344376485364570743233869)
                    ·
                      refine ⟨2004141182011714028712701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5344376485364570743233869 2004141182011714028712701)
                      ·
                        rfl

theorem cell23_3903051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 3, 3].length) (baseStart_3903051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903051 prefixEnd_3903051 := by exact prefixLift 3903051
  have htrace : WordTrace (prefixWord ++ tailWord_3903051) baseStart_3903051 baseEnd_3903051 := by
    simpa [prefixWord, tailWord_3903051, baseEnd_3903051] using wordTrace_append hprefix tailTrace_3903051
  have hstable : (prefixWord ++ tailWord_3903051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903051).length < 2 ^ (prefixWord ++ tailWord_3903051).sum := by decide
  have hdescent : baseEnd_3903051 < baseStart_3903051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903062 : List Nat := [5, 2, 2, 2, 1, 1, 1, 2, 1, 6]
def baseStart_3903062 : Nat := 118140960795 + 3903062 * 2 ^ 59
def prefixEnd_3903062 : Nat := 4983230072969 + 3 ^ 40 * 3903062 * 2
def baseEnd_3903062 : Nat := 668048943432971161891717

theorem tailTrace_3903062 : CollatzResearch.WordTrace tailWord_3903062 prefixEnd_3903062 668048943432971161891717 := by
  unfold tailWord_3903062
  simp only [CollatzResearch.WordTrace]
  refine ⟨8897272886617527422798465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94904244123920292509850293 8897272886617527422798465)
  ·
    refine ⟨6672954664963145567098849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8897272886617527422798465 6672954664963145567098849)
    ·
      refine ⟨5004715998722359175324137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6672954664963145567098849 5004715998722359175324137)
      ·
        refine ⟨3753536999041769381493103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5004715998722359175324137 3753536999041769381493103)
        ·
          refine ⟨5630305498562654072239655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3753536999041769381493103 5630305498562654072239655)
          ·
            refine ⟨8445458247843981108359483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5630305498562654072239655 8445458247843981108359483)
            ·
              refine ⟨12668187371765971662539225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8445458247843981108359483 12668187371765971662539225)
              ·
                refine ⟨9501140528824478746904419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12668187371765971662539225 9501140528824478746904419)
                ·
                  refine ⟨14251710793236718120356629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9501140528824478746904419 14251710793236718120356629)
                  ·
                    refine ⟨668048943432971161891717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14251710793236718120356629 668048943432971161891717)
                    ·
                      rfl

theorem cell23_3903062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_3903062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903062 prefixEnd_3903062 := by exact prefixLift 3903062
  have htrace : WordTrace (prefixWord ++ tailWord_3903062) baseStart_3903062 baseEnd_3903062 := by
    simpa [prefixWord, tailWord_3903062, baseEnd_3903062] using wordTrace_append hprefix tailTrace_3903062
  have hstable : (prefixWord ++ tailWord_3903062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903062).length < 2 ^ (prefixWord ++ tailWord_3903062).sum := by decide
  have hdescent : baseEnd_3903062 < baseStart_3903062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903068 : List Nat := [2, 2, 4, 1, 2, 1, 1, 1, 3, 3, 3]
def baseStart_3903068 : Nat := 118140960795 + 3903068 * 2 ^ 59
def prefixEnd_3903068 : Nat := 4983230072969 + 3 ^ 40 * 3903068 * 2
def baseEnd_3903068 : Nat := 2004149911182840462200123

theorem tailTrace_3903068 : CollatzResearch.WordTrace tailWord_3903068 prefixEnd_3903068 2004149911182840462200123 := by
  unfold tailWord_3903068
  simp only [CollatzResearch.WordTrace]
  refine ⟨71178292511929350894746929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94904390015905801192995905 71178292511929350894746929)
  ·
    refine ⟨53383719383947013171060197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71178292511929350894746929 53383719383947013171060197)
    ·
      refine ⟨10009447384490064969573787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53383719383947013171060197 10009447384490064969573787)
      ·
        refine ⟨15014171076735097454360681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10009447384490064969573787 15014171076735097454360681)
        ·
          refine ⟨11260628307551323090770511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15014171076735097454360681 11260628307551323090770511)
          ·
            refine ⟨16890942461326984636155767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11260628307551323090770511 16890942461326984636155767)
            ·
              refine ⟨25336413691990476954233651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16890942461326984636155767 25336413691990476954233651)
              ·
                refine ⟨38004620537985715431350477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25336413691990476954233651 38004620537985715431350477)
                ·
                  refine ⟨14251732701744643286756429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38004620537985715431350477 14251732701744643286756429)
                  ·
                    refine ⟨5344399763154241232533661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14251732701744643286756429 5344399763154241232533661)
                    ·
                      refine ⟨2004149911182840462200123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5344399763154241232533661 2004149911182840462200123)
                      ·
                        rfl

theorem cell23_3903068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_3903068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903068 prefixEnd_3903068 := by exact prefixLift 3903068
  have htrace : WordTrace (prefixWord ++ tailWord_3903068) baseStart_3903068 baseEnd_3903068 := by
    simpa [prefixWord, tailWord_3903068, baseEnd_3903068] using wordTrace_append hprefix tailTrace_3903068
  have hstable : (prefixWord ++ tailWord_3903068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903068).length < 2 ^ (prefixWord ++ tailWord_3903068).sum := by decide
  have hdescent : baseEnd_3903068 < baseStart_3903068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903069 : List Nat := [1, 4, 4, 2, 1, 1, 3, 1, 1, 1, 4]
def baseStart_3903069 : Nat := 118140960795 + 3903069 * 2 ^ 59
def prefixEnd_3903069 : Nat := 4983230072969 + 3 ^ 40 * 3903069 * 2
def baseEnd_3903069 : Nat := 2004150424663494958287619

theorem tailTrace_3903069 : CollatzResearch.WordTrace tailWord_3903069 prefixEnd_3903069 2004150424663494958287619 := by
  unfold tailWord_3903069
  simp only [CollatzResearch.WordTrace]
  refine ⟨142356621496855078960280261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94904414331236719306853507 142356621496855078960280261)
  ·
    refine ⟨26691866530660327305052549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142356621496855078960280261 26691866530660327305052549)
    ·
      refine ⟨5004724974498811369697353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26691866530660327305052549 5004724974498811369697353)
      ·
        refine ⟨3753543730874108527273015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5004724974498811369697353 3753543730874108527273015)
        ·
          refine ⟨5630315596311162790909523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3753543730874108527273015 5630315596311162790909523)
          ·
            refine ⟨8445473394466744186364285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5630315596311162790909523 8445473394466744186364285)
            ·
              refine ⟨3167052522925029069886607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8445473394466744186364285 3167052522925029069886607)
              ·
                refine ⟨4750578784387543604829911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3167052522925029069886607 4750578784387543604829911)
                ·
                  refine ⟨7125868176581315407244867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4750578784387543604829911 7125868176581315407244867)
                  ·
                    refine ⟨10688802264871973110867301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7125868176581315407244867 10688802264871973110867301)
                    ·
                      refine ⟨2004150424663494958287619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10688802264871973110867301 2004150424663494958287619)
                      ·
                        rfl

theorem cell23_3903069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_3903069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903069 prefixEnd_3903069 := by exact prefixLift 3903069
  have htrace : WordTrace (prefixWord ++ tailWord_3903069) baseStart_3903069 baseEnd_3903069 := by
    simpa [prefixWord, tailWord_3903069, baseEnd_3903069] using wordTrace_append hprefix tailTrace_3903069
  have hstable : (prefixWord ++ tailWord_3903069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903069).length < 2 ^ (prefixWord ++ tailWord_3903069).sum := by decide
  have hdescent : baseEnd_3903069 < baseStart_3903069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903101 : List Nat := [1, 4, 1, 1, 4, 1, 1, 1, 1, 8]
def baseStart_3903101 : Nat := 118140960795 + 3903101 * 2 ^ 59
def prefixEnd_3903101 : Nat := 4983230072969 + 3 ^ 40 * 3903101 * 2
def baseEnd_3903101 : Nat := 668055618681479611029157

theorem tailTrace_3903101 : CollatzResearch.WordTrace tailWord_3903101 prefixEnd_3903101 668055618681479611029157 := by
  unfold tailWord_3903101
  simp only [CollatzResearch.WordTrace]
  refine ⟨142357788632739148425445157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94905192421826098950296771 142357788632739148425445157)
  ·
    refine ⟨26692085368638590329770967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142357788632739148425445157 26692085368638590329770967)
    ·
      refine ⟨40038128052957885494656451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26692085368638590329770967 40038128052957885494656451)
      ·
        refine ⟨60057192079436828241984677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40038128052957885494656451 60057192079436828241984677)
        ·
          refine ⟨11260723514894405295372127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60057192079436828241984677 11260723514894405295372127)
          ·
            refine ⟨16891085272341607943058191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11260723514894405295372127 16891085272341607943058191)
            ·
              refine ⟨25336627908512411914587287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16891085272341607943058191 25336627908512411914587287)
              ·
                refine ⟨38004941862768617871880931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25336627908512411914587287 38004941862768617871880931)
                ·
                  refine ⟨57007412794152926807821397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38004941862768617871880931 57007412794152926807821397)
                  ·
                    refine ⟨668055618681479611029157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57007412794152926807821397 668055618681479611029157)
                    ·
                      rfl

theorem cell23_3903101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_3903101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903101 prefixEnd_3903101 := by exact prefixLift 3903101
  have htrace : WordTrace (prefixWord ++ tailWord_3903101) baseStart_3903101 baseEnd_3903101 := by
    simpa [prefixWord, tailWord_3903101, baseEnd_3903101] using wordTrace_append hprefix tailTrace_3903101
  have hstable : (prefixWord ++ tailWord_3903101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903101).length < 2 ^ (prefixWord ++ tailWord_3903101).sum := by decide
  have hdescent : baseEnd_3903101 < baseStart_3903101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903159 : List Nat := [1, 1, 3, 1, 5, 2, 3, 1, 2, 2, 2]
def baseStart_3903159 : Nat := 118140960795 + 3903159 * 2 ^ 59
def prefixEnd_3903159 : Nat := 4983230072969 + 3 ^ 40 * 3903159 * 2
def baseEnd_3903159 : Nat := 2004196637922399606162205

theorem tailTrace_3903159 : CollatzResearch.WordTrace tailWord_3903159 prefixEnd_3903159 2004196637922399606162205 := by
  unfold tailWord_3903159
  simp only [CollatzResearch.WordTrace]
  refine ⟨142359904066529024331056531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94906602711019349554037687 142359904066529024331056531)
  ·
    refine ⟨213539856099793536496584797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142359904066529024331056531 213539856099793536496584797)
    ·
      refine ⟨80077446037422576186219299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213539856099793536496584797 80077446037422576186219299)
      ·
        refine ⟨120116169056133864279328949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80077446037422576186219299 120116169056133864279328949)
        ·
          refine ⟨11260890849012549776187089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120116169056133864279328949 11260890849012549776187089)
          ·
            refine ⟨8445668136759412332140317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11260890849012549776187089 8445668136759412332140317)
            ·
              refine ⟨3167125551284779624552619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8445668136759412332140317 3167125551284779624552619)
              ·
                refine ⟨4750688326927169436828929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3167125551284779624552619 4750688326927169436828929)
                ·
                  refine ⟨3563016245195377077621697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4750688326927169436828929 3563016245195377077621697)
                  ·
                    refine ⟨2672262183896532808216273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3563016245195377077621697 2672262183896532808216273)
                    ·
                      refine ⟨2004196637922399606162205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2672262183896532808216273 2004196637922399606162205)
                      ·
                        rfl

theorem cell23_3903159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 2, 2, 2].length) (baseStart_3903159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903159 prefixEnd_3903159 := by exact prefixLift 3903159
  have htrace : WordTrace (prefixWord ++ tailWord_3903159) baseStart_3903159 baseEnd_3903159 := by
    simpa [prefixWord, tailWord_3903159, baseEnd_3903159] using wordTrace_append hprefix tailTrace_3903159
  have hstable : (prefixWord ++ tailWord_3903159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903159).length < 2 ^ (prefixWord ++ tailWord_3903159).sum := by decide
  have hdescent : baseEnd_3903159 < baseStart_3903159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903161 : List Nat := [1, 2, 1, 4, 1, 1, 3, 2, 1, 7]
def baseStart_3903161 : Nat := 118140960795 + 3903161 * 2 ^ 59
def prefixEnd_3903161 : Nat := 4983230072969 + 3 ^ 40 * 3903161 * 2
def baseEnd_3903161 : Nat := 668065888294569532779065

theorem tailTrace_3903161 : CollatzResearch.WordTrace tailWord_3903161 prefixEnd_3903161 668065888294569532779065 := by
  unfold tailWord_3903161
  simp only [CollatzResearch.WordTrace]
  refine ⟨142359977012521778672629337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94906651341681185781752891 142359977012521778672629337)
  ·
    refine ⟨106769982759391334004472003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142359977012521778672629337 106769982759391334004472003)
    ·
      refine ⟨160154974139087001006708005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106769982759391334004472003 160154974139087001006708005)
      ·
        refine ⟨30029057651078812688757751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160154974139087001006708005 30029057651078812688757751)
        ·
          refine ⟨45043586476618219033136627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30029057651078812688757751 45043586476618219033136627)
          ·
            refine ⟨67565379714927328549704941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45043586476618219033136627 67565379714927328549704941)
            ·
              refine ⟨25337017393097748206139353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67565379714927328549704941 25337017393097748206139353)
              ·
                refine ⟨19002763044823311154604515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25337017393097748206139353 19002763044823311154604515)
                ·
                  refine ⟨28504144567234966731906773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19002763044823311154604515 28504144567234966731906773)
                  ·
                    refine ⟨668065888294569532779065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28504144567234966731906773 668065888294569532779065)
                    ·
                      rfl

theorem cell23_3903161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 7].length) (baseStart_3903161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903161 prefixEnd_3903161 := by exact prefixLift 3903161
  have htrace : WordTrace (prefixWord ++ tailWord_3903161) baseStart_3903161 baseEnd_3903161 := by
    simpa [prefixWord, tailWord_3903161, baseEnd_3903161] using wordTrace_append hprefix tailTrace_3903161
  have hstable : (prefixWord ++ tailWord_3903161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903161).length < 2 ^ (prefixWord ++ tailWord_3903161).sum := by decide
  have hdescent : baseEnd_3903161 < baseStart_3903161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903211 : List Nat := [1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 6]
def baseStart_3903211 : Nat := 118140960795 + 3903211 * 2 ^ 59
def prefixEnd_3903211 : Nat := 4983230072969 + 3 ^ 40 * 3903211 * 2
def baseEnd_3903211 : Nat := 2004223338916433402711965

theorem tailTrace_3903211 : CollatzResearch.WordTrace tailWord_3903211 prefixEnd_3903211 2004223338916433402711965 := by
  unfold tailWord_3903211
  simp only [CollatzResearch.WordTrace]
  refine ⟨142361800662340637211949487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94907867108227091474632991 142361800662340637211949487)
  ·
    refine ⟨213542700993510955817924231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142361800662340637211949487 213542700993510955817924231)
    ·
      refine ⟨320314051490266433726886347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213542700993510955817924231 320314051490266433726886347)
      ·
        refine ⟨480471077235399650590329521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320314051490266433726886347 480471077235399650590329521)
        ·
          refine ⟨360353307926549737942747141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480471077235399650590329521 360353307926549737942747141)
          ·
            refine ⟨67566245236228075864265089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 360353307926549737942747141 67566245236228075864265089)
            ·
              refine ⟨50674683927171056898198817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67566245236228075864265089 50674683927171056898198817)
              ·
                refine ⟨38006012945378292673649113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50674683927171056898198817 38006012945378292673649113)
                ·
                  refine ⟨28504509709033719505236835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38006012945378292673649113 28504509709033719505236835)
                  ·
                    refine ⟨42756764563550579257855253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28504509709033719505236835 42756764563550579257855253)
                    ·
                      refine ⟨2004223338916433402711965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42756764563550579257855253 2004223338916433402711965)
                      ·
                        rfl

theorem cell23_3903211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 6].length) (baseStart_3903211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903211 prefixEnd_3903211 := by exact prefixLift 3903211
  have htrace : WordTrace (prefixWord ++ tailWord_3903211) baseStart_3903211 baseEnd_3903211 := by
    simpa [prefixWord, tailWord_3903211, baseEnd_3903211] using wordTrace_append hprefix tailTrace_3903211
  have hstable : (prefixWord ++ tailWord_3903211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903211).length < 2 ^ (prefixWord ++ tailWord_3903211).sum := by decide
  have hdescent : baseEnd_3903211 < baseStart_3903211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903241 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 1, 1, 8]
def baseStart_3903241 : Nat := 118140960795 + 3903241 * 2 ^ 59
def prefixEnd_3903241 : Nat := 4983230072969 + 3 ^ 40 * 3903241 * 2
def baseEnd_3903241 : Nat := 2004238743336068285336827

theorem tailTrace_3903241 : CollatzResearch.WordTrace tailWord_3903241 prefixEnd_3903241 2004238743336068285336827 := by
  unfold tailWord_3903241
  simp only [CollatzResearch.WordTrace]
  refine ⟨142362894852231952335541577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94908596568154634890361051 142362894852231952335541577)
  ·
    refine ⟨106772171139173964251656183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142362894852231952335541577 106772171139173964251656183)
    ·
      refine ⟨160158256708760946377484275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106772171139173964251656183 160158256708760946377484275)
      ·
        refine ⟨240237385063141419566226413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160158256708760946377484275 240237385063141419566226413)
        ·
          refine ⟨90089019398678032337334905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240237385063141419566226413 90089019398678032337334905)
          ·
            refine ⟨67566764549008524253001179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90089019398678032337334905 67566764549008524253001179)
            ·
              refine ⟨101350146823512786379501769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67566764549008524253001179 101350146823512786379501769)
              ·
                refine ⟨76012610117634589784626327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101350146823512786379501769 76012610117634589784626327)
                ·
                  refine ⟨114018915176451884676939491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76012610117634589784626327 114018915176451884676939491)
                  ·
                    refine ⟨171028372764677827015409237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114018915176451884676939491 171028372764677827015409237)
                    ·
                      refine ⟨2004238743336068285336827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 171028372764677827015409237 2004238743336068285336827)
                      ·
                        rfl

theorem cell23_3903241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 1, 8].length) (baseStart_3903241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903241 prefixEnd_3903241 := by exact prefixLift 3903241
  have htrace : WordTrace (prefixWord ++ tailWord_3903241) baseStart_3903241 baseEnd_3903241 := by
    simpa [prefixWord, tailWord_3903241, baseEnd_3903241] using wordTrace_append hprefix tailTrace_3903241
  have hstable : (prefixWord ++ tailWord_3903241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903241).length < 2 ^ (prefixWord ++ tailWord_3903241).sum := by decide
  have hdescent : baseEnd_3903241 < baseStart_3903241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903255 : List Nat := [1, 1, 3, 4, 2, 2, 2, 2, 6]
def baseStart_3903255 : Nat := 118140960795 + 3903255 * 2 ^ 59
def prefixEnd_3903255 : Nat := 4983230072969 + 3 ^ 40 * 3903255 * 2
def baseEnd_3903255 : Nat := 222693992451692358951307

theorem tailTrace_3903255 : CollatzResearch.WordTrace tailWord_3903255 prefixEnd_3903255 222693992451692358951307 := by
  unfold tailWord_3903255
  simp only [CollatzResearch.WordTrace]
  refine ⟨142363405474181232726551219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94908936982787488484367479 142363405474181232726551219)
  ·
    refine ⟨213545108211271849089826829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142363405474181232726551219 213545108211271849089826829)
    ·
      refine ⟨80079415579226943408685061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213545108211271849089826829 80079415579226943408685061)
      ·
        refine ⟨15014890421105051889128449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80079415579226943408685061 15014890421105051889128449)
        ·
          refine ⟨11261167815828788916846337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15014890421105051889128449 11261167815828788916846337)
          ·
            refine ⟨8445875861871591687634753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11261167815828788916846337 8445875861871591687634753)
            ·
              refine ⟨6334406896403693765726065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8445875861871591687634753 6334406896403693765726065)
              ·
                refine ⟨4750805172302770324294549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6334406896403693765726065 4750805172302770324294549)
                ·
                  refine ⟨222693992451692358951307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4750805172302770324294549 222693992451692358951307)
                  ·
                    rfl

theorem cell23_3903255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 6].length) (baseStart_3903255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903255 prefixEnd_3903255 := by exact prefixLift 3903255
  have htrace : WordTrace (prefixWord ++ tailWord_3903255) baseStart_3903255 baseEnd_3903255 := by
    simpa [prefixWord, tailWord_3903255, baseEnd_3903255] using wordTrace_append hprefix tailTrace_3903255
  have hstable : (prefixWord ++ tailWord_3903255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903255).length < 2 ^ (prefixWord ++ tailWord_3903255).sum := by decide
  have hdescent : baseEnd_3903255 < baseStart_3903255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903282 : List Nat := [3, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3]
def baseStart_3903282 : Nat := 118140960795 + 3903282 * 2 ^ 59
def prefixEnd_3903282 : Nat := 4983230072969 + 3 ^ 40 * 3903282 * 2
def baseEnd_3903282 : Nat := 2004259796042902624924139

theorem tailTrace_3903282 : CollatzResearch.WordTrace tailWord_3903282 prefixEnd_3903282 2004259796042902624924139 := by
  unfold tailWord_3903282
  simp only [CollatzResearch.WordTrace]
  refine ⟨35591097561270854084446025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94909593496722277558522733 35591097561270854084446025)
  ·
    refine ⟨26693323170953140563334519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35591097561270854084446025 26693323170953140563334519)
    ·
      refine ⟨40039984756429710845001779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26693323170953140563334519 40039984756429710845001779)
      ·
        refine ⟨60059977134644566267502669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40039984756429710845001779 60059977134644566267502669)
        ·
          refine ⟨22522491425491712350313501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60059977134644566267502669 22522491425491712350313501)
          ·
            refine ⟨8445934284559392131367563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22522491425491712350313501 8445934284559392131367563)
            ·
              refine ⟨12668901426839088197051345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8445934284559392131367563 12668901426839088197051345)
              ·
                refine ⟨9501676070129316147788509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12668901426839088197051345 9501676070129316147788509)
                ·
                  refine ⟨3563128526298493555420691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9501676070129316147788509 3563128526298493555420691)
                  ·
                    refine ⟨5344692789447740333131037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3563128526298493555420691 5344692789447740333131037)
                    ·
                      refine ⟨2004259796042902624924139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5344692789447740333131037 2004259796042902624924139)
                      ·
                        rfl

theorem cell23_3903282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3].length) (baseStart_3903282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903282 prefixEnd_3903282 := by exact prefixLift 3903282
  have htrace : WordTrace (prefixWord ++ tailWord_3903282) baseStart_3903282 baseEnd_3903282 := by
    simpa [prefixWord, tailWord_3903282, baseEnd_3903282] using wordTrace_append hprefix tailTrace_3903282
  have hstable : (prefixWord ++ tailWord_3903282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903282).length < 2 ^ (prefixWord ++ tailWord_3903282).sum := by decide
  have hdescent : baseEnd_3903282 < baseStart_3903282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903292 : List Nat := [2, 2, 2, 2, 1, 1, 5, 1, 2, 3, 2]
def baseStart_3903292 : Nat := 118140960795 + 3903292 * 2 ^ 59
def prefixEnd_3903292 : Nat := 4983230072969 + 3 ^ 40 * 3903292 * 2
def baseEnd_3903292 : Nat := 2004264930849447585799093

theorem tailTrace_3903292 : CollatzResearch.WordTrace tailWord_3903292 prefixEnd_3903292 2004264930849447585799093 := by
  unfold tailWord_3903292
  simp only [CollatzResearch.WordTrace]
  refine ⟨71182377487523594022824065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94909836650031458697098753 71182377487523594022824065)
  ·
    refine ⟨53386783115642695517118049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71182377487523594022824065 53386783115642695517118049)
    ·
      refine ⟨40040087336732021637838537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53386783115642695517118049 40040087336732021637838537)
      ·
        refine ⟨30030065502549016228378903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40040087336732021637838537 30030065502549016228378903)
        ·
          refine ⟨45045098253823524342568355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30030065502549016228378903 45045098253823524342568355)
          ·
            refine ⟨67567647380735286513852533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45045098253823524342568355 67567647380735286513852533)
            ·
              refine ⟨6334466941943933110673675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67567647380735286513852533 6334466941943933110673675)
              ·
                refine ⟨9501700412915899666010513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6334466941943933110673675 9501700412915899666010513)
                ·
                  refine ⟨7126275309686924749507885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9501700412915899666010513 7126275309686924749507885)
                  ·
                    refine ⟨2672353241132596781065457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7126275309686924749507885 2672353241132596781065457)
                    ·
                      refine ⟨2004264930849447585799093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2672353241132596781065457 2004264930849447585799093)
                      ·
                        rfl

theorem cell23_3903292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_3903292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903292 prefixEnd_3903292 := by exact prefixLift 3903292
  have htrace : WordTrace (prefixWord ++ tailWord_3903292) baseStart_3903292 baseEnd_3903292 := by
    simpa [prefixWord, tailWord_3903292, baseEnd_3903292] using wordTrace_append hprefix tailTrace_3903292
  have hstable : (prefixWord ++ tailWord_3903292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903292).length < 2 ^ (prefixWord ++ tailWord_3903292).sum := by decide
  have hdescent : baseEnd_3903292 < baseStart_3903292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903299 : List Nat := [1, 1, 1, 3, 1, 6, 2, 3, 1, 1, 3]
def baseStart_3903299 : Nat := 118140960795 + 3903299 * 2 ^ 59
def prefixEnd_3903299 : Nat := 4983230072969 + 3 ^ 40 * 3903299 * 2
def baseEnd_3903299 : Nat := 2004268525214029058411561

theorem tailTrace_3903299 : CollatzResearch.WordTrace tailWord_3903299 prefixEnd_3903299 2004268525214029058411561 := by
  unfold tailWord_3903299
  simp only [CollatzResearch.WordTrace]
  refine ⟨142365010286021828241152951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94910006857347885494101967 142365010286021828241152951)
  ·
    refine ⟨213547515429032742361729427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142365010286021828241152951 213547515429032742361729427)
    ·
      refine ⟨320321273143549113542594141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213547515429032742361729427 320321273143549113542594141)
      ·
        refine ⟨120120477428830917578472803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320321273143549113542594141 120120477428830917578472803)
        ·
          refine ⟨180180716143246376367709205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120120477428830917578472803 180180716143246376367709205)
          ·
            refine ⟨8445971069214673892236369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 180180716143246376367709205 8445971069214673892236369)
            ·
              refine ⟨6334478301911005419177277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8445971069214673892236369 6334478301911005419177277)
              ·
                refine ⟨2375429363216627032191479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6334478301911005419177277 2375429363216627032191479)
                ·
                  refine ⟨3563144044824940548287219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2375429363216627032191479 3563144044824940548287219)
                  ·
                    refine ⟨5344716067237410822430829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3563144044824940548287219 5344716067237410822430829)
                    ·
                      refine ⟨2004268525214029058411561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5344716067237410822430829 2004268525214029058411561)
                      ·
                        rfl

theorem cell23_3903299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 3, 1, 1, 3].length) (baseStart_3903299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903299 prefixEnd_3903299 := by exact prefixLift 3903299
  have htrace : WordTrace (prefixWord ++ tailWord_3903299) baseStart_3903299 baseEnd_3903299 := by
    simpa [prefixWord, tailWord_3903299, baseEnd_3903299] using wordTrace_append hprefix tailTrace_3903299
  have hstable : (prefixWord ++ tailWord_3903299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903299).length < 2 ^ (prefixWord ++ tailWord_3903299).sum := by decide
  have hdescent : baseEnd_3903299 < baseStart_3903299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903305 : List Nat := [1, 2, 1, 1, 2, 4, 3, 3, 1, 1, 4]
def baseStart_3903305 : Nat := 118140960795 + 3903305 * 2 ^ 59
def prefixEnd_3903305 : Nat := 4983230072969 + 3 ^ 40 * 3903305 * 2
def baseEnd_3903305 : Nat := 2004271606097956034936533

theorem tailTrace_3903305 : CollatzResearch.WordTrace tailWord_3903305 prefixEnd_3903305 2004271606097956034936533 := by
  unfold tailWord_3903305
  simp only [CollatzResearch.WordTrace]
  refine ⟨142365229124000091265871369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94910152749333394177247579 142365229124000091265871369)
  ·
    refine ⟨106773921843000068449403527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142365229124000091265871369 106773921843000068449403527)
    ·
      refine ⟨160160882764500102674105291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106773921843000068449403527 160160882764500102674105291)
      ·
        refine ⟨240241324146750154011157937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160160882764500102674105291 240241324146750154011157937)
        ·
          refine ⟨180180993110062615508368453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240241324146750154011157937 180180993110062615508368453)
          ·
            refine ⟨33783936208136740407819085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180180993110062615508368453 33783936208136740407819085)
            ·
              refine ⟨12668976078051277652932157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33783936208136740407819085 12668976078051277652932157)
              ·
                refine ⟨4750866029269229119849559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12668976078051277652932157 4750866029269229119849559)
                ·
                  refine ⟨7126299043903843679774339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4750866029269229119849559 7126299043903843679774339)
                  ·
                    refine ⟨10689448565855765519661509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7126299043903843679774339 10689448565855765519661509)
                    ·
                      refine ⟨2004271606097956034936533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10689448565855765519661509 2004271606097956034936533)
                      ·
                        rfl

theorem cell23_3903305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 1, 4].length) (baseStart_3903305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903305 prefixEnd_3903305 := by exact prefixLift 3903305
  have htrace : WordTrace (prefixWord ++ tailWord_3903305) baseStart_3903305 baseEnd_3903305 := by
    simpa [prefixWord, tailWord_3903305, baseEnd_3903305] using wordTrace_append hprefix tailTrace_3903305
  have hstable : (prefixWord ++ tailWord_3903305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903305).length < 2 ^ (prefixWord ++ tailWord_3903305).sum := by decide
  have hdescent : baseEnd_3903305 < baseStart_3903305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903332 : List Nat := [2, 3, 1, 1, 5, 2, 1, 1, 1, 6]
def baseStart_3903332 : Nat := 118140960795 + 3903332 * 2 ^ 59
def prefixEnd_3903332 : Nat := 4983230072969 + 3 ^ 40 * 3903332 * 2
def baseEnd_3903332 : Nat := 668095156691875809766303

theorem tailTrace_3903332 : CollatzResearch.WordTrace tailWord_3903332 prefixEnd_3903332 668095156691875809766303 := by
  unfold tailWord_3903332
  simp only [CollatzResearch.WordTrace]
  refine ⟨71183106947451137438552125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94910809263268183251402833 71183106947451137438552125)
  ·
    refine ⟨26693665105294176539457047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71183106947451137438552125 26693665105294176539457047)
    ·
      refine ⟨40040497657941264809185571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26693665105294176539457047 40040497657941264809185571)
      ·
        refine ⟨60060746486911897213778357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40040497657941264809185571 60060746486911897213778357)
        ·
          refine ⟨5630694983147990363791721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60060746486911897213778357 5630694983147990363791721)
          ·
            refine ⟨4223021237360992772843791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5630694983147990363791721 4223021237360992772843791)
            ·
              refine ⟨6334531856041489159265687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4223021237360992772843791 6334531856041489159265687)
              ·
                refine ⟨9501797784062233738898531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6334531856041489159265687 9501797784062233738898531)
                ·
                  refine ⟨14252696676093350608347797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9501797784062233738898531 14252696676093350608347797)
                  ·
                    refine ⟨668095156691875809766303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14252696676093350608347797 668095156691875809766303)
                    ·
                      rfl

theorem cell23_3903332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_3903332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903332 prefixEnd_3903332 := by exact prefixLift 3903332
  have htrace : WordTrace (prefixWord ++ tailWord_3903332) baseStart_3903332 baseEnd_3903332 := by
    simpa [prefixWord, tailWord_3903332, baseEnd_3903332] using wordTrace_append hprefix tailTrace_3903332
  have hstable : (prefixWord ++ tailWord_3903332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903332).length < 2 ^ (prefixWord ++ tailWord_3903332).sum := by decide
  have hdescent : baseEnd_3903332 < baseStart_3903332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903350 : List Nat := [5, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3]
def baseStart_3903350 : Nat := 118140960795 + 3903350 * 2 ^ 59
def prefixEnd_3903350 : Nat := 4983230072969 + 3 ^ 40 * 3903350 * 2
def baseEnd_3903350 : Nat := 2004294712727408358873827

theorem tailTrace_3903350 : CollatzResearch.WordTrace tailWord_3903350 prefixEnd_3903350 2004294712727408358873827 := by
  unfold tailWord_3903350
  simp only [CollatzResearch.WordTrace]
  refine ⟨8897929400552316496953719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94911246939224709300839669 8897929400552316496953719)
  ·
    refine ⟨13346894100828474745430579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8897929400552316496953719 13346894100828474745430579)
    ·
      refine ⟨20020341151242712118145869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13346894100828474745430579 20020341151242712118145869)
      ·
        refine ⟨7507627931716017044304701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20020341151242712118145869 7507627931716017044304701)
        ·
          refine ⟨2815360474393506391614263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7507627931716017044304701 2815360474393506391614263)
          ·
            refine ⟨4223040711590259587421395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2815360474393506391614263 4223040711590259587421395)
            ·
              refine ⟨6334561067385389381132093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4223040711590259587421395 6334561067385389381132093)
              ·
                refine ⟨2375460400269521017924535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6334561067385389381132093 2375460400269521017924535)
                ·
                  refine ⟨3563190600404281526886803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2375460400269521017924535 3563190600404281526886803)
                  ·
                    refine ⟨5344785900606422290330205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3563190600404281526886803 5344785900606422290330205)
                    ·
                      refine ⟨2004294712727408358873827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5344785900606422290330205 2004294712727408358873827)
                      ·
                        rfl

theorem cell23_3903350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_3903350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903350 prefixEnd_3903350 := by exact prefixLift 3903350
  have htrace : WordTrace (prefixWord ++ tailWord_3903350) baseStart_3903350 baseEnd_3903350 := by
    simpa [prefixWord, tailWord_3903350, baseEnd_3903350] using wordTrace_append hprefix tailTrace_3903350
  have hstable : (prefixWord ++ tailWord_3903350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903350).length < 2 ^ (prefixWord ++ tailWord_3903350).sum := by decide
  have hdescent : baseEnd_3903350 < baseStart_3903350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903372 : List Nat := [2, 2, 1, 2, 1, 2, 1, 6, 2, 1, 3]
def baseStart_3903372 : Nat := 118140960795 + 3903372 * 2 ^ 59
def prefixEnd_3903372 : Nat := 4983230072969 + 3 ^ 40 * 3903372 * 2
def baseEnd_3903372 : Nat := 2004306009301807272798725

theorem tailTrace_3903372 : CollatzResearch.WordTrace tailWord_3903372 prefixEnd_3903372 2004306009301807272798725 := by
  unfold tailWord_3903372
  simp only [CollatzResearch.WordTrace]
  refine ⟨71183836407378680854280185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94911781876504907805706913 71183836407378680854280185)
  ·
    refine ⟨53387877305534010640710139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71183836407378680854280185 53387877305534010640710139)
    ·
      refine ⟨80081815958301015961065209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53387877305534010640710139 80081815958301015961065209)
      ·
        refine ⟨60061361968725761970798907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80081815958301015961065209 60061361968725761970798907)
        ·
          refine ⟨90092042953088642956198361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60061361968725761970798907 90092042953088642956198361)
          ·
            refine ⟨67569032214816482217148771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90092042953088642956198361 67569032214816482217148771)
            ·
              refine ⟨101353548322224723325723157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67569032214816482217148771 101353548322224723325723157)
              ·
                refine ⟨4750947577604283905893273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101353548322224723325723157 4750947577604283905893273)
                ·
                  refine ⟨3563210683203212929419955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4750947577604283905893273 3563210683203212929419955)
                  ·
                    refine ⟨5344816024804819394129933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3563210683203212929419955 5344816024804819394129933)
                    ·
                      refine ⟨2004306009301807272798725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5344816024804819394129933 2004306009301807272798725)
                      ·
                        rfl

theorem cell23_3903372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 2, 1, 3].length) (baseStart_3903372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903372 prefixEnd_3903372 := by exact prefixLift 3903372
  have htrace : WordTrace (prefixWord ++ tailWord_3903372) baseStart_3903372 baseEnd_3903372 := by
    simpa [prefixWord, tailWord_3903372, baseEnd_3903372] using wordTrace_append hprefix tailTrace_3903372
  have hstable : (prefixWord ++ tailWord_3903372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903372).length < 2 ^ (prefixWord ++ tailWord_3903372).sum := by decide
  have hdescent : baseEnd_3903372 < baseStart_3903372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903389 : List Nat := [1, 4, 2, 1, 2, 3, 1, 3, 2, 1, 3]
def baseStart_3903389 : Nat := 118140960795 + 3903389 * 2 ^ 59
def prefixEnd_3903389 : Nat := 4983230072969 + 3 ^ 40 * 3903389 * 2
def baseEnd_3903389 : Nat := 2004314738472933706286147

theorem tailTrace_3903389 : CollatzResearch.WordTrace tailWord_3903389 prefixEnd_3903389 2004314738472933706286147 := by
  unfold tailWord_3903389
  simp only [CollatzResearch.WordTrace]
  refine ⟨142368292855695773611929221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94912195237130515741286147 142368292855695773611929221)
  ·
    refine ⟨26694054910442957552236729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142368292855695773611929221 26694054910442957552236729)
    ·
      refine ⟨20020541182832218164177547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26694054910442957552236729 20020541182832218164177547)
      ·
        refine ⟨30030811774248327246266321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20020541182832218164177547 30030811774248327246266321)
        ·
          refine ⟨22523108830686245434699741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30030811774248327246266321 22523108830686245434699741)
          ·
            refine ⟨8446165811507342038012403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22523108830686245434699741 8446165811507342038012403)
            ·
              refine ⟨12669248717261013057018605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8446165811507342038012403 12669248717261013057018605)
              ·
                refine ⟨4750968268972879896381977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12669248717261013057018605 4750968268972879896381977)
                ·
                  refine ⟨3563226201729659922286483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4750968268972879896381977 3563226201729659922286483)
                  ·
                    refine ⟨5344839302594489883429725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3563226201729659922286483 5344839302594489883429725)
                    ·
                      refine ⟨2004314738472933706286147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5344839302594489883429725 2004314738472933706286147)
                      ·
                        rfl

theorem cell23_3903389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_3903389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903389 prefixEnd_3903389 := by exact prefixLift 3903389
  have htrace : WordTrace (prefixWord ++ tailWord_3903389) baseStart_3903389 baseEnd_3903389 := by
    simpa [prefixWord, tailWord_3903389, baseEnd_3903389] using wordTrace_append hprefix tailTrace_3903389
  have hstable : (prefixWord ++ tailWord_3903389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903389).length < 2 ^ (prefixWord ++ tailWord_3903389).sum := by decide
  have hdescent : baseEnd_3903389 < baseStart_3903389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903399 : List Nat := [1, 1, 6, 1, 2, 2, 1, 1, 3, 3, 2]
def baseStart_3903399 : Nat := 118140960795 + 3903399 * 2 ^ 59
def prefixEnd_3903399 : Nat := 4983230072969 + 3 ^ 40 * 3903399 * 2
def baseEnd_3903399 : Nat := 2004319873279478667161101

theorem tailTrace_3903399 : CollatzResearch.WordTrace tailWord_3903399 prefixEnd_3903399 2004319873279478667161101 := by
  unfold tailWord_3903399
  simp only [CollatzResearch.WordTrace]
  refine ⟨142368657585659545319793251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94912438390439696879862167 142368657585659545319793251)
  ·
    refine ⟨213552986378489317979689877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142368657585659545319793251 213552986378489317979689877)
    ·
      refine ⟨10010296236491686780297963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 213552986378489317979689877 10010296236491686780297963)
      ·
        refine ⟨15015444354737530170446945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10010296236491686780297963 15015444354737530170446945)
        ·
          refine ⟨11261583266053147627835209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15015444354737530170446945 11261583266053147627835209)
          ·
            refine ⟨8446187449539860720876407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11261583266053147627835209 8446187449539860720876407)
            ·
              refine ⟨12669281174309791081314611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8446187449539860720876407 12669281174309791081314611)
              ·
                refine ⟨19003921761464686621971917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12669281174309791081314611 19003921761464686621971917)
                ·
                  refine ⟨7126470660549257483239469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19003921761464686621971917 7126470660549257483239469)
                  ·
                    refine ⟨2672426497705971556214801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7126470660549257483239469 2672426497705971556214801)
                    ·
                      refine ⟨2004319873279478667161101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2672426497705971556214801 2004319873279478667161101)
                      ·
                        rfl

theorem cell23_3903399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_3903399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903399 prefixEnd_3903399 := by exact prefixLift 3903399
  have htrace : WordTrace (prefixWord ++ tailWord_3903399) baseStart_3903399 baseEnd_3903399 := by
    simpa [prefixWord, tailWord_3903399, baseEnd_3903399] using wordTrace_append hprefix tailTrace_3903399
  have hstable : (prefixWord ++ tailWord_3903399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903399).length < 2 ^ (prefixWord ++ tailWord_3903399).sum := by decide
  have hdescent : baseEnd_3903399 < baseStart_3903399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903418 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 11]
def baseStart_3903418 : Nat := 118140960795 + 3903418 * 2 ^ 59
def prefixEnd_3903418 : Nat := 4983230072969 + 3 ^ 40 * 3903418 * 2
def baseEnd_3903418 : Nat := 222703292156879343647057

theorem tailTrace_3903418 : CollatzResearch.WordTrace tailWord_3903418 prefixEnd_3903418 222703292156879343647057 := by
  unfold tailWord_3903418
  simp only [CollatzResearch.WordTrace]
  refine ⟨35592337643147677891183727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94912900381727141043156605 35592337643147677891183727)
  ·
    refine ⟨53388506464721516836775591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35592337643147677891183727 53388506464721516836775591)
    ·
      refine ⟨80082759697082275255163387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53388506464721516836775591 80082759697082275255163387)
      ·
        refine ⟨120124139545623412882745081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80082759697082275255163387 120124139545623412882745081)
        ·
          refine ⟨90093104659217559662058811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120124139545623412882745081 90093104659217559662058811)
          ·
            refine ⟨135139656988826339493088217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90093104659217559662058811 135139656988826339493088217)
            ·
              refine ⟨101354742741619754619816163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135139656988826339493088217 101354742741619754619816163)
              ·
                refine ⟨152032114112429631929724245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101354742741619754619816163 152032114112429631929724245)
                ·
                  refine ⟨222703292156879343647057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 152032114112429631929724245 222703292156879343647057)
                  ·
                    rfl

theorem cell23_3903418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 11].length) (baseStart_3903418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903418 prefixEnd_3903418 := by exact prefixLift 3903418
  have htrace : WordTrace (prefixWord ++ tailWord_3903418) baseStart_3903418 baseEnd_3903418 := by
    simpa [prefixWord, tailWord_3903418, baseEnd_3903418] using wordTrace_append hprefix tailTrace_3903418
  have hstable : (prefixWord ++ tailWord_3903418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903418).length < 2 ^ (prefixWord ++ tailWord_3903418).sum := by decide
  have hdescent : baseEnd_3903418 < baseStart_3903418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903512 : List Nat := [2, 1, 2, 3, 2, 1, 1, 4, 3, 4]
def baseStart_3903512 : Nat := 118140960795 + 3903512 * 2 ^ 59
def prefixEnd_3903512 : Nat := 4983230072969 + 3 ^ 40 * 3903512 * 2
def baseEnd_3903512 : Nat := 668125965531145575016027

theorem tailTrace_3903512 : CollatzResearch.WordTrace tailWord_3903512 prefixEnd_3903512 668125965531145575016027 := by
  unfold tailWord_3903512
  simp only [CollatzResearch.WordTrace]
  refine ⟨71186389517125082809328395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94915186022833443745771193 71186389517125082809328395)
  ·
    refine ⟨106779584275687624213992593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71186389517125082809328395 106779584275687624213992593)
    ·
      refine ⟨80084688206765718160494445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106779584275687624213992593 80084688206765718160494445)
      ·
        refine ⟨30031758077537144310185417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80084688206765718160494445 30031758077537144310185417)
        ·
          refine ⟨22523818558152858232639063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30031758077537144310185417 22523818558152858232639063)
          ·
            refine ⟨33785727837229287348958595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22523818558152858232639063 33785727837229287348958595)
            ·
              refine ⟨50678591755843931023437893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33785727837229287348958595 50678591755843931023437893)
              ·
                refine ⟨9502235954220737066894605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50678591755843931023437893 9502235954220737066894605)
                ·
                  refine ⟨3563338482832776400085477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9502235954220737066894605 3563338482832776400085477)
                  ·
                    refine ⟨668125965531145575016027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3563338482832776400085477 668125965531145575016027)
                    ·
                      rfl

theorem cell23_3903512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 3, 4].length) (baseStart_3903512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903512 prefixEnd_3903512 := by exact prefixLift 3903512
  have htrace : WordTrace (prefixWord ++ tailWord_3903512) baseStart_3903512 baseEnd_3903512 := by
    simpa [prefixWord, tailWord_3903512, baseEnd_3903512] using wordTrace_append hprefix tailTrace_3903512
  have hstable : (prefixWord ++ tailWord_3903512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903512).length < 2 ^ (prefixWord ++ tailWord_3903512).sum := by decide
  have hdescent : baseEnd_3903512 < baseStart_3903512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903522 : List Nat := [3, 3, 1, 1, 1, 2, 1, 3, 1, 4, 3]
def baseStart_3903522 : Nat := 118140960795 + 3903522 * 2 ^ 59
def prefixEnd_3903522 : Nat := 4983230072969 + 3 ^ 40 * 3903522 * 2
def baseEnd_3903522 : Nat := 2004383031399981685923035

theorem tailTrace_3903522 : CollatzResearch.WordTrace tailWord_3903522 prefixEnd_3903522 2004383031399981685923035 := by
  unfold tailWord_3903522
  simp only [CollatzResearch.WordTrace]
  refine ⟨35593285941053484331630205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94915429176142624884347213 35593285941053484331630205)
  ·
    refine ⟨13347482227895056624361327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35593285941053484331630205 13347482227895056624361327)
    ·
      refine ⟨20021223341842584936541991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13347482227895056624361327 20021223341842584936541991)
      ·
        refine ⟨30031835012763877404812987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20021223341842584936541991 30031835012763877404812987)
        ·
          refine ⟨45047752519145816107219481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30031835012763877404812987 45047752519145816107219481)
          ·
            refine ⟨33785814389359362080414611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45047752519145816107219481 33785814389359362080414611)
            ·
              refine ⟨50678721584039043120621917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33785814389359362080414611 50678721584039043120621917)
              ·
                refine ⟨19004520594014641170233219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50678721584039043120621917 19004520594014641170233219)
                ·
                  refine ⟨28506780891021961755349829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19004520594014641170233219 28506780891021961755349829)
                  ·
                    refine ⟨5345021417066617829128093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28506780891021961755349829 5345021417066617829128093)
                    ·
                      refine ⟨2004383031399981685923035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5345021417066617829128093 2004383031399981685923035)
                      ·
                        rfl

theorem cell23_3903522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_3903522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903522 prefixEnd_3903522 := by exact prefixLift 3903522
  have htrace : WordTrace (prefixWord ++ tailWord_3903522) baseStart_3903522 baseEnd_3903522 := by
    simpa [prefixWord, tailWord_3903522, baseEnd_3903522] using wordTrace_append hprefix tailTrace_3903522
  have hstable : (prefixWord ++ tailWord_3903522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903522).length < 2 ^ (prefixWord ++ tailWord_3903522).sum := by decide
  have hdescent : baseEnd_3903522 < baseStart_3903522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903525 : List Nat := [1, 3, 1, 2, 2, 3, 1, 2, 8]
def baseStart_3903525 : Nat := 118140960795 + 3903525 * 2 ^ 59
def prefixEnd_3903525 : Nat := 4983230072969 + 3 ^ 40 * 3903525 * 2
def baseEnd_3903525 : Nat := 222709396871327241576169

theorem tailTrace_3903525 : CollatzResearch.WordTrace tailWord_3903525 prefixEnd_3903525 222709396871327241576169 := by
  unfold tailWord_3903525
  simp only [CollatzResearch.WordTrace]
  refine ⟨142373253183203068838880029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94915502122135379225920019 142373253183203068838880029)
  ·
    refine ⟨53389969943701150814580011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142373253183203068838880029 53389969943701150814580011)
    ·
      refine ⟨80084954915551726221870017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53389969943701150814580011 80084954915551726221870017)
      ·
        refine ⟨60063716186663794666402513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80084954915551726221870017 60063716186663794666402513)
        ·
          refine ⟨45047787139997845999801885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60063716186663794666402513 45047787139997845999801885)
          ·
            refine ⟨16892920177499192249925707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45047787139997845999801885 16892920177499192249925707)
            ·
              refine ⟨25339380266248788374888561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16892920177499192249925707 25339380266248788374888561)
              ·
                refine ⟨19004535199686591281166421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25339380266248788374888561 19004535199686591281166421)
                ·
                  refine ⟨222709396871327241576169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19004535199686591281166421 222709396871327241576169)
                  ·
                    rfl

theorem cell23_3903525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 8].length) (baseStart_3903525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903525 prefixEnd_3903525 := by exact prefixLift 3903525
  have htrace : WordTrace (prefixWord ++ tailWord_3903525) baseStart_3903525 baseEnd_3903525 := by
    simpa [prefixWord, tailWord_3903525, baseEnd_3903525] using wordTrace_append hprefix tailTrace_3903525
  have hstable : (prefixWord ++ tailWord_3903525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903525).length < 2 ^ (prefixWord ++ tailWord_3903525).sum := by decide
  have hdescent : baseEnd_3903525 < baseStart_3903525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903542 : List Nat := [5, 1, 2, 1, 1, 1, 1, 3, 8]
def baseStart_3903542 : Nat := 118140960795 + 3903542 * 2 ^ 59
def prefixEnd_3903542 : Nat := 4983230072969 + 3 ^ 40 * 3903542 * 2
def baseEnd_3903542 : Nat := 222710366779230178630327

theorem tailTrace_3903542 : CollatzResearch.WordTrace tailWord_3903542 prefixEnd_3903542 222710366779230178630327 := by
  unfold tailWord_3903542
  simp only [CollatzResearch.WordTrace]
  refine ⟨8898367076508842546390555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94915915482760987161499253 8898367076508842546390555)
  ·
    refine ⟨13347550614763263819585833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8898367076508842546390555 13347550614763263819585833)
    ·
      refine ⟨10010662961072447864689375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13347550614763263819585833 10010662961072447864689375)
      ·
        refine ⟨15015994441608671797034063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10010662961072447864689375 15015994441608671797034063)
        ·
          refine ⟨22523991662413007695551095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15015994441608671797034063 22523991662413007695551095)
          ·
            refine ⟨33785987493619511543326643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22523991662413007695551095 33785987493619511543326643)
            ·
              refine ⟨50678981240429267314989965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33785987493619511543326643 50678981240429267314989965)
              ·
                refine ⟨19004617965160975243121237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50678981240429267314989965 19004617965160975243121237)
                ·
                  refine ⟨222710366779230178630327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19004617965160975243121237 222710366779230178630327)
                  ·
                    rfl

theorem cell23_3903542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_3903542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903542 prefixEnd_3903542 := by exact prefixLift 3903542
  have htrace : WordTrace (prefixWord ++ tailWord_3903542) baseStart_3903542 baseEnd_3903542 := by
    simpa [prefixWord, tailWord_3903542, baseEnd_3903542] using wordTrace_append hprefix tailTrace_3903542
  have hstable : (prefixWord ++ tailWord_3903542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903542).length < 2 ^ (prefixWord ++ tailWord_3903542).sum := by decide
  have hdescent : baseEnd_3903542 < baseStart_3903542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903619 : List Nat := [1, 1, 1, 3, 3, 3, 2, 3, 2, 4]
def baseStart_3903619 : Nat := 118140960795 + 3903619 * 2 ^ 59
def prefixEnd_3903619 : Nat := 4983230072969 + 3 ^ 40 * 3903619 * 2
def baseEnd_3903619 : Nat := 668144279674489268803363

theorem tailTrace_3903619 : CollatzResearch.WordTrace tailWord_3903619 prefixEnd_3903619 668144279674489268803363 := by
  unfold tailWord_3903619
  simp only [CollatzResearch.WordTrace]
  refine ⟨142376681644862522892801911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94917787763241681928534607 142376681644862522892801911)
  ·
    refine ⟨213565022467293784339202867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142376681644862522892801911 213565022467293784339202867)
    ·
      refine ⟨320347533700940676508804301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213565022467293784339202867 320347533700940676508804301)
      ·
        refine ⟨120130325137852753690801613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320347533700940676508804301 120130325137852753690801613)
        ·
          refine ⟨45048871926694782634050605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120130325137852753690801613 45048871926694782634050605)
          ·
            refine ⟨16893326972510543487768977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45048871926694782634050605 16893326972510543487768977)
            ·
              refine ⟨12669995229382907615826733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16893326972510543487768977 12669995229382907615826733)
              ·
                refine ⟨4751248211018590355935025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12669995229382907615826733 4751248211018590355935025)
                ·
                  refine ⟨3563436158263942766951269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4751248211018590355935025 3563436158263942766951269)
                  ·
                    refine ⟨668144279674489268803363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3563436158263942766951269 668144279674489268803363)
                    ·
                      rfl

theorem cell23_3903619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 2, 4].length) (baseStart_3903619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903619 prefixEnd_3903619 := by exact prefixLift 3903619
  have htrace : WordTrace (prefixWord ++ tailWord_3903619) baseStart_3903619 baseEnd_3903619 := by
    simpa [prefixWord, tailWord_3903619, baseEnd_3903619] using wordTrace_append hprefix tailTrace_3903619
  have hstable : (prefixWord ++ tailWord_3903619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903619).length < 2 ^ (prefixWord ++ tailWord_3903619).sum := by decide
  have hdescent : baseEnd_3903619 < baseStart_3903619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903626 : List Nat := [3, 1, 2, 3, 1, 2, 1, 1, 5, 2, 2]
def baseStart_3903626 : Nat := 118140960795 + 3903626 * 2 ^ 59
def prefixEnd_3903626 : Nat := 4983230072969 + 3 ^ 40 * 3903626 * 2
def baseEnd_3903626 : Nat := 2004436433388049279022557

theorem tailTrace_3903626 : CollatzResearch.WordTrace tailWord_3903626 prefixEnd_3903626 2004436433388049279022557 := by
  unfold tailWord_3903626
  simp only [CollatzResearch.WordTrace]
  refine ⟨35594234238959290772076683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94917957970558108725537821 35594234238959290772076683)
  ·
    refine ⟨53391351358438936158115025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35594234238959290772076683 53391351358438936158115025)
    ·
      refine ⟨40043513518829202118586269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53391351358438936158115025 40043513518829202118586269)
      ·
        refine ⟨15016317569560950794469851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40043513518829202118586269 15016317569560950794469851)
        ·
          refine ⟨22524476354341426191704777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15016317569560950794469851 22524476354341426191704777)
          ·
            refine ⟨16893357265756069643778583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22524476354341426191704777 16893357265756069643778583)
            ·
              refine ⟨25340035898634104465667875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16893357265756069643778583 25340035898634104465667875)
              ·
                refine ⟨38010053847951156698501813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25340035898634104465667875 38010053847951156698501813)
                ·
                  refine ⟨3563442548245420940484545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38010053847951156698501813 3563442548245420940484545)
                  ·
                    refine ⟨2672581911184065705363409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3563442548245420940484545 2672581911184065705363409)
                    ·
                      refine ⟨2004436433388049279022557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2672581911184065705363409 2004436433388049279022557)
                      ·
                        rfl

theorem cell23_3903626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_3903626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903626 prefixEnd_3903626 := by exact prefixLift 3903626
  have htrace : WordTrace (prefixWord ++ tailWord_3903626) baseStart_3903626 baseEnd_3903626 := by
    simpa [prefixWord, tailWord_3903626, baseEnd_3903626] using wordTrace_append hprefix tailTrace_3903626
  have hstable : (prefixWord ++ tailWord_3903626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903626).length < 2 ^ (prefixWord ++ tailWord_3903626).sum := by decide
  have hdescent : baseEnd_3903626 < baseStart_3903626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903630 : List Nat := [4, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2]
def baseStart_3903630 : Nat := 118140960795 + 3903630 * 2 ^ 59
def prefixEnd_3903630 : Nat := 4983230072969 + 3 ^ 40 * 3903630 * 2
def baseEnd_3903630 : Nat := 2004438487310667263372539

theorem tailTrace_3903630 : CollatzResearch.WordTrace tailWord_3903630 prefixEnd_3903630 2004438487310667263372539 := by
  unfold tailWord_3903630
  simp only [CollatzResearch.WordTrace]
  refine ⟨17797135355977833971431543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94918055231881781180968229 17797135355977833971431543)
  ·
    refine ⟨26695703033966750957147315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17797135355977833971431543 26695703033966750957147315)
    ·
      refine ⟨40043554550950126435720973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26695703033966750957147315 40043554550950126435720973)
      ·
        refine ⟨15016332956606297413395365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40043554550950126435720973 15016332956606297413395365)
        ·
          refine ⟨2815562429363680765011631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15016332956606297413395365 2815562429363680765011631)
          ·
            refine ⟨4223343644045521147517447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2815562429363680765011631 4223343644045521147517447)
            ·
              refine ⟨6335015466068281721276171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4223343644045521147517447 6335015466068281721276171)
              ·
                refine ⟨9502523199102422581914257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6335015466068281721276171 9502523199102422581914257)
                ·
                  refine ⟨7126892399326816936435693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9502523199102422581914257 7126892399326816936435693)
                  ·
                    refine ⟨2672584649747556351163385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7126892399326816936435693 2672584649747556351163385)
                    ·
                      refine ⟨2004438487310667263372539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2672584649747556351163385 2004438487310667263372539)
                      ·
                        rfl

theorem cell23_3903630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_3903630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903630 prefixEnd_3903630 := by exact prefixLift 3903630
  have htrace : WordTrace (prefixWord ++ tailWord_3903630) baseStart_3903630 baseEnd_3903630 := by
    simpa [prefixWord, tailWord_3903630, baseEnd_3903630] using wordTrace_append hprefix tailTrace_3903630
  have hstable : (prefixWord ++ tailWord_3903630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903630).length < 2 ^ (prefixWord ++ tailWord_3903630).sum := by decide
  have hdescent : baseEnd_3903630 < baseStart_3903630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903632 : List Nat := [2, 1, 1, 1, 1, 1, 9, 7]
def baseStart_3903632 : Nat := 118140960795 + 3903632 * 2 ^ 59
def prefixEnd_3903632 : Nat := 4983230072969 + 3 ^ 40 * 3903632 * 2
def baseEnd_3903632 : Nat := 74238500528591713168427

theorem tailTrace_3903632 : CollatzResearch.WordTrace tailWord_3903632 prefixEnd_3903632 74238500528591713168427 := by
  unfold tailWord_3903632
  simp only [CollatzResearch.WordTrace]
  refine ⟨71188577896907713056512575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94918103862543617408683433 71188577896907713056512575)
  ·
    refine ⟨106782866845361569584768863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71188577896907713056512575 106782866845361569584768863)
    ·
      refine ⟨160174300268042354377153295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106782866845361569584768863 160174300268042354377153295)
      ·
        refine ⟨240261450402063531565729943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160174300268042354377153295 240261450402063531565729943)
        ·
          refine ⟨360392175603095297348594915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240261450402063531565729943 360392175603095297348594915)
          ·
            refine ⟨540588263404642946022892373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360392175603095297348594915 540588263404642946022892373)
            ·
              refine ⟨3167509355886579761852885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 540588263404642946022892373 3167509355886579761852885)
              ·
                refine ⟨74238500528591713168427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3167509355886579761852885 74238500528591713168427)
                ·
                  rfl

theorem cell23_3903632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 7].length) (baseStart_3903632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903632 prefixEnd_3903632 := by exact prefixLift 3903632
  have htrace : WordTrace (prefixWord ++ tailWord_3903632) baseStart_3903632 baseEnd_3903632 := by
    simpa [prefixWord, tailWord_3903632, baseEnd_3903632] using wordTrace_append hprefix tailTrace_3903632
  have hstable : (prefixWord ++ tailWord_3903632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903632).length < 2 ^ (prefixWord ++ tailWord_3903632).sum := by decide
  have hdescent : baseEnd_3903632 < baseStart_3903632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903759 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 4, 5, 2]
def baseStart_3903759 : Nat := 118140960795 + 3903759 * 2 ^ 59
def prefixEnd_3903759 : Nat := 4983230072969 + 3 ^ 40 * 3903759 * 2
def baseEnd_3903759 : Nat := 2004504726315097258659445

theorem tailTrace_3903759 : CollatzResearch.WordTrace tailWord_3903759 prefixEnd_3903759 2004504726315097258659445 := by
  unfold tailWord_3903759
  simp only [CollatzResearch.WordTrace]
  refine ⟨142381787864355326802898331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94921191909570217868598887 142381787864355326802898331)
  ·
    refine ⟨213572681796532990204347497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142381787864355326802898331 213572681796532990204347497)
    ·
      refine ⟨160179511347399742653260623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213572681796532990204347497 160179511347399742653260623)
      ·
        refine ⟨240269267021099613979890935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160179511347399742653260623 240269267021099613979890935)
        ·
          refine ⟨360403900531649420969836403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240269267021099613979890935 360403900531649420969836403)
          ·
            refine ⟨540605850797474131454754605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360403900531649420969836403 540605850797474131454754605)
            ·
              refine ⟨202727194049052799295532977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 540605850797474131454754605 202727194049052799295532977)
              ·
                refine ⟨152045395536789599471649733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202727194049052799295532977 152045395536789599471649733)
                ·
                  refine ⟨28508511663148049900934325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152045395536789599471649733 28508511663148049900934325)
                  ·
                    refine ⟨2672672968420129678212593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28508511663148049900934325 2672672968420129678212593)
                    ·
                      refine ⟨2004504726315097258659445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2672672968420129678212593 2004504726315097258659445)
                      ·
                        rfl

theorem cell23_3903759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 5, 2].length) (baseStart_3903759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903759 prefixEnd_3903759 := by exact prefixLift 3903759
  have htrace : WordTrace (prefixWord ++ tailWord_3903759) baseStart_3903759 baseEnd_3903759 := by
    simpa [prefixWord, tailWord_3903759, baseEnd_3903759] using wordTrace_append hprefix tailTrace_3903759
  have hstable : (prefixWord ++ tailWord_3903759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903759).length < 2 ^ (prefixWord ++ tailWord_3903759).sum := by decide
  have hdescent : baseEnd_3903759 < baseStart_3903759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903773 : List Nat := [1, 4, 2, 3, 2, 1, 1, 4, 5]
def baseStart_3903773 : Nat := 118140960795 + 3903773 * 2 ^ 59
def prefixEnd_3903773 : Nat := 4983230072969 + 3 ^ 40 * 3903773 * 2
def baseEnd_3903773 : Nat := 222723546116028911542709

theorem tailTrace_3903773 : CollatzResearch.WordTrace tailWord_3903773 prefixEnd_3903773 222723546116028911542709 := by
  unfold tailWord_3903773
  simp only [CollatzResearch.WordTrace]
  refine ⟨142382298486304607193907973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94921532324203071462605315 142382298486304607193907973)
  ·
    refine ⟨26696680966182113848857745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142382298486304607193907973 26696680966182113848857745)
    ·
      refine ⟨20022510724636585386643309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26696680966182113848857745 20022510724636585386643309)
      ·
        refine ⟨7508441521738719519991241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20022510724636585386643309 7508441521738719519991241)
        ·
          refine ⟨5631331141304039639993431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7508441521738719519991241 5631331141304039639993431)
          ·
            refine ⟨8446996711956059459990147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5631331141304039639993431 8446996711956059459990147)
            ·
              refine ⟨12670495067934089189985221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8446996711956059459990147 12670495067934089189985221)
              ·
                refine ⟨2375717825237641723122229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12670495067934089189985221 2375717825237641723122229)
                ·
                  refine ⟨222723546116028911542709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2375717825237641723122229 222723546116028911542709)
                  ·
                    rfl

theorem cell23_3903773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 4, 5].length) (baseStart_3903773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903773 prefixEnd_3903773 := by exact prefixLift 3903773
  have htrace : WordTrace (prefixWord ++ tailWord_3903773) baseStart_3903773 baseEnd_3903773 := by
    simpa [prefixWord, tailWord_3903773, baseEnd_3903773] using wordTrace_append hprefix tailTrace_3903773
  have hstable : (prefixWord ++ tailWord_3903773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903773).length < 2 ^ (prefixWord ++ tailWord_3903773).sum := by decide
  have hdescent : baseEnd_3903773 < baseStart_3903773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903776 : List Nat := [2, 1, 1, 5, 2, 1, 1, 1, 2, 5, 2]
def baseStart_3903776 : Nat := 118140960795 + 3903776 * 2 ^ 59
def prefixEnd_3903776 : Nat := 4983230072969 + 3 ^ 40 * 3903776 * 2
def baseEnd_3903776 : Nat := 2004513455486223692146867

theorem tailTrace_3903776 : CollatzResearch.WordTrace tailWord_3903776 prefixEnd_3903776 2004513455486223692146867 := by
  unfold tailWord_3903776
  simp only [CollatzResearch.WordTrace]
  refine ⟨71191203952646869353133591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94921605270195825804178121 71191203952646869353133591)
  ·
    refine ⟨106786805928970304029700387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71191203952646869353133591 106786805928970304029700387)
    ·
      refine ⟨160180208893455456044550581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106786805928970304029700387 160180208893455456044550581)
      ·
        refine ⟨15016894583761449004176617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160180208893455456044550581 15016894583761449004176617)
        ·
          refine ⟨11262670937821086753132463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15016894583761449004176617 11262670937821086753132463)
          ·
            refine ⟨16894006406731630129698695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11262670937821086753132463 16894006406731630129698695)
            ·
              refine ⟨25341009610097445194548043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16894006406731630129698695 25341009610097445194548043)
              ·
                refine ⟨38011514415146167791822065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25341009610097445194548043 38011514415146167791822065)
                ·
                  refine ⟨28508635811359625843866549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38011514415146167791822065 28508635811359625843866549)
                  ·
                    refine ⟨2672684607314964922862489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28508635811359625843866549 2672684607314964922862489)
                    ·
                      refine ⟨2004513455486223692146867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2672684607314964922862489 2004513455486223692146867)
                      ·
                        rfl

theorem cell23_3903776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_3903776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903776 prefixEnd_3903776 := by exact prefixLift 3903776
  have htrace : WordTrace (prefixWord ++ tailWord_3903776) baseStart_3903776 baseEnd_3903776 := by
    simpa [prefixWord, tailWord_3903776, baseEnd_3903776] using wordTrace_append hprefix tailTrace_3903776
  have hstable : (prefixWord ++ tailWord_3903776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903776).length < 2 ^ (prefixWord ++ tailWord_3903776).sum := by decide
  have hdescent : baseEnd_3903776 < baseStart_3903776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903806 : List Nat := [4, 2, 1, 2, 1, 3, 1, 1, 1, 3, 4]
def baseStart_3903806 : Nat := 118140960795 + 3903806 * 2 ^ 59
def prefixEnd_3903806 : Nat := 4983230072969 + 3 ^ 40 * 3903806 * 2
def baseEnd_3903806 : Nat := 2004528859905858574771729

theorem tailTrace_3903806 : CollatzResearch.WordTrace tailWord_3903806 prefixEnd_3903806 2004528859905858574771729 := by
  unfold tailWord_3903806
  simp only [CollatzResearch.WordTrace]
  refine ⟨17797937761898131728732409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94922334730123369219906181 17797937761898131728732409)
  ·
    refine ⟨13348453321423598796549307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17797937761898131728732409 13348453321423598796549307)
    ·
      refine ⟨20022679982135398194823961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13348453321423598796549307 20022679982135398194823961)
      ·
        refine ⟨15017009986601548646117971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20022679982135398194823961 15017009986601548646117971)
        ·
          refine ⟨22525514979902322969176957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15017009986601548646117971 22525514979902322969176957)
          ·
            refine ⟨8447068117463371113441359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22525514979902322969176957 8447068117463371113441359)
            ·
              refine ⟨12670602176195056670162039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8447068117463371113441359 12670602176195056670162039)
              ·
                refine ⟨19005903264292585005243059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12670602176195056670162039 19005903264292585005243059)
                ·
                  refine ⟨28508854896438877507864589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19005903264292585005243059 28508854896438877507864589)
                  ·
                    refine ⟨10690820586164579065449221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28508854896438877507864589 10690820586164579065449221)
                    ·
                      refine ⟨2004528859905858574771729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10690820586164579065449221 2004528859905858574771729)
                      ·
                        rfl

theorem cell23_3903806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_3903806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903806 prefixEnd_3903806 := by exact prefixLift 3903806
  have htrace : WordTrace (prefixWord ++ tailWord_3903806) baseStart_3903806 baseEnd_3903806 := by
    simpa [prefixWord, tailWord_3903806, baseEnd_3903806] using wordTrace_append hprefix tailTrace_3903806
  have hstable : (prefixWord ++ tailWord_3903806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903806).length < 2 ^ (prefixWord ++ tailWord_3903806).sum := by decide
  have hdescent : baseEnd_3903806 < baseStart_3903806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903826 : List Nat := [3, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3]
def baseStart_3903826 : Nat := 118140960795 + 3903826 * 2 ^ 59
def prefixEnd_3903826 : Nat := 4983230072969 + 3 ^ 40 * 3903826 * 2
def baseEnd_3903826 : Nat := 2004539129518948496521637

theorem tailTrace_3903826 : CollatzResearch.WordTrace tailWord_3903826 prefixEnd_3903826 2004539129518948496521637 := by
  unfold tailWord_3903826
  simp only [CollatzResearch.WordTrace]
  refine ⟨35596057888778149311396833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94922821036741731497058221 35596057888778149311396833)
  ·
    refine ⟨26697043416583611983547625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35596057888778149311396833 26697043416583611983547625)
    ·
      refine ⟨20022782562437708987660719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26697043416583611983547625 20022782562437708987660719)
      ·
        refine ⟨30034173843656563481491079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20022782562437708987660719 30034173843656563481491079)
        ·
          refine ⟨45051260765484845222236619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30034173843656563481491079 45051260765484845222236619)
          ·
            refine ⟨67576891148227267833354929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45051260765484845222236619 67576891148227267833354929)
            ·
              refine ⟨50682668361170450875016197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67576891148227267833354929 50682668361170450875016197)
              ·
                refine ⟨9503000317719459539065537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50682668361170450875016197 9503000317719459539065537)
                ·
                  refine ⟨7127250238289594654299153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9503000317719459539065537 7127250238289594654299153)
                  ·
                    refine ⟨5345437678717195990724365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7127250238289594654299153 5345437678717195990724365)
                    ·
                      refine ⟨2004539129518948496521637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5345437678717195990724365 2004539129518948496521637)
                      ·
                        rfl

theorem cell23_3903826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_3903826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903826 prefixEnd_3903826 := by exact prefixLift 3903826
  have htrace : WordTrace (prefixWord ++ tailWord_3903826) baseStart_3903826 baseEnd_3903826 := by
    simpa [prefixWord, tailWord_3903826, baseEnd_3903826] using wordTrace_append hprefix tailTrace_3903826
  have hstable : (prefixWord ++ tailWord_3903826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903826).length < 2 ^ (prefixWord ++ tailWord_3903826).sum := by decide
  have hdescent : baseEnd_3903826 < baseStart_3903826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903876 : List Nat := [2, 3, 2, 1, 1, 2, 1, 5, 1, 5]
def baseStart_3903876 : Nat := 118140960795 + 3903876 * 2 ^ 59
def prefixEnd_3903876 : Nat := 4983230072969 + 3 ^ 40 * 3903876 * 2
def baseEnd_3903876 : Nat := 668188267850557766965469

theorem tailTrace_3903876 : CollatzResearch.WordTrace tailWord_3903876 prefixEnd_3903876 668188267850557766965469 := by
  unfold tailWord_3903876
  simp only [CollatzResearch.WordTrace]
  refine ⟨71193027602465727892453741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94924036803287637189938321 71193027602465727892453741)
  ·
    refine ⟨26697385350924647959670153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71193027602465727892453741 26697385350924647959670153)
    ·
      refine ⟨20023039013193485969752615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26697385350924647959670153 20023039013193485969752615)
      ·
        refine ⟨30034558519790228954628923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20023039013193485969752615 30034558519790228954628923)
        ·
          refine ⟨45051837779685343431943385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30034558519790228954628923 45051837779685343431943385)
          ·
            refine ⟨33788878334764007573957539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45051837779685343431943385 33788878334764007573957539)
            ·
              refine ⟨50683317502146011360936309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33788878334764007573957539 50683317502146011360936309)
              ·
                refine ⟨4751561015826188565087779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50683317502146011360936309 4751561015826188565087779)
                ·
                  refine ⟨7127341523739282847631669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4751561015826188565087779 7127341523739282847631669)
                  ·
                    refine ⟨668188267850557766965469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7127341523739282847631669 668188267850557766965469)
                    ·
                      rfl

theorem cell23_3903876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_3903876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903876 prefixEnd_3903876 := by exact prefixLift 3903876
  have htrace : WordTrace (prefixWord ++ tailWord_3903876) baseStart_3903876 baseEnd_3903876 := by
    simpa [prefixWord, tailWord_3903876, baseEnd_3903876] using wordTrace_append hprefix tailTrace_3903876
  have hstable : (prefixWord ++ tailWord_3903876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903876).length < 2 ^ (prefixWord ++ tailWord_3903876).sum := by decide
  have hdescent : baseEnd_3903876 < baseStart_3903876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903883 : List Nat := [1, 1, 1, 1, 4, 5, 1, 2, 2, 3, 2]
def baseStart_3903883 : Nat := 118140960795 + 3903883 * 2 ^ 59
def prefixEnd_3903883 : Nat := 4983230072969 + 3 ^ 40 * 3903883 * 2
def baseEnd_3903883 : Nat := 2004568397916254773508875

theorem tailTrace_3903883 : CollatzResearch.WordTrace tailWord_3903883 prefixEnd_3903883 2004568397916254773508875 := by
  unfold tailWord_3903883
  simp only [CollatzResearch.WordTrace]
  refine ⟨142386310515906095980412303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94924207010604063986941535 142386310515906095980412303)
  ·
    refine ⟨213579465773859143970618455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142386310515906095980412303 213579465773859143970618455)
    ·
      refine ⟨320369198660788715955927683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213579465773859143970618455 320369198660788715955927683)
      ·
        refine ⟨480553797991183073933891525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320369198660788715955927683 480553797991183073933891525)
        ·
          refine ⟨90103837123346826362604661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 480553797991183073933891525 90103837123346826362604661)
          ·
            refine ⟨8447234730313764971494187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90103837123346826362604661 8447234730313764971494187)
            ·
              refine ⟨12670852095470647457241281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8447234730313764971494187 12670852095470647457241281)
              ·
                refine ⟨9503139071602985592930961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12670852095470647457241281 9503139071602985592930961)
                ·
                  refine ⟨7127354303702239194698221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9503139071602985592930961 7127354303702239194698221)
                  ·
                    refine ⟨2672757863888339698011833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7127354303702239194698221 2672757863888339698011833)
                    ·
                      refine ⟨2004568397916254773508875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2672757863888339698011833 2004568397916254773508875)
                      ·
                        rfl

theorem cell23_3903883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 3, 2].length) (baseStart_3903883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903883 prefixEnd_3903883 := by exact prefixLift 3903883
  have htrace : WordTrace (prefixWord ++ tailWord_3903883) baseStart_3903883 baseEnd_3903883 := by
    simpa [prefixWord, tailWord_3903883, baseEnd_3903883] using wordTrace_append hprefix tailTrace_3903883
  have hstable : (prefixWord ++ tailWord_3903883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903883).length < 2 ^ (prefixWord ++ tailWord_3903883).sum := by decide
  have hdescent : baseEnd_3903883 < baseStart_3903883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903906 : List Nat := [3, 3, 1, 2, 1, 1, 2, 3, 1, 6]
def baseStart_3903906 : Nat := 118140960795 + 3903906 * 2 ^ 59
def prefixEnd_3903906 : Nat := 4983230072969 + 3 ^ 40 * 3903906 * 2
def baseEnd_3903906 : Nat := 668193402657102727840423

theorem tailTrace_3903906 : CollatzResearch.WordTrace tailWord_3903906 prefixEnd_3903906 668193402657102727840423 := by
  unfold tailWord_3903906
  simp only [CollatzResearch.WordTrace]
  refine ⟨35596787348705692727124893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94924766263215180605666381 35596787348705692727124893)
  ·
    refine ⟨13348795255764634772671835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35596787348705692727124893 13348795255764634772671835)
    ·
      refine ⟨20023192883646952159007753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13348795255764634772671835 20023192883646952159007753)
      ·
        refine ⟨15017394662735214119255815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20023192883646952159007753 15017394662735214119255815)
        ·
          refine ⟨22526091994102821178883723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15017394662735214119255815 22526091994102821178883723)
          ·
            refine ⟨33789137991154231768325585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22526091994102821178883723 33789137991154231768325585)
            ·
              refine ⟨25341853493365673826244189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33789137991154231768325585 25341853493365673826244189)
              ·
                refine ⟨9503195060012127684841571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25341853493365673826244189 9503195060012127684841571)
                ·
                  refine ⟨14254792590018191527262357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9503195060012127684841571 14254792590018191527262357)
                  ·
                    refine ⟨668193402657102727840423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14254792590018191527262357 668193402657102727840423)
                    ·
                      rfl

theorem cell23_3903906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_3903906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903906 prefixEnd_3903906 := by exact prefixLift 3903906
  have htrace : WordTrace (prefixWord ++ tailWord_3903906) baseStart_3903906 baseEnd_3903906 := by
    simpa [prefixWord, tailWord_3903906, baseEnd_3903906] using wordTrace_append hprefix tailTrace_3903906
  have hstable : (prefixWord ++ tailWord_3903906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903906).length < 2 ^ (prefixWord ++ tailWord_3903906).sum := by decide
  have hdescent : baseEnd_3903906 < baseStart_3903906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903909 : List Nat := [1, 3, 1, 2, 1, 1, 3, 3, 1, 1, 6]
def baseStart_3903909 : Nat := 118140960795 + 3903909 * 2 ^ 59
def prefixEnd_3903909 : Nat := 4983230072969 + 3 ^ 40 * 3903909 * 2
def baseEnd_3903909 : Nat := 2004581748413271671783755

theorem tailTrace_3903909 : CollatzResearch.WordTrace tailWord_3903909 prefixEnd_3903909 2004581748413271671783755 := by
  unfold tailWord_3903909
  simp only [CollatzResearch.WordTrace]
  refine ⟨142387258813811902420858781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94924839209207934947239187 142387258813811902420858781)
  ·
    refine ⟨53395222055179463407822043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142387258813811902420858781 53395222055179463407822043)
    ·
      refine ⟨80092833082769195111733065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53395222055179463407822043 80092833082769195111733065)
      ·
        refine ⟨60069624812076896333799799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80092833082769195111733065 60069624812076896333799799)
        ·
          refine ⟨90104437218115344500699699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60069624812076896333799799 90104437218115344500699699)
          ·
            refine ⟨135156655827173016751049549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90104437218115344500699699 135156655827173016751049549)
            ·
              refine ⟨50683745935189881281643581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135156655827173016751049549 50683745935189881281643581)
              ·
                refine ⟨19006404725696205480616343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50683745935189881281643581 19006404725696205480616343)
                ·
                  refine ⟨28509607088544308220924515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19006404725696205480616343 28509607088544308220924515)
                  ·
                    refine ⟨42764410632816462331386773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28509607088544308220924515 42764410632816462331386773)
                    ·
                      refine ⟨2004581748413271671783755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42764410632816462331386773 2004581748413271671783755)
                      ·
                        rfl

theorem cell23_3903909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_3903909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903909 prefixEnd_3903909 := by exact prefixLift 3903909
  have htrace : WordTrace (prefixWord ++ tailWord_3903909) baseStart_3903909 baseEnd_3903909 := by
    simpa [prefixWord, tailWord_3903909, baseEnd_3903909] using wordTrace_append hprefix tailTrace_3903909
  have hstable : (prefixWord ++ tailWord_3903909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903909).length < 2 ^ (prefixWord ++ tailWord_3903909).sum := by decide
  have hdescent : baseEnd_3903909 < baseStart_3903909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903913 : List Nat := [1, 2, 1, 1, 1, 1, 3, 6, 3, 2, 2]
def baseStart_3903913 : Nat := 118140960795 + 3903913 * 2 ^ 59
def prefixEnd_3903913 : Nat := 4983230072969 + 3 ^ 40 * 3903913 * 2
def baseEnd_3903913 : Nat := 2004583802335889656133737

theorem tailTrace_3903913 : CollatzResearch.WordTrace tailWord_3903913 prefixEnd_3903913 2004583802335889656133737 := by
  unfold tailWord_3903913
  simp only [CollatzResearch.WordTrace]
  refine ⟨142387404705797411104004393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94924936470531607402669595 142387404705797411104004393)
  ·
    refine ⟨106790553529348058328003295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142387404705797411104004393 106790553529348058328003295)
    ·
      refine ⟨160185830294022087492004943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106790553529348058328003295 160185830294022087492004943)
      ·
        refine ⟨240278745441033131238007415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160185830294022087492004943 240278745441033131238007415)
        ·
          refine ⟨360418118161549696857011123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240278745441033131238007415 360418118161549696857011123)
          ·
            refine ⟨540627177242324545285516685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360418118161549696857011123 540627177242324545285516685)
            ·
              refine ⟨202735191465871704482068757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 540627177242324545285516685 202735191465871704482068757)
              ·
                refine ⟨9503212099962736147596973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 202735191465871704482068757 9503212099962736147596973)
                ·
                  refine ⟨3563704537486026055348865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9503212099962736147596973 3563704537486026055348865)
                  ·
                    refine ⟨2672778403114519541511649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3563704537486026055348865 2672778403114519541511649)
                    ·
                      refine ⟨2004583802335889656133737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2672778403114519541511649 2004583802335889656133737)
                      ·
                        rfl

theorem cell23_3903913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 3, 2, 2].length) (baseStart_3903913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903913 prefixEnd_3903913 := by exact prefixLift 3903913
  have htrace : WordTrace (prefixWord ++ tailWord_3903913) baseStart_3903913 baseEnd_3903913 := by
    simpa [prefixWord, tailWord_3903913, baseEnd_3903913] using wordTrace_append hprefix tailTrace_3903913
  have hstable : (prefixWord ++ tailWord_3903913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903913).length < 2 ^ (prefixWord ++ tailWord_3903913).sum := by decide
  have hdescent : baseEnd_3903913 < baseStart_3903913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903917 : List Nat := [1, 5, 2, 2, 2, 1, 2, 1, 2, 3, 2]
def baseStart_3903917 : Nat := 118140960795 + 3903917 * 2 ^ 59
def prefixEnd_3903917 : Nat := 4983230072969 + 3 ^ 40 * 3903917 * 2
def baseEnd_3903917 : Nat := 2004585856258507640483719

theorem tailTrace_3903917 : CollatzResearch.WordTrace tailWord_3903917 prefixEnd_3903917 2004585856258507640483719 := by
  unfold tailWord_3903917
  simp only [CollatzResearch.WordTrace]
  refine ⟨142387550597782919787150005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94925033731855279858100003 142387550597782919787150005)
  ·
    refine ⟨13348832868542148730045313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142387550597782919787150005 13348832868542148730045313)
    ·
      refine ⟨10011624651406611547533985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13348832868542148730045313 10011624651406611547533985)
      ·
        refine ⟨7508718488554958660650489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10011624651406611547533985 7508718488554958660650489)
        ·
          refine ⟨5631538866416218995487867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7508718488554958660650489 5631538866416218995487867)
          ·
            refine ⟨8447308299624328493231801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5631538866416218995487867 8447308299624328493231801)
            ·
              refine ⟨6335481224718246369923851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8447308299624328493231801 6335481224718246369923851)
              ·
                refine ⟨9503221837077369554885777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6335481224718246369923851 9503221837077369554885777)
                ·
                  refine ⟨7127416377808027166164333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9503221837077369554885777 7127416377808027166164333)
                  ·
                    refine ⟨2672781141678010187311625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7127416377808027166164333 2672781141678010187311625)
                    ·
                      refine ⟨2004585856258507640483719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2672781141678010187311625 2004585856258507640483719)
                      ·
                        rfl

theorem cell23_3903917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_3903917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903917 prefixEnd_3903917 := by exact prefixLift 3903917
  have htrace : WordTrace (prefixWord ++ tailWord_3903917) baseStart_3903917 baseEnd_3903917 := by
    simpa [prefixWord, tailWord_3903917, baseEnd_3903917] using wordTrace_append hprefix tailTrace_3903917
  have hstable : (prefixWord ++ tailWord_3903917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903917).length < 2 ^ (prefixWord ++ tailWord_3903917).sum := by decide
  have hdescent : baseEnd_3903917 < baseStart_3903917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903933 : List Nat := [1, 4, 1, 2, 2, 4, 1, 1, 1, 1, 5]
def baseStart_3903933 : Nat := 118140960795 + 3903933 * 2 ^ 59
def prefixEnd_3903933 : Nat := 4983230072969 + 3 ^ 40 * 3903933 * 2
def baseEnd_3903933 : Nat := 2004594071948979577883645

theorem tailTrace_3903933 : CollatzResearch.WordTrace tailWord_3903933 prefixEnd_3903933 2004594071948979577883645 := by
  unfold tailWord_3903933
  simp only [CollatzResearch.WordTrace]
  refine ⟨142388134165724954519732453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94925422777149969679821635 142388134165724954519732453)
  ·
    refine ⟨26697775156073428972449835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142388134165724954519732453 26697775156073428972449835)
    ·
      refine ⟨40046662734110143458674753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26697775156073428972449835 40046662734110143458674753)
      ·
        refine ⟨30034997050582607594006065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40046662734110143458674753 30034997050582607594006065)
        ·
          refine ⟨22526247787936955695504549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30034997050582607594006065 22526247787936955695504549)
          ·
            refine ⟨4223671460238179192907103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22526247787936955695504549 4223671460238179192907103)
            ·
              refine ⟨6335507190357268789360655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4223671460238179192907103 6335507190357268789360655)
              ·
                refine ⟨9503260785535903184040983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6335507190357268789360655 9503260785535903184040983)
                ·
                  refine ⟨14254891178303854776061475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9503260785535903184040983 14254891178303854776061475)
                  ·
                    refine ⟨21382336767455782164092213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14254891178303854776061475 21382336767455782164092213)
                    ·
                      refine ⟨2004594071948979577883645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21382336767455782164092213 2004594071948979577883645)
                      ·
                        rfl

theorem cell23_3903933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_3903933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903933 prefixEnd_3903933 := by exact prefixLift 3903933
  have htrace : WordTrace (prefixWord ++ tailWord_3903933) baseStart_3903933 baseEnd_3903933 := by
    simpa [prefixWord, tailWord_3903933, baseEnd_3903933] using wordTrace_append hprefix tailTrace_3903933
  have hstable : (prefixWord ++ tailWord_3903933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903933).length < 2 ^ (prefixWord ++ tailWord_3903933).sum := by decide
  have hdescent : baseEnd_3903933 < baseStart_3903933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903946 : List Nat := [3, 1, 2, 1, 2, 2, 1, 2, 3, 3, 3]
def baseStart_3903946 : Nat := 118140960795 + 3903946 * 2 ^ 59
def prefixEnd_3903946 : Nat := 4983230072969 + 3 ^ 40 * 3903946 * 2
def baseEnd_3903946 : Nat := 2004600747197488027021085

theorem tailTrace_3903946 : CollatzResearch.WordTrace tailWord_3903946 prefixEnd_3903946 2004600747197488027021085 := by
  unfold tailWord_3903946
  simp only [CollatzResearch.WordTrace]
  refine ⟨35597152078669464434988923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94925738876451905159970461 35597152078669464434988923)
  ·
    refine ⟨53395728118004196652483385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35597152078669464434988923 53395728118004196652483385)
    ·
      refine ⟨40046796088503147489362539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53395728118004196652483385 40046796088503147489362539)
      ·
        refine ⟨60070194132754721234043809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40046796088503147489362539 60070194132754721234043809)
        ·
          refine ⟨45052645599566040925532857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60070194132754721234043809 45052645599566040925532857)
          ·
            refine ⟨33789484199674530694149643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45052645599566040925532857 33789484199674530694149643)
            ·
              refine ⟨50684226299511796041224465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33789484199674530694149643 50684226299511796041224465)
              ·
                refine ⟨38013169724633847030918349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50684226299511796041224465 38013169724633847030918349)
                ·
                  refine ⟨14254938646737692636594381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38013169724633847030918349 14254938646737692636594381)
                  ·
                    refine ⟨5345601992526634738722893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14254938646737692636594381 5345601992526634738722893)
                    ·
                      refine ⟨2004600747197488027021085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5345601992526634738722893 2004600747197488027021085)
                      ·
                        rfl

theorem cell23_3903946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_3903946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903946 prefixEnd_3903946 := by exact prefixLift 3903946
  have htrace : WordTrace (prefixWord ++ tailWord_3903946) baseStart_3903946 baseEnd_3903946 := by
    simpa [prefixWord, tailWord_3903946, baseEnd_3903946] using wordTrace_append hprefix tailTrace_3903946
  have hstable : (prefixWord ++ tailWord_3903946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903946).length < 2 ^ (prefixWord ++ tailWord_3903946).sum := by decide
  have hdescent : baseEnd_3903946 < baseStart_3903946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903959 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 5]
def baseStart_3903959 : Nat := 118140960795 + 3903959 * 2 ^ 59
def prefixEnd_3903959 : Nat := 4983230072969 + 3 ^ 40 * 3903959 * 2
def baseEnd_3903959 : Nat := 2004607422445996476158525

theorem tailTrace_3903959 : CollatzResearch.WordTrace tailWord_3903959 prefixEnd_3903959 2004607422445996476158525 := by
  unfold tailWord_3903959
  simp only [CollatzResearch.WordTrace]
  refine ⟨142389082463630760960178931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94926054975753840640119287 142389082463630760960178931)
  ·
    refine ⟨213583623695446141440268397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142389082463630760960178931 213583623695446141440268397)
    ·
      refine ⟨80093858885792303040100649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213583623695446141440268397 80093858885792303040100649)
      ·
        refine ⟨60070394164344227280075487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80093858885792303040100649 60070394164344227280075487)
        ·
          refine ⟨90105591246516340920113231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60070394164344227280075487 90105591246516340920113231)
          ·
            refine ⟨135158386869774511380169847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90105591246516340920113231 135158386869774511380169847)
            ·
              refine ⟨202737580304661767070254771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135158386869774511380169847 202737580304661767070254771)
              ·
                refine ⟨304106370456992650605382157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202737580304661767070254771 304106370456992650605382157)
                ·
                  refine ⟨114039888921372243977018309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 304106370456992650605382157 114039888921372243977018309)
                  ·
                    refine ⟨21382479172757295745690933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114039888921372243977018309 21382479172757295745690933)
                    ·
                      refine ⟨2004607422445996476158525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21382479172757295745690933 2004607422445996476158525)
                      ·
                        rfl

theorem cell23_3903959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_3903959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903959 prefixEnd_3903959 := by exact prefixLift 3903959
  have htrace : WordTrace (prefixWord ++ tailWord_3903959) baseStart_3903959 baseEnd_3903959 := by
    simpa [prefixWord, tailWord_3903959, baseEnd_3903959] using wordTrace_append hprefix tailTrace_3903959
  have hstable : (prefixWord ++ tailWord_3903959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903959).length < 2 ^ (prefixWord ++ tailWord_3903959).sum := by decide
  have hdescent : baseEnd_3903959 < baseStart_3903959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3903979 : List Nat := [1, 1, 1, 1, 2, 3, 3, 2, 1, 8]
def baseStart_3903979 : Nat := 118140960795 + 3903979 * 2 ^ 59
def prefixEnd_3903979 : Nat := 4983230072969 + 3 ^ 40 * 3903979 * 2
def baseEnd_3903979 : Nat := 668205897353028799302811

theorem tailTrace_3903979 : CollatzResearch.WordTrace tailWord_3903979 prefixEnd_3903979 668205897353028799302811 := by
  unfold tailWord_3903979
  simp only [CollatzResearch.WordTrace]
  refine ⟨142389811923558304375906991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94926541282372202917271327 142389811923558304375906991)
  ·
    refine ⟨213584717885337456563860487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142389811923558304375906991 213584717885337456563860487)
    ·
      refine ⟨320377076828006184845790731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213584717885337456563860487 320377076828006184845790731)
      ·
        refine ⟨480565615242009277268686097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320377076828006184845790731 480565615242009277268686097)
        ·
          refine ⟨360424211431506957951514573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480565615242009277268686097 360424211431506957951514573)
          ·
            refine ⟨135159079286815109231817965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360424211431506957951514573 135159079286815109231817965)
            ·
              refine ⟨50684654732555665961931737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135159079286815109231817965 50684654732555665961931737)
              ·
                refine ⟨38013491049416749471448803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50684654732555665961931737 38013491049416749471448803)
                ·
                  refine ⟨57020236574125124207173205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38013491049416749471448803 57020236574125124207173205)
                  ·
                    refine ⟨668205897353028799302811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57020236574125124207173205 668205897353028799302811)
                    ·
                      rfl

theorem cell23_3903979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 8].length) (baseStart_3903979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3903979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3903979 prefixEnd_3903979 := by exact prefixLift 3903979
  have htrace : WordTrace (prefixWord ++ tailWord_3903979) baseStart_3903979 baseEnd_3903979 := by
    simpa [prefixWord, tailWord_3903979, baseEnd_3903979] using wordTrace_append hprefix tailTrace_3903979
  have hstable : (prefixWord ++ tailWord_3903979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3903979).length < 2 ^ (prefixWord ++ tailWord_3903979).sum := by decide
  have hdescent : baseEnd_3903979 < baseStart_3903979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3903979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904026 : List Nat := [3, 1, 1, 3, 1, 1, 4, 2, 7]
def baseStart_3904026 : Nat := 118140960795 + 3904026 * 2 ^ 59
def prefixEnd_3904026 : Nat := 4983230072969 + 3 ^ 40 * 3904026 * 2
def baseEnd_3904026 : Nat := 222737980627760857113413

theorem tailTrace_3904026 : CollatzResearch.WordTrace tailWord_3904026 prefixEnd_3904026 222737980627760857113413 := by
  unfold tailWord_3904026
  simp only [CollatzResearch.WordTrace]
  refine ⟨35597881538597007850716983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94927684102925354268578621 35597881538597007850716983)
  ·
    refine ⟨53396822307895511776075475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35597881538597007850716983 53396822307895511776075475)
    ·
      refine ⟨80095233461843267664113213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53396822307895511776075475 80095233461843267664113213)
      ·
        refine ⟨30035712548191225374042455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80095233461843267664113213 30035712548191225374042455)
        ·
          refine ⟨45053568822286838061063683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30035712548191225374042455 45053568822286838061063683)
          ·
            refine ⟨67580353233430257091595525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45053568822286838061063683 67580353233430257091595525)
            ·
              refine ⟨12671316231268173204674161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67580353233430257091595525 12671316231268173204674161)
              ·
                refine ⟨9503487173451129903505621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12671316231268173204674161 9503487173451129903505621)
                ·
                  refine ⟨222737980627760857113413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9503487173451129903505621 222737980627760857113413)
                  ·
                    rfl

theorem cell23_3904026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 7].length) (baseStart_3904026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904026 prefixEnd_3904026 := by exact prefixLift 3904026
  have htrace : WordTrace (prefixWord ++ tailWord_3904026) baseStart_3904026 baseEnd_3904026 := by
    simpa [prefixWord, tailWord_3904026, baseEnd_3904026] using wordTrace_append hprefix tailTrace_3904026
  have hstable : (prefixWord ++ tailWord_3904026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904026).length < 2 ^ (prefixWord ++ tailWord_3904026).sum := by decide
  have hdescent : baseEnd_3904026 < baseStart_3904026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904063 : List Nat := [1, 1, 2, 2, 3, 2, 2, 1, 2, 5, 2]
def baseStart_3904063 : Nat := 118140960795 + 3904063 * 2 ^ 59
def prefixEnd_3904063 : Nat := 4983230072969 + 3 ^ 40 * 3904063 * 2
def baseEnd_3904063 : Nat := 2004660824434064069258047

theorem tailTrace_3904063 : CollatzResearch.WordTrace tailWord_3904063 prefixEnd_3904063 2004660824434064069258047 := by
  unfold tailWord_3904063
  simp only [CollatzResearch.WordTrace]
  refine ⟨142392875655253986721964843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94928583770169324481309895 142392875655253986721964843)
  ·
    refine ⟨213589313482880980082947265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142392875655253986721964843 213589313482880980082947265)
    ·
      refine ⟨160191985112160735062210449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213589313482880980082947265 160191985112160735062210449)
      ·
        refine ⟨120143988834120551296657837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160191985112160735062210449 120143988834120551296657837)
        ·
          refine ⟨45053995812795206736246689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120143988834120551296657837 45053995812795206736246689)
          ·
            refine ⟨33790496859596405052185017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45053995812795206736246689 33790496859596405052185017)
            ·
              refine ⟨25342872644697303789138763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33790496859596405052185017 25342872644697303789138763)
              ·
                refine ⟨38014308967045955683708145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25342872644697303789138763 38014308967045955683708145)
                ·
                  refine ⟨28510731725284466762781109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38014308967045955683708145 28510731725284466762781109)
                  ·
                    refine ⟨2672881099245418759010729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28510731725284466762781109 2672881099245418759010729)
                    ·
                      refine ⟨2004660824434064069258047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2672881099245418759010729 2004660824434064069258047)
                      ·
                        rfl

theorem cell23_3904063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 5, 2].length) (baseStart_3904063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904063 prefixEnd_3904063 := by exact prefixLift 3904063
  have htrace : WordTrace (prefixWord ++ tailWord_3904063) baseStart_3904063 baseEnd_3904063 := by
    simpa [prefixWord, tailWord_3904063, baseEnd_3904063] using wordTrace_append hprefix tailTrace_3904063
  have hstable : (prefixWord ++ tailWord_3904063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904063).length < 2 ^ (prefixWord ++ tailWord_3904063).sum := by decide
  have hdescent : baseEnd_3904063 < baseStart_3904063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904110 : List Nat := [4, 1, 2, 2, 2, 1, 2, 2, 2, 1, 4]
def baseStart_3904110 : Nat := 118140960795 + 3904110 * 2 ^ 59
def prefixEnd_3904110 : Nat := 4983230072969 + 3 ^ 40 * 3904110 * 2
def baseEnd_3904110 : Nat := 2004684958024825385370331

theorem tailTrace_3904110 : CollatzResearch.WordTrace tailWord_3904110 prefixEnd_3904110 2004684958024825385370331 := by
  unfold tailWord_3904110
  simp only [CollatzResearch.WordTrace]
  refine ⟨17799323735760464218615723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94929726590722475832617189 17799323735760464218615723)
  ·
    refine ⟨26698985603640696327923585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17799323735760464218615723 26698985603640696327923585)
    ·
      refine ⟨20024239202730522245942689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26698985603640696327923585 20024239202730522245942689)
      ·
        refine ⟨15018179402047891684457017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20024239202730522245942689 15018179402047891684457017)
        ·
          refine ⟨11263634551535918763342763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15018179402047891684457017 11263634551535918763342763)
          ·
            refine ⟨16895451827303878145014145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11263634551535918763342763 16895451827303878145014145)
            ·
              refine ⟨12671588870477908608760609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16895451827303878145014145 12671588870477908608760609)
              ·
                refine ⟨9503691652858431456570457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12671588870477908608760609 9503691652858431456570457)
                ·
                  refine ⟨7127768739643823592427843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9503691652858431456570457 7127768739643823592427843)
                  ·
                    refine ⟨10691653109465735388641765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7127768739643823592427843 10691653109465735388641765)
                    ·
                      refine ⟨2004684958024825385370331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10691653109465735388641765 2004684958024825385370331)
                      ·
                        rfl

theorem cell23_3904110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_3904110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904110 prefixEnd_3904110 := by exact prefixLift 3904110
  have htrace : WordTrace (prefixWord ++ tailWord_3904110) baseStart_3904110 baseEnd_3904110 := by
    simpa [prefixWord, tailWord_3904110, baseEnd_3904110] using wordTrace_append hprefix tailTrace_3904110
  have hstable : (prefixWord ++ tailWord_3904110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904110).length < 2 ^ (prefixWord ++ tailWord_3904110).sum := by decide
  have hdescent : baseEnd_3904110 < baseStart_3904110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904120 : List Nat := [2, 1, 2, 1, 1, 1, 2, 8, 1, 4]
def baseStart_3904120 : Nat := 118140960795 + 3904120 * 2 ^ 59
def prefixEnd_3904120 : Nat := 4983230072969 + 3 ^ 40 * 3904120 * 2
def baseEnd_3904120 : Nat := 668230030943790115415095

theorem tailTrace_3904120 : CollatzResearch.WordTrace tailWord_3904120 prefixEnd_3904120 668230030943790115415095 := by
  unfold tailWord_3904120
  simp only [CollatzResearch.WordTrace]
  refine ⟨71197477308023742728394907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94929969744031656971193209 71197477308023742728394907)
  ·
    refine ⟨106796215962035614092592361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71197477308023742728394907 106796215962035614092592361)
    ·
      refine ⟨80097161971526710569444271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106796215962035614092592361 80097161971526710569444271)
      ·
        refine ⟨120145742957290065854166407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80097161971526710569444271 120145742957290065854166407)
        ·
          refine ⟨180218614435935098781249611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120145742957290065854166407 180218614435935098781249611)
          ·
            refine ⟨270327921653902648171874417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180218614435935098781249611 270327921653902648171874417)
            ·
              refine ⟨202745941240426986128905813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270327921653902648171874417 202745941240426986128905813)
              ·
                refine ⟨2375928998911253743698115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 202745941240426986128905813 2375928998911253743698115)
                ·
                  refine ⟨3563893498366880615547173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2375928998911253743698115 3563893498366880615547173)
                  ·
                    refine ⟨668230030943790115415095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3563893498366880615547173 668230030943790115415095)
                    ·
                      rfl

theorem cell23_3904120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 8, 1, 4].length) (baseStart_3904120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904120 prefixEnd_3904120 := by exact prefixLift 3904120
  have htrace : WordTrace (prefixWord ++ tailWord_3904120) baseStart_3904120 baseEnd_3904120 := by
    simpa [prefixWord, tailWord_3904120, baseEnd_3904120] using wordTrace_append hprefix tailTrace_3904120
  have hstable : (prefixWord ++ tailWord_3904120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904120).length < 2 ^ (prefixWord ++ tailWord_3904120).sum := by decide
  have hdescent : baseEnd_3904120 < baseStart_3904120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904133 : List Nat := [1, 3, 1, 1, 4, 2, 2, 3, 6]
def baseStart_3904133 : Nat := 118140960795 + 3904133 * 2 ^ 59
def prefixEnd_3904133 : Nat := 4983230072969 + 3 ^ 40 * 3904133 * 2
def baseEnd_3904133 : Nat := 222744085342208755042525

theorem tailTrace_3904133 : CollatzResearch.WordTrace tailWord_3904133 prefixEnd_3904133 222744085342208755042525 := by
  unfold tailWord_3904133
  simp only [CollatzResearch.WordTrace]
  refine ⟨142395428765000388677013053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94930285843333592451342035 142395428765000388677013053)
  ·
    refine ⟨53398285786875145753879895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142395428765000388677013053 53398285786875145753879895)
    ·
      refine ⟨80097428680312718630819843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53398285786875145753879895 80097428680312718630819843)
      ·
        refine ⟨120146143020469077946229765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80097428680312718630819843 120146143020469077946229765)
        ·
          refine ⟨22527401816337952114918081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120146143020469077946229765 22527401816337952114918081)
          ·
            refine ⟨16895551362253464086188561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22527401816337952114918081 16895551362253464086188561)
            ·
              refine ⟨12671663521690098064641421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16895551362253464086188561 12671663521690098064641421)
              ·
                refine ⟨4751873820633786774240533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12671663521690098064641421 4751873820633786774240533)
                ·
                  refine ⟨222744085342208755042525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4751873820633786774240533 222744085342208755042525)
                  ·
                    rfl

theorem cell23_3904133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 6].length) (baseStart_3904133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904133 prefixEnd_3904133 := by exact prefixLift 3904133
  have htrace : WordTrace (prefixWord ++ tailWord_3904133) baseStart_3904133 baseEnd_3904133 := by
    simpa [prefixWord, tailWord_3904133, baseEnd_3904133] using wordTrace_append hprefix tailTrace_3904133
  have hstable : (prefixWord ++ tailWord_3904133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904133).length < 2 ^ (prefixWord ++ tailWord_3904133).sum := by decide
  have hdescent : baseEnd_3904133 < baseStart_3904133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904200 : List Nat := [2, 1, 3, 1, 2, 3, 1, 4, 1, 1, 4]
def baseStart_3904200 : Nat := 118140960795 + 3904200 * 2 ^ 59
def prefixEnd_3904200 : Nat := 4983230072969 + 3 ^ 40 * 3904200 * 2
def baseEnd_3904200 : Nat := 2004731171283730033244917

theorem tailTrace_3904200 : CollatzResearch.WordTrace tailWord_3904200 prefixEnd_3904200 2004731171283730033244917 := by
  unfold tailWord_3904200
  simp only [CollatzResearch.WordTrace]
  refine ⟨71198936227878829559851027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94931914970505106079801369 71198936227878829559851027)
  ·
    refine ⟨106798404341818244339776541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71198936227878829559851027 106798404341818244339776541)
    ·
      refine ⟨40049401628181841627416203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106798404341818244339776541 40049401628181841627416203)
      ·
        refine ⟨60074102442272762441124305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40049401628181841627416203 60074102442272762441124305)
        ·
          refine ⟨45055576831704571830843229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60074102442272762441124305 45055576831704571830843229)
          ·
            refine ⟨16895841311889214436566211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45055576831704571830843229 16895841311889214436566211)
            ·
              refine ⟨25343761967833821654849317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16895841311889214436566211 25343761967833821654849317)
              ·
                refine ⟨4751955368968841560284247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25343761967833821654849317 4751955368968841560284247)
                ·
                  refine ⟨7127933053453262340426371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4751955368968841560284247 7127933053453262340426371)
                  ·
                    refine ⟨10691899580179893510639557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7127933053453262340426371 10691899580179893510639557)
                    ·
                      refine ⟨2004731171283730033244917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10691899580179893510639557 2004731171283730033244917)
                      ·
                        rfl

theorem cell23_3904200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 1, 1, 4].length) (baseStart_3904200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904200 prefixEnd_3904200 := by exact prefixLift 3904200
  have htrace : WordTrace (prefixWord ++ tailWord_3904200) baseStart_3904200 baseEnd_3904200 := by
    simpa [prefixWord, tailWord_3904200, baseEnd_3904200] using wordTrace_append hprefix tailTrace_3904200
  have hstable : (prefixWord ++ tailWord_3904200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904200).length < 2 ^ (prefixWord ++ tailWord_3904200).sum := by decide
  have hdescent : baseEnd_3904200 < baseStart_3904200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904223 : List Nat := [1, 1, 2, 3, 2, 5, 9]
def baseStart_3904223 : Nat := 118140960795 + 3904223 * 2 ^ 59
def prefixEnd_3904223 : Nat := 4983230072969 + 3 ^ 40 * 3904223 * 2
def baseEnd_3904223 : Nat := 24749913349861523990831

theorem tailTrace_3904223 : CollatzResearch.WordTrace tailWord_3904223 prefixEnd_3904223 24749913349861523990831 := by
  unfold tailWord_3904223
  simp only [CollatzResearch.WordTrace]
  refine ⟨142398711334674334047789323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94932474223116222698526215 142398711334674334047789323)
  ·
    refine ⟨213598067002011501071683985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142398711334674334047789323 213598067002011501071683985)
    ·
      refine ⟨160198550251508625803762989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213598067002011501071683985 160198550251508625803762989)
      ·
        refine ⟨60074456344315734676411121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160198550251508625803762989 60074456344315734676411121)
        ·
          refine ⟨45055842258236801007308341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60074456344315734676411121 45055842258236801007308341)
          ·
            refine ⟨4223985211709700094435157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45055842258236801007308341 4223985211709700094435157)
            ·
              refine ⟨24749913349861523990831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4223985211709700094435157 24749913349861523990831)
              ·
                rfl

theorem cell23_3904223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 9].length) (baseStart_3904223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904223 prefixEnd_3904223 := by exact prefixLift 3904223
  have htrace : WordTrace (prefixWord ++ tailWord_3904223) baseStart_3904223 baseEnd_3904223 := by
    simpa [prefixWord, tailWord_3904223, baseEnd_3904223] using wordTrace_append hprefix tailTrace_3904223
  have hstable : (prefixWord ++ tailWord_3904223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904223).length < 2 ^ (prefixWord ++ tailWord_3904223).sum := by decide
  have hdescent : baseEnd_3904223 < baseStart_3904223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904254 : List Nat := [4, 2, 2, 1, 2, 1, 3, 2, 1, 2, 3]
def baseStart_3904254 : Nat := 118140960795 + 3904254 * 2 ^ 59
def prefixEnd_3904254 : Nat := 4983230072969 + 3 ^ 40 * 3904254 * 2
def baseEnd_3904254 : Nat := 2004758899239072821969669

theorem tailTrace_3904254 : CollatzResearch.WordTrace tailWord_3904254 prefixEnd_3904254 2004758899239072821969669 := by
  unfold tailWord_3904254
  simp only [CollatzResearch.WordTrace]
  refine ⟨17799980249695253292770977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94933227998374684228111877 17799980249695253292770977)
  ·
    refine ⟨13349985187271439969578233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17799980249695253292770977 13349985187271439969578233)
    ·
      refine ⟨10012488890453579977183675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13349985187271439969578233 10012488890453579977183675)
      ·
        refine ⟨15018733335680369965775513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10012488890453579977183675 15018733335680369965775513)
        ·
          refine ⟨11264050001760277474331635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15018733335680369965775513 11264050001760277474331635)
          ·
            refine ⟨16896075002640416211497453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11264050001760277474331635 16896075002640416211497453)
            ·
              refine ⟨6336028125990156079311545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16896075002640416211497453 6336028125990156079311545)
              ·
                refine ⟨4752021094492617059483659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6336028125990156079311545 4752021094492617059483659)
                ·
                  refine ⟨7128031641738925589225489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4752021094492617059483659 7128031641738925589225489)
                  ·
                    refine ⟨5346023731304194191919117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7128031641738925589225489 5346023731304194191919117)
                    ·
                      refine ⟨2004758899239072821969669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5346023731304194191919117 2004758899239072821969669)
                      ·
                        rfl

theorem cell23_3904254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_3904254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904254 prefixEnd_3904254 := by exact prefixLift 3904254
  have htrace : WordTrace (prefixWord ++ tailWord_3904254) baseStart_3904254 baseEnd_3904254 := by
    simpa [prefixWord, tailWord_3904254, baseEnd_3904254] using wordTrace_append hprefix tailTrace_3904254
  have hstable : (prefixWord ++ tailWord_3904254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904254).length < 2 ^ (prefixWord ++ tailWord_3904254).sum := by decide
  have hdescent : baseEnd_3904254 < baseStart_3904254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904284 : List Nat := [2, 2, 3, 1, 1, 4, 2, 2, 2, 1, 3]
def baseStart_3904284 : Nat := 118140960795 + 3904284 * 2 ^ 59
def prefixEnd_3904284 : Nat := 4983230072969 + 3 ^ 40 * 3904284 * 2
def baseEnd_3904284 : Nat := 2004774303658707704594531

theorem tailTrace_3904284 : CollatzResearch.WordTrace tailWord_3904284 prefixEnd_3904284 2004774303658707704594531 := by
  unfold tailWord_3904284
  simp only [CollatzResearch.WordTrace]
  refine ⟨71200468093726670732879953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94933957458302227643839937 71200468093726670732879953)
  ·
    refine ⟨53400351070295003049659965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71200468093726670732879953 53400351070295003049659965)
    ·
      refine ⟨20025131651360626143622487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53400351070295003049659965 20025131651360626143622487)
      ·
        refine ⟨30037697477040939215433731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20025131651360626143622487 30037697477040939215433731)
        ·
          refine ⟨45056546215561408823150597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30037697477040939215433731 45056546215561408823150597)
          ·
            refine ⟨8448102415417764154340737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45056546215561408823150597 8448102415417764154340737)
            ·
              refine ⟨6336076811563323115755553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8448102415417764154340737 6336076811563323115755553)
              ·
                refine ⟨4752057608672492336816665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6336076811563323115755553 4752057608672492336816665)
                ·
                  refine ⟨3564043206504369252612499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4752057608672492336816665 3564043206504369252612499)
                  ·
                    refine ⟨5346064809756553878918749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3564043206504369252612499 5346064809756553878918749)
                    ·
                      refine ⟨2004774303658707704594531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5346064809756553878918749 2004774303658707704594531)
                      ·
                        rfl

theorem cell23_3904284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_3904284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904284 prefixEnd_3904284 := by exact prefixLift 3904284
  have htrace : WordTrace (prefixWord ++ tailWord_3904284) baseStart_3904284 baseEnd_3904284 := by
    simpa [prefixWord, tailWord_3904284, baseEnd_3904284] using wordTrace_append hprefix tailTrace_3904284
  have hstable : (prefixWord ++ tailWord_3904284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904284).length < 2 ^ (prefixWord ++ tailWord_3904284).sum := by decide
  have hdescent : baseEnd_3904284 < baseStart_3904284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904290 : List Nat := [3, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4]
def baseStart_3904290 : Nat := 118140960795 + 3904290 * 2 ^ 59
def prefixEnd_3904290 : Nat := 4983230072969 + 3 ^ 40 * 3904290 * 2
def baseEnd_3904290 : Nat := 2004777384542634681119503

theorem tailTrace_3904290 : CollatzResearch.WordTrace tailWord_3904290 prefixEnd_3904290 2004777384542634681119503 := by
  unfold tailWord_3904290
  simp only [CollatzResearch.WordTrace]
  refine ⟨35600288756357901122619581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94934103350287736326985549 35600288756357901122619581)
  ·
    refine ⟨13350108283634212920982343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35600288756357901122619581 13350108283634212920982343)
    ·
      refine ⟨20025162425451319381473515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13350108283634212920982343 20025162425451319381473515)
      ·
        refine ⟨30037743638176979072210273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20025162425451319381473515 30037743638176979072210273)
        ·
          refine ⟨22528307728632734304157705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30037743638176979072210273 22528307728632734304157705)
          ·
            refine ⟨16896230796474550728118279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22528307728632734304157705 16896230796474550728118279)
            ·
              refine ⟨25344346194711826092177419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16896230796474550728118279 25344346194711826092177419)
              ·
                refine ⟨38016519292067739138266129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25344346194711826092177419 38016519292067739138266129)
                ·
                  refine ⟨28512389469050804353699597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38016519292067739138266129 28512389469050804353699597)
                  ·
                    refine ⟨10692146050894051632637349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28512389469050804353699597 10692146050894051632637349)
                    ·
                      refine ⟨2004777384542634681119503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10692146050894051632637349 2004777384542634681119503)
                      ·
                        rfl

theorem cell23_3904290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_3904290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904290 prefixEnd_3904290 := by exact prefixLift 3904290
  have htrace : WordTrace (prefixWord ++ tailWord_3904290) baseStart_3904290 baseEnd_3904290 := by
    simpa [prefixWord, tailWord_3904290, baseEnd_3904290] using wordTrace_append hprefix tailTrace_3904290
  have hstable : (prefixWord ++ tailWord_3904290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904290).length < 2 ^ (prefixWord ++ tailWord_3904290).sum := by decide
  have hdescent : baseEnd_3904290 < baseStart_3904290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904301 : List Nat := [1, 5, 3, 2, 1, 1, 2, 1, 1, 3, 3]
def baseStart_3904301 : Nat := 118140960795 + 3904301 * 2 ^ 59
def prefixEnd_3904301 : Nat := 4983230072969 + 3 ^ 40 * 3904301 * 2
def baseEnd_3904301 : Nat := 2004783032829834138081953

theorem tailTrace_3904301 : CollatzResearch.WordTrace tailWord_3904301 prefixEnd_3904301 2004783032829834138081953 := by
  unfold tailWord_3904301
  simp only [CollatzResearch.WordTrace]
  refine ⟨142401556228391753369128757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94934370818927835579419171 142401556228391753369128757)
  ·
    refine ⟨13350145896411726878355821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142401556228391753369128757 13350145896411726878355821)
    ·
      refine ⟨5006304711154397579383433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13350145896411726878355821 5006304711154397579383433)
      ·
        refine ⟨3754728533365798184537575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5006304711154397579383433 3754728533365798184537575)
        ·
          refine ⟨5632092800048697276806363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3754728533365798184537575 5632092800048697276806363)
          ·
            refine ⟨8448139200073045915209545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5632092800048697276806363 8448139200073045915209545)
            ·
              refine ⟨6336104400054784436407159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8448139200073045915209545 6336104400054784436407159)
              ·
                refine ⟨9504156600082176654610739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6336104400054784436407159 9504156600082176654610739)
                ·
                  refine ⟨14256234900123264981916109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9504156600082176654610739 14256234900123264981916109)
                  ·
                    refine ⟨5346088087546224368218541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14256234900123264981916109 5346088087546224368218541)
                    ·
                      refine ⟨2004783032829834138081953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5346088087546224368218541 2004783032829834138081953)
                      ·
                        rfl

theorem cell23_3904301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_3904301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904301 prefixEnd_3904301 := by exact prefixLift 3904301
  have htrace : WordTrace (prefixWord ++ tailWord_3904301) baseStart_3904301 baseEnd_3904301 := by
    simpa [prefixWord, tailWord_3904301, baseEnd_3904301] using wordTrace_append hprefix tailTrace_3904301
  have hstable : (prefixWord ++ tailWord_3904301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904301).length < 2 ^ (prefixWord ++ tailWord_3904301).sum := by decide
  have hdescent : baseEnd_3904301 < baseStart_3904301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904307 : List Nat := [1, 1, 1, 2, 6, 1, 1, 3, 1, 4, 2]
def baseStart_3904307 : Nat := 118140960795 + 3904307 * 2 ^ 59
def prefixEnd_3904307 : Nat := 4983230072969 + 3 ^ 40 * 3904307 * 2
def baseEnd_3904307 : Nat := 2004786113713761114606925

theorem tailTrace_3904307 : CollatzResearch.WordTrace tailWord_3904307 prefixEnd_3904307 2004786113713761114606925 := by
  unfold tailWord_3904307
  simp only [CollatzResearch.WordTrace]
  refine ⟨142401775066370016393847175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94934516710913344262564783 142401775066370016393847175)
  ·
    refine ⟨213602662599555024590770763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142401775066370016393847175 213602662599555024590770763)
    ·
      refine ⟨320403993899332536886156145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213602662599555024590770763 320403993899332536886156145)
      ·
        refine ⟨240302995424499402664617109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320403993899332536886156145 240302995424499402664617109)
        ·
          refine ⟨11264202910523409499903927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 240302995424499402664617109 11264202910523409499903927)
          ·
            refine ⟨16896304365785114249855891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11264202910523409499903927 16896304365785114249855891)
            ·
              refine ⟨25344456548677671374783837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16896304365785114249855891 25344456548677671374783837)
              ·
                refine ⟨9504171205754126765543939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25344456548677671374783837 9504171205754126765543939)
                ·
                  refine ⟨14256256808631190148315909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9504171205754126765543939 14256256808631190148315909)
                  ·
                    refine ⟨2673048151618348152809233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14256256808631190148315909 2673048151618348152809233)
                    ·
                      refine ⟨2004786113713761114606925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2673048151618348152809233 2004786113713761114606925)
                      ·
                        rfl

theorem cell23_3904307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 4, 2].length) (baseStart_3904307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904307 prefixEnd_3904307 := by exact prefixLift 3904307
  have htrace : WordTrace (prefixWord ++ tailWord_3904307) baseStart_3904307 baseEnd_3904307 := by
    simpa [prefixWord, tailWord_3904307, baseEnd_3904307] using wordTrace_append hprefix tailTrace_3904307
  have hstable : (prefixWord ++ tailWord_3904307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904307).length < 2 ^ (prefixWord ++ tailWord_3904307).sum := by decide
  have hdescent : baseEnd_3904307 < baseStart_3904307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904360 : List Nat := [2, 1, 4, 2, 1, 2, 1, 2, 1, 7]
def baseStart_3904360 : Nat := 118140960795 + 3904360 * 2 ^ 59
def prefixEnd_3904360 : Nat := 4983230072969 + 3 ^ 40 * 3904360 * 2
def baseEnd_3904360 : Nat := 668271109396149802414727

theorem tailTrace_3904360 : CollatzResearch.WordTrace tailWord_3904360 prefixEnd_3904360 668271109396149802414727 := by
  unfold tailWord_3904360
  simp only [CollatzResearch.WordTrace]
  refine ⟨71201854067589003222763267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94935805423452004297017689 71201854067589003222763267)
  ·
    refine ⟨106802781101383504834144901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71201854067589003222763267 106802781101383504834144901)
    ·
      refine ⟨20025521456509407156402169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106802781101383504834144901 20025521456509407156402169)
      ·
        refine ⟨15019141092382055367301627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20025521456509407156402169 15019141092382055367301627)
        ·
          refine ⟨22528711638573083050952441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15019141092382055367301627 22528711638573083050952441)
          ·
            refine ⟨16896533728929812288214331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22528711638573083050952441 16896533728929812288214331)
            ·
              refine ⟨25344800593394718432321497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16896533728929812288214331 25344800593394718432321497)
              ·
                refine ⟨19008600445046038824241123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25344800593394718432321497 19008600445046038824241123)
                ·
                  refine ⟨28512900667569058236361685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19008600445046038824241123 28512900667569058236361685)
                  ·
                    refine ⟨668271109396149802414727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28512900667569058236361685 668271109396149802414727)
                    ·
                      rfl

theorem cell23_3904360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_3904360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904360 prefixEnd_3904360 := by exact prefixLift 3904360
  have htrace : WordTrace (prefixWord ++ tailWord_3904360) baseStart_3904360 baseEnd_3904360 := by
    simpa [prefixWord, tailWord_3904360, baseEnd_3904360] using wordTrace_append hprefix tailTrace_3904360
  have hstable : (prefixWord ++ tailWord_3904360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904360).length < 2 ^ (prefixWord ++ tailWord_3904360).sum := by decide
  have hdescent : baseEnd_3904360 < baseStart_3904360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904380 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 6, 1, 4]
def baseStart_3904380 : Nat := 118140960795 + 3904380 * 2 ^ 59
def prefixEnd_3904380 : Nat := 4983230072969 + 3 ^ 40 * 3904380 * 2
def baseEnd_3904380 : Nat := 2004823597801539328994089

theorem tailTrace_3904380 : CollatzResearch.WordTrace tailWord_3904380 prefixEnd_3904380 2004823597801539328994089 := by
  unfold tailWord_3904380
  simp only [CollatzResearch.WordTrace]
  refine ⟨71202218797552774930627297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94936291730070366574169729 71202218797552774930627297)
  ·
    refine ⟨53401664098164581197970473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71202218797552774930627297 53401664098164581197970473)
    ·
      refine ⟨40051248073623435898477855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53401664098164581197970473 40051248073623435898477855)
      ·
        refine ⟨60076872110435153847716783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40051248073623435898477855 60076872110435153847716783)
        ·
          refine ⟨90115308165652730771575175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60076872110435153847716783 90115308165652730771575175)
          ·
            refine ⟨135172962248479096157362763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90115308165652730771575175 135172962248479096157362763)
            ·
              refine ⟨202759443372718644236044145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135172962248479096157362763 202759443372718644236044145)
              ·
                refine ⟨152069582529538983177033109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202759443372718644236044145 152069582529538983177033109)
                ·
                  refine ⟨7128261681072139836423427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 152069582529538983177033109 7128261681072139836423427)
                  ·
                    refine ⟨10692392521608209754635141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7128261681072139836423427 10692392521608209754635141)
                    ·
                      refine ⟨2004823597801539328994089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10692392521608209754635141 2004823597801539328994089)
                      ·
                        rfl

theorem cell23_3904380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_3904380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904380 prefixEnd_3904380 := by exact prefixLift 3904380
  have htrace : WordTrace (prefixWord ++ tailWord_3904380) baseStart_3904380 baseEnd_3904380 := by
    simpa [prefixWord, tailWord_3904380, baseEnd_3904380] using wordTrace_append hprefix tailTrace_3904380
  have hstable : (prefixWord ++ tailWord_3904380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904380).length < 2 ^ (prefixWord ++ tailWord_3904380).sum := by decide
  have hdescent : baseEnd_3904380 < baseStart_3904380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904447 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 7, 1, 3]
def baseStart_3904447 : Nat := 118140960795 + 3904447 * 2 ^ 59
def prefixEnd_3904447 : Nat := 4983230072969 + 3 ^ 40 * 3904447 * 2
def baseEnd_3904447 : Nat := 2004858001005390566856281

theorem tailTrace_3904447 : CollatzResearch.WordTrace tailWord_3904447 prefixEnd_3904447 2004858001005390566856281 := by
  unfold tailWord_3904447
  simp only [CollatzResearch.WordTrace]
  refine ⟨142406881285862820303943595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94937920857241880202629063 142406881285862820303943595)
  ·
    refine ⟨213610321928794230455915393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142406881285862820303943595 213610321928794230455915393)
    ·
      refine ⟨160207741446595672841936545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213610321928794230455915393 160207741446595672841936545)
      ·
        refine ⟨120155806084946754631452409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160207741446595672841936545 120155806084946754631452409)
        ·
          refine ⟨90116854563710065973589307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120155806084946754631452409 90116854563710065973589307)
          ·
            refine ⟨135175281845565098960383961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90116854563710065973589307 135175281845565098960383961)
            ·
              refine ⟨101381461384173824220287971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135175281845565098960383961 101381461384173824220287971)
              ·
                refine ⟨152072192076260736330431957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101381461384173824220287971 152072192076260736330431957)
                ·
                  refine ⟨3564192001787361007744499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 152072192076260736330431957 3564192001787361007744499)
                  ·
                    refine ⟨5346288002681041511616749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3564192001787361007744499 5346288002681041511616749)
                    ·
                      refine ⟨2004858001005390566856281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5346288002681041511616749 2004858001005390566856281)
                      ·
                        rfl

theorem cell23_3904447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 7, 1, 3].length) (baseStart_3904447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904447 prefixEnd_3904447 := by exact prefixLift 3904447
  have htrace : WordTrace (prefixWord ++ tailWord_3904447) baseStart_3904447 baseEnd_3904447 := by
    simpa [prefixWord, tailWord_3904447, baseEnd_3904447] using wordTrace_append hprefix tailTrace_3904447
  have hstable : (prefixWord ++ tailWord_3904447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904447).length < 2 ^ (prefixWord ++ tailWord_3904447).sum := by decide
  have hdescent : baseEnd_3904447 < baseStart_3904447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904497 : List Nat := [1, 2, 2, 2, 4, 1, 2, 2, 1, 6]
def baseStart_3904497 : Nat := 118140960795 + 3904497 * 2 ^ 59
def prefixEnd_3904497 : Nat := 4983230072969 + 3 ^ 40 * 3904497 * 2
def baseEnd_3904497 : Nat := 668294558346038457077017

theorem tailTrace_3904497 : CollatzResearch.WordTrace tailWord_3904497 prefixEnd_3904497 668294558346038457077017 := by
  unfold tailWord_3904497
  simp only [CollatzResearch.WordTrace]
  refine ⟨142408704935681678843263745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94939136623787785895509163 142408704935681678843263745)
  ·
    refine ⟨106806528701761259132447809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142408704935681678843263745 106806528701761259132447809)
    ·
      refine ⟨80104896526320944349335857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106806528701761259132447809 80104896526320944349335857)
      ·
        refine ⟨60078672394740708262001893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80104896526320944349335857 60078672394740708262001893)
        ·
          refine ⟨11264751074013882799125355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60078672394740708262001893 11264751074013882799125355)
          ·
            refine ⟨16897126611020824198688033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11264751074013882799125355 16897126611020824198688033)
            ·
              refine ⟨12672844958265618149016025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16897126611020824198688033 12672844958265618149016025)
              ·
                refine ⟨9504633718699213611762019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12672844958265618149016025 9504633718699213611762019)
                ·
                  refine ⟨14256950578048820417643029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9504633718699213611762019 14256950578048820417643029)
                  ·
                    refine ⟨668294558346038457077017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14256950578048820417643029 668294558346038457077017)
                    ·
                      rfl

theorem cell23_3904497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 6].length) (baseStart_3904497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904497 prefixEnd_3904497 := by exact prefixLift 3904497
  have htrace : WordTrace (prefixWord ++ tailWord_3904497) baseStart_3904497 baseEnd_3904497 := by
    simpa [prefixWord, tailWord_3904497, baseEnd_3904497] using wordTrace_append hprefix tailTrace_3904497
  have hstable : (prefixWord ++ tailWord_3904497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904497).length < 2 ^ (prefixWord ++ tailWord_3904497).sum := by decide
  have hdescent : baseEnd_3904497 < baseStart_3904497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904504 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 7, 2, 2]
def baseStart_3904504 : Nat := 118140960795 + 3904504 * 2 ^ 59
def prefixEnd_3904504 : Nat := 4983230072969 + 3 ^ 40 * 3904504 * 2
def baseEnd_3904504 : Nat := 2004887269402696843843519

theorem tailTrace_3904504 : CollatzResearch.WordTrace tailWord_3904504 prefixEnd_3904504 2004887269402696843843519 := by
  unfold tailWord_3904504
  simp only [CollatzResearch.WordTrace]
  refine ⟨71204480123328159519384283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94939306831104212692512377 71204480123328159519384283)
  ·
    refine ⟨106806720184992239279076425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71204480123328159519384283 106806720184992239279076425)
    ·
      refine ⟨80105040138744179459307319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106806720184992239279076425 80105040138744179459307319)
      ·
        refine ⟨120157560208116269188960979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80105040138744179459307319 120157560208116269188960979)
        ·
          refine ⟨180236340312174403783441469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120157560208116269188960979 180236340312174403783441469)
          ·
            refine ⟨67588627617065401418790551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180236340312174403783441469 67588627617065401418790551)
            ·
              refine ⟨101382941425598102128185827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67588627617065401418790551 101382941425598102128185827)
              ·
                refine ⟨152074412138397153192278741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101382941425598102128185827 152074412138397153192278741)
                ·
                  refine ⟨3564244034493683277944033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 152074412138397153192278741 3564244034493683277944033)
                  ·
                    refine ⟨2673183025870262458458025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3564244034493683277944033 2673183025870262458458025)
                    ·
                      refine ⟨2004887269402696843843519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2673183025870262458458025 2004887269402696843843519)
                      ·
                        rfl

theorem cell23_3904504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 7, 2, 2].length) (baseStart_3904504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904504 prefixEnd_3904504 := by exact prefixLift 3904504
  have htrace : WordTrace (prefixWord ++ tailWord_3904504) baseStart_3904504 baseEnd_3904504 := by
    simpa [prefixWord, tailWord_3904504, baseEnd_3904504] using wordTrace_append hprefix tailTrace_3904504
  have hstable : (prefixWord ++ tailWord_3904504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904504).length < 2 ^ (prefixWord ++ tailWord_3904504).sum := by decide
  have hdescent : baseEnd_3904504 < baseStart_3904504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904544 : List Nat := [2, 1, 1, 7, 1, 1, 1, 9]
def baseStart_3904544 : Nat := 118140960795 + 3904544 * 2 ^ 59
def prefixEnd_3904544 : Nat := 4983230072969 + 3 ^ 40 * 3904544 * 2
def baseEnd_3904544 : Nat := 74255844764032469901605

theorem tailTrace_3904544 : CollatzResearch.WordTrace tailWord_3904544 prefixEnd_3904544 74255844764032469901605 := by
  unfold tailWord_3904544
  simp only [CollatzResearch.WordTrace]
  refine ⟨71205209583255702935112343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94940279444340937246816457 71205209583255702935112343)
  ·
    refine ⟨106807814374883554402668515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71205209583255702935112343 106807814374883554402668515)
    ·
      refine ⟨160211721562325331604002773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106807814374883554402668515 160211721562325331604002773)
      ·
        refine ⟨3754962224116999959468815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 160211721562325331604002773 3754962224116999959468815)
        ·
          refine ⟨5632443336175499939203223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3754962224116999959468815 5632443336175499939203223)
          ·
            refine ⟨8448665004263249908804835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5632443336175499939203223 8448665004263249908804835)
            ·
              refine ⟨12672997506394874863207253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8448665004263249908804835 12672997506394874863207253)
              ·
                refine ⟨74255844764032469901605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12672997506394874863207253 74255844764032469901605)
                ·
                  rfl

theorem cell23_3904544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 9].length) (baseStart_3904544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904544 prefixEnd_3904544 := by exact prefixLift 3904544
  have htrace : WordTrace (prefixWord ++ tailWord_3904544) baseStart_3904544 baseEnd_3904544 := by
    simpa [prefixWord, tailWord_3904544, baseEnd_3904544] using wordTrace_append hprefix tailTrace_3904544
  have hstable : (prefixWord ++ tailWord_3904544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904544).length < 2 ^ (prefixWord ++ tailWord_3904544).sum := by decide
  have hdescent : baseEnd_3904544 < baseStart_3904544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904597 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 4, 1, 5]
def baseStart_3904597 : Nat := 118140960795 + 3904597 * 2 ^ 59
def prefixEnd_3904597 : Nat := 4983230072969 + 3 ^ 40 * 3904597 * 2
def baseEnd_3904597 : Nat := 2004935023103564979980591

theorem tailTrace_3904597 : CollatzResearch.WordTrace tailWord_3904597 prefixEnd_3904597 2004935023103564979980591 := by
  unfold tailWord_3904597
  simp only [CollatzResearch.WordTrace]
  refine ⟨142412352235319395921904045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94941568156879597281269363 142412352235319395921904045)
  ·
    refine ⟨53404632088244773470714017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142412352235319395921904045 53404632088244773470714017)
    ·
      refine ⟨40053474066183580103035513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53404632088244773470714017 40053474066183580103035513)
      ·
        refine ⟨30040105549637685077276635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40053474066183580103035513 30040105549637685077276635)
        ·
          refine ⟨45060158324456527615914953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30040105549637685077276635 45060158324456527615914953)
          ·
            refine ⟨33795118743342395711936215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45060158324456527615914953 33795118743342395711936215)
            ·
              refine ⟨50692678115013593567904323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33795118743342395711936215 50692678115013593567904323)
              ·
                refine ⟨76039017172520390351856485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50692678115013593567904323 76039017172520390351856485)
                ·
                  refine ⟨14257315719847573190973091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76039017172520390351856485 14257315719847573190973091)
                  ·
                    refine ⟨21385973579771359786459637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14257315719847573190973091 21385973579771359786459637)
                    ·
                      refine ⟨2004935023103564979980591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21385973579771359786459637 2004935023103564979980591)
                      ·
                        rfl

theorem cell23_3904597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_3904597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904597 prefixEnd_3904597 := by exact prefixLift 3904597
  have htrace : WordTrace (prefixWord ++ tailWord_3904597) baseStart_3904597 baseEnd_3904597 := by
    simpa [prefixWord, tailWord_3904597, baseEnd_3904597] using wordTrace_append hprefix tailTrace_3904597
  have hstable : (prefixWord ++ tailWord_3904597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904597).length < 2 ^ (prefixWord ++ tailWord_3904597).sum := by decide
  have hdescent : baseEnd_3904597 < baseStart_3904597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904627 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 5, 5, 3]
def baseStart_3904627 : Nat := 118140960795 + 3904627 * 2 ^ 59
def prefixEnd_3904627 : Nat := 4983230072969 + 3 ^ 40 * 3904627 * 2
def baseEnd_3904627 : Nat := 2004950427523199862605453

theorem tailTrace_3904627 : CollatzResearch.WordTrace tailWord_3904627 prefixEnd_3904627 2004950427523199862605453 := by
  unfold tailWord_3904627
  simp only [CollatzResearch.WordTrace]
  refine ⟨142413446425210711045496135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94942297616807140696997423 142413446425210711045496135)
  ·
    refine ⟨213620169637816066568244203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142413446425210711045496135 213620169637816066568244203)
    ·
      refine ⟨320430254456724099852366305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213620169637816066568244203 320430254456724099852366305)
      ·
        refine ⟨240322690842543074889274729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320430254456724099852366305 240322690842543074889274729)
        ·
          refine ⟨180242018131907306166956047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240322690842543074889274729 180242018131907306166956047)
          ·
            refine ⟨270363027197860959250434071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180242018131907306166956047 270363027197860959250434071)
            ·
              refine ⟨405544540796791438875651107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270363027197860959250434071 405544540796791438875651107)
              ·
                refine ⟨608316811195187158313476661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 405544540796791438875651107 608316811195187158313476661)
                ·
                  refine ⟨57029701049548796091888437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 608316811195187158313476661 57029701049548796091888437)
                  ·
                    refine ⟨5346534473395199633614541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57029701049548796091888437 5346534473395199633614541)
                    ·
                      refine ⟨2004950427523199862605453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5346534473395199633614541 2004950427523199862605453)
                      ·
                        rfl

theorem cell23_3904627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 5, 3].length) (baseStart_3904627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904627 prefixEnd_3904627 := by exact prefixLift 3904627
  have htrace : WordTrace (prefixWord ++ tailWord_3904627) baseStart_3904627 baseEnd_3904627 := by
    simpa [prefixWord, tailWord_3904627, baseEnd_3904627] using wordTrace_append hprefix tailTrace_3904627
  have hstable : (prefixWord ++ tailWord_3904627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904627).length < 2 ^ (prefixWord ++ tailWord_3904627).sum := by decide
  have hdescent : baseEnd_3904627 < baseStart_3904627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904644 : List Nat := [2, 3, 2, 1, 2, 2, 1, 1, 1, 5, 3]
def baseStart_3904644 : Nat := 118140960795 + 3904644 * 2 ^ 59
def prefixEnd_3904644 : Nat := 4983230072969 + 3 ^ 40 * 3904644 * 2
def baseEnd_3904644 : Nat := 2004959156694326296092875

theorem tailTrace_3904644 : CollatzResearch.WordTrace tailWord_3904644 prefixEnd_3904644 2004959156694326296092875 := by
  unfold tailWord_3904644
  simp only [CollatzResearch.WordTrace]
  refine ⟨71207033233074561474432493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94942710977432748632576657 71207033233074561474432493)
  ·
    refine ⟨26702637462402960552912185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71207033233074561474432493 26702637462402960552912185)
    ·
      refine ⟨20026978096802220414684139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26702637462402960552912185 20026978096802220414684139)
      ·
        refine ⟨30040467145203330622026209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20026978096802220414684139 30040467145203330622026209)
        ·
          refine ⟨22530350358902497966519657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30040467145203330622026209 22530350358902497966519657)
          ·
            refine ⟨16897762769176873474889743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22530350358902497966519657 16897762769176873474889743)
            ·
              refine ⟨25346644153765310212334615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16897762769176873474889743 25346644153765310212334615)
              ·
                refine ⟨38019966230647965318501923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25346644153765310212334615 38019966230647965318501923)
                ·
                  refine ⟨57029949345971947977752885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38019966230647965318501923 57029949345971947977752885)
                  ·
                    refine ⟨5346557751184870122914333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57029949345971947977752885 5346557751184870122914333)
                    ·
                      refine ⟨2004959156694326296092875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5346557751184870122914333 2004959156694326296092875)
                      ·
                        rfl

theorem cell23_3904644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_3904644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904644 prefixEnd_3904644 := by exact prefixLift 3904644
  have htrace : WordTrace (prefixWord ++ tailWord_3904644) baseStart_3904644 baseEnd_3904644 := by
    simpa [prefixWord, tailWord_3904644, baseEnd_3904644] using wordTrace_append hprefix tailTrace_3904644
  have hstable : (prefixWord ++ tailWord_3904644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904644).length < 2 ^ (prefixWord ++ tailWord_3904644).sum := by decide
  have hdescent : baseEnd_3904644 < baseStart_3904644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904647 : List Nat := [1, 1, 4, 2, 1, 1, 1, 4, 1, 7]
def baseStart_3904647 : Nat := 118140960795 + 3904647 * 2 ^ 59
def prefixEnd_3904647 : Nat := 4983230072969 + 3 ^ 40 * 3904647 * 2
def baseEnd_3904647 : Nat := 668320232378763261451787

theorem tailTrace_3904647 : CollatzResearch.WordTrace tailWord_3904647 prefixEnd_3904647 668320232378763261451787 := by
  unfold tailWord_3904647
  simp only [CollatzResearch.WordTrace]
  refine ⟨142414175885138254461224195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94942783923425502974149463 142414175885138254461224195)
  ·
    refine ⟨213621263827707381691836293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142414175885138254461224195 213621263827707381691836293)
    ·
      refine ⟨40053986967695134067219305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213621263827707381691836293 40053986967695134067219305)
      ·
        refine ⟨30040490225771350550414479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40053986967695134067219305 30040490225771350550414479)
        ·
          refine ⟨45060735338657025825621719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30040490225771350550414479 45060735338657025825621719)
          ·
            refine ⟨67591103007985538738432579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45060735338657025825621719 67591103007985538738432579)
            ·
              refine ⟨101386654511978308107648869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67591103007985538738432579 101386654511978308107648869)
              ·
                refine ⟨19009997720995932770184163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101386654511978308107648869 19009997720995932770184163)
                ·
                  refine ⟨28514996581493899155276245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19009997720995932770184163 28514996581493899155276245)
                  ·
                    refine ⟨668320232378763261451787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28514996581493899155276245 668320232378763261451787)
                    ·
                      rfl

theorem cell23_3904647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_3904647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904647 prefixEnd_3904647 := by exact prefixLift 3904647
  have htrace : WordTrace (prefixWord ++ tailWord_3904647) baseStart_3904647 baseEnd_3904647 := by
    simpa [prefixWord, tailWord_3904647, baseEnd_3904647] using wordTrace_append hprefix tailTrace_3904647
  have hstable : (prefixWord ++ tailWord_3904647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904647).length < 2 ^ (prefixWord ++ tailWord_3904647).sum := by decide
  have hdescent : baseEnd_3904647 < baseStart_3904647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904664 : List Nat := [2, 1, 2, 4, 2, 2, 1, 1, 1, 7]
def baseStart_3904664 : Nat := 118140960795 + 3904664 * 2 ^ 59
def prefixEnd_3904664 : Nat := 4983230072969 + 3 ^ 40 * 3904664 * 2
def baseEnd_3904664 : Nat := 668323142102472072614261

theorem tailTrace_3904664 : CollatzResearch.WordTrace tailWord_3904664 prefixEnd_3904664 668323142102472072614261 := by
  unfold tailWord_3904664
  simp only [CollatzResearch.WordTrace]
  refine ⟨71207397963038333182296523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94943197284051110909728697 71207397963038333182296523)
  ·
    refine ⟨106811096944557499773444785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71207397963038333182296523 106811096944557499773444785)
    ·
      refine ⟨80108322708418124830083589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106811096944557499773444785 80108322708418124830083589)
      ·
        refine ⟨15020310507828398405640673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80108322708418124830083589 15020310507828398405640673)
        ·
          refine ⟨11265232880871298804230505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15020310507828398405640673 11265232880871298804230505)
          ·
            refine ⟨8448924660653474103172879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11265232880871298804230505 8448924660653474103172879)
            ·
              refine ⟨12673386990980211154759319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8448924660653474103172879 12673386990980211154759319)
              ·
                refine ⟨19010080486470316732138979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12673386990980211154759319 19010080486470316732138979)
                ·
                  refine ⟨28515120729705475098208469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19010080486470316732138979 28515120729705475098208469)
                  ·
                    refine ⟨668323142102472072614261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28515120729705475098208469 668323142102472072614261)
                    ·
                      rfl

theorem cell23_3904664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 1, 7].length) (baseStart_3904664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904664 prefixEnd_3904664 := by exact prefixLift 3904664
  have htrace : WordTrace (prefixWord ++ tailWord_3904664) baseStart_3904664 baseEnd_3904664 := by
    simpa [prefixWord, tailWord_3904664, baseEnd_3904664] using wordTrace_append hprefix tailTrace_3904664
  have hstable : (prefixWord ++ tailWord_3904664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904664).length < 2 ^ (prefixWord ++ tailWord_3904664).sum := by decide
  have hdescent : baseEnd_3904664 < baseStart_3904664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904687 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 5]
def baseStart_3904687 : Nat := 118140960795 + 3904687 * 2 ^ 59
def prefixEnd_3904687 : Nat := 4983230072969 + 3 ^ 40 * 3904687 * 2
def baseEnd_3904687 : Nat := 2004981236362469627855177

theorem tailTrace_3904687 : CollatzResearch.WordTrace tailWord_3904687 prefixEnd_3904687 2004981236362469627855177 := by
  unfold tailWord_3904687
  simp only [CollatzResearch.WordTrace]
  refine ⟨142415634804993341292680315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94943756536662227528453543 142415634804993341292680315)
  ·
    refine ⟨213623452207490011939020473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142415634804993341292680315 213623452207490011939020473)
    ·
      refine ⟨160217589155617508954265355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213623452207490011939020473 160217589155617508954265355)
      ·
        refine ⟨240326383733426263431398033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160217589155617508954265355 240326383733426263431398033)
        ·
          refine ⟨180244787800069697573548525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240326383733426263431398033 180244787800069697573548525)
          ·
            refine ⟨67591795425026136590080697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180244787800069697573548525 67591795425026136590080697)
            ·
              refine ⟨50693846568769602442560523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67591795425026136590080697 50693846568769602442560523)
              ·
                refine ⟨76040769853154403663840785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50693846568769602442560523 76040769853154403663840785)
                ·
                  refine ⟨57030577389865802747880589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76040769853154403663840785 57030577389865802747880589)
                  ·
                    refine ⟨21386466521199676030455221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57030577389865802747880589 21386466521199676030455221)
                    ·
                      refine ⟨2004981236362469627855177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21386466521199676030455221 2004981236362469627855177)
                      ·
                        rfl

theorem cell23_3904687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 5].length) (baseStart_3904687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904687 prefixEnd_3904687 := by exact prefixLift 3904687
  have htrace : WordTrace (prefixWord ++ tailWord_3904687) baseStart_3904687 baseEnd_3904687 := by
    simpa [prefixWord, tailWord_3904687, baseEnd_3904687] using wordTrace_append hprefix tailTrace_3904687
  have hstable : (prefixWord ++ tailWord_3904687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904687).length < 2 ^ (prefixWord ++ tailWord_3904687).sum := by decide
  have hdescent : baseEnd_3904687 < baseStart_3904687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904701 : List Nat := [1, 4, 1, 2, 1, 1, 4, 1, 2, 4, 2]
def baseStart_3904701 : Nat := 118140960795 + 3904701 * 2 ^ 59
def prefixEnd_3904701 : Nat := 4983230072969 + 3 ^ 40 * 3904701 * 2
def baseEnd_3904701 : Nat := 2004988425091632573080113

theorem tailTrace_3904701 : CollatzResearch.WordTrace tailWord_3904701 prefixEnd_3904701 2004988425091632573080113 := by
  unfold tailWord_3904701
  simp only [CollatzResearch.WordTrace]
  refine ⟨142416145426942621683689957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94944096951295081122459971 142416145426942621683689957)
  ·
    refine ⟨26703027267551741565691867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142416145426942621683689957 26703027267551741565691867)
    ·
      refine ⟨40054540901327612348537801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26703027267551741565691867 40054540901327612348537801)
      ·
        refine ⟨30040905675995709261403351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40054540901327612348537801 30040905675995709261403351)
        ·
          refine ⟨45061358513993563892105027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30040905675995709261403351 45061358513993563892105027)
          ·
            refine ⟨67592037770990345838157541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45061358513993563892105027 67592037770990345838157541)
            ·
              refine ⟨12673507082060689844654539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67592037770990345838157541 12673507082060689844654539)
              ·
                refine ⟨19010260623091034766981809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12673507082060689844654539 19010260623091034766981809)
                ·
                  refine ⟨14257695467318276075236357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19010260623091034766981809 14257695467318276075236357)
                  ·
                    refine ⟨2673317900122176764106817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14257695467318276075236357 2673317900122176764106817)
                    ·
                      refine ⟨2004988425091632573080113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2673317900122176764106817 2004988425091632573080113)
                      ·
                        rfl

theorem cell23_3904701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_3904701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904701 prefixEnd_3904701 := by exact prefixLift 3904701
  have htrace : WordTrace (prefixWord ++ tailWord_3904701) baseStart_3904701 baseEnd_3904701 := by
    simpa [prefixWord, tailWord_3904701, baseEnd_3904701] using wordTrace_append hprefix tailTrace_3904701
  have hstable : (prefixWord ++ tailWord_3904701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904701).length < 2 ^ (prefixWord ++ tailWord_3904701).sum := by decide
  have hdescent : baseEnd_3904701 < baseStart_3904701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904761 : List Nat := [1, 2, 1, 3, 1, 1, 3, 2, 4, 3, 2]
def baseStart_3904761 : Nat := 118140960795 + 3904761 * 2 ^ 59
def prefixEnd_3904761 : Nat := 4983230072969 + 3 ^ 40 * 3904761 * 2
def baseEnd_3904761 : Nat := 2005019233930902338329837

theorem tailTrace_3904761 : CollatzResearch.WordTrace tailWord_3904761 prefixEnd_3904761 2005019233930902338329837 := by
  unfold tailWord_3904761
  simp only [CollatzResearch.WordTrace]
  refine ⟨142418333806725251930874137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94945555871150167953916091 142418333806725251930874137)
  ·
    refine ⟨106813750355043938948155603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142418333806725251930874137 106813750355043938948155603)
    ·
      refine ⟨160220625532565908422233405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106813750355043938948155603 160220625532565908422233405)
      ·
        refine ⟨60082734574712215658337527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160220625532565908422233405 60082734574712215658337527)
        ·
          refine ⟨90124101862068323487506291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60082734574712215658337527 90124101862068323487506291)
          ·
            refine ⟨135186152793102485231259437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90124101862068323487506291 135186152793102485231259437)
            ·
              refine ⟨50694807297413431961722289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135186152793102485231259437 50694807297413431961722289)
              ·
                refine ⟨38021105473060073971291717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50694807297413431961722289 38021105473060073971291717)
                ·
                  refine ⟨7128957276198763869617197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38021105473060073971291717 7128957276198763869617197)
                  ·
                    refine ⟨2673358978574536451106449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7128957276198763869617197 2673358978574536451106449)
                    ·
                      refine ⟨2005019233930902338329837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2673358978574536451106449 2005019233930902338329837)
                      ·
                        rfl

theorem cell23_3904761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 3, 2].length) (baseStart_3904761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904761 prefixEnd_3904761 := by exact prefixLift 3904761
  have htrace : WordTrace (prefixWord ++ tailWord_3904761) baseStart_3904761 baseEnd_3904761 := by
    simpa [prefixWord, tailWord_3904761, baseEnd_3904761] using wordTrace_append hprefix tailTrace_3904761
  have hstable : (prefixWord ++ tailWord_3904761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904761).length < 2 ^ (prefixWord ++ tailWord_3904761).sum := by decide
  have hdescent : baseEnd_3904761 < baseStart_3904761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904771 : List Nat := [1, 1, 1, 3, 2, 4, 3, 2, 1, 5]
def baseStart_3904771 : Nat := 118140960795 + 3904771 * 2 ^ 59
def prefixEnd_3904771 : Nat := 4983230072969 + 3 ^ 40 * 3904771 * 2
def baseEnd_3904771 : Nat := 668341456245815766401597

theorem tailTrace_3904771 : CollatzResearch.WordTrace tailWord_3904771 prefixEnd_3904771 668341456245815766401597 := by
  unfold tailWord_3904771
  simp only [CollatzResearch.WordTrace]
  refine ⟨142418698536689023638738167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94945799024459349092492111 142418698536689023638738167)
  ·
    refine ⟨213628047805033535458107251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142418698536689023638738167 213628047805033535458107251)
    ·
      refine ⟨320442071707550303187160877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213628047805033535458107251 320442071707550303187160877)
      ·
        refine ⟨120165776890331363695185329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320442071707550303187160877 120165776890331363695185329)
        ·
          refine ⟨90124332667748522771388997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120165776890331363695185329 90124332667748522771388997)
          ·
            refine ⟨16898312375202848019635437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90124332667748522771388997 16898312375202848019635437)
            ·
              refine ⟨6336867140701068007363289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16898312375202848019635437 6336867140701068007363289)
              ·
                refine ⟨4752650355525801005522467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6336867140701068007363289 4752650355525801005522467)
                ·
                  refine ⟨7128975533288701508283701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4752650355525801005522467 7128975533288701508283701)
                  ·
                    refine ⟨668341456245815766401597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7128975533288701508283701 668341456245815766401597)
                    ·
                      rfl

theorem cell23_3904771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 5].length) (baseStart_3904771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904771 prefixEnd_3904771 := by exact prefixLift 3904771
  have htrace : WordTrace (prefixWord ++ tailWord_3904771) baseStart_3904771 baseEnd_3904771 := by
    simpa [prefixWord, tailWord_3904771, baseEnd_3904771] using wordTrace_append hprefix tailTrace_3904771
  have hstable : (prefixWord ++ tailWord_3904771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904771).length < 2 ^ (prefixWord ++ tailWord_3904771).sum := by decide
  have hdescent : baseEnd_3904771 < baseStart_3904771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904802 : List Nat := [3, 3, 1, 1, 4, 1, 1, 4, 1, 1, 3]
def baseStart_3904802 : Nat := 118140960795 + 3904802 * 2 ^ 59
def prefixEnd_3904802 : Nat := 4983230072969 + 3 ^ 40 * 3904802 * 2
def baseEnd_3904802 : Nat := 2005040286637736677917149

theorem tailTrace_3904802 : CollatzResearch.WordTrace tailWord_3904802 prefixEnd_3904802 2005040286637736677917149 := by
  unfold tailWord_3904802
  simp only [CollatzResearch.WordTrace]
  refine ⟨35604957299894178983279165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94946552799717810622077773 35604957299894178983279165)
  ·
    refine ⟨13351858987460317118729687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35604957299894178983279165 13351858987460317118729687)
    ·
      refine ⟨20027788481190475678094531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13351858987460317118729687 20027788481190475678094531)
      ·
        refine ⟨30041682721785713517141797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20027788481190475678094531 30041682721785713517141797)
        ·
          refine ⟨5632815510334821284464087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30041682721785713517141797 5632815510334821284464087)
          ·
            refine ⟨8449223265502231926696131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5632815510334821284464087 8449223265502231926696131)
            ·
              refine ⟨12673834898253347890044197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8449223265502231926696131 12673834898253347890044197)
              ·
                refine ⟨2376344043422502729383287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12673834898253347890044197 2376344043422502729383287)
                ·
                  refine ⟨3564516065133754094074931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2376344043422502729383287 3564516065133754094074931)
                  ·
                    refine ⟨5346774097700631141112397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3564516065133754094074931 5346774097700631141112397)
                    ·
                      refine ⟨2005040286637736677917149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5346774097700631141112397 2005040286637736677917149)
                      ·
                        rfl

theorem cell23_3904802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_3904802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904802 prefixEnd_3904802 := by exact prefixLift 3904802
  have htrace : WordTrace (prefixWord ++ tailWord_3904802) baseStart_3904802 baseEnd_3904802 := by
    simpa [prefixWord, tailWord_3904802, baseEnd_3904802] using wordTrace_append hprefix tailTrace_3904802
  have hstable : (prefixWord ++ tailWord_3904802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904802).length < 2 ^ (prefixWord ++ tailWord_3904802).sum := by decide
  have hdescent : baseEnd_3904802 < baseStart_3904802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904818 : List Nat := [3, 2, 1, 1, 4, 1, 2, 3, 2, 4]
def baseStart_3904818 : Nat := 118140960795 + 3904818 * 2 ^ 59
def prefixEnd_3904818 : Nat := 4983230072969 + 3 ^ 40 * 3904818 * 2
def baseEnd_3904818 : Nat := 668349500776069538439025

theorem tailTrace_3904818 : CollatzResearch.WordTrace tailWord_3904818 prefixEnd_3904818 668349500776069538439025 := by
  unfold tailWord_3904818
  simp only [CollatzResearch.WordTrace]
  refine ⟨35605103191879687666424777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94946941845012500443799405 35605103191879687666424777)
  ·
    refine ⟨26703827393909765749818583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35605103191879687666424777 26703827393909765749818583)
    ·
      refine ⟨40055741090864648624727875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26703827393909765749818583 40055741090864648624727875)
      ·
        refine ⟨60083611636296972937091813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40055741090864648624727875 60083611636296972937091813)
        ·
          refine ⟨11265677181805682425704715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60083611636296972937091813 11265677181805682425704715)
          ·
            refine ⟨16898515772708523638557073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11265677181805682425704715 16898515772708523638557073)
            ·
              refine ⟨12673886829531392728917805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16898515772708523638557073 12673886829531392728917805)
              ·
                refine ⟨4752707561074272273344177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12673886829531392728917805 4752707561074272273344177)
                ·
                  refine ⟨3564530670805704205008133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4752707561074272273344177 3564530670805704205008133)
                  ·
                    refine ⟨668349500776069538439025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3564530670805704205008133 668349500776069538439025)
                    ·
                      rfl

theorem cell23_3904818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_3904818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904818 prefixEnd_3904818 := by exact prefixLift 3904818
  have htrace : WordTrace (prefixWord ++ tailWord_3904818) baseStart_3904818 baseEnd_3904818 := by
    simpa [prefixWord, tailWord_3904818, baseEnd_3904818] using wordTrace_append hprefix tailTrace_3904818
  have hstable : (prefixWord ++ tailWord_3904818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904818).length < 2 ^ (prefixWord ++ tailWord_3904818).sum := by decide
  have hdescent : baseEnd_3904818 < baseStart_3904818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904821 : List Nat := [1, 3, 3, 1, 2, 2, 1, 3, 1, 2, 4]
def baseStart_3904821 : Nat := 118140960795 + 3904821 * 2 ^ 59
def prefixEnd_3904821 : Nat := 4983230072969 + 3 ^ 40 * 3904821 * 2
def baseEnd_3904821 : Nat := 2005050042770172103579561

theorem tailTrace_3904821 : CollatzResearch.WordTrace tailWord_3904821 prefixEnd_3904821 2005050042770172103579561 := by
  unfold tailWord_3904821
  simp only [CollatzResearch.WordTrace]
  refine ⟨142420522186507882178058317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94947014791005254785372211 142420522186507882178058317)
  ·
    refine ⟨53407695819940455816771869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142420522186507882178058317 53407695819940455816771869)
    ·
      refine ⟨20027885932477670931289451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53407695819940455816771869 20027885932477670931289451)
      ·
        refine ⟨30041828898716506396934177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20027885932477670931289451 30041828898716506396934177)
        ·
          refine ⟨22531371674037379797700633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30041828898716506396934177 22531371674037379797700633)
          ·
            refine ⟨16898528755528034848275475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22531371674037379797700633 16898528755528034848275475)
            ·
              refine ⟨25347793133292052272413213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16898528755528034848275475 25347793133292052272413213)
              ·
                refine ⟨9505422424984519602154955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25347793133292052272413213 9505422424984519602154955)
                ·
                  refine ⟨14258133637476779403232433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9505422424984519602154955 14258133637476779403232433)
                  ·
                    refine ⟨10693600228107584552424325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14258133637476779403232433 10693600228107584552424325)
                    ·
                      refine ⟨2005050042770172103579561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10693600228107584552424325 2005050042770172103579561)
                      ·
                        rfl

theorem cell23_3904821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_3904821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904821 prefixEnd_3904821 := by exact prefixLift 3904821
  have htrace : WordTrace (prefixWord ++ tailWord_3904821) baseStart_3904821 baseEnd_3904821 := by
    simpa [prefixWord, tailWord_3904821, baseEnd_3904821] using wordTrace_append hprefix tailTrace_3904821
  have hstable : (prefixWord ++ tailWord_3904821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904821).length < 2 ^ (prefixWord ++ tailWord_3904821).sum := by decide
  have hdescent : baseEnd_3904821 < baseStart_3904821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904829 : List Nat := [1, 4, 1, 5, 2, 1, 1, 1, 2, 3, 2]
def baseStart_3904829 : Nat := 118140960795 + 3904829 * 2 ^ 59
def prefixEnd_3904829 : Nat := 4983230072969 + 3 ^ 40 * 3904829 * 2
def baseEnd_3904829 : Nat := 2005054150615408072279525

theorem tailTrace_3904829 : CollatzResearch.WordTrace tailWord_3904829 prefixEnd_3904829 2005054150615408072279525 := by
  unfold tailWord_3904829
  simp only [CollatzResearch.WordTrace]
  refine ⟨142420813970478899544349541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94947209313652599696233027 142420813970478899544349541)
  ·
    refine ⟨26703902619464793664565539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142420813970478899544349541 26703902619464793664565539)
    ·
      refine ⟨40055853929197190496848309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26703902619464793664565539 40055853929197190496848309)
      ·
        refine ⟨3755236305862236609079529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40055853929197190496848309 3755236305862236609079529)
        ·
          refine ⟨2816427229396677456809647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3755236305862236609079529 2816427229396677456809647)
          ·
            refine ⟨4224640844095016185214471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2816427229396677456809647 4224640844095016185214471)
            ·
              refine ⟨6336961266142524277821707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4224640844095016185214471 6336961266142524277821707)
              ·
                refine ⟨9505441899213786416732561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6336961266142524277821707 9505441899213786416732561)
                ·
                  refine ⟨7129081424410339812549421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9505441899213786416732561 7129081424410339812549421)
                  ·
                    refine ⟨2673405534153877429706033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7129081424410339812549421 2673405534153877429706033)
                    ·
                      refine ⟨2005054150615408072279525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2673405534153877429706033 2005054150615408072279525)
                      ·
                        rfl

theorem cell23_3904829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_3904829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904829 prefixEnd_3904829 := by exact prefixLift 3904829
  have htrace : WordTrace (prefixWord ++ tailWord_3904829) baseStart_3904829 baseEnd_3904829 := by
    simpa [prefixWord, tailWord_3904829, baseEnd_3904829] using wordTrace_append hprefix tailTrace_3904829
  have hstable : (prefixWord ++ tailWord_3904829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904829).length < 2 ^ (prefixWord ++ tailWord_3904829).sum := by decide
  have hdescent : baseEnd_3904829 < baseStart_3904829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904831 : List Nat := [1, 1, 2, 2, 4, 3, 3, 7]
def baseStart_3904831 : Nat := 118140960795 + 3904831 * 2 ^ 59
def prefixEnd_3904831 : Nat := 4983230072969 + 3 ^ 40 * 3904831 * 2
def baseEnd_3904831 : Nat := 74261302873211743127945

theorem tailTrace_3904831 : CollatzResearch.WordTrace tailWord_3904831 prefixEnd_3904831 74261302873211743127945 := by
  unfold tailWord_3904831
  simp only [CollatzResearch.WordTrace]
  refine ⟨142420886916471653885922347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94947257944314435923948231 142420886916471653885922347)
  ·
    refine ⟨213631330374707480828883521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142420886916471653885922347 213631330374707480828883521)
    ·
      refine ⟨160223497781030610621662641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213631330374707480828883521 160223497781030610621662641)
      ·
        refine ⟨120167623335772957966246981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160223497781030610621662641 120167623335772957966246981)
        ·
          refine ⟨22531429375457429618671309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120167623335772957966246981 22531429375457429618671309)
          ·
            refine ⟨8449286015796536107001741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22531429375457429618671309 8449286015796536107001741)
            ·
              refine ⟨3168482255923701040125653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8449286015796536107001741 3168482255923701040125653)
              ·
                refine ⟨74261302873211743127945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3168482255923701040125653 74261302873211743127945)
                ·
                  rfl

theorem cell23_3904831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 7].length) (baseStart_3904831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904831 prefixEnd_3904831 := by exact prefixLift 3904831
  have htrace : WordTrace (prefixWord ++ tailWord_3904831) baseStart_3904831 baseEnd_3904831 := by
    simpa [prefixWord, tailWord_3904831, baseEnd_3904831] using wordTrace_append hprefix tailTrace_3904831
  have hstable : (prefixWord ++ tailWord_3904831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904831).length < 2 ^ (prefixWord ++ tailWord_3904831).sum := by decide
  have hdescent : baseEnd_3904831 < baseStart_3904831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904841 : List Nat := [1, 2, 1, 1, 2, 3, 4, 2, 1, 3, 3]
def baseStart_3904841 : Nat := 118140960795 + 3904841 * 2 ^ 59
def prefixEnd_3904841 : Nat := 4983230072969 + 3 ^ 40 * 3904841 * 2
def baseEnd_3904841 : Nat := 2005060312383262025329469

theorem tailTrace_3904841 : CollatzResearch.WordTrace tailWord_3904841 prefixEnd_3904841 2005060312383262025329469 := by
  unfold tailWord_3904841
  simp only [CollatzResearch.WordTrace]
  refine ⟨142421251646435425593786377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94947501097623617062524251 142421251646435425593786377)
  ·
    refine ⟨106815938734826569195339783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142421251646435425593786377 106815938734826569195339783)
    ·
      refine ⟨160223908102239853793009675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106815938734826569195339783 160223908102239853793009675)
      ·
        refine ⟨240335862153359780689514513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160223908102239853793009675 240335862153359780689514513)
        ·
          refine ⟨180251896615019835517135885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240335862153359780689514513 180251896615019835517135885)
          ·
            refine ⟨67594461230632438318925957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180251896615019835517135885 67594461230632438318925957)
            ·
              refine ⟨12673961480743582184798617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67594461230632438318925957 12673961480743582184798617)
              ·
                refine ⟨9505471110557686638598963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12673961480743582184798617 9505471110557686638598963)
                ·
                  refine ⟨14258206665836529957898445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9505471110557686638598963 14258206665836529957898445)
                  ·
                    refine ⟨5346827499688698734211917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14258206665836529957898445 5346827499688698734211917)
                    ·
                      refine ⟨2005060312383262025329469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5346827499688698734211917 2005060312383262025329469)
                      ·
                        rfl

theorem cell23_3904841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 3, 3].length) (baseStart_3904841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904841 prefixEnd_3904841 := by exact prefixLift 3904841
  have htrace : WordTrace (prefixWord ++ tailWord_3904841) baseStart_3904841 baseEnd_3904841 := by
    simpa [prefixWord, tailWord_3904841, baseEnd_3904841] using wordTrace_append hprefix tailTrace_3904841
  have hstable : (prefixWord ++ tailWord_3904841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904841).length < 2 ^ (prefixWord ++ tailWord_3904841).sum := by decide
  have hdescent : baseEnd_3904841 < baseStart_3904841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904921 : List Nat := [1, 2, 1, 2, 1, 5, 3, 1, 7]
def baseStart_3904921 : Nat := 118140960795 + 3904921 * 2 ^ 59
def prefixEnd_3904921 : Nat := 4983230072969 + 3 ^ 40 * 3904921 * 2
def baseEnd_3904921 : Nat := 222789043426180190258789

theorem tailTrace_3904921 : CollatzResearch.WordTrace tailWord_3904921 prefixEnd_3904921 222789043426180190258789 := by
  unfold tailWord_3904921
  simp only [CollatzResearch.WordTrace]
  refine ⟨142424169486145599256698617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94949446324097066171132411 142424169486145599256698617)
  ·
    refine ⟨106818127114609199442523963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142424169486145599256698617 106818127114609199442523963)
    ·
      refine ⟨160227190671913799163785945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106818127114609199442523963 160227190671913799163785945)
      ·
        refine ⟨120170393003935349372839459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160227190671913799163785945 120170393003935349372839459)
        ·
          refine ⟨180255589505903024059259189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120170393003935349372839459 180255589505903024059259189)
          ·
            refine ⟨16898961516178408505555549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 180255589505903024059259189 16898961516178408505555549)
            ·
              refine ⟨6337110568566903189583331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16898961516178408505555549 6337110568566903189583331)
              ·
                refine ⟨9505665852850354784374997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6337110568566903189583331 9505665852850354784374997)
                ·
                  refine ⟨222789043426180190258789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9505665852850354784374997 222789043426180190258789)
                  ·
                    rfl

theorem cell23_3904921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 7].length) (baseStart_3904921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904921 prefixEnd_3904921 := by exact prefixLift 3904921
  have htrace : WordTrace (prefixWord ++ tailWord_3904921) baseStart_3904921 baseEnd_3904921 := by
    simpa [prefixWord, tailWord_3904921, baseEnd_3904921] using wordTrace_append hprefix tailTrace_3904921
  have hstable : (prefixWord ++ tailWord_3904921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904921).length < 2 ^ (prefixWord ++ tailWord_3904921).sum := by decide
  have hdescent : baseEnd_3904921 < baseStart_3904921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904926 : List Nat := [4, 3, 1, 2, 2, 2, 2, 1, 2, 1, 3]
def baseStart_3904926 : Nat := 118140960795 + 3904926 * 2 ^ 59
def prefixEnd_3904926 : Nat := 4983230072969 + 3 ^ 40 * 3904926 * 2
def baseEnd_3904926 : Nat := 2005103958238894192766579

theorem tailTrace_3904926 : CollatzResearch.WordTrace tailWord_3904926 prefixEnd_3904926 2005103958238894192766579 := by
  unfold tailWord_3904926
  simp only [CollatzResearch.WordTrace]
  refine ⟨17803043981390935638828829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94949567900751656740420421 17803043981390935638828829)
  ·
    refine ⟨6676141493021600864560811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17803043981390935638828829 6676141493021600864560811)
    ·
      refine ⟨10014212239532401296841217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6676141493021600864560811 10014212239532401296841217)
      ·
        refine ⟨7510659179649300972630913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10014212239532401296841217 7510659179649300972630913)
        ·
          refine ⟨5632994384736975729473185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7510659179649300972630913 5632994384736975729473185)
          ·
            refine ⟨4224745788552731797104889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5632994384736975729473185 4224745788552731797104889)
            ·
              refine ⟨3168559341414548847828667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4224745788552731797104889 3168559341414548847828667)
              ·
                refine ⟨4752839012121823271743001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3168559341414548847828667 4752839012121823271743001)
                ·
                  refine ⟨3564629259091367453807251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4752839012121823271743001 3564629259091367453807251)
                  ·
                    refine ⟨5346943888637051180710877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3564629259091367453807251 5346943888637051180710877)
                    ·
                      refine ⟨2005103958238894192766579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5346943888637051180710877 2005103958238894192766579)
                      ·
                        rfl

theorem cell23_3904926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_3904926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904926 prefixEnd_3904926 := by exact prefixLift 3904926
  have htrace : WordTrace (prefixWord ++ tailWord_3904926) baseStart_3904926 baseEnd_3904926 := by
    simpa [prefixWord, tailWord_3904926, baseEnd_3904926] using wordTrace_append hprefix tailTrace_3904926
  have hstable : (prefixWord ++ tailWord_3904926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904926).length < 2 ^ (prefixWord ++ tailWord_3904926).sum := by decide
  have hdescent : baseEnd_3904926 < baseStart_3904926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904931 : List Nat := [1, 1, 1, 4, 1, 3, 2, 1, 1, 5, 3]
def baseStart_3904931 : Nat := 118140960795 + 3904931 * 2 ^ 59
def prefixEnd_3904931 : Nat := 4983230072969 + 3 ^ 40 * 3904931 * 2
def baseEnd_3904931 : Nat := 2005106525642166673204055

theorem tailTrace_3904931 : CollatzResearch.WordTrace tailWord_3904931 prefixEnd_3904931 2005106525642166673204055 := by
  unfold tailWord_3904931
  simp only [CollatzResearch.WordTrace]
  refine ⟨142424534216109370964562647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94949689477406247309708431 142424534216109370964562647)
  ·
    refine ⟨213636801324164056446843971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142424534216109370964562647 213636801324164056446843971)
    ·
      refine ⟨320455201986246084670265957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213636801324164056446843971 320455201986246084670265957)
      ·
        refine ⟨60085350372421140875674867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 320455201986246084670265957 60085350372421140875674867)
        ·
          refine ⟨90128025558631711313512301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60085350372421140875674867 90128025558631711313512301)
          ·
            refine ⟨33798009584486891742567113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90128025558631711313512301 33798009584486891742567113)
            ·
              refine ⟨25348507188365168806925335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33798009584486891742567113 25348507188365168806925335)
              ·
                refine ⟨38022760782547753210388003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25348507188365168806925335 38022760782547753210388003)
                ·
                  refine ⟨57034141173821629815582005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38022760782547753210388003 57034141173821629815582005)
                  ·
                    refine ⟨5346950735045777795210813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57034141173821629815582005 5346950735045777795210813)
                    ·
                      refine ⟨2005106525642166673204055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5346950735045777795210813 2005106525642166673204055)
                      ·
                        rfl

theorem cell23_3904931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_3904931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904931 prefixEnd_3904931 := by exact prefixLift 3904931
  have htrace : WordTrace (prefixWord ++ tailWord_3904931) baseStart_3904931 baseEnd_3904931 := by
    simpa [prefixWord, tailWord_3904931, baseEnd_3904931] using wordTrace_append hprefix tailTrace_3904931
  have hstable : (prefixWord ++ tailWord_3904931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904931).length < 2 ^ (prefixWord ++ tailWord_3904931).sum := by decide
  have hdescent : baseEnd_3904931 < baseStart_3904931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904936 : List Nat := [2, 1, 6, 1, 3, 1, 1, 2, 1, 3, 2]
def baseStart_3904936 : Nat := 118140960795 + 3904936 * 2 ^ 59
def prefixEnd_3904936 : Nat := 4983230072969 + 3 ^ 40 * 3904936 * 2
def baseEnd_3904936 : Nat := 2005109093045439153641533

theorem tailTrace_3904936 : CollatzResearch.WordTrace tailWord_3904936 prefixEnd_3904936 2005109093045439153641533 := by
  unfold tailWord_3904936
  simp only [CollatzResearch.WordTrace]
  refine ⟨71212358290545628409247331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94949811054060837878996441 71212358290545628409247331)
  ·
    refine ⟨106818537435818442613870997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71212358290545628409247331 106818537435818442613870997)
    ·
      refine ⟨5007118942303989497525203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 106818537435818442613870997 5007118942303989497525203)
      ·
        refine ⟨7510678413455984246287805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5007118942303989497525203 7510678413455984246287805)
        ·
          refine ⟨2816504405045994092357927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7510678413455984246287805 2816504405045994092357927)
          ·
            refine ⟨4224756607568991138536891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2816504405045994092357927 4224756607568991138536891)
            ·
              refine ⟨6337134911353486707805337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4224756607568991138536891 6337134911353486707805337)
              ·
                refine ⟨4752851183515115030854003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6337134911353486707805337 4752851183515115030854003)
                ·
                  refine ⟨7129276775272672546281005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4752851183515115030854003 7129276775272672546281005)
                  ·
                    refine ⟨2673478790727252204855377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7129276775272672546281005 2673478790727252204855377)
                    ·
                      refine ⟨2005109093045439153641533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2673478790727252204855377 2005109093045439153641533)
                      ·
                        rfl

theorem cell23_3904936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_3904936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904936 prefixEnd_3904936 := by exact prefixLift 3904936
  have htrace : WordTrace (prefixWord ++ tailWord_3904936) baseStart_3904936 baseEnd_3904936 := by
    simpa [prefixWord, tailWord_3904936, baseEnd_3904936] using wordTrace_append hprefix tailTrace_3904936
  have hstable : (prefixWord ++ tailWord_3904936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904936).length < 2 ^ (prefixWord ++ tailWord_3904936).sum := by decide
  have hdescent : baseEnd_3904936 < baseStart_3904936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3904972 : List Nat := [2, 2, 1, 4, 2, 3, 2, 2, 5]
def baseStart_3904972 : Nat := 118140960795 + 3904972 * 2 ^ 59
def prefixEnd_3904972 : Nat := 4983230072969 + 3 ^ 40 * 3904972 * 2
def baseEnd_3904972 : Nat := 222791953149889001421263

theorem tailTrace_3904972 : CollatzResearch.WordTrace tailWord_3904972 prefixEnd_3904972 222791953149889001421263 := by
  unfold tailWord_3904972
  simp only [CollatzResearch.WordTrace]
  refine ⟨71213014804480417483402585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94950686405973889977870113 71213014804480417483402585)
  ·
    refine ⟨53409761103360313112551939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71213014804480417483402585 53409761103360313112551939)
    ·
      refine ⟨80114641655040469668827909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53409761103360313112551939 80114641655040469668827909)
      ·
        refine ⟨15021495310320088062905233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80114641655040469668827909 15021495310320088062905233)
        ·
          refine ⟨11266121482740066047178925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15021495310320088062905233 11266121482740066047178925)
          ·
            refine ⟨4224795556027524767692097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11266121482740066047178925 4224795556027524767692097)
            ·
              refine ⟨3168596667020643575769073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4224795556027524767692097 3168596667020643575769073)
              ·
                refine ⟨2376447500265482681826805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3168596667020643575769073 2376447500265482681826805)
                ·
                  refine ⟨222791953149889001421263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2376447500265482681826805 222791953149889001421263)
                  ·
                    rfl

theorem cell23_3904972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 2, 5].length) (baseStart_3904972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3904972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3904972 prefixEnd_3904972 := by exact prefixLift 3904972
  have htrace : WordTrace (prefixWord ++ tailWord_3904972) baseStart_3904972 baseEnd_3904972 := by
    simpa [prefixWord, tailWord_3904972, baseEnd_3904972] using wordTrace_append hprefix tailTrace_3904972
  have hstable : (prefixWord ++ tailWord_3904972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3904972).length < 2 ^ (prefixWord ++ tailWord_3904972).sum := by decide
  have hdescent : baseEnd_3904972 < baseStart_3904972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3904972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905002 : List Nat := [3, 1, 3, 1, 5, 1, 1, 1, 2, 5]
def baseStart_3905002 : Nat := 118140960795 + 3905002 * 2 ^ 59
def prefixEnd_3905002 : Nat := 4983230072969 + 3 ^ 40 * 3905002 * 2
def baseEnd_3905002 : Nat := 668380994256211965138743

theorem tailTrace_3905002 : CollatzResearch.WordTrace tailWord_3905002 prefixEnd_3905002 668380994256211965138743 := by
  unfold tailWord_3905002
  simp only [CollatzResearch.WordTrace]
  refine ⟨35606780949713037522599315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94951415865901433393598173 35606780949713037522599315)
  ·
    refine ⟨53410171424569556283898973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35606780949713037522599315 53410171424569556283898973)
    ·
      refine ⟨20028814284213583606462115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53410171424569556283898973 20028814284213583606462115)
      ·
        refine ⟨30043221426320375409693173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20028814284213583606462115 30043221426320375409693173)
        ·
          refine ⟨2816552008717535194658735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30043221426320375409693173 2816552008717535194658735)
          ·
            refine ⟨4224828013076302791988103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2816552008717535194658735 4224828013076302791988103)
            ·
              refine ⟨6337242019614454187982155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4224828013076302791988103 6337242019614454187982155)
              ·
                refine ⟨9505863029421681281973233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6337242019614454187982155 9505863029421681281973233)
                ·
                  refine ⟨7129397272066260961479925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9505863029421681281973233 7129397272066260961479925)
                  ·
                    refine ⟨668380994256211965138743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7129397272066260961479925 668380994256211965138743)
                    ·
                      rfl

theorem cell23_3905002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_3905002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905002 prefixEnd_3905002 := by exact prefixLift 3905002
  have htrace : WordTrace (prefixWord ++ tailWord_3905002) baseStart_3905002 baseEnd_3905002 := by
    simpa [prefixWord, tailWord_3905002, baseEnd_3905002] using wordTrace_append hprefix tailTrace_3905002
  have hstable : (prefixWord ++ tailWord_3905002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905002).length < 2 ^ (prefixWord ++ tailWord_3905002).sum := by decide
  have hdescent : baseEnd_3905002 < baseStart_3905002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905005 : List Nat := [1, 5, 1, 3, 2, 1, 1, 1, 1, 3, 4]
def baseStart_3905005 : Nat := 118140960795 + 3905005 * 2 ^ 59
def prefixEnd_3905005 : Nat := 4983230072969 + 3 ^ 40 * 3905005 * 2
def baseEnd_3905005 : Nat := 2005144523210599383678715

theorem tailTrace_3905005 : CollatzResearch.WordTrace tailWord_3905005 prefixEnd_3905005 2005144523210599383678715 := by
  unfold tailWord_3905005
  simp only [CollatzResearch.WordTrace]
  refine ⟨142427233217841281602756469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94951488811894187735170979 142427233217841281602756469)
  ·
    refine ⟨13352553114172620150258419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142427233217841281602756469 13352553114172620150258419)
    ·
      refine ⟨20028829671258930225387629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13352553114172620150258419 20028829671258930225387629)
      ·
        refine ⟨7510811126722098834520361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20028829671258930225387629 7510811126722098834520361)
        ·
          refine ⟨5633108345041574125890271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7510811126722098834520361 5633108345041574125890271)
          ·
            refine ⟨8449662517562361188835407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5633108345041574125890271 8449662517562361188835407)
            ·
              refine ⟨12674493776343541783253111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8449662517562361188835407 12674493776343541783253111)
              ·
                refine ⟨19011740664515312674879667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12674493776343541783253111 19011740664515312674879667)
                ·
                  refine ⟨28517610996772969012319501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19011740664515312674879667 28517610996772969012319501)
                  ·
                    refine ⟨10694104123789863379619813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28517610996772969012319501 10694104123789863379619813)
                    ·
                      refine ⟨2005144523210599383678715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10694104123789863379619813 2005144523210599383678715)
                      ·
                        rfl

theorem cell23_3905005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_3905005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905005 prefixEnd_3905005 := by exact prefixLift 3905005
  have htrace : WordTrace (prefixWord ++ tailWord_3905005) baseStart_3905005 baseEnd_3905005 := by
    simpa [prefixWord, tailWord_3905005, baseEnd_3905005] using wordTrace_append hprefix tailTrace_3905005
  have hstable : (prefixWord ++ tailWord_3905005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905005).length < 2 ^ (prefixWord ++ tailWord_3905005).sum := by decide
  have hdescent : baseEnd_3905005 < baseStart_3905005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905008 : List Nat := [2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 3]
def baseStart_3905008 : Nat := 118140960795 + 3905008 * 2 ^ 59
def prefixEnd_3905008 : Nat := 4983230072969 + 3 ^ 40 * 3905008 * 2
def baseEnd_3905008 : Nat := 2005146063652562871941201

theorem tailTrace_3905008 : CollatzResearch.WordTrace tailWord_3905008 prefixEnd_3905008 2005146063652562871941201 := by
  unfold tailWord_3905008
  simp only [CollatzResearch.WordTrace]
  refine ⟨71213671318415206557557839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94951561757886942076743785 71213671318415206557557839)
  ·
    refine ⟨106820506977622809836336759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71213671318415206557557839 106820506977622809836336759)
    ·
      refine ⟨160230760466434214754505139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106820506977622809836336759 160230760466434214754505139)
      ·
        refine ⟨240346140699651322131757709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160230760466434214754505139 240346140699651322131757709)
        ·
          refine ⟨90129802762369245799409141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240346140699651322131757709 90129802762369245799409141)
          ·
            refine ⟨8449669008972116793694607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90129802762369245799409141 8449669008972116793694607)
            ·
              refine ⟨12674503513458175190541911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8449669008972116793694607 12674503513458175190541911)
              ·
                refine ⟨19011755270187262785812867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12674503513458175190541911 19011755270187262785812867)
                ·
                  refine ⟨28517632905280894178719301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19011755270187262785812867 28517632905280894178719301)
                  ·
                    refine ⟨5347056169740167658509869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28517632905280894178719301 5347056169740167658509869)
                    ·
                      refine ⟨2005146063652562871941201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5347056169740167658509869 2005146063652562871941201)
                      ·
                        rfl

theorem cell23_3905008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 3].length) (baseStart_3905008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905008 prefixEnd_3905008 := by exact prefixLift 3905008
  have htrace : WordTrace (prefixWord ++ tailWord_3905008) baseStart_3905008 baseEnd_3905008 := by
    simpa [prefixWord, tailWord_3905008, baseEnd_3905008] using wordTrace_append hprefix tailTrace_3905008
  have hstable : (prefixWord ++ tailWord_3905008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905008).length < 2 ^ (prefixWord ++ tailWord_3905008).sum := by decide
  have hdescent : baseEnd_3905008 < baseStart_3905008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905045 : List Nat := [1, 3, 2, 1, 3, 3, 3, 1, 6]
def baseStart_3905045 : Nat := 118140960795 + 3905045 * 2 ^ 59
def prefixEnd_3905045 : Nat := 4983230072969 + 3 ^ 40 * 3905045 * 2
def baseEnd_3905045 : Nat := 222796118048531025242059

theorem tailTrace_3905045 : CollatzResearch.WordTrace tailWord_3905045 prefixEnd_3905045 222796118048531025242059 := by
  unfold tailWord_3905045
  simp only [CollatzResearch.WordTrace]
  refine ⟨142428692137696368434212589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94952461425130912289475059 142428692137696368434212589)
  ·
    refine ⟨53410759551636138162829721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142428692137696368434212589 53410759551636138162829721)
    ·
      refine ⟨40058069663727103622122291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53410759551636138162829721 40058069663727103622122291)
      ·
        refine ⟨60087104495590655433183437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40058069663727103622122291 60087104495590655433183437)
        ·
          refine ⟨22532664185846495787443789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60087104495590655433183437 22532664185846495787443789)
          ·
            refine ⟨8449749069692435920291421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22532664185846495787443789 8449749069692435920291421)
            ·
              refine ⟨3168655901134663470109283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8449749069692435920291421 3168655901134663470109283)
              ·
                refine ⟨4752983851701995205163925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3168655901134663470109283 4752983851701995205163925)
                ·
                  refine ⟨222796118048531025242059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4752983851701995205163925 222796118048531025242059)
                  ·
                    rfl

theorem cell23_3905045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 6].length) (baseStart_3905045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905045 prefixEnd_3905045 := by exact prefixLift 3905045
  have htrace : WordTrace (prefixWord ++ tailWord_3905045) baseStart_3905045 baseEnd_3905045 := by
    simpa [prefixWord, tailWord_3905045, baseEnd_3905045] using wordTrace_append hprefix tailTrace_3905045
  have hstable : (prefixWord ++ tailWord_3905045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905045).length < 2 ^ (prefixWord ++ tailWord_3905045).sum := by decide
  have hdescent : baseEnd_3905045 < baseStart_3905045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905055 : List Nat := [1, 1, 2, 4, 1, 1, 4, 2, 3, 1, 3]
def baseStart_3905055 : Nat := 118140960795 + 3905055 * 2 ^ 59
def prefixEnd_3905055 : Nat := 4983230072969 + 3 ^ 40 * 3905055 * 2
def baseEnd_3905055 : Nat := 2005170197243324188053485

theorem tailTrace_3905055 : CollatzResearch.WordTrace tailWord_3905055 prefixEnd_3905055 2005170197243324188053485 := by
  unfold tailWord_3905055
  simp only [CollatzResearch.WordTrace]
  refine ⟨142429056867660140142076619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94952704578440093428051079 142429056867660140142076619)
  ·
    refine ⟨213643585301490210213114929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142429056867660140142076619 213643585301490210213114929)
    ·
      refine ⟨160232688976117657659836197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213643585301490210213114929 160232688976117657659836197)
      ·
        refine ⟨30043629183022060811219287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160232688976117657659836197 30043629183022060811219287)
        ·
          refine ⟨45065443774533091216828931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30043629183022060811219287 45065443774533091216828931)
          ·
            refine ⟨67598165661799636825243397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45065443774533091216828931 67598165661799636825243397)
            ·
              refine ⟨12674656061587431904733137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67598165661799636825243397 12674656061587431904733137)
              ·
                refine ⟨9505992046190573928549853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12674656061587431904733137 9505992046190573928549853)
                ·
                  refine ⟨3564747017321465223206195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9505992046190573928549853 3564747017321465223206195)
                  ·
                    refine ⟨5347120525982197834809293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3564747017321465223206195 5347120525982197834809293)
                    ·
                      refine ⟨2005170197243324188053485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5347120525982197834809293 2005170197243324188053485)
                      ·
                        rfl

theorem cell23_3905055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_3905055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905055 prefixEnd_3905055 := by exact prefixLift 3905055
  have htrace : WordTrace (prefixWord ++ tailWord_3905055) baseStart_3905055 baseEnd_3905055 := by
    simpa [prefixWord, tailWord_3905055, baseEnd_3905055] using wordTrace_append hprefix tailTrace_3905055
  have hstable : (prefixWord ++ tailWord_3905055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905055).length < 2 ^ (prefixWord ++ tailWord_3905055).sum := by decide
  have hdescent : baseEnd_3905055 < baseStart_3905055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905058 : List Nat := [3, 3, 1, 1, 1, 1, 2, 3, 3, 5]
def baseStart_3905058 : Nat := 118140960795 + 3905058 * 2 ^ 59
def prefixEnd_3905058 : Nat := 4983230072969 + 3 ^ 40 * 3905058 * 2
def baseEnd_3905058 : Nat := 668390579228429225438657

theorem tailTrace_3905058 : CollatzResearch.WordTrace tailWord_3905058 prefixEnd_3905058 668390579228429225438657 := by
  unfold tailWord_3905058
  simp only [CollatzResearch.WordTrace]
  refine ⟨35607291571662317913608957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94952777524432847769623885 35607291571662317913608957)
  ·
    refine ⟨13352734339373369217603359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35607291571662317913608957 13352734339373369217603359)
    ·
      refine ⟨20029101509060053826405039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13352734339373369217603359 20029101509060053826405039)
      ·
        refine ⟨30043652263590080739607559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20029101509060053826405039 30043652263590080739607559)
        ·
          refine ⟨45065478395385121109411339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30043652263590080739607559 45065478395385121109411339)
          ·
            refine ⟨67598217593077681664117009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45065478395385121109411339 67598217593077681664117009)
            ·
              refine ⟨50698663194808261248087757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67598217593077681664117009 50698663194808261248087757)
              ·
                refine ⟨19011998698053097968032909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50698663194808261248087757 19011998698053097968032909)
                ·
                  refine ⟨7129499511769911738012341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19011998698053097968032909 7129499511769911738012341)
                  ·
                    refine ⟨668390579228429225438657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7129499511769911738012341 668390579228429225438657)
                    ·
                      rfl

theorem cell23_3905058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_3905058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905058 prefixEnd_3905058 := by exact prefixLift 3905058
  have htrace : WordTrace (prefixWord ++ tailWord_3905058) baseStart_3905058 baseEnd_3905058 := by
    simpa [prefixWord, tailWord_3905058, baseEnd_3905058] using wordTrace_append hprefix tailTrace_3905058
  have hstable : (prefixWord ++ tailWord_3905058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905058).length < 2 ^ (prefixWord ++ tailWord_3905058).sum := by decide
  have hdescent : baseEnd_3905058 < baseStart_3905058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905098 : List Nat := [3, 1, 2, 1, 1, 3, 1, 4, 1, 1, 5]
def baseStart_3905098 : Nat := 118140960795 + 3905098 * 2 ^ 59
def prefixEnd_3905098 : Nat := 4983230072969 + 3 ^ 40 * 3905098 * 2
def baseEnd_3905098 : Nat := 2005192276911467519815787

theorem tailTrace_3905098 : CollatzResearch.WordTrace tailWord_3905098 prefixEnd_3905098 2005192276911467519815787 := by
  unfold tailWord_3905098
  simp only [CollatzResearch.WordTrace]
  refine ⟨35607656301626089621472987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94953750137669572323927965 35607656301626089621472987)
  ·
    refine ⟨53411484452439134432209481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35607656301626089621472987 53411484452439134432209481)
    ·
      refine ⟨40058613339329350824157111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53411484452439134432209481 40058613339329350824157111)
      ·
        refine ⟨60087920008994026236235667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40058613339329350824157111 60087920008994026236235667)
        ·
          refine ⟨90131880013491039354353501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60087920008994026236235667 90131880013491039354353501)
          ·
            refine ⟨33799455005059139757882563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90131880013491039354353501 33799455005059139757882563)
            ·
              refine ⟨50699182507588709636823845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33799455005059139757882563 50699182507588709636823845)
              ·
                refine ⟨9506096720172883056904471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50699182507588709636823845 9506096720172883056904471)
                ·
                  refine ⟨14259145080259324585356707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9506096720172883056904471 14259145080259324585356707)
                  ·
                    refine ⟨21388717620388986878035061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14259145080259324585356707 21388717620388986878035061)
                    ·
                      refine ⟨2005192276911467519815787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21388717620388986878035061 2005192276911467519815787)
                      ·
                        rfl

theorem cell23_3905098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_3905098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905098 prefixEnd_3905098 := by exact prefixLift 3905098
  have htrace : WordTrace (prefixWord ++ tailWord_3905098) baseStart_3905098 baseEnd_3905098 := by
    simpa [prefixWord, tailWord_3905098, baseEnd_3905098] using wordTrace_append hprefix tailTrace_3905098
  have hstable : (prefixWord ++ tailWord_3905098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905098).length < 2 ^ (prefixWord ++ tailWord_3905098).sum := by decide
  have hdescent : baseEnd_3905098 < baseStart_3905098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905105 : List Nat := [1, 2, 2, 1, 3, 2, 3, 3, 2, 4]
def baseStart_3905105 : Nat := 118140960795 + 3905105 * 2 ^ 59
def prefixEnd_3905105 : Nat := 4983230072969 + 3 ^ 40 * 3905105 * 2
def baseEnd_3905105 : Nat := 668398623758682997476085

theorem tailTrace_3905105 : CollatzResearch.WordTrace tailWord_3905105 prefixEnd_3905105 668398623758682997476085 := by
  unfold tailWord_3905105
  simp only [CollatzResearch.WordTrace]
  refine ⟨142430880517478998681396769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94953920344985999120931179 142430880517478998681396769)
  ·
    refine ⟨106823160388109249011047577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142430880517478998681396769 106823160388109249011047577)
    ·
      refine ⟨80117370291081936758285683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106823160388109249011047577 80117370291081936758285683)
      ·
        refine ⟨120176055436622905137428525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80117370291081936758285683 120176055436622905137428525)
        ·
          refine ⟨45066020788733589426535697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120176055436622905137428525 45066020788733589426535697)
          ·
            refine ⟨33799515591550192069901773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45066020788733589426535697 33799515591550192069901773)
            ·
              refine ⟨12674818346831322026213165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33799515591550192069901773 12674818346831322026213165)
              ·
                refine ⟨4753056880061745759829937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12674818346831322026213165 4753056880061745759829937)
                ·
                  refine ⟨3564792660046309319872453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4753056880061745759829937 3564792660046309319872453)
                  ·
                    refine ⟨668398623758682997476085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3564792660046309319872453 668398623758682997476085)
                    ·
                      rfl

theorem cell23_3905105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 2, 4].length) (baseStart_3905105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905105 prefixEnd_3905105 := by exact prefixLift 3905105
  have htrace : WordTrace (prefixWord ++ tailWord_3905105) baseStart_3905105 baseEnd_3905105 := by
    simpa [prefixWord, tailWord_3905105, baseEnd_3905105] using wordTrace_append hprefix tailTrace_3905105
  have hstable : (prefixWord ++ tailWord_3905105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905105).length < 2 ^ (prefixWord ++ tailWord_3905105).sum := by decide
  have hdescent : baseEnd_3905105 < baseStart_3905105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905108 : List Nat := [2, 4, 1, 1, 1, 2, 1, 3, 1, 1, 6]
def baseStart_3905108 : Nat := 118140960795 + 3905108 * 2 ^ 59
def prefixEnd_3905108 : Nat := 4983230072969 + 3 ^ 40 * 3905108 * 2
def baseEnd_3905108 : Nat := 2005197411718012480690741

theorem tailTrace_3905108 : CollatzResearch.WordTrace tailWord_3905108 prefixEnd_3905108 2005197411718012480690741 := by
  unfold tailWord_3905108
  simp only [CollatzResearch.WordTrace]
  refine ⟨71215494968234065096877989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94953993290978753462503985 71215494968234065096877989)
  ·
    refine ⟨13352905306543887205664623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71215494968234065096877989 13352905306543887205664623)
    ·
      refine ⟨20029357959815830808496935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13352905306543887205664623 20029357959815830808496935)
      ·
        refine ⟨30044036939723746212745403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20029357959815830808496935 30044036939723746212745403)
        ·
          refine ⟨45066055409585619319118105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30044036939723746212745403 45066055409585619319118105)
          ·
            refine ⟨33799541557189214489338579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45066055409585619319118105 33799541557189214489338579)
            ·
              refine ⟨50699312335783821734007869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33799541557189214489338579 50699312335783821734007869)
              ·
                refine ⟨19012242125918933150252951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50699312335783821734007869 19012242125918933150252951)
                ·
                  refine ⟨28518363188878399725379427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19012242125918933150252951 28518363188878399725379427)
                  ·
                    refine ⟨42777544783317599588069141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28518363188878399725379427 42777544783317599588069141)
                    ·
                      refine ⟨2005197411718012480690741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42777544783317599588069141 2005197411718012480690741)
                      ·
                        rfl

theorem cell23_3905108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_3905108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905108 prefixEnd_3905108 := by exact prefixLift 3905108
  have htrace : WordTrace (prefixWord ++ tailWord_3905108) baseStart_3905108 baseEnd_3905108 := by
    simpa [prefixWord, tailWord_3905108, baseEnd_3905108] using wordTrace_append hprefix tailTrace_3905108
  have hstable : (prefixWord ++ tailWord_3905108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905108).length < 2 ^ (prefixWord ++ tailWord_3905108).sum := by decide
  have hdescent : baseEnd_3905108 < baseStart_3905108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905125 : List Nat := [1, 3, 1, 3, 3, 2, 1, 2, 1, 2, 4]
def baseStart_3905125 : Nat := 118140960795 + 3905125 * 2 ^ 59
def prefixEnd_3905125 : Nat := 4983230072969 + 3 ^ 40 * 3905125 * 2
def baseEnd_3905125 : Nat := 2005206140889138914178163

theorem tailTrace_3905125 : CollatzResearch.WordTrace tailWord_3905125 prefixEnd_3905125 2005206140889138914178163 := by
  unfold tailWord_3905125
  simp only [CollatzResearch.WordTrace]
  refine ⟨142431609977406542097124829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94954406651604361398083219 142431609977406542097124829)
  ·
    refine ⟨53411853741527453286421811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142431609977406542097124829 53411853741527453286421811)
    ·
      refine ⟨80117780612291179929632717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53411853741527453286421811 80117780612291179929632717)
      ·
        refine ⟨30044167729609192473612269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80117780612291179929632717 30044167729609192473612269)
        ·
          refine ⟨11266562898603447177604601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30044167729609192473612269 11266562898603447177604601)
          ·
            refine ⟨8449922173952585383203451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11266562898603447177604601 8449922173952585383203451)
            ·
              refine ⟨12674883260928878074805177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8449922173952585383203451 12674883260928878074805177)
              ·
                refine ⟨9506162445696658556103883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12674883260928878074805177 9506162445696658556103883)
                ·
                  refine ⟨14259243668544987834155825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9506162445696658556103883 14259243668544987834155825)
                  ·
                    refine ⟨10694432751408740875616869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14259243668544987834155825 10694432751408740875616869)
                    ·
                      refine ⟨2005206140889138914178163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10694432751408740875616869 2005206140889138914178163)
                      ·
                        rfl

theorem cell23_3905125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_3905125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905125 prefixEnd_3905125 := by exact prefixLift 3905125
  have htrace : WordTrace (prefixWord ++ tailWord_3905125) baseStart_3905125 baseEnd_3905125 := by
    simpa [prefixWord, tailWord_3905125, baseEnd_3905125] using wordTrace_append hprefix tailTrace_3905125
  have hstable : (prefixWord ++ tailWord_3905125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905125).length < 2 ^ (prefixWord ++ tailWord_3905125).sum := by decide
  have hdescent : baseEnd_3905125 < baseStart_3905125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905162 : List Nat := [3, 1, 2, 3, 2, 2, 2, 1, 1, 3, 3]
def baseStart_3905162 : Nat := 118140960795 + 3905162 * 2 ^ 59
def prefixEnd_3905162 : Nat := 4983230072969 + 3 ^ 40 * 3905162 * 2
def baseEnd_3905162 : Nat := 2005225139673355269415493

theorem tailTrace_3905162 : CollatzResearch.WordTrace tailWord_3905162 prefixEnd_3905162 2005225139673355269415493 := by
  unfold tailWord_3905162
  simp only [CollatzResearch.WordTrace]
  refine ⟨35608239869568124354055435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94955306318848331610814493 35608239869568124354055435)
  ·
    refine ⟨53412359804352186531083153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35608239869568124354055435 53412359804352186531083153)
    ·
      refine ⟨40059269853264139898312365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53412359804352186531083153 40059269853264139898312365)
      ·
        refine ⟨15022226194974052461867137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40059269853264139898312365 15022226194974052461867137)
        ·
          refine ⟨11266669646230539346400353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15022226194974052461867137 11266669646230539346400353)
          ·
            refine ⟨8450002234672904509800265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11266669646230539346400353 8450002234672904509800265)
            ·
              refine ⟨6337501676004678382350199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8450002234672904509800265 6337501676004678382350199)
              ·
                refine ⟨9506252514007017573525299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6337501676004678382350199 9506252514007017573525299)
                ·
                  refine ⟨14259378771010526360287949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9506252514007017573525299 14259378771010526360287949)
                  ·
                    refine ⟨5347267039128947385107981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14259378771010526360287949 5347267039128947385107981)
                    ·
                      refine ⟨2005225139673355269415493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5347267039128947385107981 2005225139673355269415493)
                      ·
                        rfl

theorem cell23_3905162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_3905162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905162 prefixEnd_3905162 := by exact prefixLift 3905162
  have htrace : WordTrace (prefixWord ++ tailWord_3905162) baseStart_3905162 baseEnd_3905162 := by
    simpa [prefixWord, tailWord_3905162, baseEnd_3905162] using wordTrace_append hprefix tailTrace_3905162
  have hstable : (prefixWord ++ tailWord_3905162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905162).length < 2 ^ (prefixWord ++ tailWord_3905162).sum := by decide
  have hdescent : baseEnd_3905162 < baseStart_3905162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905183 : List Nat := [1, 1, 2, 7, 2, 1, 2, 1, 1, 2, 3]
def baseStart_3905183 : Nat := 118140960795 + 3905183 * 2 ^ 59
def prefixEnd_3905183 : Nat := 4983230072969 + 3 ^ 40 * 3905183 * 2
def baseEnd_3905183 : Nat := 2005235922767099687252897

theorem tailTrace_3905183 : CollatzResearch.WordTrace tailWord_3905183 prefixEnd_3905183 2005235922767099687252897 := by
  unfold tailWord_3905183
  simp only [CollatzResearch.WordTrace]
  refine ⟨142433725411196418002736203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94955816940797612001824135 142433725411196418002736203)
  ·
    refine ⟨213650588116794627004104305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142433725411196418002736203 213650588116794627004104305)
    ·
      refine ⟨160237941087595970253078229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213650588116794627004104305 160237941087595970253078229)
      ·
        refine ⟨3755576744240530552806521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 160237941087595970253078229 3755576744240530552806521)
        ·
          refine ⟨2816682558180397914604891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3755576744240530552806521 2816682558180397914604891)
          ·
            refine ⟨4225023837270596871907337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2816682558180397914604891 4225023837270596871907337)
            ·
              refine ⟨3168767877952947653930503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4225023837270596871907337 3168767877952947653930503)
              ·
                refine ⟨4753151816929421480895755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3168767877952947653930503 4753151816929421480895755)
                ·
                  refine ⟨7129727725394132221343633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4753151816929421480895755 7129727725394132221343633)
                  ·
                    refine ⟨5347295794045599166007725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7129727725394132221343633 5347295794045599166007725)
                    ·
                      refine ⟨2005235922767099687252897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5347295794045599166007725 2005235922767099687252897)
                      ·
                        rfl

theorem cell23_3905183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_3905183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905183 prefixEnd_3905183 := by exact prefixLift 3905183
  have htrace : WordTrace (prefixWord ++ tailWord_3905183) baseStart_3905183 baseEnd_3905183 := by
    simpa [prefixWord, tailWord_3905183, baseEnd_3905183] using wordTrace_append hprefix tailTrace_3905183
  have hstable : (prefixWord ++ tailWord_3905183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905183).length < 2 ^ (prefixWord ++ tailWord_3905183).sum := by decide
  have hdescent : baseEnd_3905183 < baseStart_3905183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905189 : List Nat := [1, 3, 1, 2, 1, 2, 6, 1, 1, 3, 2]
def baseStart_3905189 : Nat := 118140960795 + 3905189 * 2 ^ 59
def prefixEnd_3905189 : Nat := 4983230072969 + 3 ^ 40 * 3905189 * 2
def baseEnd_3905189 : Nat := 2005239003651026663777869

theorem tailTrace_3905189 : CollatzResearch.WordTrace tailWord_3905189 prefixEnd_3905189 2005239003651026663777869 := by
  unfold tailWord_3905189
  simp only [CollatzResearch.WordTrace]
  refine ⟨142433944249174681027454621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94955962832783120684969747 142433944249174681027454621)
  ·
    refine ⟨53412729093440505385295483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142433944249174681027454621 53412729093440505385295483)
    ·
      refine ⟨80119093640160758077943225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53412729093440505385295483 80119093640160758077943225)
      ·
        refine ⟨60089320230120568558457419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80119093640160758077943225 60089320230120568558457419)
        ·
          refine ⟨90133980345180852837686129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60089320230120568558457419 90133980345180852837686129)
          ·
            refine ⟨67600485258885639628264597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90133980345180852837686129 67600485258885639628264597)
            ·
              refine ⟨3168772746510264357574903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67600485258885639628264597 3168772746510264357574903)
              ·
                refine ⟨4753159119765396536362355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3168772746510264357574903 4753159119765396536362355)
                ·
                  refine ⟨7129738679648094804543533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4753159119765396536362355 7129738679648094804543533)
                  ·
                    refine ⟨2673652004868035551703825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7129738679648094804543533 2673652004868035551703825)
                    ·
                      refine ⟨2005239003651026663777869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2673652004868035551703825 2005239003651026663777869)
                      ·
                        rfl

theorem cell23_3905189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 1, 3, 2].length) (baseStart_3905189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905189 prefixEnd_3905189 := by exact prefixLift 3905189
  have htrace : WordTrace (prefixWord ++ tailWord_3905189) baseStart_3905189 baseEnd_3905189 := by
    simpa [prefixWord, tailWord_3905189, baseEnd_3905189] using wordTrace_append hprefix tailTrace_3905189
  have hstable : (prefixWord ++ tailWord_3905189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905189).length < 2 ^ (prefixWord ++ tailWord_3905189).sum := by decide
  have hdescent : baseEnd_3905189 < baseStart_3905189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905242 : List Nat := [3, 1, 1, 2, 2, 3, 3, 3, 5]
def baseStart_3905242 : Nat := 118140960795 + 3905242 * 2 ^ 59
def prefixEnd_3905242 : Nat := 4983230072969 + 3 ^ 40 * 3905242 * 2
def baseEnd_3905242 : Nat := 222807357569523884046125

theorem tailTrace_3905242 : CollatzResearch.WordTrace tailWord_3905242 prefixEnd_3905242 222807357569523884046125 := by
  unfold tailWord_3905242
  simp only [CollatzResearch.WordTrace]
  refine ⟨35608969329495667769783495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94957251545321780719422653 35608969329495667769783495)
  ·
    refine ⟨53413453994243501654675243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35608969329495667769783495 53413453994243501654675243)
    ·
      refine ⟨80120180991365252482012865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53413453994243501654675243 80120180991365252482012865)
      ·
        refine ⟨60090135743523939361509649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80120180991365252482012865 60090135743523939361509649)
        ·
          refine ⟨45067601807642954521132237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60090135743523939361509649 45067601807642954521132237)
          ·
            refine ⟨16900350677866107945424589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45067601807642954521132237 16900350677866107945424589)
            ·
              refine ⟨6337631504199790479534221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16900350677866107945424589 6337631504199790479534221)
              ·
                refine ⟨2376611814074921429825333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6337631504199790479534221 2376611814074921429825333)
                ·
                  refine ⟨222807357569523884046125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2376611814074921429825333 222807357569523884046125)
                  ·
                    rfl

theorem cell23_3905242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 3, 5].length) (baseStart_3905242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905242 prefixEnd_3905242 := by exact prefixLift 3905242
  have htrace : WordTrace (prefixWord ++ tailWord_3905242) baseStart_3905242 baseEnd_3905242 := by
    simpa [prefixWord, tailWord_3905242, baseEnd_3905242] using wordTrace_append hprefix tailTrace_3905242
  have hstable : (prefixWord ++ tailWord_3905242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905242).length < 2 ^ (prefixWord ++ tailWord_3905242).sum := by decide
  have hdescent : baseEnd_3905242 < baseStart_3905242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905262 : List Nat := [4, 1, 2, 1, 1, 2, 2, 1, 2, 5, 2]
def baseStart_3905262 : Nat := 118140960795 + 3905262 * 2 ^ 59
def prefixEnd_3905262 : Nat := 4983230072969 + 3 ^ 40 * 3905262 * 2
def baseEnd_3905262 : Nat := 2005276487738804878165033

theorem tailTrace_3905262 : CollatzResearch.WordTrace tailWord_3905262 prefixEnd_3905262 2005276487738804878165033 := by
  unfold tailWord_3905262
  simp only [CollatzResearch.WordTrace]
  refine ⟨17804575847238776811857755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94957737851940142996574693 17804575847238776811857755)
  ·
    refine ⟨26706863770858165217786633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17804575847238776811857755 26706863770858165217786633)
    ·
      refine ⟨20030147828143623913339975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26706863770858165217786633 20030147828143623913339975)
      ·
        refine ⟨30045221742215435870009963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20030147828143623913339975 30045221742215435870009963)
        ·
          refine ⟨45067832613323153805014945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30045221742215435870009963 45067832613323153805014945)
          ·
            refine ⟨33800874459992365353761209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45067832613323153805014945 33800874459992365353761209)
            ·
              refine ⟨25350655844994274015320907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33800874459992365353761209 25350655844994274015320907)
              ·
                refine ⟨38025983767491411022981361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25350655844994274015320907 38025983767491411022981361)
                ·
                  refine ⟨28519487825618558267236021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38025983767491411022981361 28519487825618558267236021)
                  ·
                    refine ⟨2673701983651739837553377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28519487825618558267236021 2673701983651739837553377)
                    ·
                      refine ⟨2005276487738804878165033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2673701983651739837553377 2005276487738804878165033)
                      ·
                        rfl

theorem cell23_3905262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_3905262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905262 prefixEnd_3905262 := by exact prefixLift 3905262
  have htrace : WordTrace (prefixWord ++ tailWord_3905262) baseStart_3905262 baseEnd_3905262 := by
    simpa [prefixWord, tailWord_3905262, baseEnd_3905262] using wordTrace_append hprefix tailTrace_3905262
  have hstable : (prefixWord ++ tailWord_3905262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905262).length < 2 ^ (prefixWord ++ tailWord_3905262).sum := by decide
  have hdescent : baseEnd_3905262 < baseStart_3905262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905265 : List Nat := [1, 2, 2, 2, 2, 4, 1, 1, 1, 2, 5]
def baseStart_3905265 : Nat := 118140960795 + 3905265 * 2 ^ 59
def prefixEnd_3905265 : Nat := 4983230072969 + 3 ^ 40 * 3905265 * 2
def baseEnd_3905265 : Nat := 2005278028180768366427519

theorem tailTrace_3905265 : CollatzResearch.WordTrace tailWord_3905265 prefixEnd_3905265 2005278028180768366427519 := by
  unfold tailWord_3905265
  simp only [CollatzResearch.WordTrace]
  refine ⟨142436716196899346007221249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94957810797932897338147499 142436716196899346007221249)
  ·
    refine ⟨106827537147674509505415937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142436716196899346007221249 106827537147674509505415937)
    ·
      refine ⟨80120652860755882129061953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106827537147674509505415937 80120652860755882129061953)
      ·
        refine ⟨60090489645566911596796465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80120652860755882129061953 60090489645566911596796465)
        ·
          refine ⟨45067867234175183697597349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60090489645566911596796465 45067867234175183697597349)
          ·
            refine ⟨8450225106407846943299503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45067867234175183697597349 8450225106407846943299503)
            ·
              refine ⟨12675337659611770414949255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8450225106407846943299503 12675337659611770414949255)
              ·
                refine ⟨19013006489417655622423883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12675337659611770414949255 19013006489417655622423883)
                ·
                  refine ⟨28519509734126483433635825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19013006489417655622423883 28519509734126483433635825)
                  ·
                    refine ⟨21389632300594862575226869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28519509734126483433635825 21389632300594862575226869)
                    ·
                      refine ⟨2005278028180768366427519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21389632300594862575226869 2005278028180768366427519)
                      ·
                        rfl

theorem cell23_3905265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_3905265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905265 prefixEnd_3905265 := by exact prefixLift 3905265
  have htrace : WordTrace (prefixWord ++ tailWord_3905265) baseStart_3905265 baseEnd_3905265 := by
    simpa [prefixWord, tailWord_3905265, baseEnd_3905265] using wordTrace_append hprefix tailTrace_3905265
  have hstable : (prefixWord ++ tailWord_3905265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905265).length < 2 ^ (prefixWord ++ tailWord_3905265).sum := by decide
  have hdescent : baseEnd_3905265 < baseStart_3905265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905310 : List Nat := [4, 3, 2, 2, 1, 2, 2, 2, 5]
def baseStart_3905310 : Nat := 118140960795 + 3905310 * 2 ^ 59
def prefixEnd_3905310 : Nat := 4983230072969 + 3 ^ 40 * 3905310 * 2
def baseEnd_3905310 : Nat := 222811237201135632262757

theorem tailTrace_3905310 : CollatzResearch.WordTrace tailWord_3905310 prefixEnd_3905310 222811237201135632262757 := by
  unfold tailWord_3905310
  simp only [CollatzResearch.WordTrace]
  refine ⟨17804794685217039836576173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94958904987824212461739589 17804794685217039836576173)
  ·
    refine ⟨6676798006956389938716065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17804794685217039836576173 6676798006956389938716065)
    ·
      refine ⟨5007598505217292454037049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6676798006956389938716065 5007598505217292454037049)
      ·
        refine ⟨3755698878912969340527787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5007598505217292454037049 3755698878912969340527787)
        ·
          refine ⟨5633548318369454010791681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3755698878912969340527787 5633548318369454010791681)
          ·
            refine ⟨4225161238777090508093761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5633548318369454010791681 4225161238777090508093761)
            ·
              refine ⟨3168870929082817881070321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4225161238777090508093761 3168870929082817881070321)
              ·
                refine ⟨2376653196812113410802741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3168870929082817881070321 2376653196812113410802741)
                ·
                  refine ⟨222811237201135632262757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2376653196812113410802741 222811237201135632262757)
                  ·
                    rfl

theorem cell23_3905310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_3905310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905310 prefixEnd_3905310 := by exact prefixLift 3905310
  have htrace : WordTrace (prefixWord ++ tailWord_3905310) baseStart_3905310 baseEnd_3905310 := by
    simpa [prefixWord, tailWord_3905310, baseEnd_3905310] using wordTrace_append hprefix tailTrace_3905310
  have hstable : (prefixWord ++ tailWord_3905310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905310).length < 2 ^ (prefixWord ++ tailWord_3905310).sum := by decide
  have hdescent : baseEnd_3905310 < baseStart_3905310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905312 : List Nat := [2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 3]
def baseStart_3905312 : Nat := 118140960795 + 3905312 * 2 ^ 59
def prefixEnd_3905312 : Nat := 4983230072969 + 3 ^ 40 * 3905312 * 2
def baseEnd_3905312 : Nat := 2005302161771529682539803

theorem tailTrace_3905312 : CollatzResearch.WordTrace tailWord_3905312 prefixEnd_3905312 2005302161771529682539803 := by
  unfold tailWord_3905312
  simp only [CollatzResearch.WordTrace]
  refine ⟨71219215213864536517091095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94958953618486048689454793 71219215213864536517091095)
  ·
    refine ⟨106828822820796804775636643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71219215213864536517091095 106828822820796804775636643)
    ·
      refine ⟨160243234231195207163454965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106828822820796804775636643 160243234231195207163454965)
      ·
        refine ⟨15022803209174550671573903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160243234231195207163454965 15022803209174550671573903)
        ·
          refine ⟨22534204813761826007360855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15022803209174550671573903 22534204813761826007360855)
          ·
            refine ⟨33801307220642739011041283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22534204813761826007360855 33801307220642739011041283)
            ·
              refine ⟨50701960830964108516561925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33801307220642739011041283 50701960830964108516561925)
              ·
                refine ⟨9506617655805770346855361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50701960830964108516561925 9506617655805770346855361)
                ·
                  refine ⟨7129963241854327760141521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9506617655805770346855361 7129963241854327760141521)
                  ·
                    refine ⟨5347472431390745820106141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7129963241854327760141521 5347472431390745820106141)
                    ·
                      refine ⟨2005302161771529682539803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5347472431390745820106141 2005302161771529682539803)
                      ·
                        rfl

theorem cell23_3905312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_3905312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905312 prefixEnd_3905312 := by exact prefixLift 3905312
  have htrace : WordTrace (prefixWord ++ tailWord_3905312) baseStart_3905312 baseEnd_3905312 := by
    simpa [prefixWord, tailWord_3905312, baseEnd_3905312] using wordTrace_append hprefix tailTrace_3905312
  have hstable : (prefixWord ++ tailWord_3905312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905312).length < 2 ^ (prefixWord ++ tailWord_3905312).sum := by decide
  have hdescent : baseEnd_3905312 < baseStart_3905312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905315 : List Nat := [1, 1, 1, 4, 2, 1, 3, 4, 6]
def baseStart_3905315 : Nat := 118140960795 + 3905315 * 2 ^ 59
def prefixEnd_3905315 : Nat := 4983230072969 + 3 ^ 40 * 3905315 * 2
def baseEnd_3905315 : Nat := 222811522468165907866921

theorem tailTrace_3905315 : CollatzResearch.WordTrace tailWord_3905315 prefixEnd_3905315 222811522468165907866921 := by
  unfold tailWord_3905315
  simp only [CollatzResearch.WordTrace]
  refine ⟨142438539846718204546541399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94959026564478803031027599 142438539846718204546541399)
  ·
    refine ⟨213657809770077306819812099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142438539846718204546541399 213657809770077306819812099)
    ·
      refine ⟨320486714655115960229718149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213657809770077306819812099 320486714655115960229718149)
      ·
        refine ⟨60091258997834242543072153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 320486714655115960229718149 60091258997834242543072153)
        ·
          refine ⟨45068444248375681907304115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60091258997834242543072153 45068444248375681907304115)
          ·
            refine ⟨67602666372563522860956173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45068444248375681907304115 67602666372563522860956173)
            ·
              refine ⟨25350999889711321072858565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67602666372563522860956173 25350999889711321072858565)
              ·
                refine ⟨4753312479320872701160981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25350999889711321072858565 4753312479320872701160981)
                ·
                  refine ⟨222811522468165907866921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4753312479320872701160981 222811522468165907866921)
                  ·
                    rfl

theorem cell23_3905315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 6].length) (baseStart_3905315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905315 prefixEnd_3905315 := by exact prefixLift 3905315
  have htrace : WordTrace (prefixWord ++ tailWord_3905315) baseStart_3905315 baseEnd_3905315 := by
    simpa [prefixWord, tailWord_3905315, baseEnd_3905315] using wordTrace_append hprefix tailTrace_3905315
  have hstable : (prefixWord ++ tailWord_3905315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905315).length < 2 ^ (prefixWord ++ tailWord_3905315).sum := by decide
  have hdescent : baseEnd_3905315 < baseStart_3905315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905326 : List Nat := [4, 1, 3, 2, 2, 1, 1, 1, 2, 4, 2]
def baseStart_3905326 : Nat := 118140960795 + 3905326 * 2 ^ 59
def prefixEnd_3905326 : Nat := 4983230072969 + 3 ^ 40 * 3905326 * 2
def baseEnd_3905326 : Nat := 2005309350500692627764739

theorem tailTrace_3905326 : CollatzResearch.WordTrace tailWord_3905326 prefixEnd_3905326 2005309350500692627764739 := by
  unfold tailWord_3905326
  simp only [CollatzResearch.WordTrace]
  refine ⟨17804867631209794178148979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94959294033118902283461221 17804867631209794178148979)
  ·
    refine ⟨26707301446814691267223469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17804867631209794178148979 26707301446814691267223469)
    ·
      refine ⟨10015238042555509225208801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26707301446814691267223469 10015238042555509225208801)
      ·
        refine ⟨7511428531916631918906601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10015238042555509225208801 7511428531916631918906601)
        ·
          refine ⟨5633571398937473939179951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7511428531916631918906601 5633571398937473939179951)
          ·
            refine ⟨8450357098406210908769927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5633571398937473939179951 8450357098406210908769927)
            ·
              refine ⟨12675535647609316363154891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8450357098406210908769927 12675535647609316363154891)
              ·
                refine ⟨19013303471413974544732337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12675535647609316363154891 19013303471413974544732337)
                ·
                  refine ⟨14259977603560480908549253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19013303471413974544732337 14259977603560480908549253)
                  ·
                    refine ⟨2673745800667590170352985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14259977603560480908549253 2673745800667590170352985)
                    ·
                      refine ⟨2005309350500692627764739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2673745800667590170352985 2005309350500692627764739)
                      ·
                        rfl

theorem cell23_3905326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_3905326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905326 prefixEnd_3905326 := by exact prefixLift 3905326
  have htrace : WordTrace (prefixWord ++ tailWord_3905326) baseStart_3905326 baseEnd_3905326 := by
    simpa [prefixWord, tailWord_3905326, baseEnd_3905326] using wordTrace_append hprefix tailTrace_3905326
  have hstable : (prefixWord ++ tailWord_3905326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905326).length < 2 ^ (prefixWord ++ tailWord_3905326).sum := by decide
  have hdescent : baseEnd_3905326 < baseStart_3905326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905376 : List Nat := [2, 1, 1, 3, 3, 2, 2, 4, 1, 1, 3]
def baseStart_3905376 : Nat := 118140960795 + 3905376 * 2 ^ 59
def prefixEnd_3905376 : Nat := 4983230072969 + 3 ^ 40 * 3905376 * 2
def baseEnd_3905376 : Nat := 2005335024533417432139509

theorem tailTrace_3905376 : CollatzResearch.WordTrace tailWord_3905376 prefixEnd_3905376 2005335024533417432139509 := by
  unfold tailWord_3905376
  simp only [CollatzResearch.WordTrace]
  refine ⟨71220382349748605982255991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94960509799664807976341321 71220382349748605982255991)
  ·
    refine ⟨106830573524622908973383987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71220382349748605982255991 106830573524622908973383987)
    ·
      refine ⟨160245860286934363460075981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106830573524622908973383987 160245860286934363460075981)
      ·
        refine ⟨60092197607600386297528493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160245860286934363460075981 60092197607600386297528493)
        ·
          refine ⟨22534574102850144861573185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60092197607600386297528493 22534574102850144861573185)
          ·
            refine ⟨16900930577137608646179889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22534574102850144861573185 16900930577137608646179889)
            ·
              refine ⟨12675697932853206484634917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16900930577137608646179889 12675697932853206484634917)
              ·
                refine ⟨2376693362409976215869047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12675697932853206484634917 2376693362409976215869047)
                ·
                  refine ⟨3565040043614964323803571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2376693362409976215869047 3565040043614964323803571)
                  ·
                    refine ⟨5347560065422446485705357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3565040043614964323803571 5347560065422446485705357)
                    ·
                      refine ⟨2005335024533417432139509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5347560065422446485705357 2005335024533417432139509)
                      ·
                        rfl

theorem cell23_3905376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 4, 1, 1, 3].length) (baseStart_3905376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905376 prefixEnd_3905376 := by exact prefixLift 3905376
  have htrace : WordTrace (prefixWord ++ tailWord_3905376) baseStart_3905376 baseEnd_3905376 := by
    simpa [prefixWord, tailWord_3905376, baseEnd_3905376] using wordTrace_append hprefix tailTrace_3905376
  have hstable : (prefixWord ++ tailWord_3905376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905376).length < 2 ^ (prefixWord ++ tailWord_3905376).sum := by decide
  have hdescent : baseEnd_3905376 < baseStart_3905376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905402 : List Nat := [3, 1, 1, 1, 1, 1, 4, 3, 3, 2, 3]
def baseStart_3905402 : Nat := 118140960795 + 3905402 * 2 ^ 59
def prefixEnd_3905402 : Nat := 4983230072969 + 3 ^ 40 * 3905402 * 2
def baseEnd_3905402 : Nat := 2005348375030434330414389

theorem tailTrace_3905402 : CollatzResearch.WordTrace tailWord_3905402 prefixEnd_3905402 2005348375030434330414389 := by
  unfold tailWord_3905402
  simp only [CollatzResearch.WordTrace]
  refine ⟨35610428249350754601239615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94961141998268678936638973 35610428249350754601239615)
  ·
    refine ⟨53415642374026131901859423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35610428249350754601239615 53415642374026131901859423)
    ·
      refine ⟨80123463561039197852789135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53415642374026131901859423 80123463561039197852789135)
      ·
        refine ⟨120185195341558796779183703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80123463561039197852789135 120185195341558796779183703)
        ·
          refine ⟨180277793012338195168775555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120185195341558796779183703 180277793012338195168775555)
          ·
            refine ⟨270416689518507292753163333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180277793012338195168775555 270416689518507292753163333)
            ·
              refine ⟨50703129284720117391218125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 270416689518507292753163333 50703129284720117391218125)
              ·
                refine ⟨19013673481770044021706797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50703129284720117391218125 19013673481770044021706797)
                ·
                  refine ⟨7130127555663766508140049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19013673481770044021706797 7130127555663766508140049)
                  ·
                    refine ⟨5347595666747824881105037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7130127555663766508140049 5347595666747824881105037)
                    ·
                      refine ⟨2005348375030434330414389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5347595666747824881105037 2005348375030434330414389)
                      ·
                        rfl

theorem cell23_3905402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 3, 2, 3].length) (baseStart_3905402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905402 prefixEnd_3905402 := by exact prefixLift 3905402
  have htrace : WordTrace (prefixWord ++ tailWord_3905402) baseStart_3905402 baseEnd_3905402 := by
    simpa [prefixWord, tailWord_3905402, baseEnd_3905402] using wordTrace_append hprefix tailTrace_3905402
  have hstable : (prefixWord ++ tailWord_3905402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905402).length < 2 ^ (prefixWord ++ tailWord_3905402).sum := by decide
  have hdescent : baseEnd_3905402 < baseStart_3905402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905412 : List Nat := [2, 3, 2, 1, 1, 1, 2, 4, 1, 2, 4]
def baseStart_3905412 : Nat := 118140960795 + 3905412 * 2 ^ 59
def prefixEnd_3905412 : Nat := 4983230072969 + 3 ^ 40 * 3905412 * 2
def baseEnd_3905412 : Nat := 2005353509836979291289343

theorem tailTrace_3905412 : CollatzResearch.WordTrace tailWord_3905412 prefixEnd_3905412 2005353509836979291289343 := by
  unfold tailWord_3905412
  simp only [CollatzResearch.WordTrace]
  refine ⟨71221038863683395056411245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94961385151577860075214993 71221038863683395056411245)
  ·
    refine ⟨26707889573881273146154217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71221038863683395056411245 26707889573881273146154217)
    ·
      refine ⟨20030917180410954859615663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26707889573881273146154217 20030917180410954859615663)
      ·
        refine ⟨30046375770616432289423495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20030917180410954859615663 30046375770616432289423495)
        ·
          refine ⟨45069563655924648434135243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30046375770616432289423495 45069563655924648434135243)
          ·
            refine ⟨67604345483886972651202865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45069563655924648434135243 67604345483886972651202865)
            ·
              refine ⟨50703259112915229488402149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67604345483886972651202865 50703259112915229488402149)
              ·
                refine ⟨9506861083671605529075403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50703259112915229488402149 9506861083671605529075403)
                ·
                  refine ⟨14260291625507408293613105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9506861083671605529075403 14260291625507408293613105)
                  ·
                    refine ⟨10695218719130556220209829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14260291625507408293613105 10695218719130556220209829)
                    ·
                      refine ⟨2005353509836979291289343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10695218719130556220209829 2005353509836979291289343)
                      ·
                        rfl

theorem cell23_3905412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_3905412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905412 prefixEnd_3905412 := by exact prefixLift 3905412
  have htrace : WordTrace (prefixWord ++ tailWord_3905412) baseStart_3905412 baseEnd_3905412 := by
    simpa [prefixWord, tailWord_3905412, baseEnd_3905412] using wordTrace_append hprefix tailTrace_3905412
  have hstable : (prefixWord ++ tailWord_3905412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905412).length < 2 ^ (prefixWord ++ tailWord_3905412).sum := by decide
  have hdescent : baseEnd_3905412 < baseStart_3905412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905459 : List Nat := [1, 1, 1, 2, 3, 1, 5, 1, 3, 3, 2]
def baseStart_3905459 : Nat := 118140960795 + 3905459 * 2 ^ 59
def prefixEnd_3905459 : Nat := 4983230072969 + 3 ^ 40 * 3905459 * 2
def baseEnd_3905459 : Nat := 2005377643427740607401627

theorem tailTrace_3905459 : CollatzResearch.WordTrace tailWord_3905459 prefixEnd_3905459 2005377643427740607401627 := by
  unfold tailWord_3905459
  simp only [CollatzResearch.WordTrace]
  refine ⟨142443791958196517139783431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94962527972131011426522287 142443791958196517139783431)
  ·
    refine ⟨213665687937294775709675147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142443791958196517139783431 213665687937294775709675147)
    ·
      refine ⟨320498531905942163564512721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213665687937294775709675147 320498531905942163564512721)
      ·
        refine ⟨240373898929456622673384541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320498531905942163564512721 240373898929456622673384541)
        ·
          refine ⟨90140212098546233502519203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240373898929456622673384541 90140212098546233502519203)
          ·
            refine ⟨135210318147819350253778805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90140212098546233502519203 135210318147819350253778805)
            ·
              refine ⟨12675967326358064086291763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135210318147819350253778805 12675967326358064086291763)
              ·
                refine ⟨19013950989537096129437645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12675967326358064086291763 19013950989537096129437645)
                ·
                  refine ⟨7130231621076411048539117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19013950989537096129437645 7130231621076411048539117)
                  ·
                    refine ⟨2673836857903654143202169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7130231621076411048539117 2673836857903654143202169)
                    ·
                      refine ⟨2005377643427740607401627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2673836857903654143202169 2005377643427740607401627)
                      ·
                        rfl

theorem cell23_3905459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 3, 2].length) (baseStart_3905459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905459 prefixEnd_3905459 := by exact prefixLift 3905459
  have htrace : WordTrace (prefixWord ++ tailWord_3905459) baseStart_3905459 baseEnd_3905459 := by
    simpa [prefixWord, tailWord_3905459, baseEnd_3905459] using wordTrace_append hprefix tailTrace_3905459
  have hstable : (prefixWord ++ tailWord_3905459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905459).length < 2 ^ (prefixWord ++ tailWord_3905459).sum := by decide
  have hdescent : baseEnd_3905459 < baseStart_3905459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905500 : List Nat := [2, 2, 6, 1, 1, 1, 2, 1, 1, 3, 3]
def baseStart_3905500 : Nat := 118140960795 + 3905500 * 2 ^ 59
def prefixEnd_3905500 : Nat := 4983230072969 + 3 ^ 40 * 3905500 * 2
def baseEnd_3905500 : Nat := 2005398696134574946988939

theorem tailTrace_3905500 : CollatzResearch.WordTrace tailWord_3905500 prefixEnd_3905500 2005398696134574946988939 := by
  unfold tailWord_3905500
  simp only [CollatzResearch.WordTrace]
  refine ⟨71222643675523990571012977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94963524900698654094683969 71222643675523990571012977)
  ·
    refine ⟨53416982756642992928259733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71222643675523990571012977 53416982756642992928259733)
    ·
      refine ⟨2503921066717640293512175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53416982756642992928259733 2503921066717640293512175)
      ·
        refine ⟨3755881600076460440268263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2503921066717640293512175 3755881600076460440268263)
        ·
          refine ⟨5633822400114690660402395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3755881600076460440268263 5633822400114690660402395)
          ·
            refine ⟨8450733600172035990603593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5633822400114690660402395 8450733600172035990603593)
            ·
              refine ⟨6338050200129026992952695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8450733600172035990603593 6338050200129026992952695)
              ·
                refine ⟨9507075300193540489429043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6338050200129026992952695 9507075300193540489429043)
                ·
                  refine ⟨14260612950290310734143565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9507075300193540489429043 14260612950290310734143565)
                  ·
                    refine ⟨5347729856358866525303837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14260612950290310734143565 5347729856358866525303837)
                    ·
                      refine ⟨2005398696134574946988939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5347729856358866525303837 2005398696134574946988939)
                      ·
                        rfl

theorem cell23_3905500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_3905500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905500 prefixEnd_3905500 := by exact prefixLift 3905500
  have htrace : WordTrace (prefixWord ++ tailWord_3905500) baseStart_3905500 baseEnd_3905500 := by
    simpa [prefixWord, tailWord_3905500, baseEnd_3905500] using wordTrace_append hprefix tailTrace_3905500
  have hstable : (prefixWord ++ tailWord_3905500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905500).length < 2 ^ (prefixWord ++ tailWord_3905500).sum := by decide
  have hdescent : baseEnd_3905500 < baseStart_3905500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905529 : List Nat := [1, 2, 1, 3, 1, 4, 1, 5, 5]
def baseStart_3905529 : Nat := 118140960795 + 3905529 * 2 ^ 59
def prefixEnd_3905529 : Nat := 4983230072969 + 3 ^ 40 * 3905529 * 2
def baseEnd_3905529 : Nat := 222823731897061703725145

theorem tailTrace_3905529 : CollatzResearch.WordTrace tailWord_3905529 prefixEnd_3905529 222823731897061703725145 := by
  unfold tailWord_3905529
  simp only [CollatzResearch.WordTrace]
  refine ⟨142446345067942919094831641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94964230045295279396554427 142446345067942919094831641)
  ·
    refine ⟨106834758800957189321123731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142446345067942919094831641 106834758800957189321123731)
    ·
      refine ⟨160252138201435783981685597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106834758800957189321123731 160252138201435783981685597)
      ·
        refine ⟨60094551825538418993132099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160252138201435783981685597 60094551825538418993132099)
        ·
          refine ⟨90141827738307628489698149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60094551825538418993132099 90141827738307628489698149)
          ·
            refine ⟨16901592700932680341818403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90141827738307628489698149 16901592700932680341818403)
            ·
              refine ⟨25352389051399020512727605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16901592700932680341818403 25352389051399020512727605)
              ·
                refine ⟨2376786473568658173068213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25352389051399020512727605 2376786473568658173068213)
                ·
                  refine ⟨222823731897061703725145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2376786473568658173068213 222823731897061703725145)
                  ·
                    rfl

theorem cell23_3905529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 5, 5].length) (baseStart_3905529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905529 prefixEnd_3905529 := by exact prefixLift 3905529
  have htrace : WordTrace (prefixWord ++ tailWord_3905529) baseStart_3905529 baseEnd_3905529 := by
    simpa [prefixWord, tailWord_3905529, baseEnd_3905529] using wordTrace_append hprefix tailTrace_3905529
  have hstable : (prefixWord ++ tailWord_3905529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905529).length < 2 ^ (prefixWord ++ tailWord_3905529).sum := by decide
  have hdescent : baseEnd_3905529 < baseStart_3905529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905540 : List Nat := [2, 3, 2, 4, 1, 1, 1, 1, 4, 2, 2]
def baseStart_3905540 : Nat := 118140960795 + 3905540 * 2 ^ 59
def prefixEnd_3905540 : Nat := 4983230072969 + 3 ^ 40 * 3905540 * 2
def baseEnd_3905540 : Nat := 2005419235360754790488755

theorem tailTrace_3905540 : CollatzResearch.WordTrace tailWord_3905540 prefixEnd_3905540 2005419235360754790488755 := by
  unfold tailWord_3905540
  simp only [CollatzResearch.WordTrace]
  refine ⟨71223373135451533986741037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94964497513935378648988049 71223373135451533986741037)
  ·
    refine ⟨26708764925794325245027889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71223373135451533986741037 26708764925794325245027889)
    ·
      refine ⟨20031573694345743933770917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26708764925794325245027889 20031573694345743933770917)
      ·
        refine ⟨3755920067689826987582047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20031573694345743933770917 3755920067689826987582047)
        ·
          refine ⟨5633880101534740481373071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3755920067689826987582047 5633880101534740481373071)
          ·
            refine ⟨8450820152302110722059607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5633880101534740481373071 8450820152302110722059607)
            ·
              refine ⟨12676230228453166083089411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8450820152302110722059607 12676230228453166083089411)
              ·
                refine ⟨19014345342679749124634117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12676230228453166083089411 19014345342679749124634117)
                ·
                  refine ⟨3565189751752452960868897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19014345342679749124634117 3565189751752452960868897)
                  ·
                    refine ⟨2673892313814339720651673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3565189751752452960868897 2673892313814339720651673)
                    ·
                      refine ⟨2005419235360754790488755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2673892313814339720651673 2005419235360754790488755)
                      ·
                        rfl

theorem cell23_3905540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_3905540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905540 prefixEnd_3905540 := by exact prefixLift 3905540
  have htrace : WordTrace (prefixWord ++ tailWord_3905540) baseStart_3905540 baseEnd_3905540 := by
    simpa [prefixWord, tailWord_3905540, baseEnd_3905540] using wordTrace_append hprefix tailTrace_3905540
  have hstable : (prefixWord ++ tailWord_3905540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905540).length < 2 ^ (prefixWord ++ tailWord_3905540).sum := by decide
  have hdescent : baseEnd_3905540 < baseStart_3905540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905579 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 4, 4, 2]
def baseStart_3905579 : Nat := 118140960795 + 3905579 * 2 ^ 59
def prefixEnd_3905579 : Nat := 4983230072969 + 3 ^ 40 * 3905579 * 2
def baseEnd_3905579 : Nat := 2005439261106280137901075

theorem tailTrace_3905579 : CollatzResearch.WordTrace tailWord_3905579 prefixEnd_3905579 2005439261106280137901075 := by
  unfold tailWord_3905579
  simp only [CollatzResearch.WordTrace]
  refine ⟨142448168717761777634151791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94965445811841185089434527 142448168717761777634151791)
  ·
    refine ⟨213672253076642666451227687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142448168717761777634151791 213672253076642666451227687)
    ·
      refine ⟨320508379614963999676841531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213672253076642666451227687 320508379614963999676841531)
      ·
        refine ⟨480762569422445999515262297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320508379614963999676841531 480762569422445999515262297)
        ·
          refine ⟨360571927066834499636446723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480762569422445999515262297 360571927066834499636446723)
          ·
            refine ⟨540857890600251749454670085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360571927066834499636446723 540857890600251749454670085)
            ·
              refine ⟨101410854487547203022750641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 540857890600251749454670085 101410854487547203022750641)
              ·
                refine ⟨76058140865660402267062981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101410854487547203022750641 76058140865660402267062981)
                ·
                  refine ⟨14260901412311325425074309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76058140865660402267062981 14260901412311325425074309)
                  ·
                    refine ⟨2673919014808373517201433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14260901412311325425074309 2673919014808373517201433)
                    ·
                      refine ⟨2005439261106280137901075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2673919014808373517201433 2005439261106280137901075)
                      ·
                        rfl

theorem cell23_3905579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 4, 2].length) (baseStart_3905579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905579 prefixEnd_3905579 := by exact prefixLift 3905579
  have htrace : WordTrace (prefixWord ++ tailWord_3905579) baseStart_3905579 baseEnd_3905579 := by
    simpa [prefixWord, tailWord_3905579, baseEnd_3905579] using wordTrace_append hprefix tailTrace_3905579
  have hstable : (prefixWord ++ tailWord_3905579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905579).length < 2 ^ (prefixWord ++ tailWord_3905579).sum := by decide
  have hdescent : baseEnd_3905579 < baseStart_3905579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905589 : List Nat := [1, 3, 3, 1, 1, 1, 2, 2, 5, 4]
def baseStart_3905589 : Nat := 118140960795 + 3905589 * 2 ^ 59
def prefixEnd_3905589 : Nat := 4983230072969 + 3 ^ 40 * 3905589 * 2
def baseEnd_3905589 : Nat := 668481465304275032925343

theorem tailTrace_3905589 : CollatzResearch.WordTrace tailWord_3905589 prefixEnd_3905589 668481465304275032925343 := by
  unfold tailWord_3905589
  simp only [CollatzResearch.WordTrace]
  refine ⟨142448533447725549342015821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94965688965150366228010547 142448533447725549342015821)
  ·
    refine ⟨53418200042897081003255933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142448533447725549342015821 53418200042897081003255933)
    ·
      refine ⟨20031825016086405376220975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53418200042897081003255933 20031825016086405376220975)
      ·
        refine ⟨30047737524129608064331463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20031825016086405376220975 30047737524129608064331463)
        ·
          refine ⟨45071606286194412096497195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30047737524129608064331463 45071606286194412096497195)
          ·
            refine ⟨67607409429291618144745793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45071606286194412096497195 67607409429291618144745793)
            ·
              refine ⟨50705557071968713608559345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67607409429291618144745793 50705557071968713608559345)
              ·
                refine ⟨38029167803976535206419509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50705557071968713608559345 38029167803976535206419509)
                ·
                  refine ⟨3565234481622800175601829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38029167803976535206419509 3565234481622800175601829)
                  ·
                    refine ⟨668481465304275032925343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3565234481622800175601829 668481465304275032925343)
                    ·
                      rfl

theorem cell23_3905589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_3905589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905589 prefixEnd_3905589 := by exact prefixLift 3905589
  have htrace : WordTrace (prefixWord ++ tailWord_3905589) baseStart_3905589 baseEnd_3905589 := by
    simpa [prefixWord, tailWord_3905589, baseEnd_3905589] using wordTrace_append hprefix tailTrace_3905589
  have hstable : (prefixWord ++ tailWord_3905589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905589).length < 2 ^ (prefixWord ++ tailWord_3905589).sum := by decide
  have hdescent : baseEnd_3905589 < baseStart_3905589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905599 : List Nat := [1, 1, 2, 2, 3, 1, 3, 1, 4, 2, 3]
def baseStart_3905599 : Nat := 118140960795 + 3905599 * 2 ^ 59
def prefixEnd_3905599 : Nat := 4983230072969 + 3 ^ 40 * 3905599 * 2
def baseEnd_3905599 : Nat := 2005449530719370059650983

theorem tailTrace_3905599 : CollatzResearch.WordTrace tailWord_3905599 prefixEnd_3905599 2005449530719370059650983 := by
  unfold tailWord_3905599
  simp only [CollatzResearch.WordTrace]
  refine ⟨142448898177689321049879851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94965932118459547366586567 142448898177689321049879851)
  ·
    refine ⟨213673347266533981574819777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142448898177689321049879851 213673347266533981574819777)
    ·
      refine ⟨160255010449900486181114833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213673347266533981574819777 160255010449900486181114833)
      ·
        refine ⟨120191257837425364635836125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160255010449900486181114833 120191257837425364635836125)
        ·
          refine ⟨45071721689034511738438547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120191257837425364635836125 45071721689034511738438547)
          ·
            refine ⟨67607582533551767607657821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45071721689034511738438547 67607582533551767607657821)
            ·
              refine ⟨25352843450081912852871683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67607582533551767607657821 25352843450081912852871683)
              ·
                refine ⟨38029265175122869279307525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25352843450081912852871683 38029265175122869279307525)
                ·
                  refine ⟨7130487220335537989870161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38029265175122869279307525 7130487220335537989870161)
                  ·
                    refine ⟨5347865415251653492402621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7130487220335537989870161 5347865415251653492402621)
                    ·
                      refine ⟨2005449530719370059650983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5347865415251653492402621 2005449530719370059650983)
                      ·
                        rfl

theorem cell23_3905599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 2, 3].length) (baseStart_3905599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905599 prefixEnd_3905599 := by exact prefixLift 3905599
  have htrace : WordTrace (prefixWord ++ tailWord_3905599) baseStart_3905599 baseEnd_3905599 := by
    simpa [prefixWord, tailWord_3905599, baseEnd_3905599] using wordTrace_append hprefix tailTrace_3905599
  have hstable : (prefixWord ++ tailWord_3905599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905599).length < 2 ^ (prefixWord ++ tailWord_3905599).sum := by decide
  have hdescent : baseEnd_3905599 < baseStart_3905599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905700 : List Nat := [2, 3, 1, 2, 4, 2, 2, 1, 1, 5]
def baseStart_3905700 : Nat := 118140960795 + 3905700 * 2 ^ 59
def prefixEnd_3905700 : Nat := 4983230072969 + 3 ^ 40 * 3905700 * 2
def baseEnd_3905700 : Nat := 668500464088491388162673

theorem tailTrace_3905700 : CollatzResearch.WordTrace tailWord_3905700 prefixEnd_3905700 668500464088491388162673 := by
  unfold tailWord_3905700
  simp only [CollatzResearch.WordTrace]
  refine ⟨71226290975161707649653277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94968387966882276866204369 71226290975161707649653277)
  ·
    refine ⟨26709859115685640368619979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71226290975161707649653277 26709859115685640368619979)
    ·
      refine ⟨40064788673528460552929969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26709859115685640368619979 40064788673528460552929969)
      ·
        refine ⟨30048591505146345414697477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40064788673528460552929969 30048591505146345414697477)
        ·
          refine ⟨5634110907214939765255777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30048591505146345414697477 5634110907214939765255777)
          ·
            refine ⟨4225583180411204823941833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5634110907214939765255777 4225583180411204823941833)
            ·
              refine ⟨3169187385308403617956375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4225583180411204823941833 3169187385308403617956375)
              ·
                refine ⟨4753781077962605426934563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3169187385308403617956375 4753781077962605426934563)
                ·
                  refine ⟨7130671616943908140401845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4753781077962605426934563 7130671616943908140401845)
                  ·
                    refine ⟨668500464088491388162673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7130671616943908140401845 668500464088491388162673)
                    ·
                      rfl

theorem cell23_3905700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 1, 5].length) (baseStart_3905700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905700 prefixEnd_3905700 := by exact prefixLift 3905700
  have htrace : WordTrace (prefixWord ++ tailWord_3905700) baseStart_3905700 baseEnd_3905700 := by
    simpa [prefixWord, tailWord_3905700, baseEnd_3905700] using wordTrace_append hprefix tailTrace_3905700
  have hstable : (prefixWord ++ tailWord_3905700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905700).length < 2 ^ (prefixWord ++ tailWord_3905700).sum := by decide
  have hdescent : baseEnd_3905700 < baseStart_3905700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905713 : List Nat := [1, 2, 2, 5, 2, 1, 1, 1, 4, 4]
def baseStart_3905713 : Nat := 118140960795 + 3905713 * 2 ^ 59
def prefixEnd_3905713 : Nat := 4983230072969 + 3 ^ 40 * 3905713 * 2
def baseEnd_3905713 : Nat := 668502689171327537875153

theorem tailTrace_3905713 : CollatzResearch.WordTrace tailWord_3905713 prefixEnd_3905713 668502689171327537875153 := by
  unfold tailWord_3905713
  simp only [CollatzResearch.WordTrace]
  refine ⟨142453056099276318519529793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94968704066184212346353195 142453056099276318519529793)
  ·
    refine ⟨106839792074457238889647345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142453056099276318519529793 106839792074457238889647345)
    ·
      refine ⟨80129844055842929167235509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106839792074457238889647345 80129844055842929167235509)
      ·
        refine ⟨7512172880235274609428329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80129844055842929167235509 7512172880235274609428329)
        ·
          refine ⟨5634129660176455957071247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7512172880235274609428329 5634129660176455957071247)
          ·
            refine ⟨8451194490264683935606871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5634129660176455957071247 8451194490264683935606871)
            ·
              refine ⟨12676791735397025903410307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8451194490264683935606871 12676791735397025903410307)
              ·
                refine ⟨19015187603095538855115461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12676791735397025903410307 19015187603095538855115461)
                ·
                  refine ⟨3565347675580413535334149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19015187603095538855115461 3565347675580413535334149)
                  ·
                    refine ⟨668502689171327537875153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3565347675580413535334149 668502689171327537875153)
                    ·
                      rfl

theorem cell23_3905713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 4, 4].length) (baseStart_3905713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905713 prefixEnd_3905713 := by exact prefixLift 3905713
  have htrace : WordTrace (prefixWord ++ tailWord_3905713) baseStart_3905713 baseEnd_3905713 := by
    simpa [prefixWord, tailWord_3905713, baseEnd_3905713] using wordTrace_append hprefix tailTrace_3905713
  have hstable : (prefixWord ++ tailWord_3905713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905713).length < 2 ^ (prefixWord ++ tailWord_3905713).sum := by decide
  have hdescent : baseEnd_3905713 < baseStart_3905713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905720 : List Nat := [2, 1, 2, 1, 2, 1, 3, 6, 1, 2, 2]
def baseStart_3905720 : Nat := 118140960795 + 3905720 * 2 ^ 59
def prefixEnd_3905720 : Nat := 4983230072969 + 3 ^ 40 * 3905720 * 2
def baseEnd_3905720 : Nat := 2005511661878564086237927

theorem tailTrace_3905720 : CollatzResearch.WordTrace tailWord_3905720 prefixEnd_3905720 2005511661878564086237927 := by
  unfold tailWord_3905720
  simp only [CollatzResearch.WordTrace]
  refine ⟨71226655705125479357517307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94968874273500639143356409 71226655705125479357517307)
  ·
    refine ⟨106839983557688219036275961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71226655705125479357517307 106839983557688219036275961)
    ·
      refine ⟨80129987668266164277206971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106839983557688219036275961 80129987668266164277206971)
      ·
        refine ⟨120194981502399246415810457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80129987668266164277206971 120194981502399246415810457)
        ·
          refine ⟨90146236126799434811857843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120194981502399246415810457 90146236126799434811857843)
          ·
            refine ⟨135219354190199152217786765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90146236126799434811857843 135219354190199152217786765)
            ·
              refine ⟨50707257821324682081670037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135219354190199152217786765 50707257821324682081670037)
              ·
                refine ⟨2376902710374594472578283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50707257821324682081670037 2376902710374594472578283)
                ·
                  refine ⟨3565354065561891708867425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2376902710374594472578283 3565354065561891708867425)
                  ·
                    refine ⟨2674015549171418781650569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3565354065561891708867425 2674015549171418781650569)
                    ·
                      refine ⟨2005511661878564086237927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2674015549171418781650569 2005511661878564086237927)
                      ·
                        rfl

theorem cell23_3905720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 6, 1, 2, 2].length) (baseStart_3905720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905720 prefixEnd_3905720 := by exact prefixLift 3905720
  have htrace : WordTrace (prefixWord ++ tailWord_3905720) baseStart_3905720 baseEnd_3905720 := by
    simpa [prefixWord, tailWord_3905720, baseEnd_3905720] using wordTrace_append hprefix tailTrace_3905720
  have hstable : (prefixWord ++ tailWord_3905720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905720).length < 2 ^ (prefixWord ++ tailWord_3905720).sum := by decide
  have hdescent : baseEnd_3905720 < baseStart_3905720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905730 : List Nat := [3, 5, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_3905730 : Nat := 118140960795 + 3905730 * 2 ^ 59
def prefixEnd_3905730 : Nat := 4983230072969 + 3 ^ 40 * 3905730 * 2
def baseEnd_3905730 : Nat := 668505598895036349037627

theorem tailTrace_3905730 : CollatzResearch.WordTrace tailWord_3905730 prefixEnd_3905730 668505598895036349037627 := by
  unfold tailWord_3905730
  simp only [CollatzResearch.WordTrace]
  refine ⟨35613419035053682605724661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94969117426809820281932429 35613419035053682605724661)
  ·
    refine ⟨3338758034536282744286687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35613419035053682605724661 3338758034536282744286687)
    ·
      refine ⟨5008137051804424116430031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3338758034536282744286687 5008137051804424116430031)
      ·
        refine ⟨7512205577706636174645047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5008137051804424116430031 7512205577706636174645047)
        ·
          refine ⟨11268308366559954261967571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7512205577706636174645047 11268308366559954261967571)
          ·
            refine ⟨16902462549839931392951357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11268308366559954261967571 16902462549839931392951357)
            ·
              refine ⟨6338423456189974272356759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16902462549839931392951357 6338423456189974272356759)
              ·
                refine ⟨9507635184284961408535139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6338423456189974272356759 9507635184284961408535139)
                ·
                  refine ⟨14261452776427442112802709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9507635184284961408535139 14261452776427442112802709)
                  ·
                    refine ⟨668505598895036349037627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14261452776427442112802709 668505598895036349037627)
                    ·
                      rfl

theorem cell23_3905730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_3905730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905730 prefixEnd_3905730 := by exact prefixLift 3905730
  have htrace : WordTrace (prefixWord ++ tailWord_3905730) baseStart_3905730 baseEnd_3905730 := by
    simpa [prefixWord, tailWord_3905730, baseEnd_3905730] using wordTrace_append hprefix tailTrace_3905730
  have hstable : (prefixWord ++ tailWord_3905730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905730).length < 2 ^ (prefixWord ++ tailWord_3905730).sum := by decide
  have hdescent : baseEnd_3905730 < baseStart_3905730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905759 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 4]
def baseStart_3905759 : Nat := 118140960795 + 3905759 * 2 ^ 59
def prefixEnd_3905759 : Nat := 4983230072969 + 3 ^ 40 * 3905759 * 2
def baseEnd_3905759 : Nat := 2005531687624089433650247

theorem tailTrace_3905759 : CollatzResearch.WordTrace tailWord_3905759 prefixEnd_3905759 2005531687624089433650247 := by
  unfold tailWord_3905759
  simp only [CollatzResearch.WordTrace]
  refine ⟨142454733857109668375704331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94969822571406445583802887 142454733857109668375704331)
  ·
    refine ⟨213682100785664502563556497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142454733857109668375704331 213682100785664502563556497)
    ·
      refine ⟨160261575589248376922667373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213682100785664502563556497 160261575589248376922667373)
      ·
        refine ⟨60098090845968141346000265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160261575589248376922667373 60098090845968141346000265)
        ·
          refine ⟨45073568134476106009500199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60098090845968141346000265 45073568134476106009500199)
          ·
            refine ⟨67610352201714159014250299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45073568134476106009500199 67610352201714159014250299)
            ·
              refine ⟨101415528302571238521375449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67610352201714159014250299 101415528302571238521375449)
              ·
                refine ⟨76061646226928428891031587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101415528302571238521375449 76061646226928428891031587)
                ·
                  refine ⟨114092469340392643336547381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76061646226928428891031587 114092469340392643336547381)
                  ·
                    refine ⟨10696169000661810312801317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114092469340392643336547381 10696169000661810312801317)
                    ·
                      refine ⟨2005531687624089433650247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10696169000661810312801317 2005531687624089433650247)
                      ·
                        rfl

theorem cell23_3905759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_3905759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905759 prefixEnd_3905759 := by exact prefixLift 3905759
  have htrace : WordTrace (prefixWord ++ tailWord_3905759) baseStart_3905759 baseEnd_3905759 := by
    simpa [prefixWord, tailWord_3905759, baseEnd_3905759] using wordTrace_append hprefix tailTrace_3905759
  have hstable : (prefixWord ++ tailWord_3905759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905759).length < 2 ^ (prefixWord ++ tailWord_3905759).sum := by decide
  have hdescent : baseEnd_3905759 < baseStart_3905759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905779 : List Nat := [1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 5]
def baseStart_3905779 : Nat := 118140960795 + 3905779 * 2 ^ 59
def prefixEnd_3905779 : Nat := 4983230072969 + 3 ^ 40 * 3905779 * 2
def baseEnd_3905779 : Nat := 2005541957237179355400155

theorem tailTrace_3905779 : CollatzResearch.WordTrace tailWord_3905779 prefixEnd_3905779 2005541957237179355400155 := by
  unfold tailWord_3905779
  simp only [CollatzResearch.WordTrace]
  refine ⟨142455463317037211791432391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94970308878024807860954927 142455463317037211791432391)
  ·
    refine ⟨213683194975555817687148587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142455463317037211791432391 213683194975555817687148587)
    ·
      refine ⟨320524792463333726530722881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213683194975555817687148587 320524792463333726530722881)
      ·
        refine ⟨240393594347500294898042161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320524792463333726530722881 240393594347500294898042161)
        ·
          refine ⟨180295195760625221173531621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240393594347500294898042161 180295195760625221173531621)
          ·
            refine ⟨33805349205117228970037179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180295195760625221173531621 33805349205117228970037179)
            ·
              refine ⟨50708023807675843455055769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33805349205117228970037179 50708023807675843455055769)
              ·
                refine ⟨38031017855756882591291827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50708023807675843455055769 38031017855756882591291827)
                ·
                  refine ⟨57046526783635323886937741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38031017855756882591291827 57046526783635323886937741)
                  ·
                    refine ⟨21392447543863246457601653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57046526783635323886937741 21392447543863246457601653)
                    ·
                      refine ⟨2005541957237179355400155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21392447543863246457601653 2005541957237179355400155)
                      ·
                        rfl

theorem cell23_3905779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 5].length) (baseStart_3905779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905779 prefixEnd_3905779 := by exact prefixLift 3905779
  have htrace : WordTrace (prefixWord ++ tailWord_3905779) baseStart_3905779 baseEnd_3905779 := by
    simpa [prefixWord, tailWord_3905779, baseEnd_3905779] using wordTrace_append hprefix tailTrace_3905779
  have hstable : (prefixWord ++ tailWord_3905779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905779).length < 2 ^ (prefixWord ++ tailWord_3905779).sum := by decide
  have hdescent : baseEnd_3905779 < baseStart_3905779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905789 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 2, 3, 6]
def baseStart_3905789 : Nat := 118140960795 + 3905789 * 2 ^ 59
def prefixEnd_3905789 : Nat := 4983230072969 + 3 ^ 40 * 3905789 * 2
def baseEnd_3905789 : Nat := 2005547092043724316275109

theorem tailTrace_3905789 : CollatzResearch.WordTrace tailWord_3905789 prefixEnd_3905789 2005547092043724316275109 := by
  unfold tailWord_3905789
  simp only [CollatzResearch.WordTrace]
  refine ⟨142455828047000983499296421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94970552031333988999530947 142455828047000983499296421)
  ·
    refine ⟨26710467758812684406118079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142455828047000983499296421 26710467758812684406118079)
    ·
      refine ⟨40065701638219026609177119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26710467758812684406118079 40065701638219026609177119)
      ·
        refine ⟨60098552457328539913765679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40065701638219026609177119 60098552457328539913765679)
        ·
          refine ⟨90147828685992809870648519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60098552457328539913765679 90147828685992809870648519)
          ·
            refine ⟨135221743028989214805972779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90147828685992809870648519 135221743028989214805972779)
            ·
              refine ⟨202832614543483822208959169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135221743028989214805972779 202832614543483822208959169)
              ·
                refine ⟨152124460907612866656719377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202832614543483822208959169 152124460907612866656719377)
                ·
                  refine ⟨114093345680709649992539533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152124460907612866656719377 114093345680709649992539533)
                  ·
                    refine ⟨42785004630266118747202325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 114093345680709649992539533 42785004630266118747202325)
                    ·
                      refine ⟨2005547092043724316275109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42785004630266118747202325 2005547092043724316275109)
                      ·
                        rfl

theorem cell23_3905789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_3905789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905789 prefixEnd_3905789 := by exact prefixLift 3905789
  have htrace : WordTrace (prefixWord ++ tailWord_3905789) baseStart_3905789 baseEnd_3905789 := by
    simpa [prefixWord, tailWord_3905789, baseEnd_3905789] using wordTrace_append hprefix tailTrace_3905789
  have hstable : (prefixWord ++ tailWord_3905789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905789).length < 2 ^ (prefixWord ++ tailWord_3905789).sum := by decide
  have hdescent : baseEnd_3905789 < baseStart_3905789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905793 : List Nat := [1, 2, 4, 1, 1, 2, 2, 3, 1, 4, 2]
def baseStart_3905793 : Nat := 118140960795 + 3905793 * 2 ^ 59
def prefixEnd_3905793 : Nat := 4983230072969 + 3 ^ 40 * 3905793 * 2
def baseEnd_3905793 : Nat := 2005549145966342300625091

theorem tailTrace_3905793 : CollatzResearch.WordTrace tailWord_3905793 prefixEnd_3905793 2005549145966342300625091 := by
  unfold tailWord_3905793
  simp only [CollatzResearch.WordTrace]
  refine ⟨142455973938986492182442033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94970649292657661454961355 142455973938986492182442033)
  ·
    refine ⟨106841980454239869136831525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142455973938986492182442033 106841980454239869136831525)
    ·
      refine ⟨20032871335169975463155911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106841980454239869136831525 20032871335169975463155911)
      ·
        refine ⟨30049307002754963194733867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20032871335169975463155911 30049307002754963194733867)
        ·
          refine ⟨45073960504132444792100801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30049307002754963194733867 45073960504132444792100801)
          ·
            refine ⟨33805470378099333594075601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45073960504132444792100801 33805470378099333594075601)
            ·
              refine ⟨25354102783574500195556701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33805470378099333594075601 25354102783574500195556701)
              ·
                refine ⟨9507788543840437573333763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25354102783574500195556701 9507788543840437573333763)
                ·
                  refine ⟨14261682815760656360000645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9507788543840437573333763 14261682815760656360000645)
                  ·
                    refine ⟨2674065527955123067500121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14261682815760656360000645 2674065527955123067500121)
                    ·
                      refine ⟨2005549145966342300625091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2674065527955123067500121 2005549145966342300625091)
                      ·
                        rfl

theorem cell23_3905793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_3905793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905793 prefixEnd_3905793 := by exact prefixLift 3905793
  have htrace : WordTrace (prefixWord ++ tailWord_3905793) baseStart_3905793 baseEnd_3905793 := by
    simpa [prefixWord, tailWord_3905793, baseEnd_3905793] using wordTrace_append hprefix tailTrace_3905793
  have hstable : (prefixWord ++ tailWord_3905793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905793).length < 2 ^ (prefixWord ++ tailWord_3905793).sum := by decide
  have hdescent : baseEnd_3905793 < baseStart_3905793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905893 : List Nat := [1, 3, 1, 3, 1, 3, 1, 3, 3, 4]
def baseStart_3905893 : Nat := 118140960795 + 3905893 * 2 ^ 59
def prefixEnd_3905893 : Nat := 4983230072969 + 3 ^ 40 * 3905893 * 2
def baseEnd_3905893 : Nat := 668533498010597303124877

theorem tailTrace_3905893 : CollatzResearch.WordTrace tailWord_3905893 prefixEnd_3905893 668533498010597303124877 := by
  unfold tailWord_3905893
  simp only [CollatzResearch.WordTrace]
  refine ⟨142459621238624209261082333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94973080825749472840721555 142459621238624209261082333)
  ·
    refine ⟨53422357964484078472905875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142459621238624209261082333 53422357964484078472905875)
    ·
      refine ⟨80133536946726117709358813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53422357964484078472905875 80133536946726117709358813)
      ·
        refine ⟨30050076355022294141009555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80133536946726117709358813 30050076355022294141009555)
        ·
          refine ⟨45075114532533441211514333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30050076355022294141009555 45075114532533441211514333)
          ·
            refine ⟨16903167949700040454317875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45075114532533441211514333 16903167949700040454317875)
            ·
              refine ⟨25354751924550060681476813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16903167949700040454317875 25354751924550060681476813)
              ·
                refine ⟨9508031971706272755553805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25354751924550060681476813 9508031971706272755553805)
                ·
                  refine ⟨3565511989389852283332677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9508031971706272755553805 3565511989389852283332677)
                  ·
                    refine ⟨668533498010597303124877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3565511989389852283332677 668533498010597303124877)
                    ·
                      rfl

theorem cell23_3905893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 3, 4].length) (baseStart_3905893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905893 prefixEnd_3905893 := by exact prefixLift 3905893
  have htrace : WordTrace (prefixWord ++ tailWord_3905893) baseStart_3905893 baseEnd_3905893 := by
    simpa [prefixWord, tailWord_3905893, baseEnd_3905893] using wordTrace_append hprefix tailTrace_3905893
  have hstable : (prefixWord ++ tailWord_3905893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905893).length < 2 ^ (prefixWord ++ tailWord_3905893).sum := by decide
  have hdescent : baseEnd_3905893 < baseStart_3905893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905944 : List Nat := [2, 1, 2, 5, 1, 2, 3, 2, 1, 4]
def baseStart_3905944 : Nat := 118140960795 + 3905944 * 2 ^ 59
def prefixEnd_3905944 : Nat := 4983230072969 + 3 ^ 40 * 3905944 * 2
def baseEnd_3905944 : Nat := 668542227181723736612299

theorem tailTrace_3905944 : CollatzResearch.WordTrace tailWord_3905944 prefixEnd_3905944 668542227181723736612299 := by
  unfold tailWord_3905944
  simp only [CollatzResearch.WordTrace]
  refine ⟨71230740680719722485594443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94974320907626296647459257 71230740680719722485594443)
  ·
    refine ⟨106846111021079583728391665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71230740680719722485594443 106846111021079583728391665)
    ·
      refine ⟨80134583265809687796293749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106846111021079583728391665 80134583265809687796293749)
      ·
        refine ⟨7512617181169658230902539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80134583265809687796293749 7512617181169658230902539)
        ·
          refine ⟨11268925771754487346353809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7512617181169658230902539 11268925771754487346353809)
          ·
            refine ⟨8451694328815865509765357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11268925771754487346353809 8451694328815865509765357)
            ·
              refine ⟨3169385373305949566162009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8451694328815865509765357 3169385373305949566162009)
              ·
                refine ⟨2377039029979462174621507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3169385373305949566162009 2377039029979462174621507)
                ·
                  refine ⟨3565558544969193261932261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2377039029979462174621507 3565558544969193261932261)
                  ·
                    refine ⟨668542227181723736612299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3565558544969193261932261 668542227181723736612299)
                    ·
                      rfl

theorem cell23_3905944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 2, 1, 4].length) (baseStart_3905944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905944 prefixEnd_3905944 := by exact prefixLift 3905944
  have htrace : WordTrace (prefixWord ++ tailWord_3905944) baseStart_3905944 baseEnd_3905944 := by
    simpa [prefixWord, tailWord_3905944, baseEnd_3905944] using wordTrace_append hprefix tailTrace_3905944
  have hstable : (prefixWord ++ tailWord_3905944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905944).length < 2 ^ (prefixWord ++ tailWord_3905944).sum := by decide
  have hdescent : baseEnd_3905944 < baseStart_3905944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905977 : List Nat := [1, 2, 1, 4, 3, 2, 2, 1, 2, 3, 2]
def baseStart_3905977 : Nat := 118140960795 + 3905977 * 2 ^ 59
def prefixEnd_3905977 : Nat := 4983230072969 + 3 ^ 40 * 3905977 * 2
def baseEnd_3905977 : Nat := 2005643626406769580724245

theorem tailTrace_3905977 : CollatzResearch.WordTrace tailWord_3905977 prefixEnd_3905977 2005643626406769580724245 := by
  unfold tailWord_3905977
  simp only [CollatzResearch.WordTrace]
  refine ⟨142462684970319891607140185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94975123313546594404760123 142462684970319891607140185)
  ·
    refine ⟨106847013727739918705355139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142462684970319891607140185 106847013727739918705355139)
    ·
      refine ⟨160270520591609878058032709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106847013727739918705355139 160270520591609878058032709)
      ·
        refine ⟨30050722610926852135881133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160270520591609878058032709 30050722610926852135881133)
        ·
          refine ⟨11269020979097569550955425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30050722610926852135881133 11269020979097569550955425)
          ·
            refine ⟨8451765734323177163216569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11269020979097569550955425 8451765734323177163216569)
            ·
              refine ⟨6338824300742382872412427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8451765734323177163216569 6338824300742382872412427)
              ·
                refine ⟨9508236451113574308618641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6338824300742382872412427 9508236451113574308618641)
                ·
                  refine ⟨7131177338335180731463981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9508236451113574308618641 7131177338335180731463981)
                  ·
                    refine ⟨2674191501875692774298993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7131177338335180731463981 2674191501875692774298993)
                    ·
                      refine ⟨2005643626406769580724245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2674191501875692774298993 2005643626406769580724245)
                      ·
                        rfl

theorem cell23_3905977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_3905977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905977 prefixEnd_3905977 := by exact prefixLift 3905977
  have htrace : WordTrace (prefixWord ++ tailWord_3905977) baseStart_3905977 baseEnd_3905977 := by
    simpa [prefixWord, tailWord_3905977, baseEnd_3905977] using wordTrace_append hprefix tailTrace_3905977
  have hstable : (prefixWord ++ tailWord_3905977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905977).length < 2 ^ (prefixWord ++ tailWord_3905977).sum := by decide
  have hdescent : baseEnd_3905977 < baseStart_3905977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905993 : List Nat := [1, 2, 1, 1, 2, 1, 7, 1, 1, 1, 5]
def baseStart_3905993 : Nat := 118140960795 + 3905993 * 2 ^ 59
def prefixEnd_3905993 : Nat := 4983230072969 + 3 ^ 40 * 3905993 * 2
def baseEnd_3905993 : Nat := 2005651842097241518124171

theorem tailTrace_3905993 : CollatzResearch.WordTrace tailWord_3905993 prefixEnd_3905993 2005651842097241518124171 := by
  unfold tailWord_3905993
  simp only [CollatzResearch.WordTrace]
  refine ⟨142463268538261926339722633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94975512358841284226481755 142463268538261926339722633)
  ·
    refine ⟨106847451403696444754791975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142463268538261926339722633 106847451403696444754791975)
    ·
      refine ⟨160271177105544667132187963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106847451403696444754791975 160271177105544667132187963)
      ·
        refine ⟨240406765658317000698281945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160271177105544667132187963 240406765658317000698281945)
        ·
          refine ⟨180305074243737750523711459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240406765658317000698281945 180305074243737750523711459)
          ·
            refine ⟨270457611365606625785567189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180305074243737750523711459 270457611365606625785567189)
            ·
              refine ⟨6338850266381405291849231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 270457611365606625785567189 6338850266381405291849231)
              ·
                refine ⟨9508275399572107937773847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6338850266381405291849231 9508275399572107937773847)
                ·
                  refine ⟨14262413099358161906660771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9508275399572107937773847 14262413099358161906660771)
                  ·
                    refine ⟨21393619649037242859991157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14262413099358161906660771 21393619649037242859991157)
                    ·
                      refine ⟨2005651842097241518124171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21393619649037242859991157 2005651842097241518124171)
                      ·
                        rfl

theorem cell23_3905993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 1, 5].length) (baseStart_3905993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905993 prefixEnd_3905993 := by exact prefixLift 3905993
  have htrace : WordTrace (prefixWord ++ tailWord_3905993) baseStart_3905993 baseEnd_3905993 := by
    simpa [prefixWord, tailWord_3905993, baseEnd_3905993] using wordTrace_append hprefix tailTrace_3905993
  have hstable : (prefixWord ++ tailWord_3905993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905993).length < 2 ^ (prefixWord ++ tailWord_3905993).sum := by decide
  have hdescent : baseEnd_3905993 < baseStart_3905993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905996 : List Nat := [2, 2, 1, 4, 14]
def baseStart_3905996 : Nat := 118140960795 + 3905996 * 2 ^ 59
def prefixEnd_3905996 : Nat := 4983230072969 + 3 ^ 40 * 3905996 * 2
def baseEnd_3905996 : Nat := 2751239207872709199433

theorem tailTrace_3905996 : CollatzResearch.WordTrace tailWord_3905996 prefixEnd_3905996 2751239207872709199433 := by
  unfold tailWord_3905996
  simp only [CollatzResearch.WordTrace]
  refine ⟨71231688978625528926040921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94975585304834038568054561 71231688978625528926040921)
  ·
    refine ⟨53423766733969146694530691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71231688978625528926040921 53423766733969146694530691)
    ·
      refine ⟨80135650100953720041796037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53423766733969146694530691 80135650100953720041796037)
      ·
        refine ⟨15025434393928822507836757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80135650100953720041796037 15025434393928822507836757)
        ·
          refine ⟨2751239207872709199433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 15025434393928822507836757 2751239207872709199433)
          ·
            rfl

theorem cell23_3905996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 14].length) (baseStart_3905996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3905996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3905996 prefixEnd_3905996 := by exact prefixLift 3905996
  have htrace : WordTrace (prefixWord ++ tailWord_3905996) baseStart_3905996 baseEnd_3905996 := by
    simpa [prefixWord, tailWord_3905996, baseEnd_3905996] using wordTrace_append hprefix tailTrace_3905996
  have hstable : (prefixWord ++ tailWord_3905996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905996).length < 2 ^ (prefixWord ++ tailWord_3905996).sum := by decide
  have hdescent : baseEnd_3905996 < baseStart_3905996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906030 : List Nat := [4, 1, 2, 1, 2, 3, 3, 7]
def baseStart_3906030 : Nat := 118140960795 + 3906030 * 2 ^ 59
def prefixEnd_3906030 : Nat := 4983230072969 + 3 ^ 40 * 3906030 * 2
def baseEnd_3906030 : Nat := 74284105217831773087463

theorem tailTrace_3906030 : CollatzResearch.WordTrace tailWord_3906030 prefixEnd_3906030 74284105217831773087463 := by
  unfold tailWord_3906030
  simp only [CollatzResearch.WordTrace]
  refine ⟨17808077254890985207352443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94976412026085254439213029 17808077254890985207352443)
  ·
    refine ⟨26712115882336477811028665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17808077254890985207352443 26712115882336477811028665)
    ·
      refine ⟨20034086911752358358271499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26712115882336477811028665 20034086911752358358271499)
      ·
        refine ⟨30051130367628537537407249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20034086911752358358271499 30051130367628537537407249)
        ·
          refine ⟨22538347775721403153055437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30051130367628537537407249 22538347775721403153055437)
          ·
            refine ⟨8451880415895526182395789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22538347775721403153055437 8451880415895526182395789)
            ·
              refine ⟨3169455155960822318398421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8451880415895526182395789 3169455155960822318398421)
              ·
                refine ⟨74284105217831773087463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3169455155960822318398421 74284105217831773087463)
                ·
                  rfl

theorem cell23_3906030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 7].length) (baseStart_3906030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906030 prefixEnd_3906030 := by exact prefixLift 3906030
  have htrace : WordTrace (prefixWord ++ tailWord_3906030) baseStart_3906030 baseEnd_3906030 := by
    simpa [prefixWord, tailWord_3906030, baseEnd_3906030] using wordTrace_append hprefix tailTrace_3906030
  have hstable : (prefixWord ++ tailWord_3906030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906030).length < 2 ^ (prefixWord ++ tailWord_3906030).sum := by decide
  have hdescent : baseEnd_3906030 < baseStart_3906030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906040 : List Nat := [2, 1, 2, 1, 1, 4, 2, 2, 4, 1, 3]
def baseStart_3906040 : Nat := 118140960795 + 3906040 * 2 ^ 59
def prefixEnd_3906040 : Nat := 4983230072969 + 3 ^ 40 * 3906040 * 2
def baseEnd_3906040 : Nat := 2005675975688002834236455

theorem tailTrace_3906040 : CollatzResearch.WordTrace tailWord_3906040 prefixEnd_3906040 2005675975688002834236455 := by
  unfold tailWord_3906040
  simp only [CollatzResearch.WordTrace]
  refine ⟨71232491384545826683341787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94976655179394435577789049 71232491384545826683341787)
  ·
    refine ⟨106848737076818740025012681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71232491384545826683341787 106848737076818740025012681)
    ·
      refine ⟨80136552807614055018759511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106848737076818740025012681 80136552807614055018759511)
      ·
        refine ⟨120204829211421082528139267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80136552807614055018759511 120204829211421082528139267)
        ·
          refine ⟨180307243817131623792208901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120204829211421082528139267 180307243817131623792208901)
          ·
            refine ⟨33807608215712179461039169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180307243817131623792208901 33807608215712179461039169)
            ·
              refine ⟨25355706161784134595779377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33807608215712179461039169 25355706161784134595779377)
              ·
                refine ⟨19016779621338100946834533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25355706161784134595779377 19016779621338100946834533)
                ·
                  refine ⟨3565646179000893927531475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19016779621338100946834533 3565646179000893927531475)
                  ·
                    refine ⟨5348469268501340891297213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3565646179000893927531475 5348469268501340891297213)
                    ·
                      refine ⟨2005675975688002834236455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5348469268501340891297213 2005675975688002834236455)
                      ·
                        rfl

theorem cell23_3906040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 4, 1, 3].length) (baseStart_3906040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906040 prefixEnd_3906040 := by exact prefixLift 3906040
  have htrace : WordTrace (prefixWord ++ tailWord_3906040) baseStart_3906040 baseEnd_3906040 := by
    simpa [prefixWord, tailWord_3906040, baseEnd_3906040] using wordTrace_append hprefix tailTrace_3906040
  have hstable : (prefixWord ++ tailWord_3906040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906040).length < 2 ^ (prefixWord ++ tailWord_3906040).sum := by decide
  have hdescent : baseEnd_3906040 < baseStart_3906040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906097 : List Nat := [1, 2, 2, 3, 1, 1, 3, 2, 4, 2, 2]
def baseStart_3906097 : Nat := 118140960795 + 3906097 * 2 ^ 59
def prefixEnd_3906097 : Nat := 4983230072969 + 3 ^ 40 * 3906097 * 2
def baseEnd_3906097 : Nat := 2005705244085309111223693

theorem tailTrace_3906097 : CollatzResearch.WordTrace tailWord_3906097 prefixEnd_3906097 2005705244085309111223693 := by
  unfold tailWord_3906097
  simp only [CollatzResearch.WordTrace]
  refine ⟨142467061729885152101508545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94978041153256768067672363 142467061729885152101508545)
  ·
    refine ⟨106850296297413864076131409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142467061729885152101508545 106850296297413864076131409)
    ·
      refine ⟨80137722223060398057098557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106850296297413864076131409 80137722223060398057098557)
      ·
        refine ⟨30051645833647649271411959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80137722223060398057098557 30051645833647649271411959)
        ·
          refine ⟨45077468750471473907117939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30051645833647649271411959 45077468750471473907117939)
          ·
            refine ⟨67616203125707210860676909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45077468750471473907117939 67616203125707210860676909)
            ·
              refine ⟨25356076172140204072753841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67616203125707210860676909 25356076172140204072753841)
              ·
                refine ⟨19017057129105153054565381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25356076172140204072753841 19017057129105153054565381)
                ·
                  refine ⟨3565698211707216197731009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19017057129105153054565381 3565698211707216197731009)
                  ·
                    refine ⟨2674273658780412148298257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3565698211707216197731009 2674273658780412148298257)
                    ·
                      refine ⟨2005705244085309111223693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2674273658780412148298257 2005705244085309111223693)
                      ·
                        rfl

theorem cell23_3906097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_3906097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906097 prefixEnd_3906097 := by exact prefixLift 3906097
  have htrace : WordTrace (prefixWord ++ tailWord_3906097) baseStart_3906097 baseEnd_3906097 := by
    simpa [prefixWord, tailWord_3906097, baseEnd_3906097] using wordTrace_append hprefix tailTrace_3906097
  have hstable : (prefixWord ++ tailWord_3906097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906097).length < 2 ^ (prefixWord ++ tailWord_3906097).sum := by decide
  have hdescent : baseEnd_3906097 < baseStart_3906097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906120 : List Nat := [2, 1, 3, 1, 1, 1, 1, 8, 5]
def baseStart_3906120 : Nat := 118140960795 + 3906120 * 2 ^ 59
def prefixEnd_3906120 : Nat := 4983230072969 + 3 ^ 40 * 3906120 * 2
def baseEnd_3906120 : Nat := 222857450460040280137343

theorem tailTrace_3906120 : CollatzResearch.WordTrace tailWord_3906120 prefixEnd_3906120 222857450460040280137343 := by
  unfold tailWord_3906120
  simp only [CollatzResearch.WordTrace]
  refine ⟨71233950304400913514797907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94978600405867884686397209 71233950304400913514797907)
  ·
    refine ⟨106850925456601370272196861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71233950304400913514797907 106850925456601370272196861)
    ·
      refine ⟨40069097046225513852073823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106850925456601370272196861 40069097046225513852073823)
      ·
        refine ⟨60103645569338270778110735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40069097046225513852073823 60103645569338270778110735)
        ·
          refine ⟨90155468354007406167166103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60103645569338270778110735 90155468354007406167166103)
          ·
            refine ⟨135233202531011109250749155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90155468354007406167166103 135233202531011109250749155)
            ·
              refine ⟨202849803796516663876123733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135233202531011109250749155 202849803796516663876123733)
              ·
                refine ⟨2377146138240429654798325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 202849803796516663876123733 2377146138240429654798325)
                ·
                  refine ⟨222857450460040280137343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2377146138240429654798325 222857450460040280137343)
                  ·
                    rfl

theorem cell23_3906120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 8, 5].length) (baseStart_3906120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906120 prefixEnd_3906120 := by exact prefixLift 3906120
  have htrace : WordTrace (prefixWord ++ tailWord_3906120) baseStart_3906120 baseEnd_3906120 := by
    simpa [prefixWord, tailWord_3906120, baseEnd_3906120] using wordTrace_append hprefix tailTrace_3906120
  have hstable : (prefixWord ++ tailWord_3906120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906120).length < 2 ^ (prefixWord ++ tailWord_3906120).sum := by decide
  have hdescent : baseEnd_3906120 < baseStart_3906120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906130 : List Nat := [3, 2, 2, 1, 2, 1, 2, 1, 1, 5, 3]
def baseStart_3906130 : Nat := 118140960795 + 3906130 * 2 ^ 59
def prefixEnd_3906130 : Nat := 4983230072969 + 3 ^ 40 * 3906130 * 2
def baseEnd_3906130 : Nat := 2005722188946907482111041

theorem tailTrace_3906130 : CollatzResearch.WordTrace tailWord_3906130 prefixEnd_3906130 2005722188946907482111041 := by
  unfold tailWord_3906130
  simp only [CollatzResearch.WordTrace]
  refine ⟨35617066334691399684364961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94978843559177065824973229 35617066334691399684364961)
  ·
    refine ⟨26712799751018549763273721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35617066334691399684364961 26712799751018549763273721)
    ·
      refine ⟨20034599813263912322455291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26712799751018549763273721 20034599813263912322455291)
      ·
        refine ⟨30051899719895868483682937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20034599813263912322455291 30051899719895868483682937)
        ·
          refine ⟨22538924789921901362762203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30051899719895868483682937 22538924789921901362762203)
          ·
            refine ⟨33808387184882852044143305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22538924789921901362762203 33808387184882852044143305)
            ·
              refine ⟨25356290388662139033107479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33808387184882852044143305 25356290388662139033107479)
              ·
                refine ⟨38034435582993208549661219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25356290388662139033107479 38034435582993208549661219)
                ·
                  refine ⟨57051653374489812824491829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38034435582993208549661219 57051653374489812824491829)
                  ·
                    refine ⟨5348592503858419952296109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57051653374489812824491829 5348592503858419952296109)
                    ·
                      refine ⟨2005722188946907482111041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5348592503858419952296109 2005722188946907482111041)
                      ·
                        rfl

theorem cell23_3906130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_3906130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906130 prefixEnd_3906130 := by exact prefixLift 3906130
  have htrace : WordTrace (prefixWord ++ tailWord_3906130) baseStart_3906130 baseEnd_3906130 := by
    simpa [prefixWord, tailWord_3906130, baseEnd_3906130] using wordTrace_append hprefix tailTrace_3906130
  have hstable : (prefixWord ++ tailWord_3906130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906130).length < 2 ^ (prefixWord ++ tailWord_3906130).sum := by decide
  have hdescent : baseEnd_3906130 < baseStart_3906130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906133 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 3, 7]
def baseStart_3906133 : Nat := 118140960795 + 3906133 * 2 ^ 59
def prefixEnd_3906133 : Nat := 4983230072969 + 3 ^ 40 * 3906133 * 2
def baseEnd_3906133 : Nat := 668574576462956990124509

theorem tailTrace_3906133 : CollatzResearch.WordTrace tailWord_3906133 prefixEnd_3906133 668574576462956990124509 := by
  unfold tailWord_3906133
  simp only [CollatzResearch.WordTrace]
  refine ⟨142468374757754730249819053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94978916505169820166546035 142468374757754730249819053)
  ·
    refine ⟨53425640534158023843682145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142468374757754730249819053 53425640534158023843682145)
    ·
      refine ⟨40069230400618517882761609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53425640534158023843682145 40069230400618517882761609)
      ·
        refine ⟨30051922800463888412071207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40069230400618517882761609 30051922800463888412071207)
        ·
          refine ⟨45077884200695832618106811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30051922800463888412071207 45077884200695832618106811)
          ·
            refine ⟨67616826301043748927160217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45077884200695832618106811 67616826301043748927160217)
            ·
              refine ⟨50712619725782811695370163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67616826301043748927160217 50712619725782811695370163)
              ·
                refine ⟨76068929588674217543055245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50712619725782811695370163 76068929588674217543055245)
                ·
                  refine ⟨28525848595752831578645717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76068929588674217543055245 28525848595752831578645717)
                  ·
                    refine ⟨668574576462956990124509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28525848595752831578645717 668574576462956990124509)
                    ·
                      rfl

theorem cell23_3906133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_3906133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906133 prefixEnd_3906133 := by exact prefixLift 3906133
  have htrace : WordTrace (prefixWord ++ tailWord_3906133) baseStart_3906133 baseEnd_3906133 := by
    simpa [prefixWord, tailWord_3906133, baseEnd_3906133] using wordTrace_append hprefix tailTrace_3906133
  have hstable : (prefixWord ++ tailWord_3906133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906133).length < 2 ^ (prefixWord ++ tailWord_3906133).sum := by decide
  have hdescent : baseEnd_3906133 < baseStart_3906133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906204 : List Nat := [2, 2, 3, 2, 2, 3, 1, 1, 2, 1, 4]
def baseStart_3906204 : Nat := 118140960795 + 3906204 * 2 ^ 59
def prefixEnd_3906204 : Nat := 4983230072969 + 3 ^ 40 * 3906204 * 2
def baseEnd_3906204 : Nat := 2005760186515340192585701

theorem tailTrace_3906204 : CollatzResearch.WordTrace tailWord_3906204 prefixEnd_3906204 2005760186515340192585701 := by
  unfold tailWord_3906204
  simp only [CollatzResearch.WordTrace]
  refine ⟨71235482170248754687826833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94980642893665006250435777 71235482170248754687826833)
  ·
    refine ⟨53426611627686566015870125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71235482170248754687826833 53426611627686566015870125)
    ·
      refine ⟨20034979360382462255951297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53426611627686566015870125 20034979360382462255951297)
      ·
        refine ⟨15026234520286846691963473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20034979360382462255951297 15026234520286846691963473)
        ·
          refine ⟨11269675890215135018972605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15026234520286846691963473 11269675890215135018972605)
          ·
            refine ⟨4226128458830675632114727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11269675890215135018972605 4226128458830675632114727)
            ·
              refine ⟨6339192688246013448172091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4226128458830675632114727 6339192688246013448172091)
              ·
                refine ⟨9508789032369020172258137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6339192688246013448172091 9508789032369020172258137)
                ·
                  refine ⟨7131591774276765129193603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9508789032369020172258137 7131591774276765129193603)
                  ·
                    refine ⟨10697387661415147693790405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7131591774276765129193603 10697387661415147693790405)
                    ·
                      refine ⟨2005760186515340192585701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10697387661415147693790405 2005760186515340192585701)
                      ·
                        rfl

theorem cell23_3906204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_3906204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906204 prefixEnd_3906204 := by exact prefixLift 3906204
  have htrace : WordTrace (prefixWord ++ tailWord_3906204) baseStart_3906204 baseEnd_3906204 := by
    simpa [prefixWord, tailWord_3906204, baseEnd_3906204] using wordTrace_append hprefix tailTrace_3906204
  have hstable : (prefixWord ++ tailWord_3906204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906204).length < 2 ^ (prefixWord ++ tailWord_3906204).sum := by decide
  have hdescent : baseEnd_3906204 < baseStart_3906204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906227 : List Nat := [1, 1, 1, 2, 3, 6, 1, 2, 6]
def baseStart_3906227 : Nat := 118140960795 + 3906227 * 2 ^ 59
def prefixEnd_3906227 : Nat := 4983230072969 + 3 ^ 40 * 3906227 * 2
def baseEnd_3906227 : Nat := 222863555174488178066455

theorem tailTrace_3906227 : CollatzResearch.WordTrace tailWord_3906227 prefixEnd_3906227 222863555174488178066455 := by
  unfold tailWord_3906227
  simp only [CollatzResearch.WordTrace]
  refine ⟨142471803219414184303740935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94981202146276122869160623 142471803219414184303740935)
  ·
    refine ⟨213707704829121276455611403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142471803219414184303740935 213707704829121276455611403)
    ·
      refine ⟨320561557243681914683417105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213707704829121276455611403 320561557243681914683417105)
      ·
        refine ⟨240421167932761436012562829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320561557243681914683417105 240421167932761436012562829)
        ·
          refine ⟨90157937974785538504711061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240421167932761436012562829 90157937974785538504711061)
          ·
            refine ⟨4226153342568072117408331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 90157937974785538504711061 4226153342568072117408331)
            ·
              refine ⟨6339230013852108176112497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4226153342568072117408331 6339230013852108176112497)
              ·
                refine ⟨4754422510389081132084373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6339230013852108176112497 4754422510389081132084373)
                ·
                  refine ⟨222863555174488178066455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4754422510389081132084373 222863555174488178066455)
                  ·
                    rfl

theorem cell23_3906227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 6].length) (baseStart_3906227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906227 prefixEnd_3906227 := by exact prefixLift 3906227
  have htrace : WordTrace (prefixWord ++ tailWord_3906227) baseStart_3906227 baseEnd_3906227 := by
    simpa [prefixWord, tailWord_3906227, baseEnd_3906227] using wordTrace_append hprefix tailTrace_3906227
  have hstable : (prefixWord ++ tailWord_3906227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906227).length < 2 ^ (prefixWord ++ tailWord_3906227).sum := by decide
  have hdescent : baseEnd_3906227 < baseStart_3906227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906244 : List Nat := [2, 3, 3, 1, 1, 3, 3, 1, 6]
def baseStart_3906244 : Nat := 118140960795 + 3906244 * 2 ^ 59
def prefixEnd_3906244 : Nat := 4983230072969 + 3 ^ 40 * 3906244 * 2
def baseEnd_3906244 : Nat := 222864525082391115120613

theorem tailTrace_3906244 : CollatzResearch.WordTrace tailWord_3906244 prefixEnd_3906244 222864525082391115120613 := by
  unfold tailWord_3906244
  simp only [CollatzResearch.WordTrace]
  refine ⟨71236211630176298103554893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94981615506901730804739857 71236211630176298103554893)
  ·
    refine ⟨26713579361316111788833085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71236211630176298103554893 26713579361316111788833085)
    ·
      refine ⟨10017592260493541920812407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26713579361316111788833085 10017592260493541920812407)
      ·
        refine ⟨15026388390740312881218611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10017592260493541920812407 15026388390740312881218611)
        ·
          refine ⟨22539582586110469321827917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15026388390740312881218611 22539582586110469321827917)
          ·
            refine ⟨8452343469791425995685469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22539582586110469321827917 8452343469791425995685469)
            ·
              refine ⟨3169628801171784748382051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8452343469791425995685469 3169628801171784748382051)
              ·
                refine ⟨4754443201757677122573077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3169628801171784748382051 4754443201757677122573077)
                ·
                  refine ⟨222864525082391115120613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4754443201757677122573077 222864525082391115120613)
                  ·
                    rfl

theorem cell23_3906244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 6].length) (baseStart_3906244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906244 prefixEnd_3906244 := by exact prefixLift 3906244
  have htrace : WordTrace (prefixWord ++ tailWord_3906244) baseStart_3906244 baseEnd_3906244 := by
    simpa [prefixWord, tailWord_3906244, baseEnd_3906244] using wordTrace_append hprefix tailTrace_3906244
  have hstable : (prefixWord ++ tailWord_3906244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906244).length < 2 ^ (prefixWord ++ tailWord_3906244).sum := by decide
  have hdescent : baseEnd_3906244 < baseStart_3906244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906247 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 6, 3, 2]
def baseStart_3906247 : Nat := 118140960795 + 3906247 * 2 ^ 59
def prefixEnd_3906247 : Nat := 4983230072969 + 3 ^ 40 * 3906247 * 2
def baseEnd_3906247 : Nat := 2005782266183483524348003

theorem tailTrace_3906247 : CollatzResearch.WordTrace tailWord_3906247 prefixEnd_3906247 2005782266183483524348003 := by
  unfold tailWord_3906247
  simp only [CollatzResearch.WordTrace]
  refine ⟨142472532679341727719468995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94981688452894485146312663 142472532679341727719468995)
  ·
    refine ⟨213708799019012591579203493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142472532679341727719468995 213708799019012591579203493)
    ·
      refine ⟨40070399816064860921100655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213708799019012591579203493 40070399816064860921100655)
      ·
        refine ⟨60105599724097291381650983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40070399816064860921100655 60105599724097291381650983)
        ·
          refine ⟨90158399586145937072476475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60105599724097291381650983 90158399586145937072476475)
          ·
            refine ⟨135237599379218905608714713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90158399586145937072476475 135237599379218905608714713)
            ·
              refine ⟨101428199534414179206536035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135237599379218905608714713 101428199534414179206536035)
              ·
                refine ⟨152142299301621268809804053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101428199534414179206536035 152142299301621268809804053)
                ·
                  refine ⟨7131670279763496975459565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 152142299301621268809804053 7131670279763496975459565)
                  ·
                    refine ⟨2674376354911311365797337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7131670279763496975459565 2674376354911311365797337)
                    ·
                      refine ⟨2005782266183483524348003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2674376354911311365797337 2005782266183483524348003)
                      ·
                        rfl

theorem cell23_3906247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 3, 2].length) (baseStart_3906247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906247 prefixEnd_3906247 := by exact prefixLift 3906247
  have htrace : WordTrace (prefixWord ++ tailWord_3906247) baseStart_3906247 baseEnd_3906247 := by
    simpa [prefixWord, tailWord_3906247, baseEnd_3906247] using wordTrace_append hprefix tailTrace_3906247
  have hstable : (prefixWord ++ tailWord_3906247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906247).length < 2 ^ (prefixWord ++ tailWord_3906247).sum := by decide
  have hdescent : baseEnd_3906247 < baseStart_3906247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906254 : List Nat := [4, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3]
def baseStart_3906254 : Nat := 118140960795 + 3906254 * 2 ^ 59
def prefixEnd_3906254 : Nat := 4983230072969 + 3 ^ 40 * 3906254 * 2
def baseEnd_3906254 : Nat := 2005785860548064996960471

theorem tailTrace_3906254 : CollatzResearch.WordTrace tailWord_3906254 prefixEnd_3906254 2005785860548064996960471 := by
  unfold tailWord_3906254
  simp only [CollatzResearch.WordTrace]
  refine ⟨17809098498789545989371727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94981858660210911943315877 17809098498789545989371727)
  ·
    refine ⟨26713647748184318984057591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17809098498789545989371727 26713647748184318984057591)
    ·
      refine ⟨40070471622276478476086387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26713647748184318984057591 40070471622276478476086387)
      ·
        refine ⟨60105707433414717714129581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40070471622276478476086387 60105707433414717714129581)
        ·
          refine ⟨22539640287530519142798593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60105707433414717714129581 22539640287530519142798593)
          ·
            refine ⟨16904730215647889357098945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22539640287530519142798593 16904730215647889357098945)
            ·
              refine ⟨12678547661735917017824209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16904730215647889357098945 12678547661735917017824209)
              ·
                refine ⟨9508910746301937763368157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12678547661735917017824209 9508910746301937763368157)
                ·
                  refine ⟨3565841529863226661263059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9508910746301937763368157 3565841529863226661263059)
                  ·
                    refine ⟨5348762294794839991894589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3565841529863226661263059 5348762294794839991894589)
                    ·
                      refine ⟨2005785860548064996960471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5348762294794839991894589 2005785860548064996960471)
                      ·
                        rfl

theorem cell23_3906254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3].length) (baseStart_3906254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906254 prefixEnd_3906254 := by exact prefixLift 3906254
  have htrace : WordTrace (prefixWord ++ tailWord_3906254) baseStart_3906254 baseEnd_3906254 := by
    simpa [prefixWord, tailWord_3906254, baseEnd_3906254] using wordTrace_append hprefix tailTrace_3906254
  have hstable : (prefixWord ++ tailWord_3906254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906254).length < 2 ^ (prefixWord ++ tailWord_3906254).sum := by decide
  have hdescent : baseEnd_3906254 < baseStart_3906254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906257 : List Nat := [1, 2, 2, 1, 2, 3, 4, 2, 1, 5]
def baseStart_3906257 : Nat := 118140960795 + 3906257 * 2 ^ 59
def prefixEnd_3906257 : Nat := 4983230072969 + 3 ^ 40 * 3906257 * 2
def baseEnd_3906257 : Nat := 668595800330009495074319

theorem tailTrace_3906257 : CollatzResearch.WordTrace tailWord_3906257 prefixEnd_3906257 668595800330009495074319 := by
  unfold tailWord_3906257
  simp only [CollatzResearch.WordTrace]
  refine ⟨142472897409305499427333025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94981931606203666284888683 142472897409305499427333025)
  ·
    refine ⟨106854673056979124570499769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142472897409305499427333025 106854673056979124570499769)
    ·
      refine ⟨80141004792734343427874827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106854673056979124570499769 80141004792734343427874827)
      ·
        refine ⟨120211507189101515141812241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80141004792734343427874827 120211507189101515141812241)
        ·
          refine ⟨90158630391826136356359181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120211507189101515141812241 90158630391826136356359181)
          ·
            refine ⟨33809486396934801133634693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90158630391826136356359181 33809486396934801133634693)
            ·
              refine ⟨6339278699425275212556505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33809486396934801133634693 6339278699425275212556505)
              ·
                refine ⟨4754459024568956409417379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6339278699425275212556505 4754459024568956409417379)
                ·
                  refine ⟨7131688536853434614126069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4754459024568956409417379 7131688536853434614126069)
                  ·
                    refine ⟨668595800330009495074319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7131688536853434614126069 668595800330009495074319)
                    ·
                      rfl

theorem cell23_3906257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 5].length) (baseStart_3906257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906257 prefixEnd_3906257 := by exact prefixLift 3906257
  have htrace : WordTrace (prefixWord ++ tailWord_3906257) baseStart_3906257 baseEnd_3906257 := by
    simpa [prefixWord, tailWord_3906257, baseEnd_3906257] using wordTrace_append hprefix tailTrace_3906257
  have hstable : (prefixWord ++ tailWord_3906257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906257).length < 2 ^ (prefixWord ++ tailWord_3906257).sum := by decide
  have hdescent : baseEnd_3906257 < baseStart_3906257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906271 : List Nat := [1, 1, 2, 3, 2, 3, 3, 3, 1, 1, 3]
def baseStart_3906271 : Nat := 118140960795 + 3906271 * 2 ^ 59
def prefixEnd_3906271 : Nat := 4983230072969 + 3 ^ 40 * 3906271 * 2
def baseEnd_3906271 : Nat := 2005794589719191430447893

theorem tailTrace_3906271 : CollatzResearch.WordTrace tailWord_3906271 prefixEnd_3906271 2005794589719191430447893 := by
  unfold tailWord_3906271
  simp only [CollatzResearch.WordTrace]
  refine ⟨142473408031254779818342667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94982272020836519878895111 142473408031254779818342667)
  ·
    refine ⟨213710112046882169727514001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142473408031254779818342667 213710112046882169727514001)
    ·
      refine ⟨160282584035161627295635501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213710112046882169727514001 160282584035161627295635501)
      ·
        refine ⟨60105969013185610235863313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160282584035161627295635501 60105969013185610235863313)
        ·
          refine ⟨45079476759889207676897485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60105969013185610235863313 45079476759889207676897485)
          ·
            refine ⟨16904803784958452878836557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45079476759889207676897485 16904803784958452878836557)
            ·
              refine ⟨6339301419359419829563709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16904803784958452878836557 6339301419359419829563709)
              ·
                refine ⟨2377238032259782436086391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6339301419359419829563709 2377238032259782436086391)
                ·
                  refine ⟨3565857048389673654129587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2377238032259782436086391 3565857048389673654129587)
                  ·
                    refine ⟨5348785572584510481194381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3565857048389673654129587 5348785572584510481194381)
                    ·
                      refine ⟨2005794589719191430447893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5348785572584510481194381 2005794589719191430447893)
                      ·
                        rfl

theorem cell23_3906271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 3, 1, 1, 3].length) (baseStart_3906271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906271 prefixEnd_3906271 := by exact prefixLift 3906271
  have htrace : WordTrace (prefixWord ++ tailWord_3906271) baseStart_3906271 baseEnd_3906271 := by
    simpa [prefixWord, tailWord_3906271, baseEnd_3906271] using wordTrace_append hprefix tailTrace_3906271
  have hstable : (prefixWord ++ tailWord_3906271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906271).length < 2 ^ (prefixWord ++ tailWord_3906271).sum := by decide
  have hdescent : baseEnd_3906271 < baseStart_3906271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906287 : List Nat := [1, 1, 2, 1, 5, 2, 2, 1, 4, 4]
def baseStart_3906287 : Nat := 118140960795 + 3906287 * 2 ^ 59
def prefixEnd_3906287 : Nat := 4983230072969 + 3 ^ 40 * 3906287 * 2
def baseEnd_3906287 : Nat := 668600935136554455949273

theorem tailTrace_3906287 : CollatzResearch.WordTrace tailWord_3906287 prefixEnd_3906287 668600935136554455949273 := by
  unfold tailWord_3906287
  simp only [CollatzResearch.WordTrace]
  refine ⟨142473991599196814550925115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94982661066131209700616743 142473991599196814550925115)
  ·
    refine ⟨213710987398795221826387673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142473991599196814550925115 213710987398795221826387673)
    ·
      refine ⟨160283240549096416369790755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213710987398795221826387673 160283240549096416369790755)
      ·
        refine ⟨240424860823644624554686133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160283240549096416369790755 240424860823644624554686133)
        ·
          refine ⟨22539830702216683552001825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 240424860823644624554686133 22539830702216683552001825)
          ·
            refine ⟨16904873026662512664001369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22539830702216683552001825 16904873026662512664001369)
            ·
              refine ⟨12678654769996884498001027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16904873026662512664001369 12678654769996884498001027)
              ·
                refine ⟨19017982154995326747001541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12678654769996884498001027 19017982154995326747001541)
                ·
                  refine ⟨3565871654061623765062789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19017982154995326747001541 3565871654061623765062789)
                  ·
                    refine ⟨668600935136554455949273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3565871654061623765062789 668600935136554455949273)
                    ·
                      rfl

theorem cell23_3906287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 4, 4].length) (baseStart_3906287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906287 prefixEnd_3906287 := by exact prefixLift 3906287
  have htrace : WordTrace (prefixWord ++ tailWord_3906287) baseStart_3906287 baseEnd_3906287 := by
    simpa [prefixWord, tailWord_3906287, baseEnd_3906287] using wordTrace_append hprefix tailTrace_3906287
  have hstable : (prefixWord ++ tailWord_3906287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906287).length < 2 ^ (prefixWord ++ tailWord_3906287).sum := by decide
  have hdescent : baseEnd_3906287 < baseStart_3906287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906300 : List Nat := [2, 2, 2, 1, 3, 2, 1, 10]
def baseStart_3906300 : Nat := 118140960795 + 3906300 * 2 ^ 59
def prefixEnd_3906300 : Nat := 4983230072969 + 3 ^ 40 * 3906300 * 2
def baseEnd_3906300 : Nat := 74289240024376733962417

theorem tailTrace_3906300 : CollatzResearch.WordTrace tailWord_3906300 prefixEnd_3906300 74289240024376733962417 := by
  unfold tailWord_3906300
  simp only [CollatzResearch.WordTrace]
  refine ⟨71237232874074858885574177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94982977165433145180765569 71237232874074858885574177)
  ·
    refine ⟨53427924655556144164180633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71237232874074858885574177 53427924655556144164180633)
    ·
      refine ⟨40070943491667108123135475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53427924655556144164180633 40070943491667108123135475)
      ·
        refine ⟨60106415237500662184703213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40070943491667108123135475 60106415237500662184703213)
        ·
          refine ⟨22539905714062748319263705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60106415237500662184703213 22539905714062748319263705)
          ·
            refine ⟨16904929285547061239447779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22539905714062748319263705 16904929285547061239447779)
            ·
              refine ⟨25357393928320591859171669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16904929285547061239447779 25357393928320591859171669)
              ·
                refine ⟨74289240024376733962417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 25357393928320591859171669 74289240024376733962417)
                ·
                  rfl

theorem cell23_3906300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 10].length) (baseStart_3906300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906300 prefixEnd_3906300 := by exact prefixLift 3906300
  have htrace : WordTrace (prefixWord ++ tailWord_3906300) baseStart_3906300 baseEnd_3906300 := by
    simpa [prefixWord, tailWord_3906300, baseEnd_3906300] using wordTrace_append hprefix tailTrace_3906300
  have hstable : (prefixWord ++ tailWord_3906300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906300).length < 2 ^ (prefixWord ++ tailWord_3906300).sum := by decide
  have hdescent : baseEnd_3906300 < baseStart_3906300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906311 : List Nat := [1, 1, 4, 4, 1, 3, 1, 2, 1, 1, 4]
def baseStart_3906311 : Nat := 118140960795 + 3906311 * 2 ^ 59
def prefixEnd_3906311 : Nat := 4983230072969 + 3 ^ 40 * 3906311 * 2
def baseEnd_3906311 : Nat := 2005815128945371273947709

theorem tailTrace_3906311 : CollatzResearch.WordTrace tailWord_3906311 prefixEnd_3906311 2005815128945371273947709 := by
  unfold tailWord_3906311
  simp only [CollatzResearch.WordTrace]
  refine ⟨142474866951109866649798787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94983244634073244433199191 142474866951109866649798787)
  ·
    refine ⟨213712300426664799974698181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142474866951109866649798787 213712300426664799974698181)
    ·
      refine ⟨40071056329999649995255909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213712300426664799974698181 40071056329999649995255909)
      ·
        refine ⟨7513323061874934374110483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40071056329999649995255909 7513323061874934374110483)
        ·
          refine ⟨11269984592812401561165725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7513323061874934374110483 11269984592812401561165725)
          ·
            refine ⟨4226244222304650585437147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11269984592812401561165725 4226244222304650585437147)
            ·
              refine ⟨6339366333456975878155721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4226244222304650585437147 6339366333456975878155721)
              ·
                refine ⟨4754524750092731908616791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6339366333456975878155721 4754524750092731908616791)
                ·
                  refine ⟨7131787125139097862925187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4754524750092731908616791 7131787125139097862925187)
                  ·
                    refine ⟨10697680687708646794387781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7131787125139097862925187 10697680687708646794387781)
                    ·
                      refine ⟨2005815128945371273947709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10697680687708646794387781 2005815128945371273947709)
                      ·
                        rfl

theorem cell23_3906311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_3906311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906311 prefixEnd_3906311 := by exact prefixLift 3906311
  have htrace : WordTrace (prefixWord ++ tailWord_3906311) baseStart_3906311 baseEnd_3906311 := by
    simpa [prefixWord, tailWord_3906311, baseEnd_3906311] using wordTrace_append hprefix tailTrace_3906311
  have hstable : (prefixWord ++ tailWord_3906311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906311).length < 2 ^ (prefixWord ++ tailWord_3906311).sum := by decide
  have hdescent : baseEnd_3906311 < baseStart_3906311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906354 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2]
def baseStart_3906354 : Nat := 118140960795 + 3906354 * 2 ^ 59
def prefixEnd_3906354 : Nat := 4983230072969 + 3 ^ 40 * 3906354 * 2
def baseEnd_3906354 : Nat := 2005837208613514605710011

theorem tailTrace_3906354 : CollatzResearch.WordTrace tailWord_3906354 prefixEnd_3906354 2005837208613514605710011 := by
  unfold tailWord_3906354
  simp only [CollatzResearch.WordTrace]
  refine ⟨35619108822488521248403529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94984290193302723329076077 35619108822488521248403529)
  ·
    refine ⟨26714331616866390936302647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35619108822488521248403529 26714331616866390936302647)
    ·
      refine ⟨40071497425299586404453971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26714331616866390936302647 40071497425299586404453971)
      ·
        refine ⟨60107246137949379606680957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40071497425299586404453971 60107246137949379606680957)
        ·
          refine ⟨22540217301731017352505359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60107246137949379606680957 22540217301731017352505359)
          ·
            refine ⟨33810325952596526028758039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22540217301731017352505359 33810325952596526028758039)
            ·
              refine ⟨50715488928894789043137059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33810325952596526028758039 50715488928894789043137059)
              ·
                refine ⟨76073233393342183564705589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50715488928894789043137059 76073233393342183564705589)
                ·
                  refine ⟨7131865630625829709191149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76073233393342183564705589 7131865630625829709191149)
                  ·
                    refine ⟨2674449611484686140946681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7131865630625829709191149 2674449611484686140946681)
                    ·
                      refine ⟨2005837208613514605710011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2674449611484686140946681 2005837208613514605710011)
                      ·
                        rfl

theorem cell23_3906354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2].length) (baseStart_3906354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906354 prefixEnd_3906354 := by exact prefixLift 3906354
  have htrace : WordTrace (prefixWord ++ tailWord_3906354) baseStart_3906354 baseEnd_3906354 := by
    simpa [prefixWord, tailWord_3906354, baseEnd_3906354] using wordTrace_append hprefix tailTrace_3906354
  have hstable : (prefixWord ++ tailWord_3906354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906354).length < 2 ^ (prefixWord ++ tailWord_3906354).sum := by decide
  have hdescent : baseEnd_3906354 < baseStart_3906354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906384 : List Nat := [2, 1, 1, 1, 1, 4, 4, 2, 1, 4, 2]
def baseStart_3906384 : Nat := 118140960795 + 3906384 * 2 ^ 59
def prefixEnd_3906384 : Nat := 4983230072969 + 3 ^ 40 * 3906384 * 2
def baseEnd_3906384 : Nat := 2005852613033149488334873

theorem tailTrace_3906384 : CollatzResearch.WordTrace tailWord_3906384 prefixEnd_3906384 2005852613033149488334873 := by
  unfold tailWord_3906384
  simp only [CollatzResearch.WordTrace]
  refine ⟨71238764739922700058603103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94985019653230266744804137 71238764739922700058603103)
  ·
    refine ⟨106858147109884050087904655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71238764739922700058603103 106858147109884050087904655)
    ·
      refine ⟨160287220664826075131856983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106858147109884050087904655 160287220664826075131856983)
      ·
        refine ⟨240430830997239112697785475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160287220664826075131856983 240430830997239112697785475)
        ·
          refine ⟨360646246495858669046678213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240430830997239112697785475 360646246495858669046678213)
          ·
            refine ⟨67621171217973500446252165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 360646246495858669046678213 67621171217973500446252165)
            ·
              refine ⟨12678969603370031333672281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67621171217973500446252165 12678969603370031333672281)
              ·
                refine ⟨9509227202527523500254211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12678969603370031333672281 9509227202527523500254211)
                ·
                  refine ⟨14263840803791285250381317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9509227202527523500254211 14263840803791285250381317)
                  ·
                    refine ⟨2674470150710865984446497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14263840803791285250381317 2674470150710865984446497)
                    ·
                      refine ⟨2005852613033149488334873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2674470150710865984446497 2005852613033149488334873)
                      ·
                        rfl

theorem cell23_3906384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 1, 4, 2].length) (baseStart_3906384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906384 prefixEnd_3906384 := by exact prefixLift 3906384
  have htrace : WordTrace (prefixWord ++ tailWord_3906384) baseStart_3906384 baseEnd_3906384 := by
    simpa [prefixWord, tailWord_3906384, baseEnd_3906384] using wordTrace_append hprefix tailTrace_3906384
  have hstable : (prefixWord ++ tailWord_3906384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906384).length < 2 ^ (prefixWord ++ tailWord_3906384).sum := by decide
  have hdescent : baseEnd_3906384 < baseStart_3906384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906388 : List Nat := [2, 4, 1, 1, 4, 1, 1, 3, 1, 3, 2]
def baseStart_3906388 : Nat := 118140960795 + 3906388 * 2 ^ 59
def prefixEnd_3906388 : Nat := 4983230072969 + 3 ^ 40 * 3906388 * 2
def baseEnd_3906388 : Nat := 2005854666955767472684855

theorem tailTrace_3906388 : CollatzResearch.WordTrace tailWord_3906388 prefixEnd_3906388 2005854666955767472684855 := by
  unfold tailWord_3906388
  simp only [CollatzResearch.WordTrace]
  refine ⟨71238837685915454400175909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94985116914553939200234545 71238837685915454400175909)
  ·
    refine ⟨13357282066109147700032983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71238837685915454400175909 13357282066109147700032983)
    ·
      refine ⟨20035923099163721550049475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13357282066109147700032983 20035923099163721550049475)
      ·
        refine ⟨30053884648745582325074213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20035923099163721550049475 30053884648745582325074213)
        ·
          refine ⟨5635103371639796685951415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30053884648745582325074213 5635103371639796685951415)
          ·
            refine ⟨8452655057459695028927123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5635103371639796685951415 8452655057459695028927123)
            ·
              refine ⟨12678982586189542543390685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8452655057459695028927123 12678982586189542543390685)
              ·
                refine ⟨4754618469821078453771507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12678982586189542543390685 4754618469821078453771507)
                ·
                  refine ⟨7131927704731617680657261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4754618469821078453771507 7131927704731617680657261)
                  ·
                    refine ⟨2674472889274356630246473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7131927704731617680657261 2674472889274356630246473)
                    ·
                      refine ⟨2005854666955767472684855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2674472889274356630246473 2005854666955767472684855)
                      ·
                        rfl

theorem cell23_3906388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_3906388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906388 prefixEnd_3906388 := by exact prefixLift 3906388
  have htrace : WordTrace (prefixWord ++ tailWord_3906388) baseStart_3906388 baseEnd_3906388 := by
    simpa [prefixWord, tailWord_3906388, baseEnd_3906388] using wordTrace_append hprefix tailTrace_3906388
  have hstable : (prefixWord ++ tailWord_3906388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906388).length < 2 ^ (prefixWord ++ tailWord_3906388).sum := by decide
  have hdescent : baseEnd_3906388 < baseStart_3906388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906401 : List Nat := [1, 2, 3, 1, 1, 1, 2, 6, 2, 2, 2]
def baseStart_3906401 : Nat := 118140960795 + 3906401 * 2 ^ 59
def prefixEnd_3906401 : Nat := 4983230072969 + 3 ^ 40 * 3906401 * 2
def baseEnd_3906401 : Nat := 2005861342204275921822295

theorem tailTrace_3906401 : CollatzResearch.WordTrace tailWord_3906401 prefixEnd_3906401 2005861342204275921822295 := by
  unfold tailWord_3906401
  simp only [CollatzResearch.WordTrace]
  refine ⟨142478149520783812020575057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94985433013855874680383371 142478149520783812020575057)
  ·
    refine ⟨106858612140587859015431293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142478149520783812020575057 106858612140587859015431293)
    ·
      refine ⟨40071979552720447130786735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106858612140587859015431293 40071979552720447130786735)
      ·
        refine ⟨60107969329080670696180103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40071979552720447130786735 60107969329080670696180103)
        ·
          refine ⟨90161953993621006044270155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60107969329080670696180103 90161953993621006044270155)
          ·
            refine ⟨135242930990431509066405233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90161953993621006044270155 135242930990431509066405233)
            ·
              refine ⟨101432198242823631799803925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135242930990431509066405233 101432198242823631799803925)
              ·
                refine ⟨4754634292632357740615809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101432198242823631799803925 4754634292632357740615809)
                ·
                  refine ⟨3565975719474268305461857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4754634292632357740615809 3565975719474268305461857)
                  ·
                    refine ⟨2674481789605701229096393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3565975719474268305461857 2674481789605701229096393)
                    ·
                      refine ⟨2005861342204275921822295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2674481789605701229096393 2005861342204275921822295)
                      ·
                        rfl

theorem cell23_3906401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 2, 2, 2].length) (baseStart_3906401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906401 prefixEnd_3906401 := by exact prefixLift 3906401
  have htrace : WordTrace (prefixWord ++ tailWord_3906401) baseStart_3906401 baseEnd_3906401 := by
    simpa [prefixWord, tailWord_3906401, baseEnd_3906401] using wordTrace_append hprefix tailTrace_3906401
  have hstable : (prefixWord ++ tailWord_3906401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906401).length < 2 ^ (prefixWord ++ tailWord_3906401).sum := by decide
  have hdescent : baseEnd_3906401 < baseStart_3906401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906407 : List Nat := [1, 1, 5, 1, 2, 2, 1, 3, 7]
def baseStart_3906407 : Nat := 118140960795 + 3906407 * 2 ^ 59
def prefixEnd_3906407 : Nat := 4983230072969 + 3 ^ 40 * 3906407 * 2
def baseEnd_3906407 : Nat := 222873824787578099816363

theorem tailTrace_3906407 : CollatzResearch.WordTrace tailWord_3906407 prefixEnd_3906407 222873824787578099816363 := by
  unfold tailWord_3906407
  simp only [CollatzResearch.WordTrace]
  refine ⟨142478368358762075045293475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94985578905841383363528983 142478368358762075045293475)
  ·
    refine ⟨213717552538143112567940213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142478368358762075045293475 213717552538143112567940213)
    ·
      refine ⟨20036020550450916803244395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 213717552538143112567940213 20036020550450916803244395)
      ·
        refine ⟨30054030825676375204866593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20036020550450916803244395 30054030825676375204866593)
        ·
          refine ⟨22540523119257281403649945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30054030825676375204866593 22540523119257281403649945)
          ·
            refine ⟨16905392339442961052737459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22540523119257281403649945 16905392339442961052737459)
            ·
              refine ⟨25358088509164441579106189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16905392339442961052737459 25358088509164441579106189)
              ·
                refine ⟨9509283190936665592164821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25358088509164441579106189 9509283190936665592164821)
                ·
                  refine ⟨222873824787578099816363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9509283190936665592164821 222873824787578099816363)
                  ·
                    rfl

theorem cell23_3906407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 7].length) (baseStart_3906407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906407 prefixEnd_3906407 := by exact prefixLift 3906407
  have htrace : WordTrace (prefixWord ++ tailWord_3906407) baseStart_3906407 baseEnd_3906407 := by
    simpa [prefixWord, tailWord_3906407, baseEnd_3906407] using wordTrace_append hprefix tailTrace_3906407
  have hstable : (prefixWord ++ tailWord_3906407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906407).length < 2 ^ (prefixWord ++ tailWord_3906407).sum := by decide
  have hdescent : baseEnd_3906407 < baseStart_3906407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906437 : List Nat := [1, 3, 1, 1, 3, 3, 2, 1, 1, 7]
def baseStart_3906437 : Nat := 118140960795 + 3906437 * 2 ^ 59
def prefixEnd_3906437 : Nat := 4983230072969 + 3 ^ 40 * 3906437 * 2
def baseEnd_3906437 : Nat := 668626609169279260324043

theorem tailTrace_3906437 : CollatzResearch.WordTrace tailWord_3906437 prefixEnd_3906437 668626609169279260324043 := by
  unfold tailWord_3906437
  simp only [CollatzResearch.WordTrace]
  refine ⟨142479462548653390168885565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94986308365768926779257043 142479462548653390168885565)
  ·
    refine ⟨53429798455745021313332087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142479462548653390168885565 53429798455745021313332087)
    ·
      refine ⟨80144697683617531969998131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53429798455745021313332087 80144697683617531969998131)
      ·
        refine ⟨120217046525426297954997197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80144697683617531969998131 120217046525426297954997197)
        ·
          refine ⟨45081392447034861733123949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120217046525426297954997197 45081392447034861733123949)
          ·
            refine ⟨16905522167638073149921481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45081392447034861733123949 16905522167638073149921481)
            ·
              refine ⟨12679141625728554862441111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16905522167638073149921481 12679141625728554862441111)
              ·
                refine ⟨19018712438592832293661667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12679141625728554862441111 19018712438592832293661667)
                ·
                  refine ⟨28528068657889248440492501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19018712438592832293661667 28528068657889248440492501)
                  ·
                    refine ⟨668626609169279260324043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28528068657889248440492501 668626609169279260324043)
                    ·
                      rfl

theorem cell23_3906437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 7].length) (baseStart_3906437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906437 prefixEnd_3906437 := by exact prefixLift 3906437
  have htrace : WordTrace (prefixWord ++ tailWord_3906437) baseStart_3906437 baseEnd_3906437 := by
    simpa [prefixWord, tailWord_3906437, baseEnd_3906437] using wordTrace_append hprefix tailTrace_3906437
  have hstable : (prefixWord ++ tailWord_3906437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906437).length < 2 ^ (prefixWord ++ tailWord_3906437).sum := by decide
  have hdescent : baseEnd_3906437 < baseStart_3906437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906441 : List Nat := [1, 2, 1, 1, 5, 4, 1, 3, 5]
def baseStart_3906441 : Nat := 118140960795 + 3906441 * 2 ^ 59
def prefixEnd_3906441 : Nat := 4983230072969 + 3 ^ 40 * 3906441 * 2
def baseEnd_3906441 : Nat := 222875764603383973924679

theorem tailTrace_3906441 : CollatzResearch.WordTrace tailWord_3906441 prefixEnd_3906441 222875764603383973924679 := by
  unfold tailWord_3906441
  simp only [CollatzResearch.WordTrace]
  refine ⟨142479608440638898852031177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94986405627092599234687451 142479608440638898852031177)
  ·
    refine ⟨106859706330479174139023383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142479608440638898852031177 106859706330479174139023383)
    ·
      refine ⟨160289559495718761208535075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106859706330479174139023383 160289559495718761208535075)
      ·
        refine ⟨240434339243578141812802613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160289559495718761208535075 240434339243578141812802613)
        ·
          refine ⟨22540719304085450794950245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 240434339243578141812802613 22540719304085450794950245)
          ·
            refine ⟨4226384869516022024053171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22540719304085450794950245 4226384869516022024053171)
            ·
              refine ⟨6339577304274033036079757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4226384869516022024053171 6339577304274033036079757)
              ·
                refine ⟨2377341489102762388529909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6339577304274033036079757 2377341489102762388529909)
                ·
                  refine ⟨222875764603383973924679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2377341489102762388529909 222875764603383973924679)
                  ·
                    rfl

theorem cell23_3906441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 3, 5].length) (baseStart_3906441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906441 prefixEnd_3906441 := by exact prefixLift 3906441
  have htrace : WordTrace (prefixWord ++ tailWord_3906441) baseStart_3906441 baseEnd_3906441 := by
    simpa [prefixWord, tailWord_3906441, baseEnd_3906441] using wordTrace_append hprefix tailTrace_3906441
  have hstable : (prefixWord ++ tailWord_3906441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906441).length < 2 ^ (prefixWord ++ tailWord_3906441).sum := by decide
  have hdescent : baseEnd_3906441 < baseStart_3906441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906458 : List Nat := [3, 1, 1, 4, 3, 1, 3, 2, 5]
def baseStart_3906458 : Nat := 118140960795 + 3906458 * 2 ^ 59
def prefixEnd_3906458 : Nat := 4983230072969 + 3 ^ 40 * 3906458 * 2
def baseEnd_3906458 : Nat := 222876734511286910978837

theorem tailTrace_3906458 : CollatzResearch.WordTrace tailWord_3906458 prefixEnd_3906458 222876734511286910978837 := by
  unfold tailWord_3906458
  simp only [CollatzResearch.WordTrace]
  refine ⟨35620057120394327688850007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94986818987718207170266685 35620057120394327688850007)
  ·
    refine ⟨53430085680591491533275011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35620057120394327688850007 53430085680591491533275011)
    ·
      refine ⟨80145128520887237299912517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53430085680591491533275011 80145128520887237299912517)
      ·
        refine ⟨15027211597666356993733597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80145128520887237299912517 15027211597666356993733597)
        ·
          refine ⟨5635204349124883872650099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15027211597666356993733597 5635204349124883872650099)
          ·
            refine ⟨8452806523687325808975149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5635204349124883872650099 8452806523687325808975149)
            ·
              refine ⟨3169802446382747178365681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8452806523687325808975149 3169802446382747178365681)
              ·
                refine ⟨2377351834787060383774261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3169802446382747178365681 2377351834787060383774261)
                ·
                  refine ⟨222876734511286910978837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2377351834787060383774261 222876734511286910978837)
                  ·
                    rfl

theorem cell23_3906458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 3, 2, 5].length) (baseStart_3906458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906458 prefixEnd_3906458 := by exact prefixLift 3906458
  have htrace : WordTrace (prefixWord ++ tailWord_3906458) baseStart_3906458 baseEnd_3906458 := by
    simpa [prefixWord, tailWord_3906458, baseEnd_3906458] using wordTrace_append hprefix tailTrace_3906458
  have hstable : (prefixWord ++ tailWord_3906458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906458).length < 2 ^ (prefixWord ++ tailWord_3906458).sum := by decide
  have hdescent : baseEnd_3906458 < baseStart_3906458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906487 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 4]
def baseStart_3906487 : Nat := 118140960795 + 3906487 * 2 ^ 59
def prefixEnd_3906487 : Nat := 4983230072969 + 3 ^ 40 * 3906487 * 2
def baseEnd_3906487 : Nat := 2005905501540562585346899

theorem tailTrace_3906487 : CollatzResearch.WordTrace tailWord_3906487 prefixEnd_3906487 2005905501540562585346899 := by
  unfold tailWord_3906487
  simp only [CollatzResearch.WordTrace]
  refine ⟨142481286198472248708205715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94987524132314832472137143 142481286198472248708205715)
  ·
    refine ⟨213721929297708373062308573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142481286198472248708205715 213721929297708373062308573)
    ·
      refine ⟨80145723486640639898365715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213721929297708373062308573 80145723486640639898365715)
      ·
        refine ⟨120218585229960959847548573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80145723486640639898365715 120218585229960959847548573)
        ·
          refine ⟨45081969461235359942830715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120218585229960959847548573 45081969461235359942830715)
          ·
            refine ⟨67622954191853039914246073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45081969461235359942830715 67622954191853039914246073)
            ·
              refine ⟨50717215643889779935684555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67622954191853039914246073 50717215643889779935684555)
              ·
                refine ⟨76075823465834669903526833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50717215643889779935684555 76075823465834669903526833)
                ·
                  refine ⟨57056867599376002427645125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76075823465834669903526833 57056867599376002427645125)
                  ·
                    refine ⟨10698162674883000455183461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57056867599376002427645125 10698162674883000455183461)
                    ·
                      refine ⟨2005905501540562585346899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10698162674883000455183461 2005905501540562585346899)
                      ·
                        rfl

theorem cell23_3906487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_3906487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906487 prefixEnd_3906487 := by exact prefixLift 3906487
  have htrace : WordTrace (prefixWord ++ tailWord_3906487) baseStart_3906487 baseEnd_3906487 := by
    simpa [prefixWord, tailWord_3906487, baseEnd_3906487] using wordTrace_append hprefix tailTrace_3906487
  have hstable : (prefixWord ++ tailWord_3906487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906487).length < 2 ^ (prefixWord ++ tailWord_3906487).sum := by decide
  have hdescent : baseEnd_3906487 < baseStart_3906487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906509 : List Nat := [1, 6, 3, 1, 1, 2, 2, 2, 5]
def baseStart_3906509 : Nat := 118140960795 + 3906509 * 2 ^ 59
def prefixEnd_3906509 : Nat := 4983230072969 + 3 ^ 40 * 3906509 * 2
def baseEnd_3906509 : Nat := 222879644234995722141311

theorem tailTrace_3906509 : CollatzResearch.WordTrace tailWord_3906509 prefixEnd_3906509 222879644234995722141311 := by
  unfold tailWord_3906509
  simp only [CollatzResearch.WordTrace]
  refine ⟨142482088604392546465506581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94988059069595030977004387 142482088604392546465506581)
  ·
    refine ⟨6678847903330900615570621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 142482088604392546465506581 6678847903330900615570621)
    ·
      refine ⟨2504567963749087730838983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6678847903330900615570621 2504567963749087730838983)
      ·
        refine ⟨3756851945623631596258475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2504567963749087730838983 3756851945623631596258475)
        ·
          refine ⟨5635277918435447394387713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3756851945623631596258475 5635277918435447394387713)
          ·
            refine ⟨4226458438826585545790785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5635277918435447394387713 4226458438826585545790785)
            ·
              refine ⟨3169843829119939159343089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4226458438826585545790785 3169843829119939159343089)
              ·
                refine ⟨2377382871839954369507317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3169843829119939159343089 2377382871839954369507317)
                ·
                  refine ⟨222879644234995722141311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2377382871839954369507317 222879644234995722141311)
                  ·
                    rfl

theorem cell23_3906509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_3906509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906509 prefixEnd_3906509 := by exact prefixLift 3906509
  have htrace : WordTrace (prefixWord ++ tailWord_3906509) baseStart_3906509 baseEnd_3906509 := by
    simpa [prefixWord, tailWord_3906509, baseEnd_3906509] using wordTrace_append hprefix tailTrace_3906509
  have hstable : (prefixWord ++ tailWord_3906509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906509).length < 2 ^ (prefixWord ++ tailWord_3906509).sum := by decide
  have hdescent : baseEnd_3906509 < baseStart_3906509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906544 : List Nat := [2, 1, 1, 1, 3, 2, 1, 6, 1, 5]
def baseStart_3906544 : Nat := 118140960795 + 3906544 * 2 ^ 59
def prefixEnd_3906544 : Nat := 4983230072969 + 3 ^ 40 * 3906544 * 2
def baseEnd_3906544 : Nat := 668644923312622954111379

theorem tailTrace_3906544 : CollatzResearch.WordTrace tailWord_3906544 prefixEnd_3906544 668644923312622954111379 := by
  unfold tailWord_3906544
  simp only [CollatzResearch.WordTrace]
  refine ⟨71241682579632873721515343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94988910106177164962020457 71241682579632873721515343)
  ·
    refine ⟨106862523869449310582273015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71241682579632873721515343 106862523869449310582273015)
    ·
      refine ⟨160293785804173965873409523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106862523869449310582273015 160293785804173965873409523)
      ·
        refine ⟨240440678706260948810114285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160293785804173965873409523 240440678706260948810114285)
        ·
          refine ⟨90165254514847855803792857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240440678706260948810114285 90165254514847855803792857)
          ·
            refine ⟨67623940886135891852844643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90165254514847855803792857 67623940886135891852844643)
            ·
              refine ⟨101435911329203837779266965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67623940886135891852844643 101435911329203837779266965)
              ·
                refine ⟨4754808343556429895903139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101435911329203837779266965 4754808343556429895903139)
                ·
                  refine ⟨7132212515334644843854709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4754808343556429895903139 7132212515334644843854709)
                  ·
                    refine ⟨668644923312622954111379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7132212515334644843854709 668644923312622954111379)
                    ·
                      rfl

theorem cell23_3906544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 1, 5].length) (baseStart_3906544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906544 prefixEnd_3906544 := by exact prefixLift 3906544
  have htrace : WordTrace (prefixWord ++ tailWord_3906544) baseStart_3906544 baseEnd_3906544 := by
    simpa [prefixWord, tailWord_3906544, baseEnd_3906544] using wordTrace_append hprefix tailTrace_3906544
  have hstable : (prefixWord ++ tailWord_3906544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906544).length < 2 ^ (prefixWord ++ tailWord_3906544).sum := by decide
  have hdescent : baseEnd_3906544 < baseStart_3906544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906561 : List Nat := [1, 2, 4, 1, 2, 3, 1, 3, 1, 5]
def baseStart_3906561 : Nat := 118140960795 + 3906561 * 2 ^ 59
def prefixEnd_3906561 : Nat := 4983230072969 + 3 ^ 40 * 3906561 * 2
def baseEnd_3906561 : Nat := 668647833036331765273853

theorem tailTrace_3906561 : CollatzResearch.WordTrace tailWord_3906561 prefixEnd_3906561 668647833036331765273853 := by
  unfold tailWord_3906561
  simp only [CollatzResearch.WordTrace]
  refine ⟨142483985200204159346399537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94989323466802772897599691 142483985200204159346399537)
  ·
    refine ⟨106862988900153119509799653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142483985200204159346399537 106862988900153119509799653)
    ·
      refine ⟨20036810418778709908087435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106862988900153119509799653 20036810418778709908087435)
      ·
        refine ⟨30055215628168064862131153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20036810418778709908087435 30055215628168064862131153)
        ·
          refine ⟨22541411721126048646598365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30055215628168064862131153 22541411721126048646598365)
          ·
            refine ⟨8453029395422268242474387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22541411721126048646598365 8453029395422268242474387)
            ·
              refine ⟨12679544093133402363711581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8453029395422268242474387 12679544093133402363711581)
              ·
                refine ⟨4754829034925025886391843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12679544093133402363711581 4754829034925025886391843)
                ·
                  refine ⟨7132243552387538829587765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4754829034925025886391843 7132243552387538829587765)
                  ·
                    refine ⟨668647833036331765273853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7132243552387538829587765 668647833036331765273853)
                    ·
                      rfl

theorem cell23_3906561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_3906561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906561 prefixEnd_3906561 := by exact prefixLift 3906561
  have htrace : WordTrace (prefixWord ++ tailWord_3906561) baseStart_3906561 baseEnd_3906561 := by
    simpa [prefixWord, tailWord_3906561, baseEnd_3906561] using wordTrace_append hprefix tailTrace_3906561
  have hstable : (prefixWord ++ tailWord_3906561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906561).length < 2 ^ (prefixWord ++ tailWord_3906561).sum := by decide
  have hdescent : baseEnd_3906561 < baseStart_3906561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906584 : List Nat := [2, 1, 2, 3, 2, 2, 1, 1, 3, 1, 5]
def baseStart_3906584 : Nat := 118140960795 + 3906584 * 2 ^ 59
def prefixEnd_3906584 : Nat := 4983230072969 + 3 ^ 40 * 3906584 * 2
def baseEnd_3906584 : Nat := 2005955309164048705833953

theorem tailTrace_3906584 : CollatzResearch.WordTrace tailWord_3906584 prefixEnd_3906584 2005955309164048705833953 := by
  unfold tailWord_3906584
  simp only [CollatzResearch.WordTrace]
  refine ⟨71242412039560417137243403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94989882719413889516324537 71242412039560417137243403)
  ·
    refine ⟨106863618059340625705865105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71242412039560417137243403 106863618059340625705865105)
    ·
      refine ⟨80147713544505469279398829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106863618059340625705865105 80147713544505469279398829)
      ·
        refine ⟨30055392579189550979774561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80147713544505469279398829 30055392579189550979774561)
        ·
          refine ⟨22541544434392163234830921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30055392579189550979774561 22541544434392163234830921)
          ·
            refine ⟨16906158325794122426123191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22541544434392163234830921 16906158325794122426123191)
            ·
              refine ⟨25359237488691183639184787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16906158325794122426123191 25359237488691183639184787)
              ·
                refine ⟨38038856233036775458777181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25359237488691183639184787 38038856233036775458777181)
                ·
                  refine ⟨14264571087388790797041443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38038856233036775458777181 14264571087388790797041443)
                  ·
                    refine ⟨21396856631083186195562165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14264571087388790797041443 21396856631083186195562165)
                    ·
                      refine ⟨2005955309164048705833953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21396856631083186195562165 2005955309164048705833953)
                      ·
                        rfl

theorem cell23_3906584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_3906584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906584 prefixEnd_3906584 := by exact prefixLift 3906584
  have htrace : WordTrace (prefixWord ++ tailWord_3906584) baseStart_3906584 baseEnd_3906584 := by
    simpa [prefixWord, tailWord_3906584, baseEnd_3906584] using wordTrace_append hprefix tailTrace_3906584
  have hstable : (prefixWord ++ tailWord_3906584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906584).length < 2 ^ (prefixWord ++ tailWord_3906584).sum := by decide
  have hdescent : baseEnd_3906584 < baseStart_3906584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906591 : List Nat := [1, 1, 2, 4, 1, 5, 1, 1, 1, 6]
def baseStart_3906591 : Nat := 118140960795 + 3906591 * 2 ^ 59
def prefixEnd_3906591 : Nat := 4983230072969 + 3 ^ 40 * 3906591 * 2
def baseEnd_3906591 : Nat := 668652967842876726148807

theorem tailTrace_3906591 : CollatzResearch.WordTrace tailWord_3906591 prefixEnd_3906591 668652967842876726148807 := by
  unfold tailWord_3906591
  simp only [CollatzResearch.WordTrace]
  refine ⟨142485079390095474469991627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94990052926730316313327751 142485079390095474469991627)
  ·
    refine ⟨213727619085143211704987441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142485079390095474469991627 213727619085143211704987441)
    ·
      refine ⟨160295714313857408778740581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213727619085143211704987441 160295714313857408778740581)
      ·
        refine ⟨30055446433848264146013859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160295714313857408778740581 30055446433848264146013859)
        ·
          refine ⟨45083169650772396219020789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30055446433848264146013859 45083169650772396219020789)
          ·
            refine ⟨4226547154759912145533199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45083169650772396219020789 4226547154759912145533199)
            ·
              refine ⟨6339820732139868218299799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4226547154759912145533199 6339820732139868218299799)
              ·
                refine ⟨9509731098209802327449699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6339820732139868218299799 9509731098209802327449699)
                ·
                  refine ⟨14264596647314703491174549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9509731098209802327449699 14264596647314703491174549)
                  ·
                    refine ⟨668652967842876726148807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14264596647314703491174549 668652967842876726148807)
                    ·
                      rfl

theorem cell23_3906591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 6].length) (baseStart_3906591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906591 prefixEnd_3906591 := by exact prefixLift 3906591
  have htrace : WordTrace (prefixWord ++ tailWord_3906591) baseStart_3906591 baseEnd_3906591 := by
    simpa [prefixWord, tailWord_3906591, baseEnd_3906591] using wordTrace_append hprefix tailTrace_3906591
  have hstable : (prefixWord ++ tailWord_3906591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906591).length < 2 ^ (prefixWord ++ tailWord_3906591).sum := by decide
  have hdescent : baseEnd_3906591 < baseStart_3906591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906632 : List Nat := [2, 1, 3, 1, 1, 1, 7, 2, 1, 2, 2]
def baseStart_3906632 : Nat := 118140960795 + 3906632 * 2 ^ 59
def prefixEnd_3906632 : Nat := 4983230072969 + 3 ^ 40 * 3906632 * 2
def baseEnd_3906632 : Nat := 2005979956235464518033733

theorem tailTrace_3906632 : CollatzResearch.WordTrace tailWord_3906632 prefixEnd_3906632 2005979956235464518033733 := by
  unfold tailWord_3906632
  simp only [CollatzResearch.WordTrace]
  refine ⟨71243287391473469236117075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94991049855297958981489433 71243287391473469236117075)
  ·
    refine ⟨106864931087210203854175613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71243287391473469236117075 106864931087210203854175613)
    ·
      refine ⟨40074349157703826445315855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106864931087210203854175613 40074349157703826445315855)
      ·
        refine ⟨60111523736555739667973783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40074349157703826445315855 60111523736555739667973783)
        ·
          refine ⟨90167285604833609501960675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60111523736555739667973783 90167285604833609501960675)
          ·
            refine ⟨135250928407250414252941013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90167285604833609501960675 135250928407250414252941013)
            ·
              refine ⟨3169943634544931584053305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 135250928407250414252941013 3169943634544931584053305)
              ·
                refine ⟨2377457725908698688039979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3169943634544931584053305 2377457725908698688039979)
                ·
                  refine ⟨3566186588863048032059969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2377457725908698688039979 3566186588863048032059969)
                  ·
                    refine ⟨2674639941647286024044977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3566186588863048032059969 2674639941647286024044977)
                    ·
                      refine ⟨2005979956235464518033733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2674639941647286024044977 2005979956235464518033733)
                      ·
                        rfl

theorem cell23_3906632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 2, 1, 2, 2].length) (baseStart_3906632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906632 prefixEnd_3906632 := by exact prefixLift 3906632
  have htrace : WordTrace (prefixWord ++ tailWord_3906632) baseStart_3906632 baseEnd_3906632 := by
    simpa [prefixWord, tailWord_3906632, baseEnd_3906632] using wordTrace_append hprefix tailTrace_3906632
  have hstable : (prefixWord ++ tailWord_3906632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906632).length < 2 ^ (prefixWord ++ tailWord_3906632).sum := by decide
  have hdescent : baseEnd_3906632 < baseStart_3906632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906648 : List Nat := [2, 1, 2, 2, 1, 3, 3, 3, 2, 1, 3]
def baseStart_3906648 : Nat := 118140960795 + 3906648 * 2 ^ 59
def prefixEnd_3906648 : Nat := 4983230072969 + 3 ^ 40 * 3906648 * 2
def baseEnd_3906648 : Nat := 2005988171925936455433659

theorem tailTrace_3906648 : CollatzResearch.WordTrace tailWord_3906648 prefixEnd_3906648 2005988171925936455433659 := by
  unfold tailWord_3906648
  simp only [CollatzResearch.WordTrace]
  refine ⟨71243579175444486602408299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94991438900592648803211065 71243579175444486602408299)
  ·
    refine ⟨106865368763166729903612449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71243579175444486602408299 106865368763166729903612449)
    ·
      refine ⟨80149026572375047427709337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106865368763166729903612449 80149026572375047427709337)
      ·
        refine ⟨60111769929281285570782003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80149026572375047427709337 60111769929281285570782003)
        ·
          refine ⟨90167654893921928356173005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60111769929281285570782003 90167654893921928356173005)
          ·
            refine ⟨33812870585220723133564877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90167654893921928356173005 33812870585220723133564877)
            ·
              refine ⟨12679826469457771175086829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33812870585220723133564877 12679826469457771175086829)
              ·
                refine ⟨4754934926046664190657561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12679826469457771175086829 4754934926046664190657561)
                ·
                  refine ⟨3566201194534998142993171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4754934926046664190657561 3566201194534998142993171)
                  ·
                    refine ⟨5349301791802497214489757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3566201194534998142993171 5349301791802497214489757)
                    ·
                      refine ⟨2005988171925936455433659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5349301791802497214489757 2005988171925936455433659)
                      ·
                        rfl

theorem cell23_3906648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 2, 1, 3].length) (baseStart_3906648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906648 prefixEnd_3906648 := by exact prefixLift 3906648
  have htrace : WordTrace (prefixWord ++ tailWord_3906648) baseStart_3906648 baseEnd_3906648 := by
    simpa [prefixWord, tailWord_3906648, baseEnd_3906648] using wordTrace_append hprefix tailTrace_3906648
  have hstable : (prefixWord ++ tailWord_3906648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906648).length < 2 ^ (prefixWord ++ tailWord_3906648).sum := by decide
  have hdescent : baseEnd_3906648 < baseStart_3906648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906688 : List Nat := [2, 1, 1, 2, 1, 3, 2, 3, 4, 2, 2]
def baseStart_3906688 : Nat := 118140960795 + 3906688 * 2 ^ 59
def prefixEnd_3906688 : Nat := 4983230072969 + 3 ^ 40 * 3906688 * 2
def baseEnd_3906688 : Nat := 2006008711152116298933475

theorem tailTrace_3906688 : CollatzResearch.WordTrace tailWord_3906688 prefixEnd_3906688 2006008711152116298933475 := by
  unfold tailWord_3906688
  simp only [CollatzResearch.WordTrace]
  refine ⟨71244308635372030018136359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94992411513829373357515145 71244308635372030018136359)
  ·
    refine ⟨106866462953058045027204539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71244308635372030018136359 106866462953058045027204539)
    ·
      refine ⟨160299694429587067540806809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106866462953058045027204539 160299694429587067540806809)
      ·
        refine ⟨120224770822190300655605107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160299694429587067540806809 120224770822190300655605107)
        ·
          refine ⟨180337156233285450983407661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120224770822190300655605107 180337156233285450983407661)
          ·
            refine ⟨67626433587482044118777873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180337156233285450983407661 67626433587482044118777873)
            ·
              refine ⟨50719825190611533089083405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67626433587482044118777873 50719825190611533089083405)
              ·
                refine ⟨19019934446479324908406277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50719825190611533089083405 19019934446479324908406277)
                ·
                  refine ⟨3566237708714873420326177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19019934446479324908406277 3566237708714873420326177)
                  ·
                    refine ⟨2674678281536155065244633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3566237708714873420326177 2674678281536155065244633)
                    ·
                      refine ⟨2006008711152116298933475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2674678281536155065244633 2006008711152116298933475)
                      ·
                        rfl

theorem cell23_3906688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 4, 2, 2].length) (baseStart_3906688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906688 prefixEnd_3906688 := by exact prefixLift 3906688
  have htrace : WordTrace (prefixWord ++ tailWord_3906688) baseStart_3906688 baseEnd_3906688 := by
    simpa [prefixWord, tailWord_3906688, baseEnd_3906688] using wordTrace_append hprefix tailTrace_3906688
  have hstable : (prefixWord ++ tailWord_3906688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906688).length < 2 ^ (prefixWord ++ tailWord_3906688).sum := by decide
  have hdescent : baseEnd_3906688 < baseStart_3906688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906711 : List Nat := [1, 1, 3, 3, 3, 2, 1, 2, 7]
def baseStart_3906711 : Nat := 118140960795 + 3906711 * 2 ^ 59
def prefixEnd_3906711 : Nat := 4983230072969 + 3 ^ 40 * 3906711 * 2
def baseEnd_3906711 : Nat := 222891169023018856549541

theorem tailTrace_3906711 : CollatzResearch.WordTrace tailWord_3906711 prefixEnd_3906711 222891169023018856549541 := by
  unfold tailWord_3906711
  simp only [CollatzResearch.WordTrace]
  refine ⟨142489456149660734964359987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94992970766440489976239991 142489456149660734964359987)
  ·
    refine ⟨213734184224491102446539981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142489456149660734964359987 213734184224491102446539981)
    ·
      refine ⟨80150319084184163417452493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213734184224491102446539981 80150319084184163417452493)
      ·
        refine ⟨30056369656569061281544685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80150319084184163417452493 30056369656569061281544685)
        ·
          refine ⟨11271138621213397980579257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30056369656569061281544685 11271138621213397980579257)
          ·
            refine ⟨8453353965910048485434443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11271138621213397980579257 8453353965910048485434443)
            ·
              refine ⟨12680030948865072728151665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8453353965910048485434443 12680030948865072728151665)
              ·
                refine ⟨9510023211648804546113749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12680030948865072728151665 9510023211648804546113749)
                ·
                  refine ⟨222891169023018856549541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9510023211648804546113749 222891169023018856549541)
                  ·
                    rfl

theorem cell23_3906711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 7].length) (baseStart_3906711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906711 prefixEnd_3906711 := by exact prefixLift 3906711
  have htrace : WordTrace (prefixWord ++ tailWord_3906711) baseStart_3906711 baseEnd_3906711 := by
    simpa [prefixWord, tailWord_3906711, baseEnd_3906711] using wordTrace_append hprefix tailTrace_3906711
  have hstable : (prefixWord ++ tailWord_3906711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906711).length < 2 ^ (prefixWord ++ tailWord_3906711).sum := by decide
  have hdescent : baseEnd_3906711 < baseStart_3906711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906721 : List Nat := [1, 2, 3, 3, 1, 1, 1, 2, 1, 5, 3]
def baseStart_3906721 : Nat := 118140960795 + 3906721 * 2 ^ 59
def prefixEnd_3906721 : Nat := 4983230072969 + 3 ^ 40 * 3906721 * 2
def baseEnd_3906721 : Nat := 2006025656013714669820823

theorem tailTrace_3906721 : CollatzResearch.WordTrace tailWord_3906721 prefixEnd_3906721 2006025656013714669820823 := by
  unfold tailWord_3906721
  simp only [CollatzResearch.WordTrace]
  refine ⟨142489820879624506672224017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94993213919749671114816011 142489820879624506672224017)
  ·
    refine ⟨106867365659718380004168013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142489820879624506672224017 106867365659718380004168013)
    ·
      refine ⟨40075262122394392501563005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106867365659718380004168013 40075262122394392501563005)
      ·
        refine ⟨15028223295897897188086127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40075262122394392501563005 15028223295897897188086127)
        ·
          refine ⟨22542334943846845782129191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15028223295897897188086127 22542334943846845782129191)
          ·
            refine ⟨33813502415770268673193787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22542334943846845782129191 33813502415770268673193787)
            ·
              refine ⟨50720253623655403009790681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33813502415770268673193787 50720253623655403009790681)
              ·
                refine ⟨38040190217741552257343011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50720253623655403009790681 38040190217741552257343011)
                ·
                  refine ⟨57060285326612328386014517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38040190217741552257343011 57060285326612328386014517)
                  ·
                    refine ⟨5349401749369905786188861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57060285326612328386014517 5349401749369905786188861)
                    ·
                      refine ⟨2006025656013714669820823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5349401749369905786188861 2006025656013714669820823)
                      ·
                        rfl

theorem cell23_3906721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_3906721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906721 prefixEnd_3906721 := by exact prefixLift 3906721
  have htrace : WordTrace (prefixWord ++ tailWord_3906721) baseStart_3906721 baseEnd_3906721 := by
    simpa [prefixWord, tailWord_3906721, baseEnd_3906721] using wordTrace_append hprefix tailTrace_3906721
  have hstable : (prefixWord ++ tailWord_3906721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906721).length < 2 ^ (prefixWord ++ tailWord_3906721).sum := by decide
  have hdescent : baseEnd_3906721 < baseStart_3906721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906798 : List Nat := [4, 1, 2, 1, 1, 1, 3, 1, 4, 2, 3]
def baseStart_3906798 : Nat := 118140960795 + 3906798 * 2 ^ 59
def prefixEnd_3906798 : Nat := 4983230072969 + 3 ^ 40 * 3906798 * 2
def baseEnd_3906798 : Nat := 2006065194024110868557969

theorem tailTrace_3906798 : CollatzResearch.WordTrace tailWord_3906798 prefixEnd_3906798 2006065194024110868557969 := by
  unfold tailWord_3906798
  simp only [CollatzResearch.WordTrace]
  refine ⟨17811578662543193602847131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94995086200230365881851365 17811578662543193602847131)
  ·
    refine ⟨26717367993814790404270697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17811578662543193602847131 26717367993814790404270697)
    ·
      refine ⟨20038025995361092803203023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26717367993814790404270697 20038025995361092803203023)
      ·
        refine ⟨30057038993041639204804535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20038025995361092803203023 30057038993041639204804535)
        ·
          refine ⟨45085558489562458807206803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30057038993041639204804535 45085558489562458807206803)
          ·
            refine ⟨67628337734343688210810205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45085558489562458807206803 67628337734343688210810205)
            ·
              refine ⟨25360626650378883079053827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67628337734343688210810205 25360626650378883079053827)
              ·
                refine ⟨38040939975568324618580741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25360626650378883079053827 38040939975568324618580741)
                ·
                  refine ⟨7132676245419060865983889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38040939975568324618580741 7132676245419060865983889)
                  ·
                    refine ⟨5349507184064295649487917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7132676245419060865983889 5349507184064295649487917)
                    ·
                      refine ⟨2006065194024110868557969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5349507184064295649487917 2006065194024110868557969)
                      ·
                        rfl

theorem cell23_3906798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_3906798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906798 prefixEnd_3906798 := by exact prefixLift 3906798
  have htrace : WordTrace (prefixWord ++ tailWord_3906798) baseStart_3906798 baseEnd_3906798 := by
    simpa [prefixWord, tailWord_3906798, baseEnd_3906798] using wordTrace_append hprefix tailTrace_3906798
  have hstable : (prefixWord ++ tailWord_3906798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906798).length < 2 ^ (prefixWord ++ tailWord_3906798).sum := by decide
  have hdescent : baseEnd_3906798 < baseStart_3906798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906801 : List Nat := [1, 2, 2, 2, 2, 1, 1, 6, 6]
def baseStart_3906801 : Nat := 118140960795 + 3906801 * 2 ^ 59
def prefixEnd_3906801 : Nat := 4983230072969 + 3 ^ 40 * 3906801 * 2
def baseEnd_3906801 : Nat := 222896303829563817424495

theorem tailTrace_3906801 : CollatzResearch.WordTrace tailWord_3906801 prefixEnd_3906801 222896303829563817424495 := by
  unfold tailWord_3906801
  simp only [CollatzResearch.WordTrace]
  refine ⟨142492738719334680335136257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94995159146223120223424171 142492738719334680335136257)
  ·
    refine ⟨106869554039501010251352193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142492738719334680335136257 106869554039501010251352193)
    ·
      refine ⟨80152165529625757688514145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106869554039501010251352193 80152165529625757688514145)
      ·
        refine ⟨60114124147219318266385609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80152165529625757688514145 60114124147219318266385609)
        ·
          refine ⟨45085593110414488699789207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60114124147219318266385609 45085593110414488699789207)
          ·
            refine ⟨67628389665621733049683811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45085593110414488699789207 67628389665621733049683811)
            ·
              refine ⟨101442584498432599574525717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67628389665621733049683811 101442584498432599574525717)
              ·
                refine ⟨4755121148364028105055893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101442584498432599574525717 4755121148364028105055893)
                ·
                  refine ⟨222896303829563817424495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4755121148364028105055893 222896303829563817424495)
                  ·
                    rfl

theorem cell23_3906801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 6, 6].length) (baseStart_3906801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906801 prefixEnd_3906801 := by exact prefixLift 3906801
  have htrace : WordTrace (prefixWord ++ tailWord_3906801) baseStart_3906801 baseEnd_3906801 := by
    simpa [prefixWord, tailWord_3906801, baseEnd_3906801] using wordTrace_append hprefix tailTrace_3906801
  have hstable : (prefixWord ++ tailWord_3906801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906801).length < 2 ^ (prefixWord ++ tailWord_3906801).sum := by decide
  have hdescent : baseEnd_3906801 < baseStart_3906801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906911 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 6]
def baseStart_3906911 : Nat := 118140960795 + 3906911 * 2 ^ 59
def prefixEnd_3906911 : Nat := 4983230072969 + 3 ^ 40 * 3906911 * 2
def baseEnd_3906911 : Nat := 2006123217338068926444949

theorem tailTrace_3906911 : CollatzResearch.WordTrace tailWord_3906911 prefixEnd_3906911 2006123217338068926444949 := by
  unfold tailWord_3906911
  simp only [CollatzResearch.WordTrace]
  refine ⟨142496750748936169121640587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94997833832624112747760391 142496750748936169121640587)
  ·
    refine ⟨213745126123404253682460881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142496750748936169121640587 213745126123404253682460881)
    ·
      refine ⟨160308844592553190261845661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213745126123404253682460881 160308844592553190261845661)
      ·
        refine ⟨60115816722207446348192123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160308844592553190261845661 60115816722207446348192123)
        ·
          refine ⟨90173725083311169522288185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60115816722207446348192123 90173725083311169522288185)
          ·
            refine ⟨67630293812483377141716139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90173725083311169522288185 67630293812483377141716139)
            ·
              refine ⟨101445440718725065712574209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67630293812483377141716139 101445440718725065712574209)
              ·
                refine ⟨76084080539043799284430657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101445440718725065712574209 76084080539043799284430657)
                ·
                  refine ⟨57063060404282849463322993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76084080539043799284430657 57063060404282849463322993)
                  ·
                    refine ⟨42797295303212137097492245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57063060404282849463322993 42797295303212137097492245)
                    ·
                      refine ⟨2006123217338068926444949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42797295303212137097492245 2006123217338068926444949)
                      ·
                        rfl

theorem cell23_3906911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_3906911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906911 prefixEnd_3906911 := by exact prefixLift 3906911
  have htrace : WordTrace (prefixWord ++ tailWord_3906911) baseStart_3906911 baseEnd_3906911 := by
    simpa [prefixWord, tailWord_3906911, baseEnd_3906911] using wordTrace_append hprefix tailTrace_3906911
  have hstable : (prefixWord ++ tailWord_3906911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906911).length < 2 ^ (prefixWord ++ tailWord_3906911).sum := by decide
  have hdescent : baseEnd_3906911 < baseStart_3906911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906912 : List Nat := [2, 1, 1, 3, 4, 3, 1, 2, 2, 4]
def baseStart_3906912 : Nat := 118140960795 + 3906912 * 2 ^ 59
def prefixEnd_3906912 : Nat := 4983230072969 + 3 ^ 40 * 3906912 * 2
def baseEnd_3906912 : Nat := 668707910272907807510815

theorem tailTrace_3906912 : CollatzResearch.WordTrace tailWord_3906912 prefixEnd_3906912 668707910272907807510815 := by
  unfold tailWord_3906912
  simp only [CollatzResearch.WordTrace]
  refine ⟨71248393610966273146213495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94997858147955030861617993 71248393610966273146213495)
  ·
    refine ⟨106872590416449409719320243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71248393610966273146213495 106872590416449409719320243)
    ·
      refine ⟨160308885624674114578980365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106872590416449409719320243 160308885624674114578980365)
      ·
        refine ⟨60115832109252792967117637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160308885624674114578980365 60115832109252792967117637)
        ·
          refine ⟨11271718520484898681334557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60115832109252792967117637 11271718520484898681334557)
          ·
            refine ⟨4226894445181837005500459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11271718520484898681334557 4226894445181837005500459)
            ·
              refine ⟨6340341667772755508250689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4226894445181837005500459 6340341667772755508250689)
              ·
                refine ⟨4755256250829566631188017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6340341667772755508250689 4755256250829566631188017)
                ·
                  refine ⟨3566442188122174973391013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4755256250829566631188017 3566442188122174973391013)
                  ·
                    refine ⟨668707910272907807510815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3566442188122174973391013 668707910272907807510815)
                    ·
                      rfl

theorem cell23_3906912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 2, 4].length) (baseStart_3906912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906912 prefixEnd_3906912 := by exact prefixLift 3906912
  have htrace : WordTrace (prefixWord ++ tailWord_3906912) baseStart_3906912 baseEnd_3906912 := by
    simpa [prefixWord, tailWord_3906912, baseEnd_3906912] using wordTrace_append hprefix tailTrace_3906912
  have hstable : (prefixWord ++ tailWord_3906912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906912).length < 2 ^ (prefixWord ++ tailWord_3906912).sum := by decide
  have hdescent : baseEnd_3906912 < baseStart_3906912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906919 : List Nat := [1, 1, 5, 1, 4, 1, 2, 1, 3, 2, 2]
def baseStart_3906919 : Nat := 118140960795 + 3906919 * 2 ^ 59
def prefixEnd_3906919 : Nat := 4983230072969 + 3 ^ 40 * 3906919 * 2
def baseEnd_3906919 : Nat := 2006127325183304895144913

theorem tailTrace_3906919 : CollatzResearch.WordTrace tailWord_3906919 prefixEnd_3906919 2006127325183304895144913 := by
  unfold tailWord_3906919
  simp only [CollatzResearch.WordTrace]
  refine ⟨142497042532907186487931811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94998028355271457658621207 142497042532907186487931811)
  ·
    refine ⟨213745563799360779731897717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142497042532907186487931811 213745563799360779731897717)
    ·
      refine ⟨20038646606190073099865411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 213745563799360779731897717 20038646606190073099865411)
      ·
        refine ⟨30057969909285109649798117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20038646606190073099865411 30057969909285109649798117)
        ·
          refine ⟨5635869357990958059337147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30057969909285109649798117 5635869357990958059337147)
          ·
            refine ⟨8453804036986437089005721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5635869357990958059337147 8453804036986437089005721)
            ·
              refine ⟨6340353027739827816754291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8453804036986437089005721 6340353027739827816754291)
              ·
                refine ⟨9510529541609741725131437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6340353027739827816754291 9510529541609741725131437)
                ·
                  refine ⟨3566448578103653146924289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9510529541609741725131437 3566448578103653146924289)
                  ·
                    refine ⟨2674836433577739860193217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3566448578103653146924289 2674836433577739860193217)
                    ·
                      refine ⟨2006127325183304895144913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2674836433577739860193217 2006127325183304895144913)
                      ·
                        rfl

theorem cell23_3906919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_3906919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906919 prefixEnd_3906919 := by exact prefixLift 3906919
  have htrace : WordTrace (prefixWord ++ tailWord_3906919) baseStart_3906919 baseEnd_3906919 := by
    simpa [prefixWord, tailWord_3906919, baseEnd_3906919] using wordTrace_append hprefix tailTrace_3906919
  have hstable : (prefixWord ++ tailWord_3906919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906919).length < 2 ^ (prefixWord ++ tailWord_3906919).sum := by decide
  have hdescent : baseEnd_3906919 < baseStart_3906919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906921 : List Nat := [1, 2, 1, 1, 1, 3, 2, 3, 2, 7]
def baseStart_3906921 : Nat := 118140960795 + 3906921 * 2 ^ 59
def prefixEnd_3906921 : Nat := 4983230072969 + 3 ^ 40 * 3906921 * 2
def baseEnd_3906921 : Nat := 668709450714871295773301

theorem tailTrace_3906921 : CollatzResearch.WordTrace tailWord_3906921 prefixEnd_3906921 668709450714871295773301 := by
  unfold tailWord_3906921
  simp only [CollatzResearch.WordTrace]
  refine ⟨142497115478899940829504617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94998076985933293886336411 142497115478899940829504617)
  ·
    refine ⟨106872836609174955622128463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142497115478899940829504617 106872836609174955622128463)
    ·
      refine ⟨160309254913762433433192695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106872836609174955622128463 160309254913762433433192695)
      ·
        refine ⟨240463882370643650149789043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160309254913762433433192695 240463882370643650149789043)
        ·
          refine ⟨360695823555965475224683565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240463882370643650149789043 360695823555965475224683565)
          ·
            refine ⟨135260933833487053209256337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360695823555965475224683565 135260933833487053209256337)
            ·
              refine ⟨101445700375115289906942253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135260933833487053209256337 101445700375115289906942253)
              ·
                refine ⟨38042137640668233715103345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101445700375115289906942253 38042137640668233715103345)
                ·
                  refine ⟨28531603230501175286327509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38042137640668233715103345 28531603230501175286327509)
                  ·
                    refine ⟨668709450714871295773301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28531603230501175286327509 668709450714871295773301)
                    ·
                      rfl

theorem cell23_3906921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 7].length) (baseStart_3906921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906921 prefixEnd_3906921 := by exact prefixLift 3906921
  have htrace : WordTrace (prefixWord ++ tailWord_3906921) baseStart_3906921 baseEnd_3906921 := by
    simpa [prefixWord, tailWord_3906921, baseEnd_3906921] using wordTrace_append hprefix tailTrace_3906921
  have hstable : (prefixWord ++ tailWord_3906921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906921).length < 2 ^ (prefixWord ++ tailWord_3906921).sum := by decide
  have hdescent : baseEnd_3906921 < baseStart_3906921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906931 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 5]
def baseStart_3906931 : Nat := 118140960795 + 3906931 * 2 ^ 59
def prefixEnd_3906931 : Nat := 4983230072969 + 3 ^ 40 * 3906931 * 2
def baseEnd_3906931 : Nat := 2006133486951158848194857

theorem tailTrace_3906931 : CollatzResearch.WordTrace tailWord_3906931 prefixEnd_3906931 2006133486951158848194857 := by
  unfold tailWord_3906931
  simp only [CollatzResearch.WordTrace]
  refine ⟨142497480208863712537368647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94998320139242475024912431 142497480208863712537368647)
  ·
    refine ⟨213746220313295568806052971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142497480208863712537368647 213746220313295568806052971)
    ·
      refine ⟨320619330469943353209079457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213746220313295568806052971 320619330469943353209079457)
      ·
        refine ⟨240464497852457514906809593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320619330469943353209079457 240464497852457514906809593)
        ·
          refine ⟨180348373389343136180107195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240464497852457514906809593 180348373389343136180107195)
          ·
            refine ⟨270522560084014704270160793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180348373389343136180107195 270522560084014704270160793)
            ·
              refine ⟨202891920063011028202620595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270522560084014704270160793 202891920063011028202620595)
              ·
                refine ⟨304337880094516542303930893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202891920063011028202620595 304337880094516542303930893)
                ·
                  refine ⟨114126705035443703363974085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 304337880094516542303930893 114126705035443703363974085)
                  ·
                    refine ⟨21398757194145694380745141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114126705035443703363974085 21398757194145694380745141)
                    ·
                      refine ⟨2006133486951158848194857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21398757194145694380745141 2006133486951158848194857)
                      ·
                        rfl

theorem cell23_3906931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 5].length) (baseStart_3906931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906931 prefixEnd_3906931 := by exact prefixLift 3906931
  have htrace : WordTrace (prefixWord ++ tailWord_3906931) baseStart_3906931 baseEnd_3906931 := by
    simpa [prefixWord, tailWord_3906931, baseEnd_3906931] using wordTrace_append hprefix tailTrace_3906931
  have hstable : (prefixWord ++ tailWord_3906931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906931).length < 2 ^ (prefixWord ++ tailWord_3906931).sum := by decide
  have hdescent : baseEnd_3906931 < baseStart_3906931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906942 : List Nat := [4, 2, 3, 2, 1, 1, 1, 9]
def baseStart_3906942 : Nat := 118140960795 + 3906942 * 2 ^ 59
def prefixEnd_3906942 : Nat := 4983230072969 + 3 ^ 40 * 3906942 * 2
def baseEnd_3906942 : Nat := 74301449453272529820641

theorem tailTrace_3906942 : CollatzResearch.WordTrace tailWord_3906942 prefixEnd_3906942 74301449453272529820641 := by
  unfold tailWord_3906942
  simp only [CollatzResearch.WordTrace]
  refine ⟨17812235176477982677002385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94998587607882574277346053 17812235176477982677002385)
  ·
    refine ⟨13359176382358487007751789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17812235176477982677002385 13359176382358487007751789)
    ·
      refine ⟨5009691143384432627906921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13359176382358487007751789 5009691143384432627906921)
      ·
        refine ⟨3757268357538324470930191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5009691143384432627906921 3757268357538324470930191)
        ·
          refine ⟨5635902536307486706395287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3757268357538324470930191 5635902536307486706395287)
          ·
            refine ⟨8453853804461230059592931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5635902536307486706395287 8453853804461230059592931)
            ·
              refine ⟨12680780706691845089389397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8453853804461230059592931 12680780706691845089389397)
              ·
                refine ⟨74301449453272529820641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12680780706691845089389397 74301449453272529820641)
                ·
                  rfl

theorem cell23_3906942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 9].length) (baseStart_3906942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906942 prefixEnd_3906942 := by exact prefixLift 3906942
  have htrace : WordTrace (prefixWord ++ tailWord_3906942) baseStart_3906942 baseEnd_3906942 := by
    simpa [prefixWord, tailWord_3906942, baseEnd_3906942] using wordTrace_append hprefix tailTrace_3906942
  have hstable : (prefixWord ++ tailWord_3906942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906942).length < 2 ^ (prefixWord ++ tailWord_3906942).sum := by decide
  have hdescent : baseEnd_3906942 < baseStart_3906942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906948 : List Nat := [2, 3, 2, 1, 1, 3, 1, 1, 2, 2, 5]
def baseStart_3906948 : Nat := 118140960795 + 3906948 * 2 ^ 59
def prefixEnd_3906948 : Nat := 4983230072969 + 3 ^ 40 * 3906948 * 2
def baseEnd_3906948 : Nat := 2006142216122285281682279

theorem tailTrace_3906948 : CollatzResearch.WordTrace tailWord_3906948 prefixEnd_3906948 2006142216122285281682279 := by
  unfold tailWord_3906948
  simp only [CollatzResearch.WordTrace]
  refine ⟨71249050124901062220368749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94998733499868082960491665 71249050124901062220368749)
  ·
    refine ⟨26718393796837898332638281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71249050124901062220368749 26718393796837898332638281)
    ·
      refine ⟨20038795347628423749478711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26718393796837898332638281 20038795347628423749478711)
      ·
        refine ⟨30058193021442635624218067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20038795347628423749478711 30058193021442635624218067)
        ·
          refine ⟨45087289532163953436327101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30058193021442635624218067 45087289532163953436327101)
          ·
            refine ⟨16907733574561482538622663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45087289532163953436327101 16907733574561482538622663)
            ·
              refine ⟨25361600361842223807933995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16907733574561482538622663 25361600361842223807933995)
              ·
                refine ⟨38042400542763335711900993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25361600361842223807933995 38042400542763335711900993)
                ·
                  refine ⟨28531800407072501783925745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38042400542763335711900993 28531800407072501783925745)
                  ·
                    refine ⟨21398850305304376337944309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28531800407072501783925745 21398850305304376337944309)
                    ·
                      refine ⟨2006142216122285281682279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21398850305304376337944309 2006142216122285281682279)
                      ·
                        rfl

theorem cell23_3906948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_3906948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906948 prefixEnd_3906948 := by exact prefixLift 3906948
  have htrace : WordTrace (prefixWord ++ tailWord_3906948) baseStart_3906948 baseEnd_3906948 := by
    simpa [prefixWord, tailWord_3906948, baseEnd_3906948] using wordTrace_append hprefix tailTrace_3906948
  have hstable : (prefixWord ++ tailWord_3906948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906948).length < 2 ^ (prefixWord ++ tailWord_3906948).sum := by decide
  have hdescent : baseEnd_3906948 < baseStart_3906948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906953 : List Nat := [1, 2, 1, 1, 8, 1, 1, 3, 1, 2, 2]
def baseStart_3906953 : Nat := 118140960795 + 3906953 * 2 ^ 59
def prefixEnd_3906953 : Nat := 4983230072969 + 3 ^ 40 * 3906953 * 2
def baseEnd_3906953 : Nat := 2006144783525557762119757

theorem tailTrace_3906953 : CollatzResearch.WordTrace tailWord_3906953 prefixEnd_3906953 2006144783525557762119757 := by
  unfold tailWord_3906953
  simp only [CollatzResearch.WordTrace]
  refine ⟨142498282614784010294669513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94998855076522673529779675 142498282614784010294669513)
  ·
    refine ⟨106873711961088007721002135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142498282614784010294669513 106873711961088007721002135)
    ·
      refine ⟨160310567941632011581503203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106873711961088007721002135 160310567941632011581503203)
      ·
        refine ⟨240465851912448017372254805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160310567941632011581503203 240465851912448017372254805)
        ·
          refine ⟨2817959202099000203581111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 240465851912448017372254805 2817959202099000203581111)
          ·
            refine ⟨4226938803148500305371667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2817959202099000203581111 4226938803148500305371667)
            ·
              refine ⟨6340408204722750458057501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4226938803148500305371667 6340408204722750458057501)
              ·
                refine ⟨2377653076771031421771563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6340408204722750458057501 2377653076771031421771563)
                ·
                  refine ⟨3566479615156547132657345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2377653076771031421771563 3566479615156547132657345)
                  ·
                    refine ⟨2674859711367410349493009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3566479615156547132657345 2674859711367410349493009)
                    ·
                      refine ⟨2006144783525557762119757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2674859711367410349493009 2006144783525557762119757)
                      ·
                        rfl

theorem cell23_3906953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 3, 1, 2, 2].length) (baseStart_3906953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906953 prefixEnd_3906953 := by exact prefixLift 3906953
  have htrace : WordTrace (prefixWord ++ tailWord_3906953) baseStart_3906953 baseEnd_3906953 := by
    simpa [prefixWord, tailWord_3906953, baseEnd_3906953] using wordTrace_append hprefix tailTrace_3906953
  have hstable : (prefixWord ++ tailWord_3906953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906953).length < 2 ^ (prefixWord ++ tailWord_3906953).sum := by decide
  have hdescent : baseEnd_3906953 < baseStart_3906953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906988 : List Nat := [2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 4]
def baseStart_3906988 : Nat := 118140960795 + 3906988 * 2 ^ 59
def prefixEnd_3906988 : Nat := 4983230072969 + 3 ^ 40 * 3906988 * 2
def baseEnd_3906988 : Nat := 2006162755348465125182095

theorem tailTrace_3906988 : CollatzResearch.WordTrace tailWord_3906988 prefixEnd_3906988 2006162755348465125182095 := by
  unfold tailWord_3906988
  simp only [CollatzResearch.WordTrace]
  refine ⟨71249779584828605636096809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94999706113104807514795745 71249779584828605636096809)
  ·
    refine ⟨53437334688621454227072607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71249779584828605636096809 53437334688621454227072607)
    ·
      refine ⟨80156002032932181340608911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53437334688621454227072607 80156002032932181340608911)
      ·
        refine ⟨120234003049398272010913367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80156002032932181340608911 120234003049398272010913367)
        ·
          refine ⟨180351004574097408016370051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120234003049398272010913367 180351004574097408016370051)
          ·
            refine ⟨270526506861146112024555077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180351004574097408016370051 270526506861146112024555077)
            ·
              refine ⟨50723720036464896004604077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 270526506861146112024555077 50723720036464896004604077)
              ·
                refine ⟨19021395013674336001726529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50723720036464896004604077 19021395013674336001726529)
                ·
                  refine ⟨14266046260255752001294897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19021395013674336001726529 14266046260255752001294897)
                  ·
                    refine ⟨10699534695191814000971173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14266046260255752001294897 10699534695191814000971173)
                    ·
                      refine ⟨2006162755348465125182095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10699534695191814000971173 2006162755348465125182095)
                      ·
                        rfl

theorem cell23_3906988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_3906988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3906988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3906988 prefixEnd_3906988 := by exact prefixLift 3906988
  have htrace : WordTrace (prefixWord ++ tailWord_3906988) baseStart_3906988 baseEnd_3906988 := by
    simpa [prefixWord, tailWord_3906988, baseEnd_3906988] using wordTrace_append hprefix tailTrace_3906988
  have hstable : (prefixWord ++ tailWord_3906988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906988).length < 2 ^ (prefixWord ++ tailWord_3906988).sum := by decide
  have hdescent : baseEnd_3906988 < baseStart_3906988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907015 : List Nat := [1, 1, 4, 1, 1, 3, 2, 5, 5]
def baseStart_3907015 : Nat := 118140960795 + 3907015 * 2 ^ 59
def prefixEnd_3907015 : Nat := 4983230072969 + 3 ^ 40 * 3907015 * 2
def baseEnd_3907015 : Nat := 222908513258459613282719

theorem tailTrace_3907015 : CollatzResearch.WordTrace tailWord_3907015 prefixEnd_3907015 222908513258459613282719 := by
  unfold tailWord_3907015
  simp only [CollatzResearch.WordTrace]
  refine ⟨142500543940559394883426499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95000362627039596588950999 142500543940559394883426499)
  ·
    refine ⟨213750815910839092325139749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142500543940559394883426499 213750815910839092325139749)
    ·
      refine ⟨40078277983282329810963703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213750815910839092325139749 40078277983282329810963703)
      ·
        refine ⟨60117416974923494716445555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40078277983282329810963703 60117416974923494716445555)
        ·
          refine ⟨90176125462385242074668333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60117416974923494716445555 90176125462385242074668333)
          ·
            refine ⟨33816047048394465778000625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90176125462385242074668333 33816047048394465778000625)
            ·
              refine ⟨25362035286295849333500469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33816047048394465778000625 25362035286295849333500469)
              ·
                refine ⟨2377690808090235875015669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25362035286295849333500469 2377690808090235875015669)
                ·
                  refine ⟨222908513258459613282719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2377690808090235875015669 222908513258459613282719)
                  ·
                    rfl

theorem cell23_3907015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 5, 5].length) (baseStart_3907015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907015 prefixEnd_3907015 := by exact prefixLift 3907015
  have htrace : WordTrace (prefixWord ++ tailWord_3907015) baseStart_3907015 baseEnd_3907015 := by
    simpa [prefixWord, tailWord_3907015, baseEnd_3907015] using wordTrace_append hprefix tailTrace_3907015
  have hstable : (prefixWord ++ tailWord_3907015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907015).length < 2 ^ (prefixWord ++ tailWord_3907015).sum := by decide
  have hdescent : baseEnd_3907015 < baseStart_3907015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907032 : List Nat := [2, 1, 2, 2, 2, 1, 6, 2, 5]
def baseStart_3907032 : Nat := 118140960795 + 3907032 * 2 ^ 59
def prefixEnd_3907032 : Nat := 4983230072969 + 3 ^ 40 * 3907032 * 2
def baseEnd_3907032 : Nat := 222909483166362550336877

theorem tailTrace_3907032 : CollatzResearch.WordTrace tailWord_3907032 prefixEnd_3907032 222909483166362550336877 := by
  unfold tailWord_3907032
  simp only [CollatzResearch.WordTrace]
  refine ⟨71250581990748903393397675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95000775987665204524530233 71250581990748903393397675)
  ·
    refine ⟨106875872986123355090096513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71250581990748903393397675 106875872986123355090096513)
    ·
      refine ⟨80156904739592516317572385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106875872986123355090096513 80156904739592516317572385)
      ·
        refine ⟨60117678554694387238179289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80156904739592516317572385 60117678554694387238179289)
        ·
          refine ⟨45088258916020790428634467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60117678554694387238179289 45088258916020790428634467)
          ·
            refine ⟨67632388374031185642951701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45088258916020790428634467 67632388374031185642951701)
            ·
              refine ⟨3170268205032711827013361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67632388374031185642951701 3170268205032711827013361)
              ·
                refine ⟨2377701153774533870260021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3170268205032711827013361 2377701153774533870260021)
                ·
                  refine ⟨222909483166362550336877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2377701153774533870260021 222909483166362550336877)
                  ·
                    rfl

theorem cell23_3907032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 2, 5].length) (baseStart_3907032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907032 prefixEnd_3907032 := by exact prefixLift 3907032
  have htrace : WordTrace (prefixWord ++ tailWord_3907032) baseStart_3907032 baseEnd_3907032 := by
    simpa [prefixWord, tailWord_3907032, baseEnd_3907032] using wordTrace_append hprefix tailTrace_3907032
  have hstable : (prefixWord ++ tailWord_3907032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907032).length < 2 ^ (prefixWord ++ tailWord_3907032).sum := by decide
  have hdescent : baseEnd_3907032 < baseStart_3907032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907062 : List Nat := [5, 1, 1, 1, 2, 2, 3, 1, 2, 5]
def baseStart_3907062 : Nat := 118140960795 + 3907062 * 2 ^ 59
def prefixEnd_3907062 : Nat := 4983230072969 + 3 ^ 40 * 3907062 * 2
def baseEnd_3907062 : Nat := 668733584305632611885585

theorem tailTrace_3907062 : CollatzResearch.WordTrace tailWord_3907062 prefixEnd_3907062 668733584305632611885585 := by
  unfold tailWord_3907062
  simp only [CollatzResearch.WordTrace]
  refine ⟨8906391135711820119399215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95001505447592747940258293 8906391135711820119399215)
  ·
    refine ⟨13359586703567730179098823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8906391135711820119399215 13359586703567730179098823)
    ·
      refine ⟨20039380055351595268648235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13359586703567730179098823 20039380055351595268648235)
      ·
        refine ⟨30059070083027392902972353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20039380055351595268648235 30059070083027392902972353)
        ·
          refine ⟨22544302562270544677229265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30059070083027392902972353 22544302562270544677229265)
          ·
            refine ⟨16908226921702908507921949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22544302562270544677229265 16908226921702908507921949)
            ·
              refine ⟨6340585095638590690470731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16908226921702908507921949 6340585095638590690470731)
              ·
                refine ⟨9510877643457886035706097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6340585095638590690470731 9510877643457886035706097)
                ·
                  refine ⟨7133158232593414526779573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9510877643457886035706097 7133158232593414526779573)
                  ·
                    refine ⟨668733584305632611885585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7133158232593414526779573 668733584305632611885585)
                    ·
                      rfl

theorem cell23_3907062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_3907062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907062 prefixEnd_3907062 := by exact prefixLift 3907062
  have htrace : WordTrace (prefixWord ++ tailWord_3907062) baseStart_3907062 baseEnd_3907062 := by
    simpa [prefixWord, tailWord_3907062, baseEnd_3907062] using wordTrace_append hprefix tailTrace_3907062
  have hstable : (prefixWord ++ tailWord_3907062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907062).length < 2 ^ (prefixWord ++ tailWord_3907062).sum := by decide
  have hdescent : baseEnd_3907062 < baseStart_3907062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907065 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 3, 6, 2]
def baseStart_3907065 : Nat := 118140960795 + 3907065 * 2 ^ 59
def prefixEnd_3907065 : Nat := 4983230072969 + 3 ^ 40 * 3907065 * 2
def baseEnd_3907065 : Nat := 2006202293358861323919241

theorem tailTrace_3907065 : CollatzResearch.WordTrace tailWord_3907065 prefixEnd_3907065 2006202293358861323919241 := by
  unfold tailWord_3907065
  simp only [CollatzResearch.WordTrace]
  refine ⟨142502367590378253422746649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95001578393585502281831099 142502367590378253422746649)
  ·
    refine ⟨106876775692783690067059987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142502367590378253422746649 106876775692783690067059987)
    ·
      refine ⟨160315163539175535100589981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106876775692783690067059987 160315163539175535100589981)
      ·
        refine ⟨60118186327190825662721243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160315163539175535100589981 60118186327190825662721243)
        ·
          refine ⟨90177279490786238494081865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60118186327190825662721243 90177279490786238494081865)
          ·
            refine ⟨67632959618089678870561399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90177279490786238494081865 67632959618089678870561399)
            ·
              refine ⟨101449439427134518305842099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67632959618089678870561399 101449439427134518305842099)
              ·
                refine ⟨152174159140701777458763149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101449439427134518305842099 152174159140701777458763149)
                ·
                  refine ⟨57065309677763166547036181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152174159140701777458763149 57065309677763166547036181)
                  ·
                    refine ⟨2674936391145148431892321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57065309677763166547036181 2674936391145148431892321)
                    ·
                      refine ⟨2006202293358861323919241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2674936391145148431892321 2006202293358861323919241)
                      ·
                        rfl

theorem cell23_3907065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 6, 2].length) (baseStart_3907065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907065 prefixEnd_3907065 := by exact prefixLift 3907065
  have htrace : WordTrace (prefixWord ++ tailWord_3907065) baseStart_3907065 baseEnd_3907065 := by
    simpa [prefixWord, tailWord_3907065, baseEnd_3907065] using wordTrace_append hprefix tailTrace_3907065
  have hstable : (prefixWord ++ tailWord_3907065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907065).length < 2 ^ (prefixWord ++ tailWord_3907065).sum := by decide
  have hdescent : baseEnd_3907065 < baseStart_3907065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907082 : List Nat := [3, 1, 2, 2, 2, 2, 1, 2, 2, 4, 2]
def baseStart_3907082 : Nat := 118140960795 + 3907082 * 2 ^ 59
def prefixEnd_3907082 : Nat := 4983230072969 + 3 ^ 40 * 3907082 * 2
def baseEnd_3907082 : Nat := 2006211022529987757406663

theorem tailTrace_3907082 : CollatzResearch.WordTrace tailWord_3907082 prefixEnd_3907082 2006211022529987757406663 := by
  unfold tailWord_3907082
  simp only [CollatzResearch.WordTrace]
  refine ⟨35625746907829166331528875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95001991754211110217410333 35625746907829166331528875)
  ·
    refine ⟨53438620361743749497293313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35625746907829166331528875 53438620361743749497293313)
    ·
      refine ⟨40078965271307812122969985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53438620361743749497293313 40078965271307812122969985)
      ·
        refine ⟨30059223953480859092227489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40078965271307812122969985 30059223953480859092227489)
        ·
          refine ⟨22544417965110644319170617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30059223953480859092227489 22544417965110644319170617)
          ·
            refine ⟨16908313473832983239377963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22544417965110644319170617 16908313473832983239377963)
            ·
              refine ⟨25362470210749474859066945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16908313473832983239377963 25362470210749474859066945)
              ·
                refine ⟨19021852658062106144300209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25362470210749474859066945 19021852658062106144300209)
                ·
                  refine ⟨14266389493546579608225157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19021852658062106144300209 14266389493546579608225157)
                  ·
                    refine ⟨2674948030039983676542217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14266389493546579608225157 2674948030039983676542217)
                    ·
                      refine ⟨2006211022529987757406663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2674948030039983676542217 2006211022529987757406663)
                      ·
                        rfl

theorem cell23_3907082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_3907082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907082 prefixEnd_3907082 := by exact prefixLift 3907082
  have htrace : WordTrace (prefixWord ++ tailWord_3907082) baseStart_3907082 baseEnd_3907082 := by
    simpa [prefixWord, tailWord_3907082, baseEnd_3907082] using wordTrace_append hprefix tailTrace_3907082
  have hstable : (prefixWord ++ tailWord_3907082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907082).length < 2 ^ (prefixWord ++ tailWord_3907082).sum := by decide
  have hdescent : baseEnd_3907082 < baseStart_3907082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907172 : List Nat := [2, 3, 1, 1, 2, 4, 1, 1, 3, 1, 4]
def baseStart_3907172 : Nat := 118140960795 + 3907172 * 2 ^ 59
def prefixEnd_3907172 : Nat := 4983230072969 + 3 ^ 40 * 3907172 * 2
def baseEnd_3907172 : Nat := 2006257235788892405281249

theorem tailTrace_3907172 : CollatzResearch.WordTrace tailWord_3907172 prefixEnd_3907172 2006257235788892405281249 := by
  unfold tailWord_3907172
  simp only [CollatzResearch.WordTrace]
  refine ⟨71253135100495305348445885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95004180133993740464594513 71253135100495305348445885)
  ·
    refine ⟨26719925662685739505667207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71253135100495305348445885 26719925662685739505667207)
    ·
      refine ⟨40079888494028609258500811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26719925662685739505667207 40079888494028609258500811)
      ·
        refine ⟨60119832741042913887751217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40079888494028609258500811 60119832741042913887751217)
        ·
          refine ⟨45089874555782185415813413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60119832741042913887751217 45089874555782185415813413)
          ·
            refine ⟨8454351479209159765465015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45089874555782185415813413 8454351479209159765465015)
            ·
              refine ⟨12681527218813739648197523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8454351479209159765465015 12681527218813739648197523)
              ·
                refine ⟨19022290828220609472296285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12681527218813739648197523 19022290828220609472296285)
                ·
                  refine ⟨7133359060582728552111107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19022290828220609472296285 7133359060582728552111107)
                  ·
                    refine ⟨10700038590874092828166661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7133359060582728552111107 10700038590874092828166661)
                    ·
                      refine ⟨2006257235788892405281249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10700038590874092828166661 2006257235788892405281249)
                      ·
                        rfl

theorem cell23_3907172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_3907172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907172 prefixEnd_3907172 := by exact prefixLift 3907172
  have htrace : WordTrace (prefixWord ++ tailWord_3907172) baseStart_3907172 baseEnd_3907172 := by
    simpa [prefixWord, tailWord_3907172, baseEnd_3907172] using wordTrace_append hprefix tailTrace_3907172
  have hstable : (prefixWord ++ tailWord_3907172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907172).length < 2 ^ (prefixWord ++ tailWord_3907172).sum := by decide
  have hdescent : baseEnd_3907172 < baseStart_3907172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907175 : List Nat := [1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 5]
def baseStart_3907175 : Nat := 118140960795 + 3907175 * 2 ^ 59
def prefixEnd_3907175 : Nat := 4983230072969 + 3 ^ 40 * 3907175 * 2
def baseEnd_3907175 : Nat := 2006258776230855893543735

theorem tailTrace_3907175 : CollatzResearch.WordTrace tailWord_3907175 prefixEnd_3907175 2006258776230855893543735 := by
  unfold tailWord_3907175
  simp only [CollatzResearch.WordTrace]
  refine ⟨142506379619979742209250979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95004253079986494806167319 142506379619979742209250979)
  ·
    refine ⟨213759569429969613313876469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142506379619979742209250979 213759569429969613313876469)
    ·
      refine ⟨20039959634059651248175919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 213759569429969613313876469 20039959634059651248175919)
      ·
        refine ⟨30059939451089476872263879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20039959634059651248175919 30059939451089476872263879)
        ·
          refine ⟨45089909176634215308395819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30059939451089476872263879 45089909176634215308395819)
          ·
            refine ⟨67634863764951322962593729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45089909176634215308395819 67634863764951322962593729)
            ·
              refine ⟨50726147823713492221945297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67634863764951322962593729 50726147823713492221945297)
              ·
                refine ⟨38044610867785119166458973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50726147823713492221945297 38044610867785119166458973)
                ·
                  refine ⟨14266729075419419687422115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38044610867785119166458973 14266729075419419687422115)
                  ·
                    refine ⟨21400093613129129531133173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14266729075419419687422115 21400093613129129531133173)
                    ·
                      refine ⟨2006258776230855893543735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21400093613129129531133173 2006258776230855893543735)
                      ·
                        rfl

theorem cell23_3907175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_3907175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907175 prefixEnd_3907175 := by exact prefixLift 3907175
  have htrace : WordTrace (prefixWord ++ tailWord_3907175) baseStart_3907175 baseEnd_3907175 := by
    simpa [prefixWord, tailWord_3907175, baseEnd_3907175] using wordTrace_append hprefix tailTrace_3907175
  have hstable : (prefixWord ++ tailWord_3907175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907175).length < 2 ^ (prefixWord ++ tailWord_3907175).sum := by decide
  have hdescent : baseEnd_3907175 < baseStart_3907175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907176 : List Nat := [2, 1, 4, 3, 1, 2, 2, 1, 2, 3, 2]
def baseStart_3907176 : Nat := 118140960795 + 3907176 * 2 ^ 59
def prefixEnd_3907176 : Nat := 4983230072969 + 3 ^ 40 * 3907176 * 2
def baseEnd_3907176 : Nat := 2006259289711510389631231

theorem tailTrace_3907176 : CollatzResearch.WordTrace tailWord_3907176 prefixEnd_3907176 2006259289711510389631231 := by
  unfold tailWord_3907176
  simp only [CollatzResearch.WordTrace]
  refine ⟨71253208046488059690018691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95004277395317412920024921 71253208046488059690018691)
  ·
    refine ⟨106879812069732089535028037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71253208046488059690018691 106879812069732089535028037)
    ·
      refine ⟨20039964763074766787817757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106879812069732089535028037 20039964763074766787817757)
      ·
        refine ⟨7514986786153037545431659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20039964763074766787817757 7514986786153037545431659)
        ·
          refine ⟨11272480179229556318147489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7514986786153037545431659 11272480179229556318147489)
          ·
            refine ⟨8454360134422167238610617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11272480179229556318147489 8454360134422167238610617)
            ·
              refine ⟨6340770100816625428957963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8454360134422167238610617 6340770100816625428957963)
              ·
                refine ⟨9511155151224938143436945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6340770100816625428957963 9511155151224938143436945)
                ·
                  refine ⟨7133366363418703607577709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9511155151224938143436945 7133366363418703607577709)
                  ·
                    refine ⟨2675012386282013852841641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7133366363418703607577709 2675012386282013852841641)
                    ·
                      refine ⟨2006259289711510389631231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2675012386282013852841641 2006259289711510389631231)
                      ·
                        rfl

theorem cell23_3907176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_3907176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907176 prefixEnd_3907176 := by exact prefixLift 3907176
  have htrace : WordTrace (prefixWord ++ tailWord_3907176) baseStart_3907176 baseEnd_3907176 := by
    simpa [prefixWord, tailWord_3907176, baseEnd_3907176] using wordTrace_append hprefix tailTrace_3907176
  have hstable : (prefixWord ++ tailWord_3907176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907176).length < 2 ^ (prefixWord ++ tailWord_3907176).sum := by decide
  have hdescent : baseEnd_3907176 < baseStart_3907176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907235 : List Nat := [1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 5]
def baseStart_3907235 : Nat := 118140960795 + 3907235 * 2 ^ 59
def prefixEnd_3907235 : Nat := 4983230072969 + 3 ^ 40 * 3907235 * 2
def baseEnd_3907235 : Nat := 2006289585070125658793459

theorem tailTrace_3907235 : CollatzResearch.WordTrace tailWord_3907235 prefixEnd_3907235 2006289585070125658793459 := by
  unfold tailWord_3907235
  simp only [CollatzResearch.WordTrace]
  refine ⟨142508567999762372456435159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95005711999841581637623439 142508567999762372456435159)
  ·
    refine ⟨213762851999643558684652739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142508567999762372456435159 213762851999643558684652739)
    ·
      refine ⟨320644277999465338026979109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213762851999643558684652739 320644277999465338026979109)
      ·
        refine ⟨60120802124899750880058583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 320644277999465338026979109 60120802124899750880058583)
        ·
          refine ⟨90181203187349626320087875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60120802124899750880058583 90181203187349626320087875)
          ·
            refine ⟨135271804781024439480131813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90181203187349626320087875 135271804781024439480131813)
            ·
              refine ⟨25363463396442082402524715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135271804781024439480131813 25363463396442082402524715)
              ·
                refine ⟨38045195094663123603787073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25363463396442082402524715 38045195094663123603787073)
                ·
                  refine ⟨28533896320997342702840305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38045195094663123603787073 28533896320997342702840305)
                  ·
                    refine ⟨21400422240748007027130229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28533896320997342702840305 21400422240748007027130229)
                    ·
                      refine ⟨2006289585070125658793459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21400422240748007027130229 2006289585070125658793459)
                      ·
                        rfl

theorem cell23_3907235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_3907235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907235 prefixEnd_3907235 := by exact prefixLift 3907235
  have htrace : WordTrace (prefixWord ++ tailWord_3907235) baseStart_3907235 baseEnd_3907235 := by
    simpa [prefixWord, tailWord_3907235, baseEnd_3907235] using wordTrace_append hprefix tailTrace_3907235
  have hstable : (prefixWord ++ tailWord_3907235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907235).length < 2 ^ (prefixWord ++ tailWord_3907235).sum := by decide
  have hdescent : baseEnd_3907235 < baseStart_3907235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907299 : List Nat := [1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 5]
def baseStart_3907299 : Nat := 118140960795 + 3907299 * 2 ^ 59
def prefixEnd_3907299 : Nat := 4983230072969 + 3 ^ 40 * 3907299 * 2
def baseEnd_3907299 : Nat := 2006322447832013408393165

theorem tailTrace_3907299 : CollatzResearch.WordTrace tailWord_3907299 prefixEnd_3907299 2006322447832013408393165 := by
  unfold tailWord_3907299
  simp only [CollatzResearch.WordTrace]
  refine ⟨142510902271530511386764951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95007268181020340924509967 142510902271530511386764951)
  ·
    refine ⟨213766353407295767080147427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142510902271530511386764951 213766353407295767080147427)
    ·
      refine ⟨320649530110943650620221141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213766353407295767080147427 320649530110943650620221141)
      ·
        refine ⟨7515223361975241811411433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 320649530110943650620221141 7515223361975241811411433)
        ·
          refine ⟨5636417521481431358558575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7515223361975241811411433 5636417521481431358558575)
          ·
            refine ⟨8454626282222147037837863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5636417521481431358558575 8454626282222147037837863)
            ·
              refine ⟨12681939423333220556756795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8454626282222147037837863 12681939423333220556756795)
              ·
                refine ⟨19022909134999830835135193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12681939423333220556756795 19022909134999830835135193)
                ·
                  refine ⟨14267181851249873126351395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19022909134999830835135193 14267181851249873126351395)
                  ·
                    refine ⟨21400772776874809689527093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14267181851249873126351395 21400772776874809689527093)
                    ·
                      refine ⟨2006322447832013408393165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21400772776874809689527093 2006322447832013408393165)
                      ·
                        rfl

theorem cell23_3907299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_3907299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907299 prefixEnd_3907299 := by exact prefixLift 3907299
  have htrace : WordTrace (prefixWord ++ tailWord_3907299) baseStart_3907299 baseEnd_3907299 := by
    simpa [prefixWord, tailWord_3907299, baseEnd_3907299] using wordTrace_append hprefix tailTrace_3907299
  have hstable : (prefixWord ++ tailWord_3907299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907299).length < 2 ^ (prefixWord ++ tailWord_3907299).sum := by decide
  have hdescent : baseEnd_3907299 < baseStart_3907299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907312 : List Nat := [2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 3]
def baseStart_3907312 : Nat := 118140960795 + 3907312 * 2 ^ 59
def prefixEnd_3907312 : Nat := 4983230072969 + 3 ^ 40 * 3907312 * 2
def baseEnd_3907312 : Nat := 2006329123080521857530605

theorem tailTrace_3907312 : CollatzResearch.WordTrace tailWord_3907312 prefixEnd_3907312 2006329123080521857530605 := by
  unfold tailWord_3907312
  simp only [CollatzResearch.WordTrace]
  refine ⟨71255688210241707303494095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95007584280322276404658793 71255688210241707303494095)
  ·
    refine ⟨106883532315362560955241143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71255688210241707303494095 106883532315362560955241143)
    ·
      refine ⟨160325298473043841432861715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106883532315362560955241143 160325298473043841432861715)
      ·
        refine ⟨240487947709565762149292573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160325298473043841432861715 240487947709565762149292573)
        ·
          refine ⟨90182980391087160805984715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240487947709565762149292573 90182980391087160805984715)
          ·
            refine ⟨135274470586630741208977073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90182980391087160805984715 135274470586630741208977073)
            ·
              refine ⟨101455852939973055906732805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135274470586630741208977073 101455852939973055906732805)
              ·
                refine ⟨19022972426244947982512401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101455852939973055906732805 19022972426244947982512401)
                ·
                  refine ⟨14267229319683710986884301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19022972426244947982512401 14267229319683710986884301)
                  ·
                    refine ⟨5350210994881391620081613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14267229319683710986884301 5350210994881391620081613)
                    ·
                      refine ⟨2006329123080521857530605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5350210994881391620081613 2006329123080521857530605)
                      ·
                        rfl

theorem cell23_3907312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 3].length) (baseStart_3907312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907312 prefixEnd_3907312 := by exact prefixLift 3907312
  have htrace : WordTrace (prefixWord ++ tailWord_3907312) baseStart_3907312 baseEnd_3907312 := by
    simpa [prefixWord, tailWord_3907312, baseEnd_3907312] using wordTrace_append hprefix tailTrace_3907312
  have hstable : (prefixWord ++ tailWord_3907312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907312).length < 2 ^ (prefixWord ++ tailWord_3907312).sum := by decide
  have hdescent : baseEnd_3907312 < baseStart_3907312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907334 : List Nat := [6, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2]
def baseStart_3907334 : Nat := 118140960795 + 3907334 * 2 ^ 59
def prefixEnd_3907334 : Nat := 4983230072969 + 3 ^ 40 * 3907334 * 2
def baseEnd_3907334 : Nat := 2006340419654920771455505

theorem tailTrace_3907334 : CollatzResearch.WordTrace tailWord_3907334 prefixEnd_3907334 2006340419654920771455505 := by
  unfold tailWord_3907334
  simp only [CollatzResearch.WordTrace]
  refine ⟨4453505588325116011384033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 95008119217602474909526037 4453505588325116011384033)
  ·
    refine ⟨3340129191243837008538025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4453505588325116011384033 3340129191243837008538025)
    ·
      refine ⟨2505096893432877756403519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3340129191243837008538025 2505096893432877756403519)
      ·
        refine ⟨3757645340149316634605279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2505096893432877756403519 3757645340149316634605279)
        ·
          refine ⟨5636468010223974951907919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3757645340149316634605279 5636468010223974951907919)
          ·
            refine ⟨8454702015335962427861879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5636468010223974951907919 8454702015335962427861879)
            ·
              refine ⟨12682053023003943641792819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8454702015335962427861879 12682053023003943641792819)
              ·
                refine ⟨19023079534505915462689229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12682053023003943641792819 19023079534505915462689229)
                ·
                  refine ⟨7133654825439718298508461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19023079534505915462689229 7133654825439718298508461)
                  ·
                    refine ⟨2675120559539894361940673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7133654825439718298508461 2675120559539894361940673)
                    ·
                      refine ⟨2006340419654920771455505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2675120559539894361940673 2006340419654920771455505)
                      ·
                        rfl

theorem cell23_3907334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_3907334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907334 prefixEnd_3907334 := by exact prefixLift 3907334
  have htrace : WordTrace (prefixWord ++ tailWord_3907334) baseStart_3907334 baseEnd_3907334 := by
    simpa [prefixWord, tailWord_3907334, baseEnd_3907334] using wordTrace_append hprefix tailTrace_3907334
  have hstable : (prefixWord ++ tailWord_3907334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907334).length < 2 ^ (prefixWord ++ tailWord_3907334).sum := by decide
  have hdescent : baseEnd_3907334 < baseStart_3907334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907349 : List Nat := [1, 3, 2, 1, 2, 4, 2, 1, 2, 5]
def baseStart_3907349 : Nat := 118140960795 + 3907349 * 2 ^ 59
def prefixEnd_3907349 : Nat := 4983230072969 + 3 ^ 40 * 3907349 * 2
def baseEnd_3907349 : Nat := 668782707288246070922645

theorem tailTrace_3907349 : CollatzResearch.WordTrace tailWord_3907349 prefixEnd_3907349 668782707288246070922645 := by
  unfold tailWord_3907349
  simp only [CollatzResearch.WordTrace]
  refine ⟨142512725921349369926085101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95008483947566246617390067 142512725921349369926085101)
  ·
    refine ⟨53442272220506013722281913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142512725921349369926085101 53442272220506013722281913)
    ·
      refine ⟨40081704165379510291711435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53442272220506013722281913 40081704165379510291711435)
      ·
        refine ⟨60122556248069265437567153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40081704165379510291711435 60122556248069265437567153)
        ·
          refine ⟨45091917186051949078175365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60122556248069265437567153 45091917186051949078175365)
          ·
            refine ⟨8454734472384740452157881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45091917186051949078175365 8454734472384740452157881)
            ·
              refine ⟨6341050854288555339118411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8454734472384740452157881 6341050854288555339118411)
              ·
                refine ⟨9511576281432833008677617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6341050854288555339118411 9511576281432833008677617)
                ·
                  refine ⟨7133682211074624756508213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9511576281432833008677617 7133682211074624756508213)
                  ·
                    refine ⟨668782707288246070922645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7133682211074624756508213 668782707288246070922645)
                    ·
                      rfl

theorem cell23_3907349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_3907349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907349 prefixEnd_3907349 := by exact prefixLift 3907349
  have htrace : WordTrace (prefixWord ++ tailWord_3907349) baseStart_3907349 baseEnd_3907349 := by
    simpa [prefixWord, tailWord_3907349, baseEnd_3907349] using wordTrace_append hprefix tailTrace_3907349
  have hstable : (prefixWord ++ tailWord_3907349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907349).length < 2 ^ (prefixWord ++ tailWord_3907349).sum := by decide
  have hdescent : baseEnd_3907349 < baseStart_3907349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907352 : List Nat := [2, 1, 2, 3, 1, 1, 2, 3, 1, 3, 4]
def baseStart_3907352 : Nat := 118140960795 + 3907352 * 2 ^ 59
def prefixEnd_3907352 : Nat := 4983230072969 + 3 ^ 40 * 3907352 * 2
def baseEnd_3907352 : Nat := 2006349662306701701030421

theorem tailTrace_3907352 : CollatzResearch.WordTrace tailWord_3907352 prefixEnd_3907352 2006349662306701701030421 := by
  unfold tailWord_3907352
  simp only [CollatzResearch.WordTrace]
  refine ⟨71256417670169250719222155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95008556893559000958962873 71256417670169250719222155)
  ·
    refine ⟨106884626505253876078833233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71256417670169250719222155 106884626505253876078833233)
    ·
      refine ⟨80163469878940407059124925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106884626505253876078833233 80163469878940407059124925)
      ·
        refine ⟨30061301204602652647171847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80163469878940407059124925 30061301204602652647171847)
        ·
          refine ⟨45091951806903978970757771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30061301204602652647171847 45091951806903978970757771)
          ·
            refine ⟨67637927710355968456136657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45091951806903978970757771 67637927710355968456136657)
            ·
              refine ⟨50728445782766976342102493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67637927710355968456136657 50728445782766976342102493)
              ·
                refine ⟨19023167168537616128288435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50728445782766976342102493 19023167168537616128288435)
                ·
                  refine ⟨28534750752806424192432653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19023167168537616128288435 28534750752806424192432653)
                  ·
                    refine ⟨10700531532302409072162245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28534750752806424192432653 10700531532302409072162245)
                    ·
                      refine ⟨2006349662306701701030421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10700531532302409072162245 2006349662306701701030421)
                      ·
                        rfl

theorem cell23_3907352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_3907352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907352 prefixEnd_3907352 := by exact prefixLift 3907352
  have htrace : WordTrace (prefixWord ++ tailWord_3907352) baseStart_3907352 baseEnd_3907352 := by
    simpa [prefixWord, tailWord_3907352, baseEnd_3907352] using wordTrace_append hprefix tailTrace_3907352
  have hstable : (prefixWord ++ tailWord_3907352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907352).length < 2 ^ (prefixWord ++ tailWord_3907352).sum := by decide
  have hdescent : baseEnd_3907352 < baseStart_3907352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907386 : List Nat := [3, 1, 1, 1, 5, 2, 1, 1, 2, 4, 2]
def baseStart_3907386 : Nat := 118140960795 + 3907386 * 2 ^ 59
def prefixEnd_3907386 : Nat := 4983230072969 + 3 ^ 40 * 3907386 * 2
def baseEnd_3907386 : Nat := 2006367120648954568005265

theorem tailTrace_3907386 : CollatzResearch.WordTrace tailWord_3907386 prefixEnd_3907386 2006367120648954568005265 := by
  unfold tailWord_3907386
  simp only [CollatzResearch.WordTrace]
  refine ⟨35628518855553831311295503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95009383614810216830121341 35628518855553831311295503)
  ·
    refine ⟨53442778283330746966943255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35628518855553831311295503 53442778283330746966943255)
    ·
      refine ⟨80164167424996120450414883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53442778283330746966943255 80164167424996120450414883)
      ·
        refine ⟨120246251137494180675622325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80164167424996120450414883 120246251137494180675622325)
        ·
          refine ⟨11273086044140079438339593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120246251137494180675622325 11273086044140079438339593)
          ·
            refine ⟨8454814533105059578754695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11273086044140079438339593 8454814533105059578754695)
            ·
              refine ⟨12682221799657589368132043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8454814533105059578754695 12682221799657589368132043)
              ·
                refine ⟨19023332699486384052198065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12682221799657589368132043 19023332699486384052198065)
                ·
                  refine ⟨14267499524614788039148549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19023332699486384052198065 14267499524614788039148549)
                  ·
                    refine ⟨2675156160865272757340353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14267499524614788039148549 2675156160865272757340353)
                    ·
                      refine ⟨2006367120648954568005265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2675156160865272757340353 2006367120648954568005265)
                      ·
                        rfl

theorem cell23_3907386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 2, 4, 2].length) (baseStart_3907386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907386 prefixEnd_3907386 := by exact prefixLift 3907386
  have htrace : WordTrace (prefixWord ++ tailWord_3907386) baseStart_3907386 baseEnd_3907386 := by
    simpa [prefixWord, tailWord_3907386, baseEnd_3907386] using wordTrace_append hprefix tailTrace_3907386
  have hstable : (prefixWord ++ tailWord_3907386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907386).length < 2 ^ (prefixWord ++ tailWord_3907386).sum := by decide
  have hdescent : baseEnd_3907386 < baseStart_3907386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907413 : List Nat := [1, 3, 2, 2, 2, 3, 2, 3, 1, 4]
def baseStart_3907413 : Nat := 118140960795 + 3907413 * 2 ^ 59
def prefixEnd_3907413 : Nat := 4983230072969 + 3 ^ 40 * 3907413 * 2
def baseEnd_3907413 : Nat := 668793661542208654122547

theorem tailTrace_3907413 : CollatzResearch.WordTrace tailWord_3907413 prefixEnd_3907413 668793661542208654122547 := by
  unfold tailWord_3907413
  simp only [CollatzResearch.WordTrace]
  refine ⟨142515060193117508856414893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95010040128745005904276595 142515060193117508856414893)
  ·
    refine ⟨53443147572419065821155585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142515060193117508856414893 53443147572419065821155585)
    ·
      refine ⟨40082360679314299365866689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53443147572419065821155585 40082360679314299365866689)
      ·
        refine ⟨30061770509485724524400017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40082360679314299365866689 30061770509485724524400017)
        ·
          refine ⟨22546327882114293393300013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30061770509485724524400017 22546327882114293393300013)
          ·
            refine ⟨8454872955792860022487505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22546327882114293393300013 8454872955792860022487505)
            ·
              refine ⟨6341154716844645016865629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8454872955792860022487505 6341154716844645016865629)
              ·
                refine ⟨2377933018816741881324611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6341154716844645016865629 2377933018816741881324611)
                ·
                  refine ⟨3566899528225112821986917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2377933018816741881324611 3566899528225112821986917)
                  ·
                    refine ⟨668793661542208654122547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3566899528225112821986917 668793661542208654122547)
                    ·
                      rfl

theorem cell23_3907413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 3, 1, 4].length) (baseStart_3907413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907413 prefixEnd_3907413 := by exact prefixLift 3907413
  have htrace : WordTrace (prefixWord ++ tailWord_3907413) baseStart_3907413 baseEnd_3907413 := by
    simpa [prefixWord, tailWord_3907413, baseEnd_3907413] using wordTrace_append hprefix tailTrace_3907413
  have hstable : (prefixWord ++ tailWord_3907413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907413).length < 2 ^ (prefixWord ++ tailWord_3907413).sum := by decide
  have hdescent : baseEnd_3907413 < baseStart_3907413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907426 : List Nat := [3, 3, 2, 1, 2, 1, 3, 2, 6]
def baseStart_3907426 : Nat := 118140960795 + 3907426 * 2 ^ 59
def prefixEnd_3907426 : Nat := 4983230072969 + 3 ^ 40 * 3907426 * 2
def baseEnd_3907426 : Nat := 222931962208348267945009

theorem tailTrace_3907426 : CollatzResearch.WordTrace tailWord_3907426 prefixEnd_3907426 222931962208348267945009 := by
  unfold tailWord_3907426
  simp only [CollatzResearch.WordTrace]
  refine ⟨35628883585517603019159533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95010356228046941384425421 35628883585517603019159533)
  ·
    refine ⟨13360831344569101132184825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35628883585517603019159533 13360831344569101132184825)
    ·
      refine ⟨10020623508426825849138619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13360831344569101132184825 10020623508426825849138619)
      ·
        refine ⟨15030935262640238773707929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10020623508426825849138619 15030935262640238773707929)
        ·
          refine ⟨11273201446980179080280947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15030935262640238773707929 11273201446980179080280947)
          ·
            refine ⟨16909802170470268620421421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11273201446980179080280947 16909802170470268620421421)
            ·
              refine ⟨6341175813926350732658033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16909802170470268620421421 6341175813926350732658033)
              ·
                refine ⟨4755881860444763049493525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6341175813926350732658033 4755881860444763049493525)
                ·
                  refine ⟨222931962208348267945009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4755881860444763049493525 222931962208348267945009)
                  ·
                    rfl

theorem cell23_3907426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_3907426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907426 prefixEnd_3907426 := by exact prefixLift 3907426
  have htrace : WordTrace (prefixWord ++ tailWord_3907426) baseStart_3907426 baseEnd_3907426 := by
    simpa [prefixWord, tailWord_3907426, baseEnd_3907426] using wordTrace_append hprefix tailTrace_3907426
  have hstable : (prefixWord ++ tailWord_3907426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907426).length < 2 ^ (prefixWord ++ tailWord_3907426).sum := by decide
  have hdescent : baseEnd_3907426 < baseStart_3907426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907436 : List Nat := [2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 3]
def baseStart_3907436 : Nat := 118140960795 + 3907436 * 2 ^ 59
def prefixEnd_3907436 : Nat := 4983230072969 + 3 ^ 40 * 3907436 * 2
def baseEnd_3907436 : Nat := 2006392794681679372380035

theorem tailTrace_3907436 : CollatzResearch.WordTrace tailWord_3907436 prefixEnd_3907436 2006392794681679372380035 := by
  unfold tailWord_3907436
  simp only [CollatzResearch.WordTrace]
  refine ⟨71257949536017091892251081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95010599381356122523001441 71257949536017091892251081)
  ·
    refine ⟨53443462152012818919188311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71257949536017091892251081 53443462152012818919188311)
    ·
      refine ⟨80165193228019228378782467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53443462152012818919188311 80165193228019228378782467)
      ·
        refine ⟨120247789842028842568173701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80165193228019228378782467 120247789842028842568173701)
        ·
          refine ⟨22546460595380407981532569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120247789842028842568173701 22546460595380407981532569)
          ·
            refine ⟨16909845446535305986149427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22546460595380407981532569 16909845446535305986149427)
            ·
              refine ⟨25364768169802958979224141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16909845446535305986149427 25364768169802958979224141)
              ·
                refine ⟨9511788063676109617209053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25364768169802958979224141 9511788063676109617209053)
                ·
                  refine ⟨3566920523878541106453395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9511788063676109617209053 3566920523878541106453395)
                  ·
                    refine ⟨5350380785817811659680093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3566920523878541106453395 5350380785817811659680093)
                    ·
                      refine ⟨2006392794681679372380035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5350380785817811659680093 2006392794681679372380035)
                      ·
                        rfl

theorem cell23_3907436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 3].length) (baseStart_3907436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907436 prefixEnd_3907436 := by exact prefixLift 3907436
  have htrace : WordTrace (prefixWord ++ tailWord_3907436) baseStart_3907436 baseEnd_3907436 := by
    simpa [prefixWord, tailWord_3907436, baseEnd_3907436] using wordTrace_append hprefix tailTrace_3907436
  have hstable : (prefixWord ++ tailWord_3907436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907436).length < 2 ^ (prefixWord ++ tailWord_3907436).sum := by decide
  have hdescent : baseEnd_3907436 < baseStart_3907436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907472 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 6]
def baseStart_3907472 : Nat := 118140960795 + 3907472 * 2 ^ 59
def prefixEnd_3907472 : Nat := 4983230072969 + 3 ^ 40 * 3907472 * 2
def baseEnd_3907472 : Nat := 2006411279985241231529869

theorem tailTrace_3907472 : CollatzResearch.WordTrace tailWord_3907472 prefixEnd_3907472 2006411279985241231529869 := by
  unfold tailWord_3907472
  simp only [CollatzResearch.WordTrace]
  refine ⟨71258606049951880966406335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95011474733269174621875113 71258606049951880966406335)
  ·
    refine ⟨106887909074927821449609503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71258606049951880966406335 106887909074927821449609503)
    ·
      refine ⟨160331863612391732174414255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106887909074927821449609503 160331863612391732174414255)
      ·
        refine ⟨240497795418587598261621383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160331863612391732174414255 240497795418587598261621383)
        ·
          refine ⟨360746693127881397392432075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240497795418587598261621383 360746693127881397392432075)
          ·
            refine ⟨541120039691822096088648113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360746693127881397392432075 541120039691822096088648113)
            ·
              refine ⟨405840029768866572066486085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 541120039691822096088648113 405840029768866572066486085)
              ·
                refine ⟨76095005581662482262466141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 405840029768866572066486085 76095005581662482262466141)
                ·
                  refine ⟨28535627093123430848424803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76095005581662482262466141 28535627093123430848424803)
                  ·
                    refine ⟨42803440639685146272637205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28535627093123430848424803 42803440639685146272637205)
                    ·
                      refine ⟨2006411279985241231529869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42803440639685146272637205 2006411279985241231529869)
                      ·
                        rfl

theorem cell23_3907472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 6].length) (baseStart_3907472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907472 prefixEnd_3907472 := by exact prefixLift 3907472
  have htrace : WordTrace (prefixWord ++ tailWord_3907472) baseStart_3907472 baseEnd_3907472 := by
    simpa [prefixWord, tailWord_3907472, baseEnd_3907472] using wordTrace_append hprefix tailTrace_3907472
  have hstable : (prefixWord ++ tailWord_3907472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907472).length < 2 ^ (prefixWord ++ tailWord_3907472).sum := by decide
  have hdescent : baseEnd_3907472 < baseStart_3907472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907479 : List Nat := [1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 5]
def baseStart_3907479 : Nat := 118140960795 + 3907479 * 2 ^ 59
def prefixEnd_3907479 : Nat := 4983230072969 + 3 ^ 40 * 3907479 * 2
def baseEnd_3907479 : Nat := 2006414874349822704142337

theorem tailTrace_3907479 : CollatzResearch.WordTrace tailWord_3907479 prefixEnd_3907479 2006414874349822704142337 := by
  unfold tailWord_3907479
  simp only [CollatzResearch.WordTrace]
  refine ⟨142517467410878402128317491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95011644940585601418878327 142517467410878402128317491)
  ·
    refine ⟨213776201116317603192476237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142517467410878402128317491 213776201116317603192476237)
    ·
      refine ⟨80166075418619101197178589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213776201116317603192476237 80166075418619101197178589)
      ·
        refine ⟨30062278281982162948941971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80166075418619101197178589 30062278281982162948941971)
        ·
          refine ⟨45093417422973244423412957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30062278281982162948941971 45093417422973244423412957)
          ·
            refine ⟨16910031533614966658779859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45093417422973244423412957 16910031533614966658779859)
            ·
              refine ⟨25365047300422449988169789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16910031533614966658779859 25365047300422449988169789)
              ·
                refine ⟨9511892737658418745563671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25365047300422449988169789 9511892737658418745563671)
                ·
                  refine ⟨14267839106487628118345507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9511892737658418745563671 14267839106487628118345507)
                  ·
                    refine ⟨21401758659731442177518261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14267839106487628118345507 21401758659731442177518261)
                    ·
                      refine ⟨2006414874349822704142337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21401758659731442177518261 2006414874349822704142337)
                      ·
                        rfl

theorem cell23_3907479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_3907479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907479 prefixEnd_3907479 := by exact prefixLift 3907479
  have htrace : WordTrace (prefixWord ++ tailWord_3907479) baseStart_3907479 baseEnd_3907479 := by
    simpa [prefixWord, tailWord_3907479, baseEnd_3907479] using wordTrace_append hprefix tailTrace_3907479
  have hstable : (prefixWord ++ tailWord_3907479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907479).length < 2 ^ (prefixWord ++ tailWord_3907479).sum := by decide
  have hdescent : baseEnd_3907479 < baseStart_3907479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907480 : List Nat := [2, 1, 2, 6, 1, 1, 1, 2, 2, 3, 2]
def baseStart_3907480 : Nat := 118140960795 + 3907480 * 2 ^ 59
def prefixEnd_3907480 : Nat := 4983230072969 + 3 ^ 40 * 3907480 * 2
def baseEnd_3907480 : Nat := 2006415387830477200229833

theorem tailTrace_3907480 : CollatzResearch.WordTrace tailWord_3907480 prefixEnd_3907480 2006415387830477200229833 := by
  unfold tailWord_3907480
  simp only [CollatzResearch.WordTrace]
  refine ⟨71258751941937389649551947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95011669255916519532735929 71258751941937389649551947)
  ·
    refine ⟨106888127912906084474327921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71258751941937389649551947 106888127912906084474327921)
    ·
      refine ⟨80166095934679563355745941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106888127912906084474327921 80166095934679563355745941)
      ·
        refine ⟨3757785746938104532300591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 80166095934679563355745941 3757785746938104532300591)
        ·
          refine ⟨5636678620407156798450887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3757785746938104532300591 5636678620407156798450887)
          ·
            refine ⟨8455017930610735197676331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5636678620407156798450887 8455017930610735197676331)
            ·
              refine ⟨12682526895916102796514497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8455017930610735197676331 12682526895916102796514497)
              ·
                refine ⟨9511895171937077097385873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12682526895916102796514497 9511895171937077097385873)
                ·
                  refine ⟨7133921378952807823039405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9511895171937077097385873 7133921378952807823039405)
                  ·
                    refine ⟨2675220517107302933639777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7133921378952807823039405 2675220517107302933639777)
                    ·
                      refine ⟨2006415387830477200229833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2675220517107302933639777 2006415387830477200229833)
                      ·
                        rfl

theorem cell23_3907480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_3907480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907480 prefixEnd_3907480 := by exact prefixLift 3907480
  have htrace : WordTrace (prefixWord ++ tailWord_3907480) baseStart_3907480 baseEnd_3907480 := by
    simpa [prefixWord, tailWord_3907480, baseEnd_3907480] using wordTrace_append hprefix tailTrace_3907480
  have hstable : (prefixWord ++ tailWord_3907480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907480).length < 2 ^ (prefixWord ++ tailWord_3907480).sum := by decide
  have hdescent : baseEnd_3907480 < baseStart_3907480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907487 : List Nat := [1, 1, 2, 5, 3, 1, 3, 2, 1, 1, 3]
def baseStart_3907487 : Nat := 118140960795 + 3907487 * 2 ^ 59
def prefixEnd_3907487 : Nat := 4983230072969 + 3 ^ 40 * 3907487 * 2
def baseEnd_3907487 : Nat := 2006418982195058672842301

theorem tailTrace_3907487 : CollatzResearch.WordTrace tailWord_3907487 prefixEnd_3907487 2006418982195058672842301 := by
  unfold tailWord_3907487
  simp only [CollatzResearch.WordTrace]
  refine ⟨142517759194849419494608715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95011839463232946329739143 142517759194849419494608715)
  ·
    refine ⟨213776638792274129241913073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142517759194849419494608715 213776638792274129241913073)
    ·
      refine ⟨160332479094205596931434805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213776638792274129241913073 160332479094205596931434805)
      ·
        refine ⟨15031169915081774712322013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160332479094205596931434805 15031169915081774712322013)
        ·
          refine ⟨5636688718155665517120755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15031169915081774712322013 5636688718155665517120755)
          ·
            refine ⟨8455033077233498275681133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5636688718155665517120755 8455033077233498275681133)
            ·
              refine ⟨3170637403962561853380425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8455033077233498275681133 3170637403962561853380425)
              ·
                refine ⟨2377978052971921390035319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3170637403962561853380425 2377978052971921390035319)
                ·
                  refine ⟨3566967079457882085052979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2377978052971921390035319 3566967079457882085052979)
                  ·
                    refine ⟨5350450619186823127579469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3566967079457882085052979 5350450619186823127579469)
                    ·
                      refine ⟨2006418982195058672842301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5350450619186823127579469 2006418982195058672842301)
                      ·
                        rfl

theorem cell23_3907487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_3907487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907487 prefixEnd_3907487 := by exact prefixLift 3907487
  have htrace : WordTrace (prefixWord ++ tailWord_3907487) baseStart_3907487 baseEnd_3907487 := by
    simpa [prefixWord, tailWord_3907487, baseEnd_3907487] using wordTrace_append hprefix tailTrace_3907487
  have hstable : (prefixWord ++ tailWord_3907487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907487).length < 2 ^ (prefixWord ++ tailWord_3907487).sum := by decide
  have hdescent : baseEnd_3907487 < baseStart_3907487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907543 : List Nat := [1, 1, 3, 2, 1, 1, 6, 2, 2, 1, 3]
def baseStart_3907543 : Nat := 118140960795 + 3907543 * 2 ^ 59
def prefixEnd_3907543 : Nat := 4983230072969 + 3 ^ 40 * 3907543 * 2
def baseEnd_3907543 : Nat := 2006447737111710453742043

theorem tailTrace_3907543 : CollatzResearch.WordTrace tailWord_3907543 prefixEnd_3907543 2006447737111710453742043 := by
  unfold tailWord_3907543
  simp only [CollatzResearch.WordTrace]
  refine ⟨142519801682646541058647283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95013201121764360705764855 142519801682646541058647283)
  ·
    refine ⟨213779702523969811587970925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142519801682646541058647283 213779702523969811587970925)
    ·
      refine ⟨80167388446488679345489097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213779702523969811587970925 80167388446488679345489097)
      ·
        refine ⟨60125541334866509509116823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80167388446488679345489097 60125541334866509509116823)
        ·
          refine ⟨90188312002299764263675235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60125541334866509509116823 90188312002299764263675235)
          ·
            refine ⟨135282468003449646395512853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90188312002299764263675235 135282468003449646395512853)
            ·
              refine ⟨6341365687661702174789665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 135282468003449646395512853 6341365687661702174789665)
              ·
                refine ⟨4756024265746276631092249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6341365687661702174789665 4756024265746276631092249)
                ·
                  refine ⟨3567018199309707473319187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4756024265746276631092249 3567018199309707473319187)
                  ·
                    refine ⟨5350527298964561209978781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3567018199309707473319187 5350527298964561209978781)
                    ·
                      refine ⟨2006447737111710453742043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5350527298964561209978781 2006447737111710453742043)
                      ·
                        rfl

theorem cell23_3907543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 2, 1, 3].length) (baseStart_3907543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907543 prefixEnd_3907543 := by exact prefixLift 3907543
  have htrace : WordTrace (prefixWord ++ tailWord_3907543) baseStart_3907543 baseEnd_3907543 := by
    simpa [prefixWord, tailWord_3907543, baseEnd_3907543] using wordTrace_append hprefix tailTrace_3907543
  have hstable : (prefixWord ++ tailWord_3907543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907543).length < 2 ^ (prefixWord ++ tailWord_3907543).sum := by decide
  have hdescent : baseEnd_3907543 < baseStart_3907543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907617 : List Nat := [1, 2, 3, 2, 5, 1, 1, 1, 1, 4, 2]
def baseStart_3907617 : Nat := 118140960795 + 3907617 * 2 ^ 59
def prefixEnd_3907617 : Nat := 4983230072969 + 3 ^ 40 * 3907617 * 2
def baseEnd_3907617 : Nat := 2006485734680143164216703

theorem tailTrace_3907617 : CollatzResearch.WordTrace tailWord_3907617 prefixEnd_3907617 2006485734680143164216703 := by
  unfold tailWord_3907617
  simp only [CollatzResearch.WordTrace]
  refine ⟨142522500684378451696841105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95015000456252301131227403 142522500684378451696841105)
  ·
    refine ⟨106891875513283838772630829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142522500684378451696841105 106891875513283838772630829)
    ·
      refine ⟨40084453317481439539736561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106891875513283838772630829 40084453317481439539736561)
      ·
        refine ⟨30063339988111079654802421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40084453317481439539736561 30063339988111079654802421)
        ·
          refine ⟨2818438123885413717637727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30063339988111079654802421 2818438123885413717637727)
          ·
            refine ⟨4227657185828120576456591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2818438123885413717637727 4227657185828120576456591)
            ·
              refine ⟨6341485778742180864684887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4227657185828120576456591 6341485778742180864684887)
              ·
                refine ⟨9512228668113271297027331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6341485778742180864684887 9512228668113271297027331)
                ·
                  refine ⟨14268343002169906945540997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9512228668113271297027331 14268343002169906945540997)
                  ·
                    refine ⟨2675314312906857552288937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14268343002169906945540997 2675314312906857552288937)
                    ·
                      refine ⟨2006485734680143164216703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2675314312906857552288937 2006485734680143164216703)
                      ·
                        rfl

theorem cell23_3907617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_3907617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907617 prefixEnd_3907617 := by exact prefixLift 3907617
  have htrace : WordTrace (prefixWord ++ tailWord_3907617) baseStart_3907617 baseEnd_3907617 := by
    simpa [prefixWord, tailWord_3907617, baseEnd_3907617] using wordTrace_append hprefix tailTrace_3907617
  have hstable : (prefixWord ++ tailWord_3907617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907617).length < 2 ^ (prefixWord ++ tailWord_3907617).sum := by decide
  have hdescent : baseEnd_3907617 < baseStart_3907617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907619 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 3, 7]
def baseStart_3907619 : Nat := 118140960795 + 3907619 * 2 ^ 59
def prefixEnd_3907619 : Nat := 4983230072969 + 3 ^ 40 * 3907619 * 2
def baseEnd_3907619 : Nat := 668828920547150718797231

theorem tailTrace_3907619 : CollatzResearch.WordTrace tailWord_3907619 prefixEnd_3907619 668828920547150718797231 := by
  unfold tailWord_3907619
  simp only [CollatzResearch.WordTrace]
  refine ⟨142522573630371206038413911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95015049086914137358942607 142522573630371206038413911)
  ·
    refine ⟨213783860445556809057620867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142522573630371206038413911 213783860445556809057620867)
    ·
      refine ⟨320675790668335213586431301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213783860445556809057620867 320675790668335213586431301)
      ·
        refine ⟨60126710750312852547455869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 320675790668335213586431301 60126710750312852547455869)
        ·
          refine ⟨22547516531367319705295951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60126710750312852547455869 22547516531367319705295951)
          ·
            refine ⟨33821274797050979557943927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22547516531367319705295951 33821274797050979557943927)
            ·
              refine ⟨50731912195576469336915891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33821274797050979557943927 50731912195576469336915891)
              ·
                refine ⟨76097868293364704005373837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50731912195576469336915891 76097868293364704005373837)
                ·
                  refine ⟨28536700610011764002015189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76097868293364704005373837 28536700610011764002015189)
                  ·
                    refine ⟨668828920547150718797231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28536700610011764002015189 668828920547150718797231)
                    ·
                      rfl

theorem cell23_3907619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 7].length) (baseStart_3907619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907619 prefixEnd_3907619 := by exact prefixLift 3907619
  have htrace : WordTrace (prefixWord ++ tailWord_3907619) baseStart_3907619 baseEnd_3907619 := by
    simpa [prefixWord, tailWord_3907619, baseEnd_3907619] using wordTrace_append hprefix tailTrace_3907619
  have hstable : (prefixWord ++ tailWord_3907619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907619).length < 2 ^ (prefixWord ++ tailWord_3907619).sum := by decide
  have hdescent : baseEnd_3907619 < baseStart_3907619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907640 : List Nat := [2, 1, 2, 1, 6, 2, 1, 3, 5]
def baseStart_3907640 : Nat := 118140960795 + 3907640 * 2 ^ 59
def prefixEnd_3907640 : Nat := 4983230072969 + 3 ^ 40 * 3907640 * 2
def baseEnd_3907640 : Nat := 222944171637244063803233

theorem tailTrace_3907640 : CollatzResearch.WordTrace tailWord_3907640 prefixEnd_3907640 222944171637244063803233 := by
  unfold tailWord_3907640
  simp only [CollatzResearch.WordTrace]
  refine ⟨71261669781647563312464187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95015559708863417749952249 71261669781647563312464187)
  ·
    refine ⟨106892504672471344968696281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71261669781647563312464187 106892504672471344968696281)
    ·
      refine ⟨80169378504353508726522211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106892504672471344968696281 80169378504353508726522211)
      ·
        refine ⟨120254067756530263089783317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80169378504353508726522211 120254067756530263089783317)
        ·
          refine ⟨5636909426087356082333593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 120254067756530263089783317 5636909426087356082333593)
          ·
            refine ⟨4227682069565517061750195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5636909426087356082333593 4227682069565517061750195)
            ·
              refine ⟨6341523104348275592625293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4227682069565517061750195 6341523104348275592625293)
              ·
                refine ⟨2378071164130603347234485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6341523104348275592625293 2378071164130603347234485)
                ·
                  refine ⟨222944171637244063803233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2378071164130603347234485 222944171637244063803233)
                  ·
                    rfl

theorem cell23_3907640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 3, 5].length) (baseStart_3907640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907640 prefixEnd_3907640 := by exact prefixLift 3907640
  have htrace : WordTrace (prefixWord ++ tailWord_3907640) baseStart_3907640 baseEnd_3907640 := by
    simpa [prefixWord, tailWord_3907640, baseEnd_3907640] using wordTrace_append hprefix tailTrace_3907640
  have hstable : (prefixWord ++ tailWord_3907640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907640).length < 2 ^ (prefixWord ++ tailWord_3907640).sum := by decide
  have hdescent : baseEnd_3907640 < baseStart_3907640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907659 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 5]
def baseStart_3907659 : Nat := 118140960795 + 3907659 * 2 ^ 59
def prefixEnd_3907659 : Nat := 4983230072969 + 3 ^ 40 * 3907659 * 2
def baseEnd_3907659 : Nat := 2006507300867631999891509

theorem tailTrace_3907659 : CollatzResearch.WordTrace tailWord_3907659 prefixEnd_3907659 2006507300867631999891509 := by
  unfold tailWord_3907659
  simp only [CollatzResearch.WordTrace]
  refine ⟨142524032550226292869870031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95016021700150861913246687 142524032550226292869870031)
  ·
    refine ⟨213786048825339439304805047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142524032550226292869870031 213786048825339439304805047)
    ·
      refine ⟨320679073238009158957207571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213786048825339439304805047 320679073238009158957207571)
      ·
        refine ⟨481018609857013738435811357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320679073238009158957207571 481018609857013738435811357)
        ·
          refine ⟨180381978696380151913429259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 481018609857013738435811357 180381978696380151913429259)
          ·
            refine ⟨270572968044570227870143889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180381978696380151913429259 270572968044570227870143889)
            ·
              refine ⟨202929726033427670902607917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270572968044570227870143889 202929726033427670902607917)
              ·
                refine ⟨76098647262535376588477969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202929726033427670902607917 76098647262535376588477969)
                ·
                  refine ⟨57073985446901532441358477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76098647262535376588477969 57073985446901532441358477)
                  ·
                    refine ⟨21402744542588074665509429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57073985446901532441358477 21402744542588074665509429)
                    ·
                      refine ⟨2006507300867631999891509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21402744542588074665509429 2006507300867631999891509)
                      ·
                        rfl

theorem cell23_3907659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 5].length) (baseStart_3907659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907659 prefixEnd_3907659 := by exact prefixLift 3907659
  have htrace : WordTrace (prefixWord ++ tailWord_3907659) baseStart_3907659 baseEnd_3907659 := by
    simpa [prefixWord, tailWord_3907659, baseEnd_3907659] using wordTrace_append hprefix tailTrace_3907659
  have hstable : (prefixWord ++ tailWord_3907659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907659).length < 2 ^ (prefixWord ++ tailWord_3907659).sum := by decide
  have hdescent : baseEnd_3907659 < baseStart_3907659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907679 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 10]
def baseStart_3907679 : Nat := 118140960795 + 3907679 * 2 ^ 59
def prefixEnd_3907679 : Nat := 4983230072969 + 3 ^ 40 * 3907679 * 2
def baseEnd_3907679 : Nat := 222946396720080213515713

theorem tailTrace_3907679 : CollatzResearch.WordTrace tailWord_3907679 prefixEnd_3907679 222946396720080213515713 := by
  unfold tailWord_3907679
  simp only [CollatzResearch.WordTrace]
  refine ⟨142524762010153836285598091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95016508006769224190398727 142524762010153836285598091)
  ·
    refine ⟨213787143015230754428397137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142524762010153836285598091 213787143015230754428397137)
    ·
      refine ⟨160340357261423065821297853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213787143015230754428397137 160340357261423065821297853)
      ·
        refine ⟨60127633973033649682986695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160340357261423065821297853 60127633973033649682986695)
        ·
          refine ⟨90191450959550474524480043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60127633973033649682986695 90191450959550474524480043)
          ·
            refine ⟨135287176439325711786720065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90191450959550474524480043 135287176439325711786720065)
            ·
              refine ⟨101465382329494283840040049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135287176439325711786720065 101465382329494283840040049)
              ·
                refine ⟨76099036747120712880030037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101465382329494283840040049 76099036747120712880030037)
                ·
                  refine ⟨222946396720080213515713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 76099036747120712880030037 222946396720080213515713)
                  ·
                    rfl

theorem cell23_3907679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 10].length) (baseStart_3907679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907679 prefixEnd_3907679 := by exact prefixLift 3907679
  have htrace : WordTrace (prefixWord ++ tailWord_3907679) baseStart_3907679 baseEnd_3907679 := by
    simpa [prefixWord, tailWord_3907679, baseEnd_3907679] using wordTrace_append hprefix tailTrace_3907679
  have hstable : (prefixWord ++ tailWord_3907679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907679).length < 2 ^ (prefixWord ++ tailWord_3907679).sum := by decide
  have hdescent : baseEnd_3907679 < baseStart_3907679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907690 : List Nat := [3, 1, 3, 2, 3, 1, 2, 1, 2, 1, 4]
def baseStart_3907690 : Nat := 118140960795 + 3907690 * 2 ^ 59
def prefixEnd_3907690 : Nat := 4983230072969 + 3 ^ 40 * 3907690 * 2
def baseEnd_3907690 : Nat := 2006523218767921378603867

theorem tailTrace_3907690 : CollatzResearch.WordTrace tailWord_3907690 prefixEnd_3907690 2006523218767921378603867 := by
  unfold tailWord_3907690
  simp only [CollatzResearch.WordTrace]
  refine ⟨35631290803278496291062131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95016775475409323442832349 35631290803278496291062131)
  ·
    refine ⟨53446936204917744436593197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35631290803278496291062131 53446936204917744436593197)
    ·
      refine ⟨20042601076844154163722449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53446936204917744436593197 20042601076844154163722449)
      ·
        refine ⟨15031950807633115622791837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20042601076844154163722449 15031950807633115622791837)
        ·
          refine ⟨5636981552862418358546939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15031950807633115622791837 5636981552862418358546939)
          ·
            refine ⟨8455472329293627537820409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5636981552862418358546939 8455472329293627537820409)
            ·
              refine ⟨6341604246970220653365307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8455472329293627537820409 6341604246970220653365307)
              ·
                refine ⟨9512406370455330980047961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6341604246970220653365307 9512406370455330980047961)
                ·
                  refine ⟨7134304777841498235035971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9512406370455330980047961 7134304777841498235035971)
                  ·
                    refine ⟨10701457166762247352553957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7134304777841498235035971 10701457166762247352553957)
                    ·
                      refine ⟨2006523218767921378603867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10701457166762247352553957 2006523218767921378603867)
                      ·
                        rfl

theorem cell23_3907690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_3907690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907690 prefixEnd_3907690 := by exact prefixLift 3907690
  have htrace : WordTrace (prefixWord ++ tailWord_3907690) baseStart_3907690 baseEnd_3907690 := by
    simpa [prefixWord, tailWord_3907690, baseEnd_3907690] using wordTrace_append hprefix tailTrace_3907690
  have hstable : (prefixWord ++ tailWord_3907690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907690).length < 2 ^ (prefixWord ++ tailWord_3907690).sum := by decide
  have hdescent : baseEnd_3907690 < baseStart_3907690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907716 : List Nat := [2, 3, 2, 1, 2, 1, 2, 1, 1, 2, 6]
def baseStart_3907716 : Nat := 118140960795 + 3907716 * 2 ^ 59
def prefixEnd_3907716 : Nat := 4983230072969 + 3 ^ 40 * 3907716 * 2
def baseEnd_3907716 : Nat := 2006536569264938276878747

theorem tailTrace_3907716 : CollatzResearch.WordTrace tailWord_3907716 prefixEnd_3907716 2006536569264938276878747 := by
  unfold tailWord_3907716
  simp only [CollatzResearch.WordTrace]
  refine ⟨71263055755509895802347501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95017407674013194403130001 71263055755509895802347501)
  ·
    refine ⟨26723645908316210925880313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71263055755509895802347501 26723645908316210925880313)
    ·
      refine ⟨20042734431237158194410235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26723645908316210925880313 20042734431237158194410235)
      ·
        refine ⟨30064101646855737291615353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20042734431237158194410235 30064101646855737291615353)
        ·
          refine ⟨22548076235141802968711515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30064101646855737291615353 22548076235141802968711515)
          ·
            refine ⟨33822114352712704453067273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22548076235141802968711515 33822114352712704453067273)
            ·
              refine ⟨25366585764534528339800455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33822114352712704453067273 25366585764534528339800455)
              ·
                refine ⟨38049878646801792509700683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25366585764534528339800455 38049878646801792509700683)
                ·
                  refine ⟨57074817970202688764551025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38049878646801792509700683 57074817970202688764551025)
                  ·
                    refine ⟨42806113477652016573413269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57074817970202688764551025 42806113477652016573413269)
                    ·
                      refine ⟨2006536569264938276878747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42806113477652016573413269 2006536569264938276878747)
                      ·
                        rfl

theorem cell23_3907716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_3907716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907716 prefixEnd_3907716 := by exact prefixLift 3907716
  have htrace : WordTrace (prefixWord ++ tailWord_3907716) baseStart_3907716 baseEnd_3907716 := by
    simpa [prefixWord, tailWord_3907716, baseEnd_3907716] using wordTrace_append hprefix tailTrace_3907716
  have hstable : (prefixWord ++ tailWord_3907716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907716).length < 2 ^ (prefixWord ++ tailWord_3907716).sum := by decide
  have hdescent : baseEnd_3907716 < baseStart_3907716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907717 : List Nat := [1, 3, 1, 1, 5, 1, 4, 2, 1, 4]
def baseStart_3907717 : Nat := 118140960795 + 3907717 * 2 ^ 59
def prefixEnd_3907717 : Nat := 4983230072969 + 3 ^ 40 * 3907717 * 2
def baseEnd_3907717 : Nat := 668845694248530924322081

theorem tailTrace_3907717 : CollatzResearch.WordTrace tailWord_3907717 prefixEnd_3907717 668845694248530924322081 := by
  unfold tailWord_3907717
  simp only [CollatzResearch.WordTrace]
  refine ⟨142526147984016168775481405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95017431989344112516987603 142526147984016168775481405)
  ·
    refine ⟨53447305494006063290805527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142526147984016168775481405 53447305494006063290805527)
    ·
      refine ⟨80170958241009094936208291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53447305494006063290805527 80170958241009094936208291)
      ·
        refine ⟨120256437361513642404312437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80170958241009094936208291 120256437361513642404312437)
        ·
          refine ⟨11274041002641903975404291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120256437361513642404312437 11274041002641903975404291)
          ·
            refine ⟨16911061503962855963106437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11274041002641903975404291 16911061503962855963106437)
            ·
              refine ⟨3170824031993035493082457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16911061503962855963106437 3170824031993035493082457)
              ·
                refine ⟨2378118023994776619811843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3170824031993035493082457 2378118023994776619811843)
                ·
                  refine ⟨3567177035992164929717765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2378118023994776619811843 3567177035992164929717765)
                  ·
                    refine ⟨668845694248530924322081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3567177035992164929717765 668845694248530924322081)
                    ·
                      rfl

theorem cell23_3907717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 2, 1, 4].length) (baseStart_3907717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907717 prefixEnd_3907717 := by exact prefixLift 3907717
  have htrace : WordTrace (prefixWord ++ tailWord_3907717) baseStart_3907717 baseEnd_3907717 := by
    simpa [prefixWord, tailWord_3907717, baseEnd_3907717] using wordTrace_append hprefix tailTrace_3907717
  have hstable : (prefixWord ++ tailWord_3907717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907717).length < 2 ^ (prefixWord ++ tailWord_3907717).sum := by decide
  have hdescent : baseEnd_3907717 < baseStart_3907717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907733 : List Nat := [1, 3, 2, 1, 1, 1, 4, 2, 1, 5, 2]
def baseStart_3907733 : Nat := 118140960795 + 3907733 * 2 ^ 59
def prefixEnd_3907733 : Nat := 4983230072969 + 3 ^ 40 * 3907733 * 2
def baseEnd_3907733 : Nat := 2006545298436064710366169

theorem tailTrace_3907733 : CollatzResearch.WordTrace tailWord_3907733 prefixEnd_3907733 2006545298436064710366169 := by
  unfold tailWord_3907733
  simp only [CollatzResearch.WordTrace]
  refine ⟨142526731551958203508063853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95017821034638802338709235 142526731551958203508063853)
  ·
    refine ⟨53447524331984326315523945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142526731551958203508063853 53447524331984326315523945)
    ·
      refine ⟨40085643248988244736642959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53447524331984326315523945 40085643248988244736642959)
      ·
        refine ⟨60128464873482367104964439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40085643248988244736642959 60128464873482367104964439)
        ·
          refine ⟨90192697310223550657446659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60128464873482367104964439 90192697310223550657446659)
          ·
            refine ⟨135289045965335325986169989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90192697310223550657446659 135289045965335325986169989)
            ·
              refine ⟨25366696118500373622406873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135289045965335325986169989 25366696118500373622406873)
              ·
                refine ⟨19025022088875280216805155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25366696118500373622406873 19025022088875280216805155)
                ·
                  refine ⟨28537533133312920325207733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19025022088875280216805155 28537533133312920325207733)
                  ·
                    refine ⟨2675393731248086280488225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28537533133312920325207733 2675393731248086280488225)
                    ·
                      refine ⟨2006545298436064710366169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2675393731248086280488225 2006545298436064710366169)
                      ·
                        rfl

theorem cell23_3907733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 5, 2].length) (baseStart_3907733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907733 prefixEnd_3907733 := by exact prefixLift 3907733
  have htrace : WordTrace (prefixWord ++ tailWord_3907733) baseStart_3907733 baseEnd_3907733 := by
    simpa [prefixWord, tailWord_3907733, baseEnd_3907733] using wordTrace_append hprefix tailTrace_3907733
  have hstable : (prefixWord ++ tailWord_3907733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907733).length < 2 ^ (prefixWord ++ tailWord_3907733).sum := by decide
  have hdescent : baseEnd_3907733 < baseStart_3907733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907740 : List Nat := [2, 2, 3, 2, 1, 1, 3, 2, 3, 1, 3]
def baseStart_3907740 : Nat := 118140960795 + 3907740 * 2 ^ 59
def prefixEnd_3907740 : Nat := 4983230072969 + 3 ^ 40 * 3907740 * 2
def baseEnd_3907740 : Nat := 2006548892800646182978637

theorem tailTrace_3907740 : CollatzResearch.WordTrace tailWord_3907740 prefixEnd_3907740 2006548892800646182978637 := by
  unfold tailWord_3907740
  simp only [CollatzResearch.WordTrace]
  refine ⟨71263493431466421851784337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95017991241955229135712449 71263493431466421851784337)
  ·
    refine ⟨53447620073599816388838253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71263493431466421851784337 53447620073599816388838253)
    ·
      refine ⟨20042857527599931145814345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53447620073599816388838253 20042857527599931145814345)
      ·
        refine ⟨15032143145699948359360759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20042857527599931145814345 15032143145699948359360759)
        ·
          refine ⟨22548214718549922539041139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15032143145699948359360759 22548214718549922539041139)
          ·
            refine ⟨33822322077824883808561709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22548214718549922539041139 33822322077824883808561709)
            ·
              refine ⟨12683370779184331428210641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33822322077824883808561709 12683370779184331428210641)
              ·
                refine ⟨9512528084388248571157981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12683370779184331428210641 9512528084388248571157981)
                ·
                  refine ⟨3567198031645593214184243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9512528084388248571157981 3567198031645593214184243)
                  ·
                    refine ⟨5350797047468389821276365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3567198031645593214184243 5350797047468389821276365)
                    ·
                      refine ⟨2006548892800646182978637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5350797047468389821276365 2006548892800646182978637)
                      ·
                        rfl

theorem cell23_3907740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_3907740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907740 prefixEnd_3907740 := by exact prefixLift 3907740
  have htrace : WordTrace (prefixWord ++ tailWord_3907740) baseStart_3907740 baseEnd_3907740 := by
    simpa [prefixWord, tailWord_3907740, baseEnd_3907740] using wordTrace_append hprefix tailTrace_3907740
  have hstable : (prefixWord ++ tailWord_3907740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907740).length < 2 ^ (prefixWord ++ tailWord_3907740).sum := by decide
  have hdescent : baseEnd_3907740 < baseStart_3907740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907743 : List Nat := [1, 1, 2, 6, 1, 1, 2, 1, 3, 5]
def baseStart_3907743 : Nat := 118140960795 + 3907743 * 2 ^ 59
def prefixEnd_3907743 : Nat := 4983230072969 + 3 ^ 40 * 3907743 * 2
def baseEnd_3907743 : Nat := 668850144414203223747041

theorem tailTrace_3907743 : CollatzResearch.WordTrace tailWord_3907743 prefixEnd_3907743 668850144414203223747041 := by
  unfold tailWord_3907743
  simp only [CollatzResearch.WordTrace]
  refine ⟨142527096281921975215927883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95018064187947983477285255 142527096281921975215927883)
  ·
    refine ⟨213790644422882962823891825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142527096281921975215927883 213790644422882962823891825)
    ·
      refine ⟨160342983317162222117918869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213790644422882962823891825 160342983317162222117918869)
      ·
        refine ⟨7516077342991979161777447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 160342983317162222117918869 7516077342991979161777447)
        ·
          refine ⟨11274116014487968742666171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7516077342991979161777447 11274116014487968742666171)
          ·
            refine ⟨16911174021731953113999257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11274116014487968742666171 16911174021731953113999257)
            ·
              refine ⟨12683380516298964835499443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16911174021731953113999257 12683380516298964835499443)
              ·
                refine ⟨19025070774448447253249165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12683380516298964835499443 19025070774448447253249165)
                ·
                  refine ⟨7134401540418167719968437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19025070774448447253249165 7134401540418167719968437)
                  ·
                    refine ⟨668850144414203223747041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7134401540418167719968437 668850144414203223747041)
                    ·
                      rfl

theorem cell23_3907743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 5].length) (baseStart_3907743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907743 prefixEnd_3907743 := by exact prefixLift 3907743
  have htrace : WordTrace (prefixWord ++ tailWord_3907743) baseStart_3907743 baseEnd_3907743 := by
    simpa [prefixWord, tailWord_3907743, baseEnd_3907743] using wordTrace_append hprefix tailTrace_3907743
  have hstable : (prefixWord ++ tailWord_3907743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907743).length < 2 ^ (prefixWord ++ tailWord_3907743).sum := by decide
  have hdescent : baseEnd_3907743 < baseStart_3907743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907786 : List Nat := [3, 1, 2, 1, 3, 1, 2, 10]
def baseStart_3907786 : Nat := 118140960795 + 3907786 * 2 ^ 59
def prefixEnd_3907786 : Nat := 4983230072969 + 3 ^ 40 * 3907786 * 2
def baseEnd_3907786 : Nat := 74317500478176037148275

theorem tailTrace_3907786 : CollatzResearch.WordTrace tailWord_3907786 prefixEnd_3907786 74317500478176037148275 := by
  unfold tailWord_3907786
  simp only [CollatzResearch.WordTrace]
  refine ⟨35632166155191548389935803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95019109747177462373162141 35632166155191548389935803)
  ·
    refine ⟨53448249232787322584903705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35632166155191548389935803 53448249232787322584903705)
    ·
      refine ⟨40086186924590491938677779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53448249232787322584903705 40086186924590491938677779)
      ·
        refine ⟨60129280386885737908016669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40086186924590491938677779 60129280386885737908016669)
        ·
          refine ⟨22548480145082151715506251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60129280386885737908016669 22548480145082151715506251)
          ·
            refine ⟨33822720217623227573259377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22548480145082151715506251 33822720217623227573259377)
            ·
              refine ⟨25367040163217420679944533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33822720217623227573259377 25367040163217420679944533)
              ·
                refine ⟨74317500478176037148275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 25367040163217420679944533 74317500478176037148275)
                ·
                  rfl

theorem cell23_3907786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 10].length) (baseStart_3907786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907786 prefixEnd_3907786 := by exact prefixLift 3907786
  have htrace : WordTrace (prefixWord ++ tailWord_3907786) baseStart_3907786 baseEnd_3907786 := by
    simpa [prefixWord, tailWord_3907786, baseEnd_3907786] using wordTrace_append hprefix tailTrace_3907786
  have hstable : (prefixWord ++ tailWord_3907786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907786).length < 2 ^ (prefixWord ++ tailWord_3907786).sum := by decide
  have hdescent : baseEnd_3907786 < baseStart_3907786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
