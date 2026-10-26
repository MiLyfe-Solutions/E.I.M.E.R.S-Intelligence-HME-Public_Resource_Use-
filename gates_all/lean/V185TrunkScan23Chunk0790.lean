import V185TrunkScan23Chunk0789

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4672474 : List Nat := [3, 1, 1, 2, 4, 1, 1, 1, 1, 3, 5]
def baseStart_4672474 : Nat := 118140960795 + 4672474 * 2 ^ 59
def prefixEnd_4672474 : Nat := 4983230072969 + 3 ^ 40 * 4672474 * 2
def baseEnd_4672474 : Nat := 2399225007636057157686689

theorem tailTrace_4672474 : CollatzResearch.WordTrace tailWord_4672474 prefixEnd_4672474 2399225007636057157686689 := by
  unfold tailWord_4672474
  simp only [CollatzResearch.WordTrace]
  refine ⟨42604781818608041968170119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113612751516288111915120317 42604781818608041968170119)
  ·
    refine ⟨63907172727912062952255179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42604781818608041968170119 63907172727912062952255179)
    ·
      refine ⟨95860759091868094428382769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63907172727912062952255179 95860759091868094428382769)
      ·
        refine ⟨71895569318901070821287077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95860759091868094428382769 71895569318901070821287077)
        ·
          refine ⟨13480419247293950778991327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71895569318901070821287077 13480419247293950778991327)
          ·
            refine ⟨20220628870940926168486991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13480419247293950778991327 20220628870940926168486991)
            ·
              refine ⟨30330943306411389252730487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20220628870940926168486991 30330943306411389252730487)
              ·
                refine ⟨45496414959617083879095731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30330943306411389252730487 45496414959617083879095731)
                ·
                  refine ⟨68244622439425625818643597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45496414959617083879095731 68244622439425625818643597)
                  ·
                    refine ⟨25591733414784609681991349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68244622439425625818643597 25591733414784609681991349)
                    ·
                      refine ⟨2399225007636057157686689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25591733414784609681991349 2399225007636057157686689)
                      ·
                        rfl

theorem cell23_4672474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_4672474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672474 prefixEnd_4672474 := by exact prefixLift 4672474
  have htrace : WordTrace (prefixWord ++ tailWord_4672474) baseStart_4672474 baseEnd_4672474 := by
    simpa [prefixWord, tailWord_4672474, baseEnd_4672474] using wordTrace_append hprefix tailTrace_4672474
  have hstable : (prefixWord ++ tailWord_4672474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672474).length < 2 ^ (prefixWord ++ tailWord_4672474).sum := by decide
  have hdescent : baseEnd_4672474 < baseStart_4672474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672484 : List Nat := [2, 3, 1, 1, 1, 1, 2, 4, 2, 2, 4]
def baseStart_4672484 : Nat := 118140960795 + 4672484 * 2 ^ 59
def prefixEnd_4672484 : Nat := 4983230072969 + 3 ^ 40 * 4672484 * 2
def baseEnd_4672484 : Nat := 2399230142442602118561643

theorem tailTrace_4672484 : CollatzResearch.WordTrace tailWord_4672484 prefixEnd_4672484 2399230142442602118561643 := by
  unfold tailWord_4672484
  simp only [CollatzResearch.WordTrace]
  refine ⟨85209746002197969790272253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113612994669597293053696337 85209746002197969790272253)
  ·
    refine ⟨31953654750824238671352095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85209746002197969790272253 31953654750824238671352095)
    ·
      refine ⟨47930482126236358007028143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31953654750824238671352095 47930482126236358007028143)
      ·
        refine ⟨71895723189354537010542215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47930482126236358007028143 71895723189354537010542215)
        ·
          refine ⟨107843584784031805515813323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71895723189354537010542215 107843584784031805515813323)
          ·
            refine ⟨161765377176047708273719985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107843584784031805515813323 161765377176047708273719985)
            ·
              refine ⟨121324032882035781205289989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161765377176047708273719985 121324032882035781205289989)
              ·
                refine ⟨22748256165381708975991873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121324032882035781205289989 22748256165381708975991873)
                ·
                  refine ⟨17061192124036281731993905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22748256165381708975991873 17061192124036281731993905)
                  ·
                    refine ⟨12795894093027211298995429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17061192124036281731993905 12795894093027211298995429)
                    ·
                      refine ⟨2399230142442602118561643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12795894093027211298995429 2399230142442602118561643)
                      ·
                        rfl

theorem cell23_4672484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_4672484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672484 prefixEnd_4672484 := by exact prefixLift 4672484
  have htrace : WordTrace (prefixWord ++ tailWord_4672484) baseStart_4672484 baseEnd_4672484 := by
    simpa [prefixWord, tailWord_4672484, baseEnd_4672484] using wordTrace_append hprefix tailTrace_4672484
  have hstable : (prefixWord ++ tailWord_4672484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672484).length < 2 ^ (prefixWord ++ tailWord_4672484).sum := by decide
  have hdescent : baseEnd_4672484 < baseStart_4672484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672488 : List Nat := [2, 1, 4, 1, 1, 1, 4, 1, 4, 2, 2]
def baseStart_4672488 : Nat := 118140960795 + 4672488 * 2 ^ 59
def prefixEnd_4672488 : Nat := 4983230072969 + 3 ^ 40 * 4672488 * 2
def baseEnd_4672488 : Nat := 2399232196365220102911625

theorem tailTrace_4672488 : CollatzResearch.WordTrace tailWord_4672488 prefixEnd_4672488 2399232196365220102911625 := by
  unfold tailWord_4672488
  simp only [CollatzResearch.WordTrace]
  refine ⟨85209818948190724131845059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113613091930920965509126745 85209818948190724131845059)
  ·
    refine ⟨127814728422286086197767589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85209818948190724131845059 127814728422286086197767589)
    ·
      refine ⟨23965261579178641162081423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127814728422286086197767589 23965261579178641162081423)
      ·
        refine ⟨35947892368767961743122135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23965261579178641162081423 35947892368767961743122135)
        ·
          refine ⟨53921838553151942614683203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35947892368767961743122135 53921838553151942614683203)
          ·
            refine ⟨80882757829727913922024805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53921838553151942614683203 80882757829727913922024805)
            ·
              refine ⟨15165517093073983860379651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80882757829727913922024805 15165517093073983860379651)
              ·
                refine ⟨22748275639610975790569477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15165517093073983860379651 22748275639610975790569477)
                ·
                  refine ⟨4265301682427057960731777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22748275639610975790569477 4265301682427057960731777)
                  ·
                    refine ⟨3198976261820293470548833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4265301682427057960731777 3198976261820293470548833)
                    ·
                      refine ⟨2399232196365220102911625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3198976261820293470548833 2399232196365220102911625)
                      ·
                        rfl

theorem cell23_4672488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_4672488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672488 prefixEnd_4672488 := by exact prefixLift 4672488
  have htrace : WordTrace (prefixWord ++ tailWord_4672488) baseStart_4672488 baseEnd_4672488 := by
    simpa [prefixWord, tailWord_4672488, baseEnd_4672488] using wordTrace_append hprefix tailTrace_4672488
  have hstable : (prefixWord ++ tailWord_4672488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672488).length < 2 ^ (prefixWord ++ tailWord_4672488).sum := by decide
  have hdescent : baseEnd_4672488 < baseStart_4672488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672504 : List Nat := [2, 1, 2, 1, 1, 3, 1, 3, 1, 5, 3]
def baseStart_4672504 : Nat := 118140960795 + 4672504 * 2 ^ 59
def prefixEnd_4672504 : Nat := 4983230072969 + 3 ^ 40 * 4672504 * 2
def baseEnd_4672504 : Nat := 2399240412055692040311551

theorem tailTrace_4672504 : CollatzResearch.WordTrace tailWord_4672504 prefixEnd_4672504 2399240412055692040311551 := by
  unfold tailWord_4672504
  simp only [CollatzResearch.WordTrace]
  refine ⟨85210110732161741498136283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113613480976215655330848377 85210110732161741498136283)
  ·
    refine ⟨127815166098242612247204425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85210110732161741498136283 127815166098242612247204425)
    ·
      refine ⟨95861374573681959185403319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127815166098242612247204425 95861374573681959185403319)
      ·
        refine ⟨143792061860522938778104979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95861374573681959185403319 143792061860522938778104979)
        ·
          refine ⟨215688092790784408167157469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143792061860522938778104979 215688092790784408167157469)
          ·
            refine ⟨80883034796544153062684051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 215688092790784408167157469 80883034796544153062684051)
            ·
              refine ⟨121324552194816229594026077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80883034796544153062684051 121324552194816229594026077)
              ·
                refine ⟨45496707073056086097759779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121324552194816229594026077 45496707073056086097759779)
                ·
                  refine ⟨68245060609584129146639669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45496707073056086097759779 68245060609584129146639669)
                  ·
                    refine ⟨6397974432148512107497469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 68245060609584129146639669 6397974432148512107497469)
                    ·
                      refine ⟨2399240412055692040311551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6397974432148512107497469 2399240412055692040311551)
                      ·
                        rfl

theorem cell23_4672504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 1, 5, 3].length) (baseStart_4672504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672504 prefixEnd_4672504 := by exact prefixLift 4672504
  have htrace : WordTrace (prefixWord ++ tailWord_4672504) baseStart_4672504 baseEnd_4672504 := by
    simpa [prefixWord, tailWord_4672504, baseEnd_4672504] using wordTrace_append hprefix tailTrace_4672504
  have hstable : (prefixWord ++ tailWord_4672504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672504).length < 2 ^ (prefixWord ++ tailWord_4672504).sum := by decide
  have hdescent : baseEnd_4672504 < baseStart_4672504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672545 : List Nat := [1, 2, 3, 2, 3, 3, 2, 2, 5]
def baseStart_4672545 : Nat := 118140960795 + 4672545 * 2 ^ 59
def prefixEnd_4672545 : Nat := 4983230072969 + 3 ^ 40 * 4672545 * 2
def baseEnd_4672545 : Nat := 266584607195836264433207

theorem tailTrace_4672545 : CollatzResearch.WordTrace tailWord_4672545 prefixEnd_4672545 266584607195836264433207 := by
  unfold tailWord_4672545
  simp only [CollatzResearch.WordTrace]
  refine ⟨170421716857174946998515089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113614477904783297999010059 170421716857174946998515089)
  ·
    refine ⟨127816287642881210248886317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170421716857174946998515089 127816287642881210248886317)
    ·
      refine ⟨47931107866080453843332369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127816287642881210248886317 47931107866080453843332369)
      ·
        refine ⟨35948330899560340382499277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47931107866080453843332369 35948330899560340382499277)
        ·
          refine ⟨13480624087335127643437229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35948330899560340382499277 13480624087335127643437229)
          ·
            refine ⟨5055234032750672866288961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13480624087335127643437229 5055234032750672866288961)
            ·
              refine ⟨3791425524563004649716721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5055234032750672866288961 3791425524563004649716721)
              ·
                refine ⟨2843569143422253487287541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3791425524563004649716721 2843569143422253487287541)
                ·
                  refine ⟨266584607195836264433207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2843569143422253487287541 266584607195836264433207)
                  ·
                    rfl

theorem cell23_4672545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 2, 5].length) (baseStart_4672545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672545 prefixEnd_4672545 := by exact prefixLift 4672545
  have htrace : WordTrace (prefixWord ++ tailWord_4672545) baseStart_4672545 baseEnd_4672545 := by
    simpa [prefixWord, tailWord_4672545, baseEnd_4672545] using wordTrace_append hprefix tailTrace_4672545
  have hstable : (prefixWord ++ tailWord_4672545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672545).length < 2 ^ (prefixWord ++ tailWord_4672545).sum := by decide
  have hdescent : baseEnd_4672545 < baseStart_4672545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672548 : List Nat := [2, 3, 1, 4, 1, 1, 1, 1, 2, 5, 2]
def baseStart_4672548 : Nat := 118140960795 + 4672548 * 2 ^ 59
def prefixEnd_4672548 : Nat := 4983230072969 + 3 ^ 40 * 4672548 * 2
def baseEnd_4672548 : Nat := 2399263005204489868161349

theorem tailTrace_4672548 : CollatzResearch.WordTrace tailWord_4672548 prefixEnd_4672548 2399263005204489868161349 := by
  unfold tailWord_4672548
  simp only [CollatzResearch.WordTrace]
  refine ⟨85210913138082039255437149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113614550850776052340582865 85210913138082039255437149)
  ·
    refine ⟨31954092426780764720788931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85210913138082039255437149 31954092426780764720788931)
    ·
      refine ⟨47931138640171147081183397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31954092426780764720788931 47931138640171147081183397)
      ·
        refine ⟨8987088495032090077721887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47931138640171147081183397 8987088495032090077721887)
        ·
          refine ⟨13480632742548135116582831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8987088495032090077721887 13480632742548135116582831)
          ·
            refine ⟨20220949113822202674874247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13480632742548135116582831 20220949113822202674874247)
            ·
              refine ⟨30331423670733304012311371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20220949113822202674874247 30331423670733304012311371)
              ·
                refine ⟨45497135506099956018467057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30331423670733304012311371 45497135506099956018467057)
                ·
                  refine ⟨34122851629574967013850293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45497135506099956018467057 34122851629574967013850293)
                  ·
                    refine ⟨3199017340272653157548465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34122851629574967013850293 3199017340272653157548465)
                    ·
                      refine ⟨2399263005204489868161349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3199017340272653157548465 2399263005204489868161349)
                      ·
                        rfl

theorem cell23_4672548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_4672548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672548 prefixEnd_4672548 := by exact prefixLift 4672548
  have htrace : WordTrace (prefixWord ++ tailWord_4672548) baseStart_4672548 baseEnd_4672548 := by
    simpa [prefixWord, tailWord_4672548, baseEnd_4672548] using wordTrace_append hprefix tailTrace_4672548
  have hstable : (prefixWord ++ tailWord_4672548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672548).length < 2 ^ (prefixWord ++ tailWord_4672548).sum := by decide
  have hdescent : baseEnd_4672548 < baseStart_4672548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672584 : List Nat := [2, 1, 3, 1, 1, 1, 4, 2, 8]
def baseStart_4672584 : Nat := 118140960795 + 4672584 * 2 ^ 59
def prefixEnd_4672584 : Nat := 4983230072969 + 3 ^ 40 * 4672584 * 2
def baseEnd_4672584 : Nat := 266586832278672414145687

theorem tailTrace_4672584 : CollatzResearch.WordTrace tailWord_4672584 prefixEnd_4672584 266586832278672414145687 := by
  unfold tailWord_4672584
  simp only [CollatzResearch.WordTrace]
  refine ⟨85211569652016828329592403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113615426202689104439456537 85211569652016828329592403)
  ·
    refine ⟨127817354478025242494388605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85211569652016828329592403 127817354478025242494388605)
    ·
      refine ⟨47931507929259465935395727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127817354478025242494388605 47931507929259465935395727)
      ·
        refine ⟨71897261893889198903093591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47931507929259465935395727 71897261893889198903093591)
        ·
          refine ⟨107845892840833798354640387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71897261893889198903093591 107845892840833798354640387)
          ·
            refine ⟨161768839261250697531960581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107845892840833798354640387 161768839261250697531960581)
            ·
              refine ⟨30331657361484505787242609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 161768839261250697531960581 30331657361484505787242609)
              ·
                refine ⟨22748743021113379340431957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30331657361484505787242609 22748743021113379340431957)
                ·
                  refine ⟨266586832278672414145687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22748743021113379340431957 266586832278672414145687)
                  ·
                    rfl

theorem cell23_4672584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 8].length) (baseStart_4672584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672584 prefixEnd_4672584 := by exact prefixLift 4672584
  have htrace : WordTrace (prefixWord ++ tailWord_4672584) baseStart_4672584 baseEnd_4672584 := by
    simpa [prefixWord, tailWord_4672584, baseEnd_4672584] using wordTrace_append hprefix tailTrace_4672584
  have hstable : (prefixWord ++ tailWord_4672584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672584).length < 2 ^ (prefixWord ++ tailWord_4672584).sum := by decide
  have hdescent : baseEnd_4672584 < baseStart_4672584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672682 : List Nat := [3, 1, 5, 1, 1, 3, 1, 2, 1, 5]
def baseStart_4672682 : Nat := 118140960795 + 4672682 * 2 ^ 59
def prefixEnd_4672682 : Nat := 4983230072969 + 3 ^ 40 * 4672682 * 2
def baseEnd_4672682 : Nat := 799777270537397447961911

theorem tailTrace_4672682 : CollatzResearch.WordTrace tailWord_4672682 prefixEnd_4672682 799777270537397447961911 := by
  unfold tailWord_4672682
  simp only [CollatzResearch.WordTrace]
  refine ⟨42606678414419654849063075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113617809105119079597501533 42606678414419654849063075)
  ·
    refine ⟨63910017621629482273594613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42606678414419654849063075 63910017621629482273594613)
    ·
      refine ⟨5991564152027763963149495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63910017621629482273594613 5991564152027763963149495)
      ·
        refine ⟨8987346228041645944724243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5991564152027763963149495 8987346228041645944724243)
        ·
          refine ⟨13481019342062468917086365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8987346228041645944724243 13481019342062468917086365)
          ·
            refine ⟨5055382253273425843907387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13481019342062468917086365 5055382253273425843907387)
            ·
              refine ⟨7583073379910138765861081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5055382253273425843907387 7583073379910138765861081)
              ·
                refine ⟨5687305034932604074395811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7583073379910138765861081 5687305034932604074395811)
                ·
                  refine ⟨8530957552398906111593717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5687305034932604074395811 8530957552398906111593717)
                  ·
                    refine ⟨799777270537397447961911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8530957552398906111593717 799777270537397447961911)
                    ·
                      rfl

theorem cell23_4672682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_4672682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672682 prefixEnd_4672682 := by exact prefixLift 4672682
  have htrace : WordTrace (prefixWord ++ tailWord_4672682) baseStart_4672682 baseEnd_4672682 := by
    simpa [prefixWord, tailWord_4672682, baseEnd_4672682] using wordTrace_append hprefix tailTrace_4672682
  have hstable : (prefixWord ++ tailWord_4672682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672682).length < 2 ^ (prefixWord ++ tailWord_4672682).sum := by decide
  have hdescent : baseEnd_4672682 < baseStart_4672682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672685 : List Nat := [1, 5, 2, 1, 3, 1, 1, 1, 3, 1, 4]
def baseStart_4672685 : Nat := 118140960795 + 4672685 * 2 ^ 59
def prefixEnd_4672685 : Nat := 4983230072969 + 3 ^ 40 * 4672685 * 2
def baseEnd_4672685 : Nat := 2399333352054155832148219

theorem tailTrace_4672685 : CollatzResearch.WordTrace tailWord_4672685 prefixEnd_4672685 2399333352054155832148219 := by
  unfold tailWord_4672685
  simp only [CollatzResearch.WordTrace]
  refine ⟨170426823076667750908611509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113617882051111833939074339 170426823076667750908611509)
  ·
    refine ⟨15977514663437601647682329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 170426823076667750908611509 15977514663437601647682329)
    ·
      refine ⟨11983135997578201235761747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15977514663437601647682329 11983135997578201235761747)
      ·
        refine ⟨17974703996367301853642621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11983135997578201235761747 17974703996367301853642621)
        ·
          refine ⟨6740513998637738195115983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17974703996367301853642621 6740513998637738195115983)
          ·
            refine ⟨10110770997956607292673975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6740513998637738195115983 10110770997956607292673975)
            ·
              refine ⟨15166156496934910939010963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10110770997956607292673975 15166156496934910939010963)
              ·
                refine ⟨22749234745402366408516445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15166156496934910939010963 22749234745402366408516445)
                ·
                  refine ⟨8530963029525887403193667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22749234745402366408516445 8530963029525887403193667)
                  ·
                    refine ⟨12796444544288831104790501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8530963029525887403193667 12796444544288831104790501)
                    ·
                      refine ⟨2399333352054155832148219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12796444544288831104790501 2399333352054155832148219)
                      ·
                        rfl

theorem cell23_4672685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_4672685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672685 prefixEnd_4672685 := by exact prefixLift 4672685
  have htrace : WordTrace (prefixWord ++ tailWord_4672685) baseStart_4672685 baseEnd_4672685 := by
    simpa [prefixWord, tailWord_4672685, baseEnd_4672685] using wordTrace_append hprefix tailTrace_4672685
  have hstable : (prefixWord ++ tailWord_4672685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672685).length < 2 ^ (prefixWord ++ tailWord_4672685).sum := by decide
  have hdescent : baseEnd_4672685 < baseStart_4672685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672702 : List Nat := [4, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4]
def baseStart_4672702 : Nat := 118140960795 + 4672702 * 2 ^ 59
def prefixEnd_4672702 : Nat := 4983230072969 + 3 ^ 40 * 4672702 * 2
def baseEnd_4672702 : Nat := 2399342081225282265635641

theorem tailTrace_4672702 : CollatzResearch.WordTrace tailWord_4672702 prefixEnd_4672702 2399342081225282265635641 := by
  unfold tailWord_4672702
  simp only [CollatzResearch.WordTrace]
  refine ⟨21303430389700770351497545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113618295411737441874653573 21303430389700770351497545)
  ·
    refine ⟨15977572792275577763623159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21303430389700770351497545 15977572792275577763623159)
    ·
      refine ⟨23966359188413366645434739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15977572792275577763623159 23966359188413366645434739)
      ·
        refine ⟨35949538782620049968152109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23966359188413366645434739 35949538782620049968152109)
        ·
          refine ⟨13481077043482518738057041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35949538782620049968152109 13481077043482518738057041)
          ·
            refine ⟨10110807782611889053542781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13481077043482518738057041 10110807782611889053542781)
            ·
              refine ⟨3791552918479458395078543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10110807782611889053542781 3791552918479458395078543)
              ·
                refine ⟨5687329377719187592617815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3791552918479458395078543 5687329377719187592617815)
                ·
                  refine ⟨8530994066578781388926723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5687329377719187592617815 8530994066578781388926723)
                  ·
                    refine ⟨12796491099868172083390085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8530994066578781388926723 12796491099868172083390085)
                    ·
                      refine ⟨2399342081225282265635641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12796491099868172083390085 2399342081225282265635641)
                      ·
                        rfl

theorem cell23_4672702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_4672702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672702 prefixEnd_4672702 := by exact prefixLift 4672702
  have htrace : WordTrace (prefixWord ++ tailWord_4672702) baseStart_4672702 baseEnd_4672702 := by
    simpa [prefixWord, tailWord_4672702, baseEnd_4672702] using wordTrace_append hprefix tailTrace_4672702
  have hstable : (prefixWord ++ tailWord_4672702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672702).length < 2 ^ (prefixWord ++ tailWord_4672702).sum := by decide
  have hdescent : baseEnd_4672702 < baseStart_4672702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672705 : List Nat := [1, 2, 6, 1, 1, 1, 3, 1, 1, 1, 5]
def baseStart_4672705 : Nat := 118140960795 + 4672705 * 2 ^ 59
def prefixEnd_4672705 : Nat := 4983230072969 + 3 ^ 40 * 4672705 * 2
def baseEnd_4672705 : Nat := 2399343621667245753898127

theorem tailTrace_4672705 : CollatzResearch.WordTrace tailWord_4672705 prefixEnd_4672705 2399343621667245753898127 := by
  unfold tailWord_4672705
  simp only [CollatzResearch.WordTrace]
  refine ⟨170427552536595294324339569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113618368357730196216226379 170427552536595294324339569)
  ·
    refine ⟨127820664402446470743254677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170427552536595294324339569 127820664402446470743254677)
    ·
      refine ⟨5991593643864678316090063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 127820664402446470743254677 5991593643864678316090063)
      ·
        refine ⟨8987390465797017474135095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5991593643864678316090063 8987390465797017474135095)
        ·
          refine ⟨13481085698695526211202643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8987390465797017474135095 13481085698695526211202643)
          ·
            refine ⟨20221628548043289316803965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13481085698695526211202643 20221628548043289316803965)
            ·
              refine ⟨7583110705516233493801487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20221628548043289316803965 7583110705516233493801487)
              ·
                refine ⟨11374666058274350240702231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7583110705516233493801487 11374666058274350240702231)
                ·
                  refine ⟨17061999087411525361053347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11374666058274350240702231 17061999087411525361053347)
                  ·
                    refine ⟨25592998631117288041580021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17061999087411525361053347 25592998631117288041580021)
                    ·
                      refine ⟨2399343621667245753898127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25592998631117288041580021 2399343621667245753898127)
                      ·
                        rfl

theorem cell23_4672705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_4672705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672705 prefixEnd_4672705 := by exact prefixLift 4672705
  have htrace : WordTrace (prefixWord ++ tailWord_4672705) baseStart_4672705 baseEnd_4672705 := by
    simpa [prefixWord, tailWord_4672705, baseEnd_4672705] using wordTrace_append hprefix tailTrace_4672705
  have hstable : (prefixWord ++ tailWord_4672705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672705).length < 2 ^ (prefixWord ++ tailWord_4672705).sum := by decide
  have hdescent : baseEnd_4672705 < baseStart_4672705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672708 : List Nat := [2, 3, 3, 1, 4, 10]
def baseStart_4672708 : Nat := 118140960795 + 4672708 * 2 ^ 59
def prefixEnd_4672708 : Nat := 4983230072969 + 3 ^ 40 * 4672708 * 2
def baseEnd_4672708 : Nat := 9873848403741601819591

theorem tailTrace_4672708 : CollatzResearch.WordTrace tailWord_4672708 prefixEnd_4672708 9873848403741601819591 := by
  unfold tailWord_4672708
  simp only [CollatzResearch.WordTrace]
  refine ⟨85213830977792212918349389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113618441303722950557799185 85213830977792212918349389)
  ·
    refine ⟨31955186616672079844381021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85213830977792212918349389 31955186616672079844381021)
    ·
      refine ⟨11983194981252029941642883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31955186616672079844381021 11983194981252029941642883)
      ·
        refine ⟨17974792471878044912464325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11983194981252029941642883 17974792471878044912464325)
        ·
          refine ⟨3370273588477133421087061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17974792471878044912464325 3370273588477133421087061)
          ·
            refine ⟨9873848403741601819591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3370273588477133421087061 9873848403741601819591)
            ·
              rfl

theorem cell23_4672708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 10].length) (baseStart_4672708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672708 prefixEnd_4672708 := by exact prefixLift 4672708
  have htrace : WordTrace (prefixWord ++ tailWord_4672708) baseStart_4672708 baseEnd_4672708 := by
    simpa [prefixWord, tailWord_4672708, baseEnd_4672708] using wordTrace_append hprefix tailTrace_4672708
  have hstable : (prefixWord ++ tailWord_4672708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672708).length < 2 ^ (prefixWord ++ tailWord_4672708).sum := by decide
  have hdescent : baseEnd_4672708 < baseStart_4672708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672735 : List Nat := [1, 1, 2, 3, 2, 1, 4, 3, 2, 1, 3]
def baseStart_4672735 : Nat := 118140960795 + 4672735 * 2 ^ 59
def prefixEnd_4672735 : Nat := 4983230072969 + 3 ^ 40 * 4672735 * 2
def baseEnd_4672735 : Nat := 2399359026086880636522989

theorem tailTrace_4672735 : CollatzResearch.WordTrace tailWord_4672735 prefixEnd_4672735 2399359026086880636522989 := by
  unfold tailWord_4672735
  simp only [CollatzResearch.WordTrace]
  refine ⟨170428646726486609447931659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113619097817657739631954439 170428646726486609447931659)
  ·
    refine ⟨255642970089729914171897489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170428646726486609447931659 255642970089729914171897489)
    ·
      refine ⟨191732227567297435628923117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255642970089729914171897489 191732227567297435628923117)
      ·
        refine ⟨71899585337736538360846169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191732227567297435628923117 71899585337736538360846169)
        ·
          refine ⟨53924689003302403770634627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71899585337736538360846169 53924689003302403770634627)
          ·
            refine ⟨80887033504953605655951941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53924689003302403770634627 80887033504953605655951941)
            ·
              refine ⟨15166318782178801060490989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80887033504953605655951941 15166318782178801060490989)
              ·
                refine ⟨5687369543317050397684121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15166318782178801060490989 5687369543317050397684121)
                ·
                  refine ⟨4265527157487787798263091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5687369543317050397684121 4265527157487787798263091)
                  ·
                    refine ⟨6398290736231681697394637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4265527157487787798263091 6398290736231681697394637)
                    ·
                      refine ⟨2399359026086880636522989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6398290736231681697394637 2399359026086880636522989)
                      ·
                        rfl

theorem cell23_4672735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 2, 1, 3].length) (baseStart_4672735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672735 prefixEnd_4672735 := by exact prefixLift 4672735
  have htrace : WordTrace (prefixWord ++ tailWord_4672735) baseStart_4672735 baseEnd_4672735 := by
    simpa [prefixWord, tailWord_4672735, baseEnd_4672735] using wordTrace_append hprefix tailTrace_4672735
  have hstable : (prefixWord ++ tailWord_4672735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672735).length < 2 ^ (prefixWord ++ tailWord_4672735).sum := by decide
  have hdescent : baseEnd_4672735 < baseStart_4672735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672756 : List Nat := [2, 6, 1, 2, 1, 1, 1, 3, 1, 2, 3]
def baseStart_4672756 : Nat := 118140960795 + 4672756 * 2 ^ 59
def prefixEnd_4672756 : Nat := 4983230072969 + 3 ^ 40 * 4672756 * 2
def baseEnd_4672756 : Nat := 2399369809180625054360393

theorem tailTrace_4672756 : CollatzResearch.WordTrace tailWord_4672756 prefixEnd_4672756 2399369809180625054360393 := by
  unfold tailWord_4672756
  simp only [CollatzResearch.WordTrace]
  refine ⟨85214706329705265017223061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113619608439607020022964081 85214706329705265017223061)
  ·
    refine ⟨3994439359204934297682331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 85214706329705265017223061 3994439359204934297682331)
    ·
      refine ⟨5991659038807401446523497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3994439359204934297682331 5991659038807401446523497)
      ·
        refine ⟨4493744279105551084892623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5991659038807401446523497 4493744279105551084892623)
        ·
          refine ⟨6740616418658326627338935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4493744279105551084892623 6740616418658326627338935)
          ·
            refine ⟨10110924627987489941008403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6740616418658326627338935 10110924627987489941008403)
            ·
              refine ⟨15166386941981234911512605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10110924627987489941008403 15166386941981234911512605)
              ·
                refine ⟨5687395103242963091817227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15166386941981234911512605 5687395103242963091817227)
                ·
                  refine ⟨8531092654864444637725841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5687395103242963091817227 8531092654864444637725841)
                  ·
                    refine ⟨6398319491148333478294381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8531092654864444637725841 6398319491148333478294381)
                    ·
                      refine ⟨2399369809180625054360393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6398319491148333478294381 2399369809180625054360393)
                      ·
                        rfl

theorem cell23_4672756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_4672756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672756 prefixEnd_4672756 := by exact prefixLift 4672756
  have htrace : WordTrace (prefixWord ++ tailWord_4672756) baseStart_4672756 baseEnd_4672756 := by
    simpa [prefixWord, tailWord_4672756, baseEnd_4672756] using wordTrace_append hprefix tailTrace_4672756
  have hstable : (prefixWord ++ tailWord_4672756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672756).length < 2 ^ (prefixWord ++ tailWord_4672756).sum := by decide
  have hdescent : baseEnd_4672756 < baseStart_4672756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672761 : List Nat := [1, 2, 1, 3, 1, 1, 4, 1, 1, 3, 5]
def baseStart_4672761 : Nat := 118140960795 + 4672761 * 2 ^ 59
def prefixEnd_4672761 : Nat := 4983230072969 + 3 ^ 40 * 4672761 * 2
def baseEnd_4672761 : Nat := 2399372376583897534797869

theorem tailTrace_4672761 : CollatzResearch.WordTrace tailWord_4672761 prefixEnd_4672761 2399372376583897534797869 := by
  unfold tailWord_4672761
  simp only [CollatzResearch.WordTrace]
  refine ⟨170429595024392415888378137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113619730016261610592252091 170429595024392415888378137)
  ·
    refine ⟨127822196268294311916283603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170429595024392415888378137 127822196268294311916283603)
    ·
      refine ⟨191733294402441467874425405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127822196268294311916283603 191733294402441467874425405)
      ·
        refine ⟨71899985400915550452909527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191733294402441467874425405 71899985400915550452909527)
        ·
          refine ⟨107849978101373325679364291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71899985400915550452909527 107849978101373325679364291)
          ·
            refine ⟨161774967152059988519046437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107849978101373325679364291 161774967152059988519046437)
            ·
              refine ⟨30332806341011247847321207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 161774967152059988519046437 30332806341011247847321207)
              ·
                refine ⟨45499209511516871770981811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30332806341011247847321207 45499209511516871770981811)
                ·
                  refine ⟨68248814267275307656472717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45499209511516871770981811 68248814267275307656472717)
                  ·
                    refine ⟨25593305350228240371177269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68248814267275307656472717 25593305350228240371177269)
                    ·
                      refine ⟨2399372376583897534797869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25593305350228240371177269 2399372376583897534797869)
                      ·
                        rfl

theorem cell23_4672761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_4672761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672761 prefixEnd_4672761 := by exact prefixLift 4672761
  have htrace : WordTrace (prefixWord ++ tailWord_4672761) baseStart_4672761 baseEnd_4672761 := by
    simpa [prefixWord, tailWord_4672761, baseEnd_4672761] using wordTrace_append hprefix tailTrace_4672761
  have hstable : (prefixWord ++ tailWord_4672761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672761).length < 2 ^ (prefixWord ++ tailWord_4672761).sum := by decide
  have hdescent : baseEnd_4672761 < baseStart_4672761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672786 : List Nat := [3, 2, 4, 2, 2, 1, 1, 1, 1, 3, 3]
def baseStart_4672786 : Nat := 118140960795 + 4672786 * 2 ^ 59
def prefixEnd_4672786 : Nat := 4983230072969 + 3 ^ 40 * 4672786 * 2
def baseEnd_4672786 : Nat := 2399385213600259936985255

theorem tailTrace_4672786 : CollatzResearch.WordTrace tailWord_4672786 prefixEnd_4672786 2399385213600259936985255 := by
  unfold tailWord_4672786
  simp only [CollatzResearch.WordTrace]
  refine ⟨42607626712325461289509553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113620337899534563438692141 42607626712325461289509553)
  ·
    refine ⟨31955720034244095967132165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42607626712325461289509553 31955720034244095967132165)
    ·
      refine ⟨5991697506420767993837281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31955720034244095967132165 5991697506420767993837281)
      ·
        refine ⟨4493773129815575995377961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5991697506420767993837281 4493773129815575995377961)
        ·
          refine ⟨3370329847361681996533471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4493773129815575995377961 3370329847361681996533471)
          ·
            refine ⟨5055494771042522994800207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3370329847361681996533471 5055494771042522994800207)
            ·
              refine ⟨7583242156563784492200311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5055494771042522994800207 7583242156563784492200311)
              ·
                refine ⟨11374863234845676738300467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7583242156563784492200311 11374863234845676738300467)
                ·
                  refine ⟨17062294852268515107450701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11374863234845676738300467 17062294852268515107450701)
                  ·
                    refine ⟨6398360569600693165294013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17062294852268515107450701 6398360569600693165294013)
                    ·
                      refine ⟨2399385213600259936985255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6398360569600693165294013 2399385213600259936985255)
                      ·
                        rfl

theorem cell23_4672786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_4672786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672786 prefixEnd_4672786 := by exact prefixLift 4672786
  have htrace : WordTrace (prefixWord ++ tailWord_4672786) baseStart_4672786 baseEnd_4672786 := by
    simpa [prefixWord, tailWord_4672786, baseEnd_4672786] using wordTrace_append hprefix tailTrace_4672786
  have hstable : (prefixWord ++ tailWord_4672786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672786).length < 2 ^ (prefixWord ++ tailWord_4672786).sum := by decide
  have hdescent : baseEnd_4672786 < baseStart_4672786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672792 : List Nat := [2, 1, 2, 3, 1, 5, 1, 1, 1, 4, 2]
def baseStart_4672792 : Nat := 118140960795 + 4672792 * 2 ^ 59
def prefixEnd_4672792 : Nat := 4983230072969 + 3 ^ 40 * 4672792 * 2
def baseEnd_4672792 : Nat := 2399388294484186913510227

theorem tailTrace_4672792 : CollatzResearch.WordTrace tailWord_4672792 prefixEnd_4672792 2399388294484186913510227 := by
  unfold tailWord_4672792
  simp only [CollatzResearch.WordTrace]
  refine ⟨85215362843640054091378315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113620483791520072121837753 85215362843640054091378315)
  ·
    refine ⟨127823044265460081137067473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85215362843640054091378315 127823044265460081137067473)
    ·
      refine ⟨95867283199095060852800605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127823044265460081137067473 95867283199095060852800605)
      ·
        refine ⟨35950231199660647819800227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95867283199095060852800605 35950231199660647819800227)
        ·
          refine ⟨53925346799490971729700341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35950231199660647819800227 53925346799490971729700341)
          ·
            refine ⟨5055501262452278599659407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53925346799490971729700341 5055501262452278599659407)
            ·
              refine ⟨7583251893678417899489111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5055501262452278599659407 7583251893678417899489111)
              ·
                refine ⟨11374877840517626849233667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7583251893678417899489111 11374877840517626849233667)
                ·
                  refine ⟨17062316760776440273850501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11374877840517626849233667 17062316760776440273850501)
                  ·
                    refine ⟨3199184392645582551346969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17062316760776440273850501 3199184392645582551346969)
                    ·
                      refine ⟨2399388294484186913510227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3199184392645582551346969 2399388294484186913510227)
                      ·
                        rfl

theorem cell23_4672792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_4672792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672792 prefixEnd_4672792 := by exact prefixLift 4672792
  have htrace : WordTrace (prefixWord ++ tailWord_4672792) baseStart_4672792 baseEnd_4672792 := by
    simpa [prefixWord, tailWord_4672792, baseEnd_4672792] using wordTrace_append hprefix tailTrace_4672792
  have hstable : (prefixWord ++ tailWord_4672792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672792).length < 2 ^ (prefixWord ++ tailWord_4672792).sum := by decide
  have hdescent : baseEnd_4672792 < baseStart_4672792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672828 : List Nat := [2, 2, 2, 2, 1, 3, 1, 1, 4, 5]
def baseStart_4672828 : Nat := 118140960795 + 4672828 * 2 ^ 59
def prefixEnd_4672828 : Nat := 4983230072969 + 3 ^ 40 * 4672828 * 2
def baseEnd_4672828 : Nat := 799802259929249590886687

theorem tailTrace_4672828 : CollatzResearch.WordTrace tailWord_4672828 prefixEnd_4672828 799802259929249590886687 := by
  unfold tailWord_4672828
  simp only [CollatzResearch.WordTrace]
  refine ⟨85216019357574843165533569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113621359143433124220711425 85216019357574843165533569)
  ·
    refine ⟨63912014518181132374150177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85216019357574843165533569 63912014518181132374150177)
    ·
      refine ⟨47934010888635849280612633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63912014518181132374150177 47934010888635849280612633)
      ·
        refine ⟨35950508166476886960459475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47934010888635849280612633 35950508166476886960459475)
        ·
          refine ⟨53925762249715330440689213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35950508166476886960459475 53925762249715330440689213)
          ·
            refine ⟨20222160843643248915258455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53925762249715330440689213 20222160843643248915258455)
            ·
              refine ⟨30333241265464873372887683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20222160843643248915258455 30333241265464873372887683)
              ·
                refine ⟨45499861898197310059331525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30333241265464873372887683 45499861898197310059331525)
                ·
                  refine ⟨8531224105911995636124661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45499861898197310059331525 8531224105911995636124661)
                  ·
                    refine ⟨799802259929249590886687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8531224105911995636124661 799802259929249590886687)
                    ·
                      rfl

theorem cell23_4672828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_4672828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672828 prefixEnd_4672828 := by exact prefixLift 4672828
  have htrace : WordTrace (prefixWord ++ tailWord_4672828) baseStart_4672828 baseEnd_4672828 := by
    simpa [prefixWord, tailWord_4672828, baseEnd_4672828] using wordTrace_append hprefix tailTrace_4672828
  have hstable : (prefixWord ++ tailWord_4672828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672828).length < 2 ^ (prefixWord ++ tailWord_4672828).sum := by decide
  have hdescent : baseEnd_4672828 < baseStart_4672828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672848 : List Nat := [2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 4]
def baseStart_4672848 : Nat := 118140960795 + 4672848 * 2 ^ 59
def prefixEnd_4672848 : Nat := 4983230072969 + 3 ^ 40 * 4672848 * 2
def baseEnd_4672848 : Nat := 2399417049400838694409969

theorem tailTrace_4672848 : CollatzResearch.WordTrace tailWord_4672848 prefixEnd_4672848 2399417049400838694409969 := by
  unfold tailWord_4672848
  simp only [CollatzResearch.WordTrace]
  refine ⟨85216384087538614873397599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113621845450051486497863465 85216384087538614873397599)
  ·
    refine ⟨127824576131307922310096399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85216384087538614873397599 127824576131307922310096399)
    ·
      refine ⟨191736864196961883465144599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127824576131307922310096399 191736864196961883465144599)
      ·
        refine ⟨287605296295442825197716899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191736864196961883465144599 287605296295442825197716899)
        ·
          refine ⟨431407944443164237796575349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287605296295442825197716899 431407944443164237796575349)
          ·
            refine ⟨40444494791546647293428939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 431407944443164237796575349 40444494791546647293428939)
            ·
              refine ⟨60666742187319970940143409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40444494791546647293428939 60666742187319970940143409)
              ·
                refine ⟨45500056640489978205107557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60666742187319970940143409 45500056640489978205107557)
                ·
                  refine ⟨8531260620091870913457667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45500056640489978205107557 8531260620091870913457667)
                  ·
                    refine ⟨12796890930137806370186501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8531260620091870913457667 12796890930137806370186501)
                    ·
                      refine ⟨2399417049400838694409969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12796890930137806370186501 2399417049400838694409969)
                      ·
                        rfl

theorem cell23_4672848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 4].length) (baseStart_4672848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672848 prefixEnd_4672848 := by exact prefixLift 4672848
  have htrace : WordTrace (prefixWord ++ tailWord_4672848) baseStart_4672848 baseEnd_4672848 := by
    simpa [prefixWord, tailWord_4672848, baseEnd_4672848] using wordTrace_append hprefix tailTrace_4672848
  have hstable : (prefixWord ++ tailWord_4672848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672848).length < 2 ^ (prefixWord ++ tailWord_4672848).sum := by decide
  have hdescent : baseEnd_4672848 < baseStart_4672848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672892 : List Nat := [2, 2, 2, 1, 1, 1, 5, 4, 1, 4]
def baseStart_4672892 : Nat := 118140960795 + 4672892 * 2 ^ 59
def prefixEnd_4672892 : Nat := 4983230072969 + 3 ^ 40 * 4672892 * 2
def baseEnd_4672892 : Nat := 799813214183212174086589

theorem tailTrace_4672892 : CollatzResearch.WordTrace tailWord_4672892 prefixEnd_4672892 799813214183212174086589 := by
  unfold tailWord_4672892
  simp only [CollatzResearch.WordTrace]
  refine ⟨85217186493458912630698465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113622915324611883507597953 85217186493458912630698465)
  ·
    refine ⟨63912889870094184473023849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85217186493458912630698465 63912889870094184473023849)
    ·
      refine ⟨47934667402570638354767887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63912889870094184473023849 47934667402570638354767887)
      ·
        refine ⟨71902001103855957532151831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47934667402570638354767887 71902001103855957532151831)
        ·
          refine ⟨107853001655783936298227747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71902001103855957532151831 107853001655783936298227747)
          ·
            refine ⟨161779502483675904447341621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107853001655783936298227747 161779502483675904447341621)
            ·
              refine ⟨15166828357844616041938277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 161779502483675904447341621 15166828357844616041938277)
              ·
                refine ⟨2843780317095865507863427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15166828357844616041938277 2843780317095865507863427)
                ·
                  refine ⟨4265670475643798261795141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2843780317095865507863427 4265670475643798261795141)
                  ·
                    refine ⟨799813214183212174086589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4265670475643798261795141 799813214183212174086589)
                    ·
                      rfl

theorem cell23_4672892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 4, 1, 4].length) (baseStart_4672892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672892 prefixEnd_4672892 := by exact prefixLift 4672892
  have htrace : WordTrace (prefixWord ++ tailWord_4672892) baseStart_4672892 baseEnd_4672892 := by
    simpa [prefixWord, tailWord_4672892, baseEnd_4672892] using wordTrace_append hprefix tailTrace_4672892
  have hstable : (prefixWord ++ tailWord_4672892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672892).length < 2 ^ (prefixWord ++ tailWord_4672892).sum := by decide
  have hdescent : baseEnd_4672892 < baseStart_4672892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672949 : List Nat := [1, 3, 3, 2, 2, 2, 2, 1, 3, 1, 3]
def baseStart_4672949 : Nat := 118140960795 + 4672949 * 2 ^ 59
def prefixEnd_4672949 : Nat := 4983230072969 + 3 ^ 40 * 4672949 * 2
def baseEnd_4672949 : Nat := 2399468910946942799247005

theorem tailTrace_4672949 : CollatzResearch.WordTrace tailWord_4672949 prefixEnd_4672949 2399468910946942799247005 := by
  unfold tailWord_4672949
  simp only [CollatzResearch.WordTrace]
  refine ⟨170436451947711323996221901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113624301298474215997481267 170436451947711323996221901)
  ·
    refine ⟨63913669480391746498583213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170436451947711323996221901 63913669480391746498583213)
    ·
      refine ⟨23967626055146904936968705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63913669480391746498583213 23967626055146904936968705)
      ·
        refine ⟨17975719541360178702726529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23967626055146904936968705 17975719541360178702726529)
        ·
          refine ⟨13481789656020134027044897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17975719541360178702726529 13481789656020134027044897)
          ·
            refine ⟨10111342242015100520283673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13481789656020134027044897 10111342242015100520283673)
            ·
              refine ⟨7583506681511325390212755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10111342242015100520283673 7583506681511325390212755)
              ·
                refine ⟨11375260022266988085319133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7583506681511325390212755 11375260022266988085319133)
                ·
                  refine ⟨4265722508350120531994675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11375260022266988085319133 4265722508350120531994675)
                  ·
                    refine ⟨6398583762525180797992013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4265722508350120531994675 6398583762525180797992013)
                    ·
                      refine ⟨2399468910946942799247005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6398583762525180797992013 2399468910946942799247005)
                      ·
                        rfl

theorem cell23_4672949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_4672949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672949 prefixEnd_4672949 := by exact prefixLift 4672949
  have htrace : WordTrace (prefixWord ++ tailWord_4672949) baseStart_4672949 baseEnd_4672949 := by
    simpa [prefixWord, tailWord_4672949, baseEnd_4672949] using wordTrace_append hprefix tailTrace_4672949
  have hstable : (prefixWord ++ tailWord_4672949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672949).length < 2 ^ (prefixWord ++ tailWord_4672949).sum := by decide
  have hdescent : baseEnd_4672949 < baseStart_4672949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672972 : List Nat := [2, 2, 1, 4, 2, 1, 1, 4, 1, 1, 4]
def baseStart_4672972 : Nat := 118140960795 + 4672972 * 2 ^ 59
def prefixEnd_4672972 : Nat := 4983230072969 + 3 ^ 40 * 4672972 * 2
def baseEnd_4672972 : Nat := 2399480721001996209259399

theorem tailTrace_4672972 : CollatzResearch.WordTrace tailWord_4672972 prefixEnd_4672972 2399480721001996209259399 := by
  unfold tailWord_4672972
  simp only [CollatzResearch.WordTrace]
  refine ⟨85218645413313999462154585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113624860551085332616206113 85218645413313999462154585)
  ·
    refine ⟨63913984059985499596615939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85218645413313999462154585 63913984059985499596615939)
    ·
      refine ⟨95870976089978249394923909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63913984059985499596615939 95870976089978249394923909)
      ·
        refine ⟨17975808016870921761548233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95870976089978249394923909 17975808016870921761548233)
        ·
          refine ⟨13481856012653191321161175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17975808016870921761548233 13481856012653191321161175)
          ·
            refine ⟨20222784018979786981741763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13481856012653191321161175 20222784018979786981741763)
            ·
              refine ⟨30334176028469680472612645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20222784018979786981741763 30334176028469680472612645)
              ·
                refine ⟨5687658005338065088614871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30334176028469680472612645 5687658005338065088614871)
                ·
                  refine ⟨8531487008007097632922307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5687658005338065088614871 8531487008007097632922307)
                  ·
                    refine ⟨12797230512010646449383461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8531487008007097632922307 12797230512010646449383461)
                    ·
                      refine ⟨2399480721001996209259399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12797230512010646449383461 2399480721001996209259399)
                      ·
                        rfl

theorem cell23_4672972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_4672972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672972 prefixEnd_4672972 := by exact prefixLift 4672972
  have htrace : WordTrace (prefixWord ++ tailWord_4672972) baseStart_4672972 baseEnd_4672972 := by
    simpa [prefixWord, tailWord_4672972, baseEnd_4672972] using wordTrace_append hprefix tailTrace_4672972
  have hstable : (prefixWord ++ tailWord_4672972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672972).length < 2 ^ (prefixWord ++ tailWord_4672972).sum := by decide
  have hdescent : baseEnd_4672972 < baseStart_4672972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672975 : List Nat := [1, 1, 2, 1, 1, 4, 2, 3, 3, 2, 3]
def baseStart_4672975 : Nat := 118140960795 + 4672975 * 2 ^ 59
def prefixEnd_4672975 : Nat := 4983230072969 + 3 ^ 40 * 4672975 * 2
def baseEnd_4672975 : Nat := 2399482261443959697521885

theorem tailTrace_4672975 : CollatzResearch.WordTrace tailWord_4672975 prefixEnd_4672975 2399482261443959697521885 := by
  unfold tailWord_4672975
  simp only [CollatzResearch.WordTrace]
  refine ⟨170437400245617130436668379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113624933497078086957778919 170437400245617130436668379)
  ·
    refine ⟨255656100368425695655002569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170437400245617130436668379 255656100368425695655002569)
    ·
      refine ⟨191742075276319271741251927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255656100368425695655002569 191742075276319271741251927)
      ·
        refine ⟨287613112914478907611877891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191742075276319271741251927 287613112914478907611877891)
        ·
          refine ⟨431419669371718361417816837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287613112914478907611877891 431419669371718361417816837)
          ·
            refine ⟨80891188007197192765840657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 431419669371718361417816837 80891188007197192765840657)
            ·
              refine ⟨60668391005397894574380493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80891188007197192765840657 60668391005397894574380493)
              ·
                refine ⟨22750646627024210465392685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60668391005397894574380493 22750646627024210465392685)
                ·
                  refine ⟨8531492485134078924522257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22750646627024210465392685 8531492485134078924522257)
                  ·
                    refine ⟨6398619363850559193391693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8531492485134078924522257 6398619363850559193391693)
                    ·
                      refine ⟨2399482261443959697521885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6398619363850559193391693 2399482261443959697521885)
                      ·
                        rfl

theorem cell23_4672975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 2, 3].length) (baseStart_4672975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672975 prefixEnd_4672975 := by exact prefixLift 4672975
  have htrace : WordTrace (prefixWord ++ tailWord_4672975) baseStart_4672975 baseEnd_4672975 := by
    simpa [prefixWord, tailWord_4672975, baseEnd_4672975] using wordTrace_append hprefix tailTrace_4672975
  have hstable : (prefixWord ++ tailWord_4672975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672975).length < 2 ^ (prefixWord ++ tailWord_4672975).sum := by decide
  have hdescent : baseEnd_4672975 < baseStart_4672975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4672995 : List Nat := [1, 1, 1, 6, 2, 3, 9]
def baseStart_4672995 : Nat := 118140960795 + 4672995 * 2 ^ 59
def prefixEnd_4672995 : Nat := 4983230072969 + 3 ^ 40 * 4672995 * 2
def baseEnd_4672995 : Nat := 29623364580951229867553

theorem tailTrace_4672995 : CollatzResearch.WordTrace tailWord_4672995 prefixEnd_4672995 29623364580951229867553 := by
  unfold tailWord_4672995
  simp only [CollatzResearch.WordTrace]
  refine ⟨170438129705544673852396439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113625419803696449234930959 170438129705544673852396439)
  ·
    refine ⟨255657194558317010778594659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170438129705544673852396439 255657194558317010778594659)
    ·
      refine ⟨383485791837475516167891989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255657194558317010778594659 383485791837475516167891989)
      ·
        refine ⟨17975896492381664820369937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 383485791837475516167891989 17975896492381664820369937)
        ·
          refine ⟨13481922369286248615277453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17975896492381664820369937 13481922369286248615277453)
          ·
            refine ⟨5055720888482343230729045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13481922369286248615277453 5055720888482343230729045)
            ·
              refine ⟨29623364580951229867553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5055720888482343230729045 29623364580951229867553)
              ·
                rfl

theorem cell23_4672995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 9].length) (baseStart_4672995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4672995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4672995 prefixEnd_4672995 := by exact prefixLift 4672995
  have htrace : WordTrace (prefixWord ++ tailWord_4672995) baseStart_4672995 baseEnd_4672995 := by
    simpa [prefixWord, tailWord_4672995, baseEnd_4672995] using wordTrace_append hprefix tailTrace_4672995
  have hstable : (prefixWord ++ tailWord_4672995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4672995).length < 2 ^ (prefixWord ++ tailWord_4672995).sum := by decide
  have hdescent : baseEnd_4672995 < baseStart_4672995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4672995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673026 : List Nat := [3, 4, 1, 2, 1, 1, 3, 2, 1, 2, 3]
def baseStart_4673026 : Nat := 118140960795 + 4673026 * 2 ^ 59
def prefixEnd_4673026 : Nat := 4983230072969 + 3 ^ 40 * 4673026 * 2
def baseEnd_4673026 : Nat := 2399508448957338997984151

theorem tailTrace_4673026 : CollatzResearch.WordTrace tailWord_4673026 prefixEnd_4673026 2399508448957338997984151 := by
  unfold tailWord_4673026
  simp only [CollatzResearch.WordTrace]
  refine ⟨42609815092108091536693733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113626173578954910764516621 42609815092108091536693733)
  ·
    refine ⟨7989340329770267163130075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42609815092108091536693733 7989340329770267163130075)
    ·
      refine ⟨11984010494655400744695113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7989340329770267163130075 11984010494655400744695113)
      ·
        refine ⟨8988007870991550558521335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11984010494655400744695113 8988007870991550558521335)
        ·
          refine ⟨13482011806487325837782003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8988007870991550558521335 13482011806487325837782003)
          ·
            refine ⟨20223017709730988756673005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13482011806487325837782003 20223017709730988756673005)
            ·
              refine ⟨7583631641149120783752377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20223017709730988756673005 7583631641149120783752377)
              ·
                refine ⟨5687723730861840587814283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7583631641149120783752377 5687723730861840587814283)
                ·
                  refine ⟨8531585596292760881721425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5687723730861840587814283 8531585596292760881721425)
                  ·
                    refine ⟨6398689197219570661291069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8531585596292760881721425 6398689197219570661291069)
                    ·
                      refine ⟨2399508448957338997984151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6398689197219570661291069 2399508448957338997984151)
                      ·
                        rfl

theorem cell23_4673026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_4673026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673026 prefixEnd_4673026 := by exact prefixLift 4673026
  have htrace : WordTrace (prefixWord ++ tailWord_4673026) baseStart_4673026 baseEnd_4673026 := by
    simpa [prefixWord, tailWord_4673026, baseEnd_4673026] using wordTrace_append hprefix tailTrace_4673026
  have hstable : (prefixWord ++ tailWord_4673026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673026).length < 2 ^ (prefixWord ++ tailWord_4673026).sum := by decide
  have hdescent : baseEnd_4673026 < baseStart_4673026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673056 : List Nat := [2, 1, 1, 6, 1, 2, 2, 2, 2, 1, 3]
def baseStart_4673056 : Nat := 118140960795 + 4673056 * 2 ^ 59
def prefixEnd_4673056 : Nat := 4983230072969 + 3 ^ 40 * 4673056 * 2
def baseEnd_4673056 : Nat := 2399523853376973880609013

theorem tailTrace_4673056 : CollatzResearch.WordTrace tailWord_4673056 prefixEnd_4673056 2399523853376973880609013 := by
  unfold tailWord_4673056
  simp only [CollatzResearch.WordTrace]
  refine ⟨85220177279161840635183511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113626903038882454180244681 85220177279161840635183511)
  ·
    refine ⟨127830265918742760952775267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85220177279161840635183511 127830265918742760952775267)
    ·
      refine ⟨191745398878114141429162901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127830265918742760952775267 191745398878114141429162901)
      ·
        refine ⟨8988065572411600379492011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 191745398878114141429162901 8988065572411600379492011)
        ·
          refine ⟨13482098358617400569238017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8988065572411600379492011 13482098358617400569238017)
          ·
            refine ⟨10111573768963050426928513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13482098358617400569238017 10111573768963050426928513)
            ·
              refine ⟨7583680326722287820196385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10111573768963050426928513 7583680326722287820196385)
              ·
                refine ⟨5687760245041715865147289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7583680326722287820196385 5687760245041715865147289)
                ·
                  refine ⟨4265820183781286898860467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5687760245041715865147289 4265820183781286898860467)
                  ·
                    refine ⟨6398730275671930348290701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4265820183781286898860467 6398730275671930348290701)
                    ·
                      refine ⟨2399523853376973880609013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6398730275671930348290701 2399523853376973880609013)
                      ·
                        rfl

theorem cell23_4673056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_4673056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673056 prefixEnd_4673056 := by exact prefixLift 4673056
  have htrace : WordTrace (prefixWord ++ tailWord_4673056) baseStart_4673056 baseEnd_4673056 := by
    simpa [prefixWord, tailWord_4673056, baseEnd_4673056] using wordTrace_append hprefix tailTrace_4673056
  have hstable : (prefixWord ++ tailWord_4673056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673056).length < 2 ^ (prefixWord ++ tailWord_4673056).sum := by decide
  have hdescent : baseEnd_4673056 < baseStart_4673056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673075 : List Nat := [1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 4]
def baseStart_4673075 : Nat := 118140960795 + 4673075 * 2 ^ 59
def prefixEnd_4673075 : Nat := 4983230072969 + 3 ^ 40 * 4673075 * 2
def baseEnd_4673075 : Nat := 2399533609509409306271425

theorem tailTrace_4673075 : CollatzResearch.WordTrace tailWord_4673075 prefixEnd_4673075 2399533609509409306271425 := by
  unfold tailWord_4673075
  simp only [CollatzResearch.WordTrace]
  refine ⟨170441047545254847515308679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113627365030169898343539119 170441047545254847515308679)
  ·
    refine ⟨255661571317882271272963019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170441047545254847515308679 255661571317882271272963019)
    ·
      refine ⟨383492356976823406909444529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255661571317882271272963019 383492356976823406909444529)
      ·
        refine ⟨287619267732617555182083397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 383492356976823406909444529 287619267732617555182083397)
        ·
          refine ⟨53928612699865791596640637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 287619267732617555182083397 53928612699865791596640637)
          ·
            refine ⟨20223229762449671848740239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53928612699865791596640637 20223229762449671848740239)
            ·
              refine ⟨30334844643674507773110359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20223229762449671848740239 30334844643674507773110359)
              ·
                refine ⟨45502266965511761659665539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30334844643674507773110359 45502266965511761659665539)
                ·
                  refine ⟨68253400448267642489498309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45502266965511761659665539 68253400448267642489498309)
                  ·
                    refine ⟨12797512584050182966780933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68253400448267642489498309 12797512584050182966780933)
                    ·
                      refine ⟨2399533609509409306271425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12797512584050182966780933 2399533609509409306271425)
                      ·
                        rfl

theorem cell23_4673075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 4].length) (baseStart_4673075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673075 prefixEnd_4673075 := by exact prefixLift 4673075
  have htrace : WordTrace (prefixWord ++ tailWord_4673075) baseStart_4673075 baseEnd_4673075 := by
    simpa [prefixWord, tailWord_4673075, baseEnd_4673075] using wordTrace_append hprefix tailTrace_4673075
  have hstable : (prefixWord ++ tailWord_4673075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673075).length < 2 ^ (prefixWord ++ tailWord_4673075).sum := by decide
  have hdescent : baseEnd_4673075 < baseStart_4673075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673079 : List Nat := [1, 1, 3, 1, 2, 5, 2, 1, 1, 4, 2]
def baseStart_4673079 : Nat := 118140960795 + 4673079 * 2 ^ 59
def prefixEnd_4673079 : Nat := 4983230072969 + 3 ^ 40 * 4673079 * 2
def baseEnd_4673079 : Nat := 2399535663432027290621407

theorem tailTrace_4673079 : CollatzResearch.WordTrace tailWord_4673079 prefixEnd_4673079 2399535663432027290621407 := by
  unfold tailWord_4673079
  simp only [CollatzResearch.WordTrace]
  refine ⟨170441193437240356198454291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113627462291493570798969527 170441193437240356198454291)
  ·
    refine ⟨255661790155860534297681437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170441193437240356198454291 255661790155860534297681437)
    ·
      refine ⟨95873171308447700361630539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255661790155860534297681437 95873171308447700361630539)
      ·
        refine ⟨143809756962671550542445809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95873171308447700361630539 143809756962671550542445809)
        ·
          refine ⟨107857317722003662906834357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143809756962671550542445809 107857317722003662906834357)
          ·
            refine ⟨10111623536437843397515721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 107857317722003662906834357 10111623536437843397515721)
            ·
              refine ⟨7583717652328382548136791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10111623536437843397515721 7583717652328382548136791)
              ·
                refine ⟨11375576478492573822205187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7583717652328382548136791 11375576478492573822205187)
                ·
                  refine ⟨17063364717738860733307781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11375576478492573822205187 17063364717738860733307781)
                  ·
                    refine ⟨3199380884576036387495209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17063364717738860733307781 3199380884576036387495209)
                    ·
                      refine ⟨2399535663432027290621407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3199380884576036387495209 2399535663432027290621407)
                      ·
                        rfl

theorem cell23_4673079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 4, 2].length) (baseStart_4673079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673079 prefixEnd_4673079 := by exact prefixLift 4673079
  have htrace : WordTrace (prefixWord ++ tailWord_4673079) baseStart_4673079 baseEnd_4673079 := by
    simpa [prefixWord, tailWord_4673079, baseEnd_4673079] using wordTrace_append hprefix tailTrace_4673079
  have hstable : (prefixWord ++ tailWord_4673079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673079).length < 2 ^ (prefixWord ++ tailWord_4673079).sum := by decide
  have hdescent : baseEnd_4673079 < baseStart_4673079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673145 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 2, 8]
def baseStart_4673145 : Nat := 118140960795 + 4673145 * 2 ^ 59
def prefixEnd_4673145 : Nat := 4983230072969 + 3 ^ 40 * 4673145 * 2
def baseEnd_4673145 : Nat := 799856517718408010798701

theorem tailTrace_4673145 : CollatzResearch.WordTrace tailWord_4673145 prefixEnd_4673145 799856517718408010798701 := by
  unfold tailWord_4673145
  simp only [CollatzResearch.WordTrace]
  refine ⟨170443600655001249470356889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113629067103334166313571259 170443600655001249470356889)
  ·
    refine ⟨127832700491250937102767667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170443600655001249470356889 127832700491250937102767667)
    ·
      refine ⟨191749050736876405654151501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127832700491250937102767667 191749050736876405654151501)
      ·
        refine ⟨71905894026328652120306813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191749050736876405654151501 71905894026328652120306813)
        ·
          refine ⟨26964710259873244545115055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71905894026328652120306813 26964710259873244545115055)
          ·
            refine ⟨40447065389809866817672583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26964710259873244545115055 40447065389809866817672583)
            ·
              refine ⟨60670598084714800226508875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40447065389809866817672583 60670598084714800226508875)
              ·
                refine ⟨91005897127072200339763313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60670598084714800226508875 91005897127072200339763313)
                ·
                  refine ⟨68254422845304150254822485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91005897127072200339763313 68254422845304150254822485)
                  ·
                    refine ⟨799856517718408010798701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68254422845304150254822485 799856517718408010798701)
                    ·
                      rfl

theorem cell23_4673145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 8].length) (baseStart_4673145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673145 prefixEnd_4673145 := by exact prefixLift 4673145
  have htrace : WordTrace (prefixWord ++ tailWord_4673145) baseStart_4673145 baseEnd_4673145 := by
    simpa [prefixWord, tailWord_4673145, baseEnd_4673145] using wordTrace_append hprefix tailTrace_4673145
  have hstable : (prefixWord ++ tailWord_4673145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673145).length < 2 ^ (prefixWord ++ tailWord_4673145).sum := by decide
  have hdescent : baseEnd_4673145 < baseStart_4673145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673152 : List Nat := [2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 4]
def baseStart_4673152 : Nat := 118140960795 + 4673152 * 2 ^ 59
def prefixEnd_4673152 : Nat := 4983230072969 + 3 ^ 40 * 4673152 * 2
def baseEnd_4673152 : Nat := 2399573147519805505008571

theorem tailTrace_4673152 : CollatzResearch.WordTrace tailWord_4673152 prefixEnd_4673152 2399573147519805505008571 := by
  unfold tailWord_4673152
  simp only [CollatzResearch.WordTrace]
  refine ⟨85221927982987944832930855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113629237310650593110574473 85221927982987944832930855)
  ·
    refine ⟨127832891974481917249396283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85221927982987944832930855 127832891974481917249396283)
    ·
      refine ⟨191749337961722875874094425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127832891974481917249396283 191749337961722875874094425)
      ·
        refine ⟨143812003471292156905570819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191749337961722875874094425 143812003471292156905570819)
        ·
          refine ⟨215718005206938235358356229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143812003471292156905570819 215718005206938235358356229)
          ·
            refine ⟨40447125976300919129691793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 215718005206938235358356229 40447125976300919129691793)
            ·
              refine ⟨30335344482225689347268845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40447125976300919129691793 30335344482225689347268845)
              ·
                refine ⟨11375754180834633505225817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30335344482225689347268845 11375754180834633505225817)
                ·
                  refine ⟨8531815635625975128919363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11375754180834633505225817 8531815635625975128919363)
                  ·
                    refine ⟨12797723453438962693379045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8531815635625975128919363 12797723453438962693379045)
                    ·
                      refine ⟨2399573147519805505008571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12797723453438962693379045 2399573147519805505008571)
                      ·
                        rfl

theorem cell23_4673152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 4].length) (baseStart_4673152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673152 prefixEnd_4673152 := by exact prefixLift 4673152
  have htrace : WordTrace (prefixWord ++ tailWord_4673152) baseStart_4673152 baseEnd_4673152 := by
    simpa [prefixWord, tailWord_4673152, baseEnd_4673152] using wordTrace_append hprefix tailTrace_4673152
  have hstable : (prefixWord ++ tailWord_4673152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673152).length < 2 ^ (prefixWord ++ tailWord_4673152).sum := by decide
  have hdescent : baseEnd_4673152 < baseStart_4673152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673155 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 5]
def baseStart_4673155 : Nat := 118140960795 + 4673155 * 2 ^ 59
def prefixEnd_4673155 : Nat := 4983230072969 + 3 ^ 40 * 4673155 * 2
def baseEnd_4673155 : Nat := 2399574687961768993271057

theorem tailTrace_4673155 : CollatzResearch.WordTrace tailWord_4673155 prefixEnd_4673155 2399574687961768993271057 := by
  unfold tailWord_4673155
  simp only [CollatzResearch.WordTrace]
  refine ⟨170443965384965021178220919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113629310256643347452147279 170443965384965021178220919)
  ·
    refine ⟨255665948077447531767331379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170443965384965021178220919 255665948077447531767331379)
    ·
      refine ⟨383498922116171297650997069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255665948077447531767331379 383498922116171297650997069)
      ·
        refine ⟨143812095793564236619123901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 383498922116171297650997069 143812095793564236619123901)
        ·
          refine ⟨53929535922586588732171463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143812095793564236619123901 53929535922586588732171463)
          ·
            refine ⟨80894303883879883098257195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53929535922586588732171463 80894303883879883098257195)
            ·
              refine ⟨121341455825819824647385793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80894303883879883098257195 121341455825819824647385793)
              ·
                refine ⟨91006091869364868485539345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121341455825819824647385793 91006091869364868485539345)
                ·
                  refine ⟨68254568902023651364154509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91006091869364868485539345 68254568902023651364154509)
                  ·
                    refine ⟨25595463338258869261557941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68254568902023651364154509 25595463338258869261557941)
                    ·
                      refine ⟨2399574687961768993271057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25595463338258869261557941 2399574687961768993271057)
                      ·
                        rfl

theorem cell23_4673155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_4673155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673155 prefixEnd_4673155 := by exact prefixLift 4673155
  have htrace : WordTrace (prefixWord ++ tailWord_4673155) baseStart_4673155 baseEnd_4673155 := by
    simpa [prefixWord, tailWord_4673155, baseEnd_4673155] using wordTrace_append hprefix tailTrace_4673155
  have hstable : (prefixWord ++ tailWord_4673155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673155).length < 2 ^ (prefixWord ++ tailWord_4673155).sum := by decide
  have hdescent : baseEnd_4673155 < baseStart_4673155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673202 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3]
def baseStart_4673202 : Nat := 118140960795 + 4673202 * 2 ^ 59
def prefixEnd_4673202 : Nat := 4983230072969 + 3 ^ 40 * 4673202 * 2
def baseEnd_4673202 : Nat := 2399598821552530309383341

theorem tailTrace_4673202 : CollatzResearch.WordTrace tailWord_4673202 prefixEnd_4673202 2399598821552530309383341 := by
  unfold tailWord_4673202
  simp only [CollatzResearch.WordTrace]
  refine ⟨42611419903948687051295465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113630453077196498803454573 42611419903948687051295465)
  ·
    refine ⟨31958564927961515288471599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42611419903948687051295465 31958564927961515288471599)
    ·
      refine ⟨47937847391942272932707399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31958564927961515288471599 47937847391942272932707399)
      ·
        refine ⟨71906771087913409399061099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47937847391942272932707399 71906771087913409399061099)
        ·
          refine ⟨107860156631870114098591649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71906771087913409399061099 107860156631870114098591649)
          ·
            refine ⟨80895117473902585573943737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107860156631870114098591649 80895117473902585573943737)
            ·
              refine ⟨60671338105426939180457803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80895117473902585573943737 60671338105426939180457803)
              ·
                refine ⟨91007007158140408770686705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60671338105426939180457803 91007007158140408770686705)
                ·
                  refine ⟨68255255368605306578015029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91007007158140408770686705 68255255368605306578015029)
                  ·
                    refine ⟨6398930190806747491688909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 68255255368605306578015029 6398930190806747491688909)
                    ·
                      refine ⟨2399598821552530309383341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6398930190806747491688909 2399598821552530309383341)
                      ·
                        rfl

theorem cell23_4673202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_4673202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673202 prefixEnd_4673202 := by exact prefixLift 4673202
  have htrace : WordTrace (prefixWord ++ tailWord_4673202) baseStart_4673202 baseEnd_4673202 := by
    simpa [prefixWord, tailWord_4673202, baseEnd_4673202] using wordTrace_append hprefix tailTrace_4673202
  have hstable : (prefixWord ++ tailWord_4673202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673202).length < 2 ^ (prefixWord ++ tailWord_4673202).sum := by decide
  have hdescent : baseEnd_4673202 < baseStart_4673202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673270 : List Nat := [5, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3]
def baseStart_4673270 : Nat := 118140960795 + 4673270 * 2 ^ 59
def prefixEnd_4673270 : Nat := 4983230072969 + 3 ^ 40 * 4673270 * 2
def baseEnd_4673270 : Nat := 2399633738237036043333029

theorem tailTrace_4673270 : CollatzResearch.WordTrace tailWord_4673270 prefixEnd_4673270 2399633738237036043333029 := by
  unfold tailWord_4673270
  simp only [CollatzResearch.WordTrace]
  refine ⟨10653009986221774738666079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113632106519698930545771509 10653009986221774738666079)
  ·
    refine ⟨15979514979332662107999119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10653009986221774738666079 15979514979332662107999119)
    ·
      refine ⟨23969272468998993161998679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15979514979332662107999119 23969272468998993161998679)
      ·
        refine ⟨35953908703498489742998019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23969272468998993161998679 35953908703498489742998019)
        ·
          refine ⟨53930863055247734614497029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35953908703498489742998019 53930863055247734614497029)
          ·
            refine ⟨10112036822858950240218193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53930863055247734614497029 10112036822858950240218193)
            ·
              refine ⟨7584027617144212680163645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10112036822858950240218193 7584027617144212680163645)
              ·
                refine ⟨2844010356429079755061367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7584027617144212680163645 2844010356429079755061367)
                ·
                  refine ⟨4266015534643619632592051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2844010356429079755061367 4266015534643619632592051)
                  ·
                    refine ⟨6399023301965429448888077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4266015534643619632592051 6399023301965429448888077)
                    ·
                      refine ⟨2399633738237036043333029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6399023301965429448888077 2399633738237036043333029)
                      ·
                        rfl

theorem cell23_4673270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_4673270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673270 prefixEnd_4673270 := by exact prefixLift 4673270
  have htrace : WordTrace (prefixWord ++ tailWord_4673270) baseStart_4673270 baseEnd_4673270 := by
    simpa [prefixWord, tailWord_4673270, baseEnd_4673270] using wordTrace_append hprefix tailTrace_4673270
  have hstable : (prefixWord ++ tailWord_4673270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673270).length < 2 ^ (prefixWord ++ tailWord_4673270).sum := by decide
  have hdescent : baseEnd_4673270 < baseStart_4673270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673272 : List Nat := [2, 1, 2, 1, 1, 2, 2, 3, 3, 2, 4]
def baseStart_4673272 : Nat := 118140960795 + 4673272 * 2 ^ 59
def prefixEnd_4673272 : Nat := 4983230072969 + 3 ^ 40 * 4673272 * 2
def baseEnd_4673272 : Nat := 2399634765198345035508019

theorem tailTrace_4673272 : CollatzResearch.WordTrace tailWord_4673272 prefixEnd_4673272 2399634765198345035508019 := by
  unfold tailWord_4673272
  simp only [CollatzResearch.WordTrace]
  refine ⟨85224116362770575080115035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113632155150360766773486713 85224116362770575080115035)
  ·
    refine ⟨127836174544155862620172553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85224116362770575080115035 127836174544155862620172553)
    ·
      refine ⟨95877130908116896965129415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127836174544155862620172553 95877130908116896965129415)
      ·
        refine ⟨143815696362175345447694123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95877130908116896965129415 143815696362175345447694123)
        ·
          refine ⟨215723544543263018171541185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143815696362175345447694123 215723544543263018171541185)
          ·
            refine ⟨161792658407447263628655889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215723544543263018171541185 161792658407447263628655889)
            ·
              refine ⟨121344493805585447721491917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161792658407447263628655889 121344493805585447721491917)
              ·
                refine ⟨45504185177094542895559469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121344493805585447721491917 45504185177094542895559469)
                ·
                  refine ⟨17064069441410453585834801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45504185177094542895559469 17064069441410453585834801)
                  ·
                    refine ⟨12798052081057840189376101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17064069441410453585834801 12798052081057840189376101)
                    ·
                      refine ⟨2399634765198345035508019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12798052081057840189376101 2399634765198345035508019)
                      ·
                        rfl

theorem cell23_4673272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_4673272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673272 prefixEnd_4673272 := by exact prefixLift 4673272
  have htrace : WordTrace (prefixWord ++ tailWord_4673272) baseStart_4673272 baseEnd_4673272 := by
    simpa [prefixWord, tailWord_4673272, baseEnd_4673272] using wordTrace_append hprefix tailTrace_4673272
  have hstable : (prefixWord ++ tailWord_4673272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673272).length < 2 ^ (prefixWord ++ tailWord_4673272).sum := by decide
  have hdescent : baseEnd_4673272 < baseStart_4673272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673276 : List Nat := [2, 2, 2, 1, 3, 1, 1, 2, 5, 2, 2]
def baseStart_4673276 : Nat := 118140960795 + 4673276 * 2 ^ 59
def prefixEnd_4673276 : Nat := 4983230072969 + 3 ^ 40 * 4673276 * 2
def baseEnd_4673276 : Nat := 2399636819120963019858001

theorem tailTrace_4673276 : CollatzResearch.WordTrace tailWord_4673276 prefixEnd_4673276 2399636819120963019858001 := by
  unfold tailWord_4673276
  simp only [CollatzResearch.WordTrace]
  refine ⟨85224189308763329421687841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113632252411684439228917121 85224189308763329421687841)
  ·
    refine ⟨63918141981572497066265881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85224189308763329421687841 63918141981572497066265881)
    ·
      refine ⟨47938606486179372799699411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63918141981572497066265881 47938606486179372799699411)
      ·
        refine ⟨71907909729269059199549117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47938606486179372799699411 71907909729269059199549117)
        ·
          refine ⟨26965466148475897199830919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71907909729269059199549117 26965466148475897199830919)
          ·
            refine ⟨40448199222713845799746379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26965466148475897199830919 40448199222713845799746379)
            ·
              refine ⟨60672298834070768699619569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40448199222713845799746379 60672298834070768699619569)
              ·
                refine ⟨45504224125553076524714677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60672298834070768699619569 45504224125553076524714677)
                ·
                  refine ⟨4266021011770600924192001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45504224125553076524714677 4266021011770600924192001)
                  ·
                    refine ⟨3199515758827950693144001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4266021011770600924192001 3199515758827950693144001)
                    ·
                      refine ⟨2399636819120963019858001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3199515758827950693144001 2399636819120963019858001)
                      ·
                        rfl

theorem cell23_4673276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 5, 2, 2].length) (baseStart_4673276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673276 prefixEnd_4673276 := by exact prefixLift 4673276
  have htrace : WordTrace (prefixWord ++ tailWord_4673276) baseStart_4673276 baseEnd_4673276 := by
    simpa [prefixWord, tailWord_4673276, baseEnd_4673276] using wordTrace_append hprefix tailTrace_4673276
  have hstable : (prefixWord ++ tailWord_4673276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673276).length < 2 ^ (prefixWord ++ tailWord_4673276).sum := by decide
  have hdescent : baseEnd_4673276 < baseStart_4673276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673303 : List Nat := [1, 1, 3, 4, 2, 2, 3, 1, 2, 4]
def baseStart_4673303 : Nat := 118140960795 + 4673303 * 2 ^ 59
def prefixEnd_4673303 : Nat := 4983230072969 + 3 ^ 40 * 4673303 * 2
def baseEnd_4673303 : Nat := 799883561032878138073459

theorem tailTrace_4673303 : CollatzResearch.WordTrace tailWord_4673303 prefixEnd_4673303 799883561032878138073459 := by
  unfold tailWord_4673303
  simp only [CollatzResearch.WordTrace]
  refine ⟨170449363388428842454608563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113632908925619228303072375 170449363388428842454608563)
  ·
    refine ⟨255674045082643263681912845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170449363388428842454608563 255674045082643263681912845)
    ·
      refine ⟨95877766905991223880717317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255674045082643263681912845 95877766905991223880717317)
      ·
        refine ⟨17977081294873354477634497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95877766905991223880717317 17977081294873354477634497)
        ·
          refine ⟨13482810971155015858225873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17977081294873354477634497 13482810971155015858225873)
          ·
            refine ⟨10112108228366261893669405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13482810971155015858225873 10112108228366261893669405)
            ·
              refine ⟨3792040585637348210126027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10112108228366261893669405 3792040585637348210126027)
              ·
                refine ⟨5688060878456022315189041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3792040585637348210126027 5688060878456022315189041)
                ·
                  refine ⟨4266045658842016736391781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5688060878456022315189041 4266045658842016736391781)
                  ·
                    refine ⟨799883561032878138073459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4266045658842016736391781 799883561032878138073459)
                    ·
                      rfl

theorem cell23_4673303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 2, 4].length) (baseStart_4673303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673303 prefixEnd_4673303 := by exact prefixLift 4673303
  have htrace : WordTrace (prefixWord ++ tailWord_4673303) baseStart_4673303 baseEnd_4673303 := by
    simpa [prefixWord, tailWord_4673303, baseEnd_4673303] using wordTrace_append hprefix tailTrace_4673303
  have hstable : (prefixWord ++ tailWord_4673303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673303).length < 2 ^ (prefixWord ++ tailWord_4673303).sum := by decide
  have hdescent : baseEnd_4673303 < baseStart_4673303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673306 : List Nat := [3, 1, 1, 3, 2, 4, 1, 1, 1, 2, 4]
def baseStart_4673306 : Nat := 118140960795 + 4673306 * 2 ^ 59
def prefixEnd_4673306 : Nat := 4983230072969 + 3 ^ 40 * 4673306 * 2
def baseEnd_4673306 : Nat := 2399652223540597902482863

theorem tailTrace_4673306 : CollatzResearch.WordTrace tailWord_4673306 prefixEnd_4673306 2399652223540597902482863 := by
  unfold tailWord_4673306
  simp only [CollatzResearch.WordTrace]
  refine ⟨42612368201854493491741943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113632981871611982644645181 42612368201854493491741943)
  ·
    refine ⟨63918552302781740237612915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42612368201854493491741943 63918552302781740237612915)
    ·
      refine ⟨95877828454172610356419373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63918552302781740237612915 95877828454172610356419373)
      ·
        refine ⟨35954185670314728883657265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95877828454172610356419373 35954185670314728883657265)
        ·
          refine ⟨26965639252736046662742949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35954185670314728883657265 26965639252736046662742949)
          ·
            refine ⟨5056057359888008749264303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26965639252736046662742949 5056057359888008749264303)
            ·
              refine ⟨7584086039832013123896455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5056057359888008749264303 7584086039832013123896455)
              ·
                refine ⟨11376129059748019685844683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7584086039832013123896455 11376129059748019685844683)
                ·
                  refine ⟨17064193589622029528767025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11376129059748019685844683 17064193589622029528767025)
                  ·
                    refine ⟨12798145192216522146575269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17064193589622029528767025 12798145192216522146575269)
                    ·
                      refine ⟨2399652223540597902482863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12798145192216522146575269 2399652223540597902482863)
                      ·
                        rfl

theorem cell23_4673306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_4673306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673306 prefixEnd_4673306 := by exact prefixLift 4673306
  have htrace : WordTrace (prefixWord ++ tailWord_4673306) baseStart_4673306 baseEnd_4673306 := by
    simpa [prefixWord, tailWord_4673306, baseEnd_4673306] using wordTrace_append hprefix tailTrace_4673306
  have hstable : (prefixWord ++ tailWord_4673306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673306).length < 2 ^ (prefixWord ++ tailWord_4673306).sum := by decide
  have hdescent : baseEnd_4673306 < baseStart_4673306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673316 : List Nat := [2, 3, 1, 3, 2, 3, 2, 7]
def baseStart_4673316 : Nat := 118140960795 + 4673316 * 2 ^ 59
def prefixEnd_4673316 : Nat := 4983230072969 + 3 ^ 40 * 4673316 * 2
def baseEnd_4673316 : Nat := 88876198457301587531771

theorem tailTrace_4673316 : CollatzResearch.WordTrace tailWord_4673316 prefixEnd_4673316 88876198457301587531771 := by
  unfold tailWord_4673316
  simp only [CollatzResearch.WordTrace]
  refine ⟨85224918768690872837415901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113633225024921163783221201 85224918768690872837415901)
  ·
    refine ⟨31959344538259077314030963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85224918768690872837415901 31959344538259077314030963)
    ·
      refine ⟨47939016807388615971046445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31959344538259077314030963 47939016807388615971046445)
      ·
        refine ⟨17977131302770730989142417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47939016807388615971046445 17977131302770730989142417)
        ·
          refine ⟨13482848477078048241856813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17977131302770730989142417 13482848477078048241856813)
          ·
            refine ⟨5056068178904268090696305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13482848477078048241856813 5056068178904268090696305)
            ·
              refine ⟨3792051134178201068022229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5056068178904268090696305 3792051134178201068022229)
              ·
                refine ⟨88876198457301587531771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3792051134178201068022229 88876198457301587531771)
                ·
                  rfl

theorem cell23_4673316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 7].length) (baseStart_4673316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673316 prefixEnd_4673316 := by exact prefixLift 4673316
  have htrace : WordTrace (prefixWord ++ tailWord_4673316) baseStart_4673316 baseEnd_4673316 := by
    simpa [prefixWord, tailWord_4673316, baseEnd_4673316] using wordTrace_append hprefix tailTrace_4673316
  have hstable : (prefixWord ++ tailWord_4673316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673316).length < 2 ^ (prefixWord ++ tailWord_4673316).sum := by decide
  have hdescent : baseEnd_4673316 < baseStart_4673316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673436 : List Nat := [2, 2, 3, 3, 1, 2, 1, 1, 1, 7]
def baseStart_4673436 : Nat := 118140960795 + 4673436 * 2 ^ 59
def prefixEnd_4673436 : Nat := 4983230072969 + 3 ^ 40 * 4673436 * 2
def baseEnd_4673436 : Nat := 799906325341894131285755

theorem tailTrace_4673436 : CollatzResearch.WordTrace tailWord_4673436 prefixEnd_4673436 799906325341894131285755 := by
  unfold tailWord_4673436
  simp only [CollatzResearch.WordTrace]
  refine ⟨85227107148473503084600081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113636142864631337446133441 85227107148473503084600081)
  ·
    refine ⟨63920330361355127313450061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85227107148473503084600081 63920330361355127313450061)
    ·
      refine ⟨23970123885508172742543773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63920330361355127313450061 23970123885508172742543773)
      ·
        refine ⟨8988796457065564778453915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23970123885508172742543773 8988796457065564778453915)
        ·
          refine ⟨13483194685598347167680873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8988796457065564778453915 13483194685598347167680873)
          ·
            refine ⟨10112396014198760375760655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13483194685598347167680873 10112396014198760375760655)
            ·
              refine ⟨15168594021298140563640983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10112396014198760375760655 15168594021298140563640983)
              ·
                refine ⟨22752891031947210845461475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15168594021298140563640983 22752891031947210845461475)
                ·
                  refine ⟨34129336547920816268192213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22752891031947210845461475 34129336547920816268192213)
                  ·
                    refine ⟨799906325341894131285755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34129336547920816268192213 799906325341894131285755)
                    ·
                      rfl

theorem cell23_4673436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_4673436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673436 prefixEnd_4673436 := by exact prefixLift 4673436
  have htrace : WordTrace (prefixWord ++ tailWord_4673436) baseStart_4673436 baseEnd_4673436 := by
    simpa [prefixWord, tailWord_4673436, baseEnd_4673436] using wordTrace_append hprefix tailTrace_4673436
  have hstable : (prefixWord ++ tailWord_4673436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673436).length < 2 ^ (prefixWord ++ tailWord_4673436).sum := by decide
  have hdescent : baseEnd_4673436 < baseStart_4673436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673517 : List Nat := [1, 5, 1, 4, 1, 2, 1, 1, 3, 4]
def baseStart_4673517 : Nat := 118140960795 + 4673517 * 2 ^ 59
def prefixEnd_4673517 : Nat := 4983230072969 + 3 ^ 40 * 4673517 * 2
def baseEnd_4673517 : Nat := 799920189319565525648131

theorem tailTrace_4673517 : CollatzResearch.WordTrace tailWord_4673517 prefixEnd_4673517 799920189319565525648131 := by
  unfold tailWord_4673517
  simp only [CollatzResearch.WordTrace]
  refine ⟨170457168609653557002898805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113638112406435704668599203 170457168609653557002898805)
  ·
    refine ⟨15980359557155020969021763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 170457168609653557002898805 15980359557155020969021763)
    ·
      refine ⟨23970539335732531453532645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15980359557155020969021763 23970539335732531453532645)
      ·
        refine ⟨4494476125449849647537371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23970539335732531453532645 4494476125449849647537371)
        ·
          refine ⟨6741714188174774471306057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4494476125449849647537371 6741714188174774471306057)
          ·
            refine ⟨5056285641131080853479543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6741714188174774471306057 5056285641131080853479543)
            ·
              refine ⟨7584428461696621280219315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5056285641131080853479543 7584428461696621280219315)
              ·
                refine ⟨11376642692544931920328973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7584428461696621280219315 11376642692544931920328973)
                ·
                  refine ⟨4266241009704349470123365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11376642692544931920328973 4266241009704349470123365)
                  ·
                    refine ⟨799920189319565525648131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4266241009704349470123365 799920189319565525648131)
                    ·
                      rfl

theorem cell23_4673517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_4673517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673517 prefixEnd_4673517 := by exact prefixLift 4673517
  have htrace : WordTrace (prefixWord ++ tailWord_4673517) baseStart_4673517 baseEnd_4673517 := by
    simpa [prefixWord, tailWord_4673517, baseEnd_4673517] using wordTrace_append hprefix tailTrace_4673517
  have hstable : (prefixWord ++ tailWord_4673517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673517).length < 2 ^ (prefixWord ++ tailWord_4673517).sum := by decide
  have hdescent : baseEnd_4673517 < baseStart_4673517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673539 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 5, 6]
def baseStart_4673539 : Nat := 118140960795 + 4673539 * 2 ^ 59
def prefixEnd_4673539 : Nat := 4983230072969 + 3 ^ 40 * 4673539 * 2
def baseEnd_4673539 : Nat := 799923954844365163623097

theorem tailTrace_4673539 : CollatzResearch.WordTrace tailWord_4673539 prefixEnd_4673539 799923954844365163623097 := by
  unfold tailWord_4673539
  simp only [CollatzResearch.WordTrace]
  refine ⟨170457971015573854760199671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113638647343715903173466447 170457971015573854760199671)
  ·
    refine ⟨255686956523360782140299507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170457971015573854760199671 255686956523360782140299507)
    ·
      refine ⟨383530434785041173210449261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255686956523360782140299507 383530434785041173210449261)
      ·
        refine ⟨143823913044390439953918473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 383530434785041173210449261 143823913044390439953918473)
        ·
          refine ⟨107867934783292829965438855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143823913044390439953918473 107867934783292829965438855)
          ·
            refine ⟨161801902174939244948158283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107867934783292829965438855 161801902174939244948158283)
            ·
              refine ⟨242702853262408867422237425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161801902174939244948158283 242702853262408867422237425)
              ·
                refine ⟨182027139946806650566678069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 242702853262408867422237425 182027139946806650566678069)
                ·
                  refine ⟨17065044370013123490626069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 182027139946806650566678069 17065044370013123490626069)
                  ·
                    refine ⟨799923954844365163623097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17065044370013123490626069 799923954844365163623097)
                    ·
                      rfl

theorem cell23_4673539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 6].length) (baseStart_4673539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673539 prefixEnd_4673539 := by exact prefixLift 4673539
  have htrace : WordTrace (prefixWord ++ tailWord_4673539) baseStart_4673539 baseEnd_4673539 := by
    simpa [prefixWord, tailWord_4673539, baseEnd_4673539] using wordTrace_append hprefix tailTrace_4673539
  have hstable : (prefixWord ++ tailWord_4673539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673539).length < 2 ^ (prefixWord ++ tailWord_4673539).sum := by decide
  have hdescent : baseEnd_4673539 < baseStart_4673539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673543 : List Nat := [1, 1, 4, 3, 1, 2, 3, 2, 1, 5]
def baseStart_4673543 : Nat := 118140960795 + 4673543 * 2 ^ 59
def prefixEnd_4673543 : Nat := 4983230072969 + 3 ^ 40 * 4673543 * 2
def baseEnd_4673543 : Nat := 799924639485237825073091

theorem tailTrace_4673543 : CollatzResearch.WordTrace tailWord_4673543 prefixEnd_4673543 799924639485237825073091 := by
  unfold tailWord_4673543
  simp only [CollatzResearch.WordTrace]
  refine ⟨170458116907559363443345283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113638744605039575628896855 170458116907559363443345283)
  ·
    refine ⟨255687175361339045165017925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170458116907559363443345283 255687175361339045165017925)
    ·
      refine ⟨47941345380251070968440861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 255687175361339045165017925 47941345380251070968440861)
      ·
        refine ⟨17978004517594151613165323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47941345380251070968440861 17978004517594151613165323)
        ·
          refine ⟨26967006776391227419747985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17978004517594151613165323 26967006776391227419747985)
          ·
            refine ⟨20225255082293420564810989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26967006776391227419747985 20225255082293420564810989)
            ·
              refine ⟨7584470655860032711804121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20225255082293420564810989 7584470655860032711804121)
              ·
                refine ⟨5688352991895024533853091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7584470655860032711804121 5688352991895024533853091)
                ·
                  refine ⟨8532529487842536800779637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5688352991895024533853091 8532529487842536800779637)
                  ·
                    refine ⟨799924639485237825073091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8532529487842536800779637 799924639485237825073091)
                    ·
                      rfl

theorem cell23_4673543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_4673543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673543 prefixEnd_4673543 := by exact prefixLift 4673543
  have htrace : WordTrace (prefixWord ++ tailWord_4673543) baseStart_4673543 baseEnd_4673543 := by
    simpa [prefixWord, tailWord_4673543, baseEnd_4673543] using wordTrace_append hprefix tailTrace_4673543
  have hstable : (prefixWord ++ tailWord_4673543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673543).length < 2 ^ (prefixWord ++ tailWord_4673543).sum := by decide
  have hdescent : baseEnd_4673543 < baseStart_4673543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673550 : List Nat := [4, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2]
def baseStart_4673550 : Nat := 118140960795 + 4673550 * 2 ^ 59
def prefixEnd_4673550 : Nat := 4983230072969 + 3 ^ 40 * 4673550 * 2
def baseEnd_4673550 : Nat := 2399777512820294947831741

theorem tailTrace_4673550 : CollatzResearch.WordTrace tailWord_4673550 prefixEnd_4673550 2399777512820294947831741 := by
  unfold tailWord_4673550
  simp only [CollatzResearch.WordTrace]
  refine ⟨21307296527316750454856263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113638914812356002425900069 21307296527316750454856263)
  ·
    refine ⟨31960944790975125682284395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21307296527316750454856263 31960944790975125682284395)
    ·
      refine ⟨47941417186462688523426593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31960944790975125682284395 47941417186462688523426593)
      ·
        refine ⟨35956062889847016392569945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47941417186462688523426593 35956062889847016392569945)
        ·
          refine ⟨26967047167385262294427459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35956062889847016392569945 26967047167385262294427459)
          ·
            refine ⟨40450570751077893441641189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26967047167385262294427459 40450570751077893441641189)
            ·
              refine ⟨7584482015827105020307723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40450570751077893441641189 7584482015827105020307723)
              ·
                refine ⟨11376723023740657530461585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7584482015827105020307723 11376723023740657530461585)
                ·
                  refine ⟨8532542267805493147846189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11376723023740657530461585 8532542267805493147846189)
                  ·
                    refine ⟨3199703350427059930442321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8532542267805493147846189 3199703350427059930442321)
                    ·
                      refine ⟨2399777512820294947831741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3199703350427059930442321 2399777512820294947831741)
                      ·
                        rfl

theorem cell23_4673550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_4673550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673550 prefixEnd_4673550 := by exact prefixLift 4673550
  have htrace : WordTrace (prefixWord ++ tailWord_4673550) baseStart_4673550 baseEnd_4673550 := by
    simpa [prefixWord, tailWord_4673550, baseEnd_4673550] using wordTrace_append hprefix tailTrace_4673550
  have hstable : (prefixWord ++ tailWord_4673550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673550).length < 2 ^ (prefixWord ++ tailWord_4673550).sum := by decide
  have hdescent : baseEnd_4673550 < baseStart_4673550 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673563 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 7, 2, 2]
def baseStart_4673563 : Nat := 118140960795 + 4673563 * 2 ^ 59
def prefixEnd_4673563 : Nat := 4983230072969 + 3 ^ 40 * 4673563 * 2
def baseEnd_4673563 : Nat := 2399784188068803396969181

theorem tailTrace_4673563 : CollatzResearch.WordTrace tailWord_4673563 prefixEnd_4673563 2399784188068803396969181 := by
  unfold tailWord_4673563
  simp only [CollatzResearch.WordTrace]
  refine ⟨170458846367486906859073343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113639230911657937906048895 170458846367486906859073343)
  ·
    refine ⟨255688269551230360288610015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170458846367486906859073343 255688269551230360288610015)
    ·
      refine ⟨383532404326845540432915023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255688269551230360288610015 383532404326845540432915023)
      ·
        refine ⟨575298606490268310649372535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383532404326845540432915023 575298606490268310649372535)
        ·
          refine ⟨862947909735402465974058803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 575298606490268310649372535 862947909735402465974058803)
          ·
            refine ⟨1294421864603103698961088205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 862947909735402465974058803 1294421864603103698961088205)
            ·
              refine ⟨485408199226163887110408077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1294421864603103698961088205 485408199226163887110408077)
              ·
                refine ⟨182028074709811457666403029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 485408199226163887110408077 182028074709811457666403029)
                ·
                  refine ⟨4266283001011206039056321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 182028074709811457666403029 4266283001011206039056321)
                  ·
                    refine ⟨3199712250758404529292241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4266283001011206039056321 3199712250758404529292241)
                    ·
                      refine ⟨2399784188068803396969181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3199712250758404529292241 2399784188068803396969181)
                      ·
                        rfl

theorem cell23_4673563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7, 2, 2].length) (baseStart_4673563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673563 prefixEnd_4673563 := by exact prefixLift 4673563
  have htrace : WordTrace (prefixWord ++ tailWord_4673563) baseStart_4673563 baseEnd_4673563 := by
    simpa [prefixWord, tailWord_4673563, baseEnd_4673563] using wordTrace_append hprefix tailTrace_4673563
  have hstable : (prefixWord ++ tailWord_4673563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673563).length < 2 ^ (prefixWord ++ tailWord_4673563).sum := by decide
  have hdescent : baseEnd_4673563 < baseStart_4673563 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673569 : List Nat := [1, 2, 3, 2, 15]
def baseStart_4673569 : Nat := 118140960795 + 4673569 * 2 ^ 59
def prefixEnd_4673569 : Nat := 4983230072969 + 3 ^ 40 * 4673569 * 2
def baseEnd_4673569 : Nat := 3291889257822675409457

theorem tailTrace_4673569 : CollatzResearch.WordTrace tailWord_4673569 prefixEnd_4673569 3291889257822675409457 := by
  unfold tailWord_4673569
  simp only [CollatzResearch.WordTrace]
  refine ⟨170459065205465169883791761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113639376803643446589194507 170459065205465169883791761)
  ·
    refine ⟨127844298904098877412843821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170459065205465169883791761 127844298904098877412843821)
    ·
      refine ⟨47941612089037079029816433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127844298904098877412843821 47941612089037079029816433)
      ·
        refine ⟨35956209066777809272362325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47941612089037079029816433 35956209066777809272362325)
        ·
          refine ⟨3291889257822675409457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 35956209066777809272362325 3291889257822675409457)
          ·
            rfl

theorem cell23_4673569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 15].length) (baseStart_4673569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673569 prefixEnd_4673569 := by exact prefixLift 4673569
  have htrace : WordTrace (prefixWord ++ tailWord_4673569) baseStart_4673569 baseEnd_4673569 := by
    simpa [prefixWord, tailWord_4673569, baseEnd_4673569] using wordTrace_append hprefix tailTrace_4673569
  have hstable : (prefixWord ++ tailWord_4673569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673569).length < 2 ^ (prefixWord ++ tailWord_4673569).sum := by decide
  have hdescent : baseEnd_4673569 < baseStart_4673569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673573 : List Nat := [1, 3, 1, 2, 2, 3, 1, 4, 2, 4]
def baseStart_4673573 : Nat := 118140960795 + 4673573 * 2 ^ 59
def prefixEnd_4673573 : Nat := 4983230072969 + 3 ^ 40 * 4673573 * 2
def baseEnd_4673573 : Nat := 799929774291782785948045

theorem tailTrace_4673573 : CollatzResearch.WordTrace tailWord_4673573 prefixEnd_4673573 799929774291782785948045 := by
  unfold tailWord_4673573
  simp only [CollatzResearch.WordTrace]
  refine ⟨170459211097450678566937373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113639474064967119044624915 170459211097450678566937373)
  ·
    refine ⟨63922204161544004462601515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170459211097450678566937373 63922204161544004462601515)
    ·
      refine ⟨95883306242316006693902273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63922204161544004462601515 95883306242316006693902273)
      ·
        refine ⟨71912479681737005020426705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95883306242316006693902273 71912479681737005020426705)
        ·
          refine ⟨53934359761302753765320029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71912479681737005020426705 53934359761302753765320029)
          ·
            refine ⟨20225384910488532661995011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53934359761302753765320029 20225384910488532661995011)
            ·
              refine ⟨30338077365732798992992517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20225384910488532661995011 30338077365732798992992517)
              ·
                refine ⟨5688389506074899811186097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30338077365732798992992517 5688389506074899811186097)
                ·
                  refine ⟨4266292129556174858389573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5688389506074899811186097 4266292129556174858389573)
                  ·
                    refine ⟨799929774291782785948045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4266292129556174858389573 799929774291782785948045)
                    ·
                      rfl

theorem cell23_4673573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 2, 4].length) (baseStart_4673573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673573 prefixEnd_4673573 := by exact prefixLift 4673573
  have htrace : WordTrace (prefixWord ++ tailWord_4673573) baseStart_4673573 baseEnd_4673573 := by
    simpa [prefixWord, tailWord_4673573, baseEnd_4673573] using wordTrace_append hprefix tailTrace_4673573
  have hstable : (prefixWord ++ tailWord_4673573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673573).length < 2 ^ (prefixWord ++ tailWord_4673573).sum := by decide
  have hdescent : baseEnd_4673573 < baseStart_4673573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673579 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 7]
def baseStart_4673579 : Nat := 118140960795 + 4673579 * 2 ^ 59
def prefixEnd_4673579 : Nat := 4983230072969 + 3 ^ 40 * 4673579 * 2
def baseEnd_4673579 : Nat := 2399792403759275334369107

theorem tailTrace_4673579 : CollatzResearch.WordTrace tailWord_4673579 prefixEnd_4673579 2399792403759275334369107 := by
  unfold tailWord_4673579
  simp only [CollatzResearch.WordTrace]
  refine ⟨170459429935428941591655791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113639619956952627727770527 170459429935428941591655791)
  ·
    refine ⟨255689144903143412387483687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170459429935428941591655791 255689144903143412387483687)
    ·
      refine ⟨383533717354715118581225531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255689144903143412387483687 383533717354715118581225531)
      ·
        refine ⟨575300576032072677871838297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383533717354715118581225531 575300576032072677871838297)
        ·
          refine ⟨431475432024054508403878723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 575300576032072677871838297 431475432024054508403878723)
          ·
            refine ⟨647213148036081762605818085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431475432024054508403878723 647213148036081762605818085)
            ·
              refine ⟨121352465256765330488590891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 647213148036081762605818085 121352465256765330488590891)
              ·
                refine ⟨182028697885147995732886337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121352465256765330488590891 182028697885147995732886337)
                ·
                  refine ⟨136521523413860996799664753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 182028697885147995732886337 136521523413860996799664753)
                  ·
                    refine ⟨102391142560395747599748565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 136521523413860996799664753 102391142560395747599748565)
                    ·
                      refine ⟨2399792403759275334369107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 102391142560395747599748565 2399792403759275334369107)
                      ·
                        rfl

theorem cell23_4673579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 7].length) (baseStart_4673579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673579 prefixEnd_4673579 := by exact prefixLift 4673579
  have htrace : WordTrace (prefixWord ++ tailWord_4673579) baseStart_4673579 baseEnd_4673579 := by
    simpa [prefixWord, tailWord_4673579, baseEnd_4673579] using wordTrace_append hprefix tailTrace_4673579
  have hstable : (prefixWord ++ tailWord_4673579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673579).length < 2 ^ (prefixWord ++ tailWord_4673579).sum := by decide
  have hdescent : baseEnd_4673579 < baseStart_4673579 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673586 : List Nat := [3, 2, 1, 1, 2, 3, 3, 8]
def baseStart_4673586 : Nat := 118140960795 + 4673586 * 2 ^ 59
def prefixEnd_4673586 : Nat := 4983230072969 + 3 ^ 40 * 4673586 * 2
def baseEnd_4673586 : Nat := 88881333263846548406725

theorem tailTrace_4673586 : CollatzResearch.WordTrace tailWord_4673586 prefixEnd_4673586 88881333263846548406725 := by
  unfold tailWord_4673586
  simp only [CollatzResearch.WordTrace]
  refine ⟨42614921311600895446790153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113639790164269054524773741 42614921311600895446790153)
  ·
    refine ⟨31961190983700671585092615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42614921311600895446790153 31961190983700671585092615)
    ·
      refine ⟨47941786475551007377638923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31961190983700671585092615 47941786475551007377638923)
      ·
        refine ⟨71912679713326511066458385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47941786475551007377638923 71912679713326511066458385)
        ·
          refine ⟨53934509784994883299843789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71912679713326511066458385 53934509784994883299843789)
          ·
            refine ⟨20225441169373081237441421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53934509784994883299843789 20225441169373081237441421)
            ·
              refine ⟨7584540438514905464040533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20225441169373081237441421 7584540438514905464040533)
              ·
                refine ⟨88881333263846548406725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7584540438514905464040533 88881333263846548406725)
                ·
                  rfl

theorem cell23_4673586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 8].length) (baseStart_4673586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673586 prefixEnd_4673586 := by exact prefixLift 4673586
  have htrace : WordTrace (prefixWord ++ tailWord_4673586) baseStart_4673586 baseEnd_4673586 := by
    simpa [prefixWord, tailWord_4673586, baseEnd_4673586] using wordTrace_append hprefix tailTrace_4673586
  have hstable : (prefixWord ++ tailWord_4673586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673586).length < 2 ^ (prefixWord ++ tailWord_4673586).sum := by decide
  have hdescent : baseEnd_4673586 < baseStart_4673586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673590 : List Nat := [5, 1, 2, 1, 1, 1, 1, 5, 2, 4]
def baseStart_4673590 : Nat := 118140960795 + 4673590 * 2 ^ 59
def prefixEnd_4673590 : Nat := 4983230072969 + 3 ^ 40 * 4673590 * 2
def baseEnd_4673590 : Nat := 799932684015491597110519

theorem tailTrace_4673590 : CollatzResearch.WordTrace tailWord_4673590 prefixEnd_4673590 799932684015491597110519 := by
  unfold tailWord_4673590
  simp only [CollatzResearch.WordTrace]
  refine ⟨10653739446149318154394139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113639887425592726980204149 10653739446149318154394139)
  ·
    refine ⟨15980609169223977231591209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10653739446149318154394139 15980609169223977231591209)
    ·
      refine ⟨11985456876917982923693407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15980609169223977231591209 11985456876917982923693407)
      ·
        refine ⟨17978185315376974385540111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11985456876917982923693407 17978185315376974385540111)
        ·
          refine ⟨26967277973065461578310167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17978185315376974385540111 26967277973065461578310167)
          ·
            refine ⟨40450916959598192367465251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26967277973065461578310167 40450916959598192367465251)
            ·
              refine ⟨60676375439397288551197877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40450916959598192367465251 60676375439397288551197877)
              ·
                refine ⟨5688410197443495801674801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60676375439397288551197877 5688410197443495801674801)
                ·
                  refine ⟨4266307648082621851256101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5688410197443495801674801 4266307648082621851256101)
                  ·
                    refine ⟨799932684015491597110519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4266307648082621851256101 799932684015491597110519)
                    ·
                      rfl

theorem cell23_4673590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_4673590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673590 prefixEnd_4673590 := by exact prefixLift 4673590
  have htrace : WordTrace (prefixWord ++ tailWord_4673590) baseStart_4673590 baseEnd_4673590 := by
    simpa [prefixWord, tailWord_4673590, baseEnd_4673590] using wordTrace_append hprefix tailTrace_4673590
  have hstable : (prefixWord ++ tailWord_4673590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673590).length < 2 ^ (prefixWord ++ tailWord_4673590).sum := by decide
  have hdescent : baseEnd_4673590 < baseStart_4673590 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673614 : List Nat := [4, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2]
def baseStart_4673614 : Nat := 118140960795 + 4673614 * 2 ^ 59
def prefixEnd_4673614 : Nat := 4983230072969 + 3 ^ 40 * 4673614 * 2
def baseEnd_4673614 : Nat := 2399810375582182697431447

theorem tailTrace_4673614 : CollatzResearch.WordTrace tailWord_4673614 prefixEnd_4673614 2399810375582182697431447 := by
  unfold tailWord_4673614
  simp only [CollatzResearch.WordTrace]
  refine ⟨21307588311287767821147487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113640470993534761712786597 21307588311287767821147487)
  ·
    refine ⟨31961382466931651731721231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21307588311287767821147487 31961382466931651731721231)
    ·
      refine ⟨47942073700397477597581847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31961382466931651731721231 47942073700397477597581847)
      ·
        refine ⟨71913110550596216396372771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47942073700397477597581847 71913110550596216396372771)
        ·
          refine ⟨107869665825894324594559157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71913110550596216396372771 107869665825894324594559157)
          ·
            refine ⟨10112781171177592930739921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 107869665825894324594559157 10112781171177592930739921)
            ·
              refine ⟨7584585878383194698054941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10112781171177592930739921 7584585878383194698054941)
              ·
                refine ⟨2844219704393698011770603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7584585878383194698054941 2844219704393698011770603)
                ·
                  refine ⟨4266329556590547017655905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2844219704393698011770603 4266329556590547017655905)
                  ·
                    refine ⟨3199747167442910263241929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4266329556590547017655905 3199747167442910263241929)
                    ·
                      refine ⟨2399810375582182697431447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3199747167442910263241929 2399810375582182697431447)
                      ·
                        rfl

theorem cell23_4673614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2].length) (baseStart_4673614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673614 prefixEnd_4673614 := by exact prefixLift 4673614
  have htrace : WordTrace (prefixWord ++ tailWord_4673614) baseStart_4673614 baseEnd_4673614 := by
    simpa [prefixWord, tailWord_4673614, baseEnd_4673614] using wordTrace_append hprefix tailTrace_4673614
  have hstable : (prefixWord ++ tailWord_4673614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673614).length < 2 ^ (prefixWord ++ tailWord_4673614).sum := by decide
  have hdescent : baseEnd_4673614 < baseStart_4673614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673636 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 1, 5, 4]
def baseStart_4673636 : Nat := 118140960795 + 4673636 * 2 ^ 59
def prefixEnd_4673636 : Nat := 4983230072969 + 3 ^ 40 * 4673636 * 2
def baseEnd_4673636 : Nat := 2399821672156581611356345

theorem tailTrace_4673636 : CollatzResearch.WordTrace tailWord_4673636 prefixEnd_4673636 2399821672156581611356345 := by
  unfold tailWord_4673636
  simp only [CollatzResearch.WordTrace]
  refine ⟨85230754448111220163240381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113641005930814960217653841 85230754448111220163240381)
  ·
    refine ⟨31961532918041707561215143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85230754448111220163240381 31961532918041707561215143)
    ·
      refine ⟨47942299377062561341822715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31961532918041707561215143 47942299377062561341822715)
      ·
        refine ⟨71913449065593842012734073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47942299377062561341822715 71913449065593842012734073)
        ·
          refine ⟨53935086799195381509550555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71913449065593842012734073 53935086799195381509550555)
          ·
            refine ⟨80902630198793072264325833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53935086799195381509550555 80902630198793072264325833)
            ·
              refine ⟨60676972649094804198244375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80902630198793072264325833 60676972649094804198244375)
              ·
                refine ⟨91015458973642206297366563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60676972649094804198244375 91015458973642206297366563)
                ·
                  refine ⟨136523188460463309446049845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91015458973642206297366563 136523188460463309446049845)
                  ·
                    refine ⟨12799048918168435260567173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 136523188460463309446049845 12799048918168435260567173)
                    ·
                      refine ⟨2399821672156581611356345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12799048918168435260567173 2399821672156581611356345)
                      ·
                        rfl

theorem cell23_4673636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_4673636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673636 prefixEnd_4673636 := by exact prefixLift 4673636
  have htrace : WordTrace (prefixWord ++ tailWord_4673636) baseStart_4673636 baseEnd_4673636 := by
    simpa [prefixWord, tailWord_4673636, baseEnd_4673636] using wordTrace_append hprefix tailTrace_4673636
  have hstable : (prefixWord ++ tailWord_4673636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673636).length < 2 ^ (prefixWord ++ tailWord_4673636).sum := by decide
  have hdescent : baseEnd_4673636 < baseStart_4673636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673647 : List Nat := [1, 1, 2, 1, 3, 5, 3, 1, 2, 1, 3]
def baseStart_4673647 : Nat := 118140960795 + 4673647 * 2 ^ 59
def prefixEnd_4673647 : Nat := 4983230072969 + 3 ^ 40 * 4673647 * 2
def baseEnd_4673647 : Nat := 2399827320443781068318795

theorem tailTrace_4673647 : CollatzResearch.WordTrace tailWord_4673647 prefixEnd_4673647 2399827320443781068318795 := by
  unfold tailWord_4673647
  simp only [CollatzResearch.WordTrace]
  refine ⟨170461910099182589205131195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113641273399455059470087463 170461910099182589205131195)
  ·
    refine ⟨255692865148773883807696793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170461910099182589205131195 255692865148773883807696793)
    ·
      refine ⟨191769648861580412855772595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255692865148773883807696793 191769648861580412855772595)
      ·
        refine ⟨287654473292370619283658893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191769648861580412855772595 287654473292370619283658893)
        ·
          refine ⟨107870427484638982231372085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 287654473292370619283658893 107870427484638982231372085)
          ·
            refine ⟨10112852576684904584191133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 107870427484638982231372085 10112852576684904584191133)
            ·
              refine ⟨3792319716256839219071675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10112852576684904584191133 3792319716256839219071675)
              ·
                refine ⟨5688479574385258828607513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3792319716256839219071675 5688479574385258828607513)
                ·
                  refine ⟨4266359680788944121455635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5688479574385258828607513 4266359680788944121455635)
                  ·
                    refine ⟨6399539521183416182183453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4266359680788944121455635 6399539521183416182183453)
                    ·
                      refine ⟨2399827320443781068318795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6399539521183416182183453 2399827320443781068318795)
                      ·
                        rfl

theorem cell23_4673647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 2, 1, 3].length) (baseStart_4673647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673647 prefixEnd_4673647 := by exact prefixLift 4673647
  have htrace : WordTrace (prefixWord ++ tailWord_4673647) baseStart_4673647 baseEnd_4673647 := by
    simpa [prefixWord, tailWord_4673647, baseEnd_4673647] using wordTrace_append hprefix tailTrace_4673647
  have hstable : (prefixWord ++ tailWord_4673647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673647).length < 2 ^ (prefixWord ++ tailWord_4673647).sum := by decide
  have hdescent : baseEnd_4673647 < baseStart_4673647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673656 : List Nat := [2, 1, 2, 1, 1, 1, 3, 4, 2, 1, 5]
def baseStart_4673656 : Nat := 118140960795 + 4673656 * 2 ^ 59
def prefixEnd_4673656 : Nat := 4983230072969 + 3 ^ 40 * 4673656 * 2
def baseEnd_4673656 : Nat := 2399831941769671533106253

theorem tailTrace_4673656 : CollatzResearch.WordTrace tailWord_4673656 prefixEnd_4673656 2399831941769671533106253 := by
  unfold tailWord_4673656
  simp only [CollatzResearch.WordTrace]
  refine ⟨85231119178074991871104411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113641492237433322494805881 85231119178074991871104411)
  ·
    refine ⟨127846678767112487806656617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85231119178074991871104411 127846678767112487806656617)
    ·
      refine ⟨95885009075334365854992463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127846678767112487806656617 95885009075334365854992463)
      ·
        refine ⟨143827513613001548782488695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95885009075334365854992463 143827513613001548782488695)
        ·
          refine ⟨215741270419502323173733043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143827513613001548782488695 215741270419502323173733043)
          ·
            refine ⟨323611905629253484760599565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215741270419502323173733043 323611905629253484760599565)
            ·
              refine ⟨121354464610970056785224837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 323611905629253484760599565 121354464610970056785224837)
              ·
                refine ⟨22753962114556885647229657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121354464610970056785224837 22753962114556885647229657)
                ·
                  refine ⟨17065471585917664235422243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22753962114556885647229657 17065471585917664235422243)
                  ·
                    refine ⟨25598207378876496353133365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17065471585917664235422243 25598207378876496353133365)
                    ·
                      refine ⟨2399831941769671533106253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25598207378876496353133365 2399831941769671533106253)
                      ·
                        rfl

theorem cell23_4673656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_4673656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673656 prefixEnd_4673656 := by exact prefixLift 4673656
  have htrace : WordTrace (prefixWord ++ tailWord_4673656) baseStart_4673656 baseEnd_4673656 := by
    simpa [prefixWord, tailWord_4673656, baseEnd_4673656] using wordTrace_append hprefix tailTrace_4673656
  have hstable : (prefixWord ++ tailWord_4673656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673656).length < 2 ^ (prefixWord ++ tailWord_4673656).sum := by decide
  have hdescent : baseEnd_4673656 < baseStart_4673656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673657 : List Nat := [1, 2, 1, 3, 4, 2, 2, 2, 1, 3, 2]
def baseStart_4673657 : Nat := 118140960795 + 4673657 * 2 ^ 59
def prefixEnd_4673657 : Nat := 4983230072969 + 3 ^ 40 * 4673657 * 2
def baseEnd_4673657 : Nat := 2399832455250326029193749

theorem tailTrace_4673657 : CollatzResearch.WordTrace tailWord_4673657 prefixEnd_4673657 2399832455250326029193749 := by
  unfold tailWord_4673657
  simp only [CollatzResearch.WordTrace]
  refine ⟨170462274829146360912995225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113641516552764240608663483 170462274829146360912995225)
  ·
    refine ⟨127846706121859770684746419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170462274829146360912995225 127846706121859770684746419)
    ·
      refine ⟨191770059182789656027119629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127846706121859770684746419 191770059182789656027119629)
      ·
        refine ⟨71913772193546121010169861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191770059182789656027119629 71913772193546121010169861)
        ·
          refine ⟨13483832286289897689406849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71913772193546121010169861 13483832286289897689406849)
          ·
            refine ⟨10112874214717423267055137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13483832286289897689406849 10112874214717423267055137)
            ·
              refine ⟨7584655661038067450291353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10112874214717423267055137 7584655661038067450291353)
              ·
                refine ⟨5688491745778550587718515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7584655661038067450291353 5688491745778550587718515)
                ·
                  refine ⟨8532737618667825881577773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5688491745778550587718515 8532737618667825881577773)
                  ·
                    refine ⟨3199776607000434705591665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8532737618667825881577773 3199776607000434705591665)
                    ·
                      refine ⟨2399832455250326029193749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3199776607000434705591665 2399832455250326029193749)
                      ·
                        rfl

theorem cell23_4673657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 3, 2].length) (baseStart_4673657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673657 prefixEnd_4673657 := by exact prefixLift 4673657
  have htrace : WordTrace (prefixWord ++ tailWord_4673657) baseStart_4673657 baseEnd_4673657 := by
    simpa [prefixWord, tailWord_4673657, baseEnd_4673657] using wordTrace_append hprefix tailTrace_4673657
  have hstable : (prefixWord ++ tailWord_4673657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673657).length < 2 ^ (prefixWord ++ tailWord_4673657).sum := by decide
  have hdescent : baseEnd_4673657 < baseStart_4673657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673693 : List Nat := [1, 4, 2, 1, 1, 3, 3, 1, 7]
def baseStart_4673693 : Nat := 118140960795 + 4673693 * 2 ^ 59
def prefixEnd_4673693 : Nat := 4983230072969 + 3 ^ 40 * 4673693 * 2
def baseEnd_4673693 : Nat := 266650104505987543149287

theorem tailTrace_4673693 : CollatzResearch.WordTrace tailWord_4673693 prefixEnd_4673693 266650104505987543149287 := by
  unfold tailWord_4673693
  simp only [CollatzResearch.WordTrace]
  refine ⟨170463587857015939061305733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113642391904677292707537155 170463587857015939061305733)
  ·
    refine ⟨31961922723190488573994825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170463587857015939061305733 31961922723190488573994825)
    ·
      refine ⟨23971442042392866430496119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31961922723190488573994825 23971442042392866430496119)
      ·
        refine ⟨35957163063589299645744179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23971442042392866430496119 35957163063589299645744179)
        ·
          refine ⟨53935744595383949468616269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35957163063589299645744179 53935744595383949468616269)
          ·
            refine ⟨20225904223268981050731101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53935744595383949468616269 20225904223268981050731101)
            ·
              refine ⟨7584714083725867894024163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20225904223268981050731101 7584714083725867894024163)
              ·
                refine ⟨11377071125588801841036245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7584714083725867894024163 11377071125588801841036245)
                ·
                  refine ⟨266650104505987543149287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11377071125588801841036245 266650104505987543149287)
                  ·
                    rfl

theorem cell23_4673693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 7].length) (baseStart_4673693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673693 prefixEnd_4673693 := by exact prefixLift 4673693
  have htrace : WordTrace (prefixWord ++ tailWord_4673693) baseStart_4673693 baseEnd_4673693 := by
    simpa [prefixWord, tailWord_4673693, baseEnd_4673693] using wordTrace_append hprefix tailTrace_4673693
  have hstable : (prefixWord ++ tailWord_4673693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673693).length < 2 ^ (prefixWord ++ tailWord_4673693).sum := by decide
  have hdescent : baseEnd_4673693 < baseStart_4673693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673723 : List Nat := [1, 1, 1, 1, 1, 2, 8, 1, 2, 5]
def baseStart_4673723 : Nat := 118140960795 + 4673723 * 2 ^ 59
def prefixEnd_4673723 : Nat := 4983230072969 + 3 ^ 40 * 4673723 * 2
def baseEnd_4673723 : Nat := 799955448324507590322815

theorem tailTrace_4673723 : CollatzResearch.WordTrace tailWord_4673723 prefixEnd_4673723 799955448324507590322815 := by
  unfold tailWord_4673723
  simp only [CollatzResearch.WordTrace]
  refine ⟨170464682046907254184897823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113643121364604836123265215 170464682046907254184897823)
  ·
    refine ⟨255697023070360881277346735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170464682046907254184897823 255697023070360881277346735)
    ·
      refine ⟨383545534605541321916020103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255697023070360881277346735 383545534605541321916020103)
      ·
        refine ⟨575318301908311982874030155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383545534605541321916020103 575318301908311982874030155)
        ·
          refine ⟨862977452862467974311045233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 575318301908311982874030155 862977452862467974311045233)
          ·
            refine ⟨647233089646850980733283925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 862977452862467974311045233 647233089646850980733283925)
            ·
              refine ⟨7584762769299034930468171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 647233089646850980733283925 7584762769299034930468171)
              ·
                refine ⟨11377144153948552395702257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7584762769299034930468171 11377144153948552395702257)
                ·
                  refine ⟨8532858115461414296776693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11377144153948552395702257 8532858115461414296776693)
                  ·
                    refine ⟨799955448324507590322815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8532858115461414296776693 799955448324507590322815)
                    ·
                      rfl

theorem cell23_4673723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 5].length) (baseStart_4673723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673723 prefixEnd_4673723 := by exact prefixLift 4673723
  have htrace : WordTrace (prefixWord ++ tailWord_4673723) baseStart_4673723 baseEnd_4673723 := by
    simpa [prefixWord, tailWord_4673723, baseEnd_4673723] using wordTrace_append hprefix tailTrace_4673723
  have hstable : (prefixWord ++ tailWord_4673723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673723).length < 2 ^ (prefixWord ++ tailWord_4673723).sum := by decide
  have hdescent : baseEnd_4673723 < baseStart_4673723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673743 : List Nat := [1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 4]
def baseStart_4673743 : Nat := 118140960795 + 4673743 * 2 ^ 59
def prefixEnd_4673743 : Nat := 4983230072969 + 3 ^ 40 * 4673743 * 2
def baseEnd_4673743 : Nat := 2399876614586612692718353

theorem tailTrace_4673743 : CollatzResearch.WordTrace tailWord_4673743 prefixEnd_4673743 2399876614586612692718353 := by
  unfold tailWord_4673743
  simp only [CollatzResearch.WordTrace]
  refine ⟨170465411506834797600625883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113643607671223198400417255 170465411506834797600625883)
  ·
    refine ⟨255698117260252196400938825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170465411506834797600625883 255698117260252196400938825)
    ·
      refine ⟨191773587945189147300704119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255698117260252196400938825 191773587945189147300704119)
      ·
        refine ⟨287660381917783720951056179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191773587945189147300704119 287660381917783720951056179)
        ·
          refine ⟨431490572876675581426584269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287660381917783720951056179 431490572876675581426584269)
          ·
            refine ⟨161808964828753343034969101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 431490572876675581426584269 161808964828753343034969101)
            ·
              refine ⟨60678361810782503638113413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161808964828753343034969101 60678361810782503638113413)
              ·
                refine ⟨11377192839521719432146265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60678361810782503638113413 11377192839521719432146265)
                ·
                  refine ⟨8532894629641289574109699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11377192839521719432146265 8532894629641289574109699)
                  ·
                    refine ⟨12799341944461934361164549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8532894629641289574109699 12799341944461934361164549)
                    ·
                      refine ⟨2399876614586612692718353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12799341944461934361164549 2399876614586612692718353)
                      ·
                        rfl

theorem cell23_4673743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 4].length) (baseStart_4673743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673743 prefixEnd_4673743 := by exact prefixLift 4673743
  have htrace : WordTrace (prefixWord ++ tailWord_4673743) baseStart_4673743 baseEnd_4673743 := by
    simpa [prefixWord, tailWord_4673743, baseEnd_4673743] using wordTrace_append hprefix tailTrace_4673743
  have hstable : (prefixWord ++ tailWord_4673743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673743).length < 2 ^ (prefixWord ++ tailWord_4673743).sum := by decide
  have hdescent : baseEnd_4673743 < baseStart_4673743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673760 : List Nat := [2, 1, 1, 3, 1, 3, 3, 1, 2, 4, 2]
def baseStart_4673760 : Nat := 118140960795 + 4673760 * 2 ^ 59
def prefixEnd_4673760 : Nat := 4983230072969 + 3 ^ 40 * 4673760 * 2
def baseEnd_4673760 : Nat := 2399885343757739126205775

theorem tailTrace_4673760 : CollatzResearch.WordTrace tailWord_4673760 prefixEnd_4673760 2399885343757739126205775 := by
  unfold tailWord_4673760
  simp only [CollatzResearch.WordTrace]
  refine ⟨85233015773886604751997367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113644021031848806335996489 85233015773886604751997367)
  ·
    refine ⟨127849523660829907127996051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85233015773886604751997367 127849523660829907127996051)
    ·
      refine ⟨191774285491244860691994077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127849523660829907127996051 191774285491244860691994077)
      ·
        refine ⟨71915357059216822759497779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191774285491244860691994077 71915357059216822759497779)
        ·
          refine ⟨107873035588825234139246669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71915357059216822759497779 107873035588825234139246669)
          ·
            refine ⟨40452388345809462802217501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107873035588825234139246669 40452388345809462802217501)
            ·
              refine ⟨15169645629678548550831563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40452388345809462802217501 15169645629678548550831563)
              ·
                refine ⟨22754468444517822826247345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15169645629678548550831563 22754468444517822826247345)
                ·
                  refine ⟨17065851333388367119685509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22754468444517822826247345 17065851333388367119685509)
                  ·
                    refine ⟨3199847125010318834941033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17065851333388367119685509 3199847125010318834941033)
                    ·
                      refine ⟨2399885343757739126205775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3199847125010318834941033 2399885343757739126205775)
                      ·
                        rfl

theorem cell23_4673760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 2, 4, 2].length) (baseStart_4673760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673760 prefixEnd_4673760 := by exact prefixLift 4673760
  have htrace : WordTrace (prefixWord ++ tailWord_4673760) baseStart_4673760 baseEnd_4673760 := by
    simpa [prefixWord, tailWord_4673760, baseEnd_4673760] using wordTrace_append hprefix tailTrace_4673760
  have hstable : (prefixWord ++ tailWord_4673760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673760).length < 2 ^ (prefixWord ++ tailWord_4673760).sum := by decide
  have hdescent : baseEnd_4673760 < baseStart_4673760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673770 : List Nat := [3, 1, 3, 1, 1, 2, 3, 2, 3, 4]
def baseStart_4673770 : Nat := 118140960795 + 4673770 * 2 ^ 59
def prefixEnd_4673770 : Nat := 4983230072969 + 3 ^ 40 * 4673770 * 2
def baseEnd_4673770 : Nat := 799963492854761362360243

theorem tailTrace_4673770 : CollatzResearch.WordTrace tailWord_4673770 prefixEnd_4673770 799963492854761362360243 := by
  unfold tailWord_4673770
  simp only [CollatzResearch.WordTrace]
  refine ⟨42616599069434245302964691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113644264185157987474572509 42616599069434245302964691)
  ·
    refine ⟨63924898604151367954447037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42616599069434245302964691 63924898604151367954447037)
    ·
      refine ⟨23971836976556762982917639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63924898604151367954447037 23971836976556762982917639)
      ·
        refine ⟨35957755464835144474376459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23971836976556762982917639 35957755464835144474376459)
        ·
          refine ⟨53936633197252716711564689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35957755464835144474376459 53936633197252716711564689)
          ·
            refine ⟨40452474897939537533673517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53936633197252716711564689 40452474897939537533673517)
            ·
              refine ⟨15169678086727326575127569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40452474897939537533673517 15169678086727326575127569)
              ·
                refine ⟨11377258565045494931345677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15169678086727326575127569 11377258565045494931345677)
                ·
                  refine ⟨4266471961892060599254629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11377258565045494931345677 4266471961892060599254629)
                  ·
                    refine ⟨799963492854761362360243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4266471961892060599254629 799963492854761362360243)
                    ·
                      rfl

theorem cell23_4673770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_4673770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673770 prefixEnd_4673770 := by exact prefixLift 4673770
  have htrace : WordTrace (prefixWord ++ tailWord_4673770) baseStart_4673770 baseEnd_4673770 := by
    simpa [prefixWord, tailWord_4673770, baseEnd_4673770] using wordTrace_append hprefix tailTrace_4673770
  have hstable : (prefixWord ++ tailWord_4673770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673770).length < 2 ^ (prefixWord ++ tailWord_4673770).sum := by decide
  have hdescent : baseEnd_4673770 < baseStart_4673770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673800 : List Nat := [2, 1, 3, 2, 3, 1, 3, 2, 6]
def baseStart_4673800 : Nat := 118140960795 + 4673800 * 2 ^ 59
def prefixEnd_4673800 : Nat := 4983230072969 + 3 ^ 40 * 4673800 * 2
def baseEnd_4673800 : Nat := 266656209220435441078399

theorem tailTrace_4673800 : CollatzResearch.WordTrace tailWord_4673800 prefixEnd_4673800 266656209220435441078399 := by
  unfold tailWord_4673800
  simp only [CollatzResearch.WordTrace]
  refine ⟨85233745233814148167725427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113644993645085530890300569 85233745233814148167725427)
  ·
    refine ⟨127850617850721222251588141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85233745233814148167725427 127850617850721222251588141)
    ·
      refine ⟨47943981694020458344345553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127850617850721222251588141 47943981694020458344345553)
      ·
        refine ⟨35957986270515343758259165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47943981694020458344345553 35957986270515343758259165)
        ·
          refine ⟨13484244851443253909347187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35957986270515343758259165 13484244851443253909347187)
          ·
            refine ⟨20226367277164880864020781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13484244851443253909347187 20226367277164880864020781)
            ·
              refine ⟨7584887728936830324007793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20226367277164880864020781 7584887728936830324007793)
              ·
                refine ⟨5688665796702622743005845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7584887728936830324007793 5688665796702622743005845)
                ·
                  refine ⟨266656209220435441078399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5688665796702622743005845 266656209220435441078399)
                  ·
                    rfl

theorem cell23_4673800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 6].length) (baseStart_4673800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673800 prefixEnd_4673800 := by exact prefixLift 4673800
  have htrace : WordTrace (prefixWord ++ tailWord_4673800) baseStart_4673800 baseEnd_4673800 := by
    simpa [prefixWord, tailWord_4673800, baseEnd_4673800] using wordTrace_append hprefix tailTrace_4673800
  have hstable : (prefixWord ++ tailWord_4673800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673800).length < 2 ^ (prefixWord ++ tailWord_4673800).sum := by decide
  have hdescent : baseEnd_4673800 < baseStart_4673800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673813 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 5, 5]
def baseStart_4673813 : Nat := 118140960795 + 4673813 * 2 ^ 59
def prefixEnd_4673813 : Nat := 4983230072969 + 3 ^ 40 * 4673813 * 2
def baseEnd_4673813 : Nat := 799970852744142472947677

theorem tailTrace_4673813 : CollatzResearch.WordTrace tailWord_4673813 prefixEnd_4673813 799970852744142472947677 := by
  unfold tailWord_4673813
  simp only [CollatzResearch.WordTrace]
  refine ⟨170467964616581199555674093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113645309744387466370449395 170467964616581199555674093)
  ·
    refine ⟨63925486731217949833377785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170467964616581199555674093 63925486731217949833377785)
    ·
      refine ⟨47944115048413462375033339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63925486731217949833377785 47944115048413462375033339)
      ·
        refine ⟨71916172572620193562550009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47944115048413462375033339 71916172572620193562550009)
        ·
          refine ⟨53937129429465145171912507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71916172572620193562550009 53937129429465145171912507)
          ·
            refine ⟨80905694144197717757868761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53937129429465145171912507 80905694144197717757868761)
            ·
              refine ⟨60679270608148288318401571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80905694144197717757868761 60679270608148288318401571)
              ·
                refine ⟨91018905912222432477602357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60679270608148288318401571 91018905912222432477602357)
                ·
                  refine ⟨8533022429270853044775221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 91018905912222432477602357 8533022429270853044775221)
                  ·
                    refine ⟨799970852744142472947677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8533022429270853044775221 799970852744142472947677)
                    ·
                      rfl

theorem cell23_4673813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_4673813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673813 prefixEnd_4673813 := by exact prefixLift 4673813
  have htrace : WordTrace (prefixWord ++ tailWord_4673813) baseStart_4673813 baseEnd_4673813 := by
    simpa [prefixWord, tailWord_4673813, baseEnd_4673813] using wordTrace_append hprefix tailTrace_4673813
  have hstable : (prefixWord ++ tailWord_4673813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673813).length < 2 ^ (prefixWord ++ tailWord_4673813).sum := by decide
  have hdescent : baseEnd_4673813 < baseStart_4673813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673838 : List Nat := [4, 1, 3, 3, 1, 2, 1, 3, 1, 4]
def baseStart_4673838 : Nat := 118140960795 + 4673838 * 2 ^ 59
def prefixEnd_4673838 : Nat := 4983230072969 + 3 ^ 40 * 4673838 * 2
def baseEnd_4673838 : Nat := 799975131749596607010139

theorem tailTrace_4673838 : CollatzResearch.WordTrace tailWord_4673838 prefixEnd_4673838 799975131749596607010139 := by
  unfold tailWord_4673838
  simp only [CollatzResearch.WordTrace]
  refine ⟨21308609555186328603166771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113645917627660419216889445 21308609555186328603166771)
  ·
    refine ⟨31962914332779492904750157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21308609555186328603166771 31962914332779492904750157)
    ·
      refine ⟨11986092874792309839281309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31962914332779492904750157 11986092874792309839281309)
      ·
        refine ⟨4494784828047116189730491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11986092874792309839281309 4494784828047116189730491)
        ·
          refine ⟨6742177242070674284595737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4494784828047116189730491 6742177242070674284595737)
          ·
            refine ⟨5056632931553005713446803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6742177242070674284595737 5056632931553005713446803)
            ·
              refine ⟨7584949397329508570170205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5056632931553005713446803 7584949397329508570170205)
              ·
                refine ⟨2844356023998565713813827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7584949397329508570170205 2844356023998565713813827)
                ·
                  refine ⟨4266534035997848570720741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2844356023998565713813827 4266534035997848570720741)
                  ·
                    refine ⟨799975131749596607010139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4266534035997848570720741 799975131749596607010139)
                    ·
                      rfl

theorem cell23_4673838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_4673838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673838 prefixEnd_4673838 := by exact prefixLift 4673838
  have htrace : WordTrace (prefixWord ++ tailWord_4673838) baseStart_4673838 baseEnd_4673838 := by
    simpa [prefixWord, tailWord_4673838, baseEnd_4673838] using wordTrace_append hprefix tailTrace_4673838
  have hstable : (prefixWord ++ tailWord_4673838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673838).length < 2 ^ (prefixWord ++ tailWord_4673838).sum := by decide
  have hdescent : baseEnd_4673838 < baseStart_4673838 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673843 : List Nat := [1, 1, 1, 2, 5, 1, 2, 1, 3, 6]
def baseStart_4673843 : Nat := 118140960795 + 4673843 * 2 ^ 59
def prefixEnd_4673843 : Nat := 4983230072969 + 3 ^ 40 * 4673843 * 2
def baseEnd_4673843 : Nat := 799975987550687433822631

theorem tailTrace_4673843 : CollatzResearch.WordTrace tailWord_4673843 prefixEnd_4673843 799975987550687433822631 := by
  unfold tailWord_4673843
  simp only [CollatzResearch.WordTrace]
  refine ⟨170469058806472514679266183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113646039204315009786177455 170469058806472514679266183)
  ·
    refine ⟨255703588209708772018899275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170469058806472514679266183 255703588209708772018899275)
    ·
      refine ⟨383555382314563158028348913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255703588209708772018899275 383555382314563158028348913)
      ·
        refine ⟨287666536735922368521261685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 383555382314563158028348913 287666536735922368521261685)
        ·
          refine ⟨26968737818992722048868283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 287666536735922368521261685 26968737818992722048868283)
          ·
            refine ⟨40453106728489083073302425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26968737818992722048868283 40453106728489083073302425)
            ·
              refine ⟨30339830046366812304976819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40453106728489083073302425 30339830046366812304976819)
              ·
                refine ⟨45509745069550218457465229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30339830046366812304976819 45509745069550218457465229)
                ·
                  refine ⟨17066154401081331921549461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45509745069550218457465229 17066154401081331921549461)
                  ·
                    refine ⟨799975987550687433822631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17066154401081331921549461 799975987550687433822631)
                    ·
                      rfl

theorem cell23_4673843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 6].length) (baseStart_4673843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673843 prefixEnd_4673843 := by exact prefixLift 4673843
  have htrace : WordTrace (prefixWord ++ tailWord_4673843) baseStart_4673843 baseEnd_4673843 := by
    simpa [prefixWord, tailWord_4673843, baseEnd_4673843] using wordTrace_append hprefix tailTrace_4673843
  have hstable : (prefixWord ++ tailWord_4673843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673843).length < 2 ^ (prefixWord ++ tailWord_4673843).sum := by decide
  have hdescent : baseEnd_4673843 < baseStart_4673843 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673854 : List Nat := [4, 2, 1, 2, 1, 3, 1, 2, 2, 3, 2]
def baseStart_4673854 : Nat := 118140960795 + 4673854 * 2 ^ 59
def prefixEnd_4673854 : Nat := 4983230072969 + 3 ^ 40 * 4673854 * 2
def baseEnd_4673854 : Nat := 2399933610939261758430343

theorem tailTrace_4673854 : CollatzResearch.WordTrace tailWord_4673854 prefixEnd_4673854 2399933610939261758430343 := by
  unfold tailWord_4673854
  simp only [CollatzResearch.WordTrace]
  refine ⟨21308682501179082944739577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113646306672955109038611077 21308682501179082944739577)
  ·
    refine ⟨15981511875884312208554683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21308682501179082944739577 15981511875884312208554683)
    ·
      refine ⟨23972267813826468312832025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15981511875884312208554683 23972267813826468312832025)
      ·
        refine ⟨17979200860369851234624019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23972267813826468312832025 17979200860369851234624019)
        ·
          refine ⟨26968801290554776851936029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17979200860369851234624019 26968801290554776851936029)
          ·
            refine ⟨10113300483958041319476011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26968801290554776851936029 10113300483958041319476011)
            ·
              refine ⟨15169950725937061979214017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10113300483958041319476011 15169950725937061979214017)
              ·
                refine ⟨11377463044452796484410513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15169950725937061979214017 11377463044452796484410513)
                ·
                  refine ⟨8533097283339597363307885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11377463044452796484410513 8533097283339597363307885)
                  ·
                    refine ⟨3199911481252349011240457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8533097283339597363307885 3199911481252349011240457)
                    ·
                      refine ⟨2399933610939261758430343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3199911481252349011240457 2399933610939261758430343)
                      ·
                        rfl

theorem cell23_4673854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_4673854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673854 prefixEnd_4673854 := by exact prefixLift 4673854
  have htrace : WordTrace (prefixWord ++ tailWord_4673854) baseStart_4673854 baseEnd_4673854 := by
    simpa [prefixWord, tailWord_4673854, baseEnd_4673854] using wordTrace_append hprefix tailTrace_4673854
  have hstable : (prefixWord ++ tailWord_4673854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673854).length < 2 ^ (prefixWord ++ tailWord_4673854).sum := by decide
  have hdescent : baseEnd_4673854 < baseStart_4673854 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673863 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 6]
def baseStart_4673863 : Nat := 118140960795 + 4673863 * 2 ^ 59
def prefixEnd_4673863 : Nat := 4983230072969 + 3 ^ 40 * 4673863 * 2
def baseEnd_4673863 : Nat := 2399938232265152223217801

theorem tailTrace_4673863 : CollatzResearch.WordTrace tailWord_4673863 prefixEnd_4673863 2399938232265152223217801 := by
  unfold tailWord_4673863
  simp only [CollatzResearch.WordTrace]
  refine ⟨170469788266400058094994243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113646525510933372063329495 170469788266400058094994243)
  ·
    refine ⟨255704682399600087142491365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170469788266400058094994243 255704682399600087142491365)
    ·
      refine ⟨47944627949925016339217131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 255704682399600087142491365 47944627949925016339217131)
      ·
        refine ⟨71916941924887524508825697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47944627949925016339217131 71916941924887524508825697)
        ·
          refine ⟨53937706443665643381619273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71916941924887524508825697 53937706443665643381619273)
          ·
            refine ⟨40453279832749232536214455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53937706443665643381619273 40453279832749232536214455)
            ·
              refine ⟨60679919749123848804321683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40453279832749232536214455 60679919749123848804321683)
              ·
                refine ⟨91019879623685773206482525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60679919749123848804321683 91019879623685773206482525)
                ·
                  refine ⟨34132454858882164952430947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91019879623685773206482525 34132454858882164952430947)
                  ·
                    refine ⟨51198682288323247428646421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34132454858882164952430947 51198682288323247428646421)
                    ·
                      refine ⟨2399938232265152223217801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51198682288323247428646421 2399938232265152223217801)
                      ·
                        rfl

theorem cell23_4673863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_4673863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673863 prefixEnd_4673863 := by exact prefixLift 4673863
  have htrace : WordTrace (prefixWord ++ tailWord_4673863) baseStart_4673863 baseEnd_4673863 := by
    simpa [prefixWord, tailWord_4673863, baseEnd_4673863] using wordTrace_append hprefix tailTrace_4673863
  have hstable : (prefixWord ++ tailWord_4673863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673863).length < 2 ^ (prefixWord ++ tailWord_4673863).sum := by decide
  have hdescent : baseEnd_4673863 < baseStart_4673863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673867 : List Nat := [1, 1, 1, 1, 3, 1, 1, 7, 3, 2, 2]
def baseStart_4673867 : Nat := 118140960795 + 4673867 * 2 ^ 59
def prefixEnd_4673867 : Nat := 4983230072969 + 3 ^ 40 * 4673867 * 2
def baseEnd_4673867 : Nat := 2399940286187770207567783

theorem tailTrace_4673867 : CollatzResearch.WordTrace tailWord_4673867 prefixEnd_4673867 2399940286187770207567783 := by
  unfold tailWord_4673867
  simp only [CollatzResearch.WordTrace]
  refine ⟨170469934158385566778139855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113646622772257044518759903 170469934158385566778139855)
  ·
    refine ⟨255704901237578350167209783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170469934158385566778139855 255704901237578350167209783)
    ·
      refine ⟨383557351856367525250814675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255704901237578350167209783 383557351856367525250814675)
      ·
        refine ⟨575336027784551287876222013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383557351856367525250814675 575336027784551287876222013)
        ·
          refine ⟨215751010419206732953583255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 575336027784551287876222013 215751010419206732953583255)
          ·
            refine ⟨323626515628810099430374883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215751010419206732953583255 323626515628810099430374883)
            ·
              refine ⟨485439773443215149145562325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323626515628810099430374883 485439773443215149145562325)
              ·
                refine ⟨11377494690075355058099117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 485439773443215149145562325 11377494690075355058099117)
                ·
                  refine ⟨4266560508778258146787169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11377494690075355058099117 4266560508778258146787169)
                  ·
                    refine ⟨3199920381583693610090377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4266560508778258146787169 3199920381583693610090377)
                    ·
                      refine ⟨2399940286187770207567783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3199920381583693610090377 2399940286187770207567783)
                      ·
                        rfl

theorem cell23_4673867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 3, 2, 2].length) (baseStart_4673867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673867 prefixEnd_4673867 := by exact prefixLift 4673867
  have htrace : WordTrace (prefixWord ++ tailWord_4673867) baseStart_4673867 baseEnd_4673867 := by
    simpa [prefixWord, tailWord_4673867, baseEnd_4673867] using wordTrace_append hprefix tailTrace_4673867
  have hstable : (prefixWord ++ tailWord_4673867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673867).length < 2 ^ (prefixWord ++ tailWord_4673867).sum := by decide
  have hdescent : baseEnd_4673867 < baseStart_4673867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673873 : List Nat := [1, 2, 2, 1, 4, 2, 1, 10]
def baseStart_4673873 : Nat := 118140960795 + 4673873 * 2 ^ 59
def prefixEnd_4673873 : Nat := 4983230072969 + 3 ^ 40 * 4673873 * 2
def baseEnd_4673873 : Nat := 88886791373025821633065

theorem tailTrace_4673873 : CollatzResearch.WordTrace tailWord_4673873 prefixEnd_4673873 88886791373025821633065 := by
  unfold tailWord_4673873
  simp only [CollatzResearch.WordTrace]
  refine ⟨170470152996363829802858273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113646768664242553201905515 170470152996363829802858273)
  ·
    refine ⟨127852614747272872352143705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170470152996363829802858273 127852614747272872352143705)
    ·
      refine ⟨95889461060454654264107779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127852614747272872352143705 95889461060454654264107779)
      ·
        refine ⟨143834191590681981396161669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95889461060454654264107779 143834191590681981396161669)
        ·
          refine ⟨26968910923252871511780313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143834191590681981396161669 26968910923252871511780313)
          ·
            refine ⟨20226683192439653633835235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26968910923252871511780313 20226683192439653633835235)
            ·
              refine ⟨30340024788659480450752853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20226683192439653633835235 30340024788659480450752853)
              ·
                refine ⟨88886791373025821633065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 30340024788659480450752853 88886791373025821633065)
                ·
                  rfl

theorem cell23_4673873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 10].length) (baseStart_4673873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673873 prefixEnd_4673873 := by exact prefixLift 4673873
  have htrace : WordTrace (prefixWord ++ tailWord_4673873) baseStart_4673873 baseEnd_4673873 := by
    simpa [prefixWord, tailWord_4673873, baseEnd_4673873] using wordTrace_append hprefix tailTrace_4673873
  have hstable : (prefixWord ++ tailWord_4673873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673873).length < 2 ^ (prefixWord ++ tailWord_4673873).sum := by decide
  have hdescent : baseEnd_4673873 < baseStart_4673873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673884 : List Nat := [2, 2, 4, 3, 1, 1, 1, 1, 3, 1, 4]
def baseStart_4673884 : Nat := 118140960795 + 4673884 * 2 ^ 59
def prefixEnd_4673884 : Nat := 4983230072969 + 3 ^ 40 * 4673884 * 2
def baseEnd_4673884 : Nat := 2399949015358896641055205

theorem tailTrace_4673884 : CollatzResearch.WordTrace tailWord_4673884 prefixEnd_4673884 2399949015358896641055205 := by
  unfold tailWord_4673884
  simp only [CollatzResearch.WordTrace]
  refine ⟨85235277099661989340754353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113647036132882652454339137 85235277099661989340754353)
  ·
    refine ⟨63926457824746492005565765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85235277099661989340754353 63926457824746492005565765)
    ·
      refine ⟨11986210842139967251043581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63926457824746492005565765 11986210842139967251043581)
      ·
        refine ⟨4494829065802487719141343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11986210842139967251043581 4494829065802487719141343)
        ·
          refine ⟨6742243598703731578712015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4494829065802487719141343 6742243598703731578712015)
          ·
            refine ⟨10113365398055597368068023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6742243598703731578712015 10113365398055597368068023)
            ·
              refine ⟨15170048097083396052102035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10113365398055597368068023 15170048097083396052102035)
              ·
                refine ⟨22755072145625094078153053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15170048097083396052102035 22755072145625094078153053)
                ·
                  refine ⟨8533152054609410279307395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22755072145625094078153053 8533152054609410279307395)
                  ·
                    refine ⟨12799728081914115418961093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8533152054609410279307395 12799728081914115418961093)
                    ·
                      refine ⟨2399949015358896641055205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12799728081914115418961093 2399949015358896641055205)
                      ·
                        rfl

theorem cell23_4673884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_4673884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673884 prefixEnd_4673884 := by exact prefixLift 4673884
  have htrace : WordTrace (prefixWord ++ tailWord_4673884) baseStart_4673884 baseEnd_4673884 := by
    simpa [prefixWord, tailWord_4673884, baseEnd_4673884] using wordTrace_append hprefix tailTrace_4673884
  have hstable : (prefixWord ++ tailWord_4673884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673884).length < 2 ^ (prefixWord ++ tailWord_4673884).sum := by decide
  have hdescent : baseEnd_4673884 < baseStart_4673884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673887 : List Nat := [1, 1, 2, 3, 1, 2, 5, 2, 1, 2, 3]
def baseStart_4673887 : Nat := 118140960795 + 4673887 * 2 ^ 59
def prefixEnd_4673887 : Nat := 4983230072969 + 3 ^ 40 * 4673887 * 2
def baseEnd_4673887 : Nat := 2399950555800860129317691

theorem tailTrace_4673887 : CollatzResearch.WordTrace tailWord_4673887 prefixEnd_4673887 2399950555800860129317691 := by
  unfold tailWord_4673887
  simp only [CollatzResearch.WordTrace]
  refine ⟨170470663618313110193867915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113647109078875406795911943 170470663618313110193867915)
  ·
    refine ⟨255705995427469665290801873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170470663618313110193867915 255705995427469665290801873)
    ·
      refine ⟨191779496570602248968101405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255705995427469665290801873 191779496570602248968101405)
      ·
        refine ⟨71917311213975843363038027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191779496570602248968101405 71917311213975843363038027)
        ·
          refine ⟨107875966820963765044557041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71917311213975843363038027 107875966820963765044557041)
          ·
            refine ⟨80906975115722823783417781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107875966820963765044557041 80906975115722823783417781)
            ·
              refine ⟨7585028917099014729695417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80906975115722823783417781 7585028917099014729695417)
              ·
                refine ⟨5688771687824261047271563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7585028917099014729695417 5688771687824261047271563)
                ·
                  refine ⟨8533157531736391570907345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5688771687824261047271563 8533157531736391570907345)
                  ·
                    refine ⟨6399868148802293678180509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8533157531736391570907345 6399868148802293678180509)
                    ·
                      refine ⟨2399950555800860129317691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6399868148802293678180509 2399950555800860129317691)
                      ·
                        rfl

theorem cell23_4673887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 2, 3].length) (baseStart_4673887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673887 prefixEnd_4673887 := by exact prefixLift 4673887
  have htrace : WordTrace (prefixWord ++ tailWord_4673887) baseStart_4673887 baseEnd_4673887 := by
    simpa [prefixWord, tailWord_4673887, baseEnd_4673887] using wordTrace_append hprefix tailTrace_4673887
  have hstable : (prefixWord ++ tailWord_4673887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673887).length < 2 ^ (prefixWord ++ tailWord_4673887).sum := by decide
  have hdescent : baseEnd_4673887 < baseStart_4673887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673890 : List Nat := [3, 3, 2, 1, 1, 2, 2, 9]
def baseStart_4673890 : Nat := 118140960795 + 4673890 * 2 ^ 59
def prefixEnd_4673890 : Nat := 4983230072969 + 3 ^ 40 * 4673890 * 2
def baseEnd_4673890 : Nat := 88887114675660133984451

theorem tailTrace_4673890 : CollatzResearch.WordTrace tailWord_4673890 prefixEnd_4673890 88887114675660133984451 := by
  unfold tailWord_4673890
  simp only [CollatzResearch.WordTrace]
  refine ⟨42617693259325560426556781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113647182024868161137484749 42617693259325560426556781)
  ·
    refine ⟨15981634972247085159958793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42617693259325560426556781 15981634972247085159958793)
    ·
      refine ⟨11986226229185313869969095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15981634972247085159958793 11986226229185313869969095)
      ·
        refine ⟨17979339343777970804953643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11986226229185313869969095 17979339343777970804953643)
        ·
          refine ⟨26969009015666956207430465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17979339343777970804953643 26969009015666956207430465)
          ·
            refine ⟨20226756761750217155572849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26969009015666956207430465 20226756761750217155572849)
            ·
              refine ⟨15170067571312662866679637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20226756761750217155572849 15170067571312662866679637)
              ·
                refine ⟨88887114675660133984451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15170067571312662866679637 88887114675660133984451)
                ·
                  rfl

theorem cell23_4673890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 9].length) (baseStart_4673890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673890 prefixEnd_4673890 := by exact prefixLift 4673890
  have htrace : WordTrace (prefixWord ++ tailWord_4673890) baseStart_4673890 baseEnd_4673890 := by
    simpa [prefixWord, tailWord_4673890, baseEnd_4673890] using wordTrace_append hprefix tailTrace_4673890
  have hstable : (prefixWord ++ tailWord_4673890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673890).length < 2 ^ (prefixWord ++ tailWord_4673890).sum := by decide
  have hdescent : baseEnd_4673890 < baseStart_4673890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673901 : List Nat := [1, 5, 1, 1, 1, 2, 2, 5, 1, 2, 2]
def baseStart_4673901 : Nat := 118140960795 + 4673901 * 2 ^ 59
def prefixEnd_4673901 : Nat := 4983230072969 + 3 ^ 40 * 4673901 * 2
def baseEnd_4673901 : Nat := 2399957744530023074542627

theorem tailTrace_4673901 : CollatzResearch.WordTrace tailWord_4673901 prefixEnd_4673901 2399957744530023074542627 := by
  unfold tailWord_4673901
  simp only [CollatzResearch.WordTrace]
  refine ⟨170471174240262390584877557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113647449493508260389918371 170471174240262390584877557)
  ·
    refine ⟨15981672585024599117332271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 170471174240262390584877557 15981672585024599117332271)
    ·
      refine ⟨23972508877536898675998407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15981672585024599117332271 23972508877536898675998407)
      ·
        refine ⟨35958763316305348013997611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23972508877536898675998407 35958763316305348013997611)
        ·
          refine ⟨53938144974458022020996417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35958763316305348013997611 53938144974458022020996417)
          ·
            refine ⟨40453608730843516515747313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53938144974458022020996417 40453608730843516515747313)
            ·
              refine ⟨30340206548132637386810485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40453608730843516515747313 30340206548132637386810485)
              ·
                refine ⟨2844394363887434755013483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30340206548132637386810485 2844394363887434755013483)
                ·
                  refine ⟨4266591545831152132520225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2844394363887434755013483 4266591545831152132520225)
                  ·
                    refine ⟨3199943659373364099390169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4266591545831152132520225 3199943659373364099390169)
                    ·
                      refine ⟨2399957744530023074542627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3199943659373364099390169 2399957744530023074542627)
                      ·
                        rfl

theorem cell23_4673901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_4673901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673901 prefixEnd_4673901 := by exact prefixLift 4673901
  have htrace : WordTrace (prefixWord ++ tailWord_4673901) baseStart_4673901 baseEnd_4673901 := by
    simpa [prefixWord, tailWord_4673901, baseEnd_4673901] using wordTrace_append hprefix tailTrace_4673901
  have hstable : (prefixWord ++ tailWord_4673901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673901).length < 2 ^ (prefixWord ++ tailWord_4673901).sum := by decide
  have hdescent : baseEnd_4673901 < baseStart_4673901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673904 : List Nat := [2, 1, 1, 1, 4, 4, 3, 1, 1, 2, 3]
def baseStart_4673904 : Nat := 118140960795 + 4673904 * 2 ^ 59
def prefixEnd_4673904 : Nat := 4983230072969 + 3 ^ 40 * 4673904 * 2
def baseEnd_4673904 : Nat := 2399959284971986562805113

theorem tailTrace_4673904 : CollatzResearch.WordTrace tailWord_4673904 prefixEnd_4673904 2399959284971986562805113 := by
  unfold tailWord_4673904
  simp only [CollatzResearch.WordTrace]
  refine ⟨85235641829625761048618383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113647522439501014731491177 85235641829625761048618383)
  ·
    refine ⟨127853462744438641572927575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85235641829625761048618383 127853462744438641572927575)
    ·
      refine ⟨191780194116657962359391363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127853462744438641572927575 191780194116657962359391363)
      ·
        refine ⟨287670291174986943539087045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191780194116657962359391363 287670291174986943539087045)
        ·
          refine ⟨53938179595310051913578821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 287670291174986943539087045 53938179595310051913578821)
          ·
            refine ⟨10113408674120634733796029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53938179595310051913578821 10113408674120634733796029)
            ·
              refine ⟨3792528252795238025173511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10113408674120634733796029 3792528252795238025173511)
              ·
                refine ⟨5688792379192857037760267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3792528252795238025173511 5688792379192857037760267)
                ·
                  refine ⟨8533188568789285556640401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5688792379192857037760267 8533188568789285556640401)
                  ·
                    refine ⟨6399891426591964167480301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8533188568789285556640401 6399891426591964167480301)
                    ·
                      refine ⟨2399959284971986562805113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6399891426591964167480301 2399959284971986562805113)
                      ·
                        rfl

theorem cell23_4673904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 1, 2, 3].length) (baseStart_4673904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673904 prefixEnd_4673904 := by exact prefixLift 4673904
  have htrace : WordTrace (prefixWord ++ tailWord_4673904) baseStart_4673904 baseEnd_4673904 := by
    simpa [prefixWord, tailWord_4673904, baseEnd_4673904] using wordTrace_append hprefix tailTrace_4673904
  have hstable : (prefixWord ++ tailWord_4673904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673904).length < 2 ^ (prefixWord ++ tailWord_4673904).sum := by decide
  have hdescent : baseEnd_4673904 < baseStart_4673904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673927 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 5, 3, 2]
def baseStart_4673927 : Nat := 118140960795 + 4673927 * 2 ^ 59
def prefixEnd_4673927 : Nat := 4983230072969 + 3 ^ 40 * 4673927 * 2
def baseEnd_4673927 : Nat := 2399971095027039972817507

theorem tailTrace_4673927 : CollatzResearch.WordTrace tailWord_4673927 prefixEnd_4673927 2399971095027039972817507 := by
  unfold tailWord_4673927
  simp only [CollatzResearch.WordTrace]
  refine ⟨170472122538168197025324035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113648081692112131350216023 170472122538168197025324035)
  ·
    refine ⟨255708183807252295537986053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170472122538168197025324035 255708183807252295537986053)
    ·
      refine ⟨47945284463859805413372385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 255708183807252295537986053 47945284463859805413372385)
      ·
        refine ⟨35958963347894854060029289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47945284463859805413372385 35958963347894854060029289)
        ·
          refine ⟨26969222510921140545021967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35958963347894854060029289 26969222510921140545021967)
          ·
            refine ⟨40453833766381710817532951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26969222510921140545021967 40453833766381710817532951)
            ·
              refine ⟨60680750649572566226299427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40453833766381710817532951 60680750649572566226299427)
              ·
                refine ⟨91021125974358849339449141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60680750649572566226299427 91021125974358849339449141)
                ·
                  refine ⟨8533230560096142125573357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 91021125974358849339449141 8533230560096142125573357)
                  ·
                    refine ⟨3199961460036053297090009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8533230560096142125573357 3199961460036053297090009)
                    ·
                      refine ⟨2399971095027039972817507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3199961460036053297090009 2399971095027039972817507)
                      ·
                        rfl

theorem cell23_4673927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_4673927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673927 prefixEnd_4673927 := by exact prefixLift 4673927
  have htrace : WordTrace (prefixWord ++ tailWord_4673927) baseStart_4673927 baseEnd_4673927 := by
    simpa [prefixWord, tailWord_4673927, baseEnd_4673927] using wordTrace_append hprefix tailTrace_4673927
  have hstable : (prefixWord ++ tailWord_4673927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673927).length < 2 ^ (prefixWord ++ tailWord_4673927).sum := by decide
  have hdescent : baseEnd_4673927 < baseStart_4673927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673934 : List Nat := [4, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3]
def baseStart_4673934 : Nat := 118140960795 + 4673934 * 2 ^ 59
def prefixEnd_4673934 : Nat := 4983230072969 + 3 ^ 40 * 4673934 * 2
def baseEnd_4673934 : Nat := 2399974689391621445429975

theorem tailTrace_4673934 : CollatzResearch.WordTrace tailWord_4673934 prefixEnd_4673934 2399974689391621445429975 := by
  unfold tailWord_4673934
  simp only [CollatzResearch.WordTrace]
  refine ⟨21309047231142854652603607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113648251899428558147219237 21309047231142854652603607)
  ·
    refine ⟨31963570846714281978905411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21309047231142854652603607 31963570846714281978905411)
    ·
      refine ⟨47945356270071422968358117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31963570846714281978905411 47945356270071422968358117)
      ·
        refine ⟨8989754300638391806567147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47945356270071422968358117 8989754300638391806567147)
        ·
          refine ⟨13484631450957587709850721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8989754300638391806567147 13484631450957587709850721)
          ·
            refine ⟨10113473588218190782388041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13484631450957587709850721 10113473588218190782388041)
            ·
              refine ⟨7585105191163643086791031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10113473588218190782388041 7585105191163643086791031)
              ·
                refine ⟨11377657786745464630186547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7585105191163643086791031 11377657786745464630186547)
                ·
                  refine ⟨17066486680118196945279821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11377657786745464630186547 17066486680118196945279821)
                  ·
                    refine ⟨6399932505044323854479933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17066486680118196945279821 6399932505044323854479933)
                    ·
                      refine ⟨2399974689391621445429975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6399932505044323854479933 2399974689391621445429975)
                      ·
                        rfl

theorem cell23_4673934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_4673934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673934 prefixEnd_4673934 := by exact prefixLift 4673934
  have htrace : WordTrace (prefixWord ++ tailWord_4673934) baseStart_4673934 baseEnd_4673934 := by
    simpa [prefixWord, tailWord_4673934, baseEnd_4673934] using wordTrace_append hprefix tailTrace_4673934
  have hstable : (prefixWord ++ tailWord_4673934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673934).length < 2 ^ (prefixWord ++ tailWord_4673934).sum := by decide
  have hdescent : baseEnd_4673934 < baseStart_4673934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673944 : List Nat := [2, 1, 2, 5, 1, 1, 2, 1, 3, 3, 2]
def baseStart_4673944 : Nat := 118140960795 + 4673944 * 2 ^ 59
def prefixEnd_4673944 : Nat := 4983230072969 + 3 ^ 40 * 4673944 * 2
def baseEnd_4673944 : Nat := 2399979824198166406304929

theorem tailTrace_4673944 : CollatzResearch.WordTrace tailWord_4673944 prefixEnd_4673944 2399979824198166406304929 := by
  unfold tailWord_4673944
  simp only [CollatzResearch.WordTrace]
  refine ⟨85236371289553304464346443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113648495052737739285795257 85236371289553304464346443)
  ·
    refine ⟨127854556934329956696519665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85236371289553304464346443 127854556934329956696519665)
    ·
      refine ⟨95890917700747467522389749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127854556934329956696519665 95890917700747467522389749)
      ·
        refine ⟨8989773534445075080224039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95890917700747467522389749 8989773534445075080224039)
        ·
          refine ⟨13484660301667612620336059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8989773534445075080224039 13484660301667612620336059)
          ·
            refine ⟨20226990452501418930504089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13484660301667612620336059 20226990452501418930504089)
            ·
              refine ⟨15170242839376064197878067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20226990452501418930504089 15170242839376064197878067)
              ·
                refine ⟨22755364259064096296817101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15170242839376064197878067 22755364259064096296817101)
                ·
                  refine ⟨8533261597149036111306413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22755364259064096296817101 8533261597149036111306413)
                  ·
                    refine ⟨3199973098930888541739905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8533261597149036111306413 3199973098930888541739905)
                    ·
                      refine ⟨2399979824198166406304929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3199973098930888541739905 2399979824198166406304929)
                      ·
                        rfl

theorem cell23_4673944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_4673944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673944 prefixEnd_4673944 := by exact prefixLift 4673944
  have htrace : WordTrace (prefixWord ++ tailWord_4673944) baseStart_4673944 baseEnd_4673944 := by
    simpa [prefixWord, tailWord_4673944, baseEnd_4673944] using wordTrace_append hprefix tailTrace_4673944
  have hstable : (prefixWord ++ tailWord_4673944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673944).length < 2 ^ (prefixWord ++ tailWord_4673944).sum := by decide
  have hdescent : baseEnd_4673944 < baseStart_4673944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673957 : List Nat := [1, 3, 1, 2, 1, 1, 3, 4, 1, 4, 2]
def baseStart_4673957 : Nat := 118140960795 + 4673957 * 2 ^ 59
def prefixEnd_4673957 : Nat := 4983230072969 + 3 ^ 40 * 4673957 * 2
def baseEnd_4673957 : Nat := 2399986499446674855442369

theorem tailTrace_4673957 : CollatzResearch.WordTrace tailWord_4673957 prefixEnd_4673957 2399986499446674855442369 := by
  unfold tailWord_4673957
  simp only [CollatzResearch.WordTrace]
  refine ⟨170473216728059512148916125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113648811152039674765944083 170473216728059512148916125)
  ·
    refine ⟨63927456273022317055843547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170473216728059512148916125 63927456273022317055843547)
    ·
      refine ⟨95891184409533475583765321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63927456273022317055843547 95891184409533475583765321)
      ·
        refine ⟨71918388307150106687823991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95891184409533475583765321 71918388307150106687823991)
        ·
          refine ⟨107877582460725160031735987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71918388307150106687823991 107877582460725160031735987)
          ·
            refine ⟨161816373691087740047603981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107877582460725160031735987 161816373691087740047603981)
            ·
              refine ⟨60681140134157902517851493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161816373691087740047603981 60681140134157902517851493)
              ·
                refine ⟨11377713775154606722097155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60681140134157902517851493 11377713775154606722097155)
                ·
                  refine ⟨17066570662731910083145733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11377713775154606722097155 17066570662731910083145733)
                  ·
                    refine ⟨3199981999262233140589825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17066570662731910083145733 3199981999262233140589825)
                    ·
                      refine ⟨2399986499446674855442369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3199981999262233140589825 2399986499446674855442369)
                      ·
                        rfl

theorem cell23_4673957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 4, 2].length) (baseStart_4673957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673957 prefixEnd_4673957 := by exact prefixLift 4673957
  have htrace : WordTrace (prefixWord ++ tailWord_4673957) baseStart_4673957 baseEnd_4673957 := by
    simpa [prefixWord, tailWord_4673957, baseEnd_4673957] using wordTrace_append hprefix tailTrace_4673957
  have hstable : (prefixWord ++ tailWord_4673957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673957).length < 2 ^ (prefixWord ++ tailWord_4673957).sum := by decide
  have hdescent : baseEnd_4673957 < baseStart_4673957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673970 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4]
def baseStart_4673970 : Nat := 118140960795 + 4673970 * 2 ^ 59
def prefixEnd_4673970 : Nat := 4983230072969 + 3 ^ 40 * 4673970 * 2
def baseEnd_4673970 : Nat := 2399993174695183304579809

theorem tailTrace_4673970 : CollatzResearch.WordTrace tailWord_4673970 prefixEnd_4673970 2399993174695183304579809 := by
  unfold tailWord_4673970
  simp only [CollatzResearch.WordTrace]
  refine ⟨42618422719253103842284841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113649127251341610246092909 42618422719253103842284841)
  ·
    refine ⟨31963817039439827881713631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42618422719253103842284841 31963817039439827881713631)
    ·
      refine ⟨47945725559159741822570447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31963817039439827881713631 47945725559159741822570447)
      ·
        refine ⟨71918588338739612733855671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47945725559159741822570447 71918588338739612733855671)
        ·
          refine ⟨107877882508109419100783507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71918588338739612733855671 107877882508109419100783507)
          ·
            refine ⟨161816823762164128651175261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107877882508109419100783507 161816823762164128651175261)
            ·
              refine ⟨60681308910811548244190723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161816823762164128651175261 60681308910811548244190723)
              ·
                refine ⟨91021963366217322366286085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60681308910811548244190723 91021963366217322366286085)
                ·
                  refine ⟨17066618131165747943678641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91021963366217322366286085 17066618131165747943678641)
                  ·
                    refine ⟨12799963598374310957758981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17066618131165747943678641 12799963598374310957758981)
                    ·
                      refine ⟨2399993174695183304579809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12799963598374310957758981 2399993174695183304579809)
                      ·
                        rfl

theorem cell23_4673970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_4673970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673970 prefixEnd_4673970 := by exact prefixLift 4673970
  have htrace : WordTrace (prefixWord ++ tailWord_4673970) baseStart_4673970 baseEnd_4673970 := by
    simpa [prefixWord, tailWord_4673970, baseEnd_4673970] using wordTrace_append hprefix tailTrace_4673970
  have hstable : (prefixWord ++ tailWord_4673970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673970).length < 2 ^ (prefixWord ++ tailWord_4673970).sum := by decide
  have hdescent : baseEnd_4673970 < baseStart_4673970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4673985 : List Nat := [1, 2, 7, 1, 2, 1, 1, 1, 1, 3, 3]
def baseStart_4673985 : Nat := 118140960795 + 4673985 * 2 ^ 59
def prefixEnd_4673985 : Nat := 4983230072969 + 3 ^ 40 * 4673985 * 2
def baseEnd_4673985 : Nat := 2400000876905000745892241

theorem tailTrace_4673985 : CollatzResearch.WordTrace tailWord_4673985 prefixEnd_4673985 2400000876905000745892241 := by
  unfold tailWord_4673985
  simp only [CollatzResearch.WordTrace]
  refine ⟨170474237971958072930935409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113649491981305381953956939 170474237971958072930935409)
  ·
    refine ⟨127855678478968554698201557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170474237971958072930935409 127855678478968554698201557)
    ·
      refine ⟨2996617464350825500739099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 127855678478968554698201557 2996617464350825500739099)
      ·
        refine ⟨4494926196526238251108649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2996617464350825500739099 4494926196526238251108649)
        ·
          refine ⟨3371194647394678688331487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4494926196526238251108649 3371194647394678688331487)
          ·
            refine ⟨5056791971092018032497231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3371194647394678688331487 5056791971092018032497231)
            ·
              refine ⟨7585187956638027048745847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5056791971092018032497231 7585187956638027048745847)
              ·
                refine ⟨11377781934957040573118771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7585187956638027048745847 11377781934957040573118771)
                ·
                  refine ⟨17066672902435560859678157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11377781934957040573118771 17066672902435560859678157)
                  ·
                    refine ⟨6400002338413335322379309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17066672902435560859678157 6400002338413335322379309)
                    ·
                      refine ⟨2400000876905000745892241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6400002338413335322379309 2400000876905000745892241)
                      ·
                        rfl

theorem cell23_4673985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_4673985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4673985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4673985 prefixEnd_4673985 := by exact prefixLift 4673985
  have htrace : WordTrace (prefixWord ++ tailWord_4673985) baseStart_4673985 baseEnd_4673985 := by
    simpa [prefixWord, tailWord_4673985, baseEnd_4673985] using wordTrace_append hprefix tailTrace_4673985
  have hstable : (prefixWord ++ tailWord_4673985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4673985).length < 2 ^ (prefixWord ++ tailWord_4673985).sum := by decide
  have hdescent : baseEnd_4673985 < baseStart_4673985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4673985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674010 : List Nat := [3, 1, 1, 2, 3, 1, 1, 3, 1, 7]
def baseStart_4674010 : Nat := 118140960795 + 4674010 * 2 ^ 59
def prefixEnd_4674010 : Nat := 4983230072969 + 3 ^ 40 * 4674010 * 2
def baseEnd_4674010 : Nat := 800004571307121049359875

theorem tailTrace_4674010 : CollatzResearch.WordTrace tailWord_4674010 prefixEnd_4674010 800004571307121049359875 := by
  unfold tailWord_4674010
  simp only [CollatzResearch.WordTrace]
  refine ⟨42618787449216875550148871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113650099864578334800396989 42618787449216875550148871)
  ·
    refine ⟨63928181173825313325223307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42618787449216875550148871 63928181173825313325223307)
    ·
      refine ⟨95892271760737969987834961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63928181173825313325223307 95892271760737969987834961)
      ·
        refine ⟨71919203820553477490876221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95892271760737969987834961 71919203820553477490876221)
        ·
          refine ⟨26969701432707554059078583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71919203820553477490876221 26969701432707554059078583)
          ·
            refine ⟨40454552149061331088617875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26969701432707554059078583 40454552149061331088617875)
            ·
              refine ⟨60681828223591996632926813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40454552149061331088617875 60681828223591996632926813)
              ·
                refine ⟨22755685583846998737347555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60681828223591996632926813 22755685583846998737347555)
                ·
                  refine ⟨34133528375770498106021333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22755685583846998737347555 34133528375770498106021333)
                  ·
                    refine ⟨800004571307121049359875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34133528375770498106021333 800004571307121049359875)
                    ·
                      rfl

theorem cell23_4674010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 1, 7].length) (baseStart_4674010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674010 prefixEnd_4674010 := by exact prefixLift 4674010
  have htrace : WordTrace (prefixWord ++ tailWord_4674010) baseStart_4674010 baseEnd_4674010 := by
    simpa [prefixWord, tailWord_4674010, baseEnd_4674010] using wordTrace_append hprefix tailTrace_4674010
  have hstable : (prefixWord ++ tailWord_4674010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674010).length < 2 ^ (prefixWord ++ tailWord_4674010).sum := by decide
  have hdescent : baseEnd_4674010 < baseStart_4674010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674047 : List Nat := [1, 1, 2, 2, 1, 2, 4, 1, 1, 6, 2]
def baseStart_4674047 : Nat := 118140960795 + 4674047 * 2 ^ 59
def prefixEnd_4674047 : Nat := 4983230072969 + 3 ^ 40 * 4674047 * 2
def baseEnd_4674047 : Nat := 2400032712705579503316955

theorem tailTrace_4674047 : CollatzResearch.WordTrace tailWord_4674047 prefixEnd_4674047 2400032712705579503316955 := by
  unfold tailWord_4674047
  simp only [CollatzResearch.WordTrace]
  refine ⟨170476499297733457519692395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113650999531822305013128263 170476499297733457519692395)
  ·
    refine ⟨255714748946600186279538593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170476499297733457519692395 255714748946600186279538593)
    ·
      refine ⟨191786061709950139709653945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255714748946600186279538593 191786061709950139709653945)
      ·
        refine ⟨143839546282462604782240459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191786061709950139709653945 143839546282462604782240459)
        ·
          refine ⟨215759319423693907173360689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143839546282462604782240459 215759319423693907173360689)
          ·
            refine ⟨161819489567770430380020517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215759319423693907173360689 161819489567770430380020517)
            ·
              refine ⟨30341154293956955696253847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 161819489567770430380020517 30341154293956955696253847)
              ·
                refine ⟨45511731440935433544380771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30341154293956955696253847 45511731440935433544380771)
                ·
                  refine ⟨68267597161403150316571157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45511731440935433544380771 68267597161403150316571157)
                  ·
                    refine ⟨3200043616940772671089273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 68267597161403150316571157 3200043616940772671089273)
                    ·
                      refine ⟨2400032712705579503316955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3200043616940772671089273 2400032712705579503316955)
                      ·
                        rfl

theorem cell23_4674047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 6, 2].length) (baseStart_4674047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674047 prefixEnd_4674047 := by exact prefixLift 4674047
  have htrace : WordTrace (prefixWord ++ tailWord_4674047) baseStart_4674047 baseEnd_4674047 := by
    simpa [prefixWord, tailWord_4674047, baseEnd_4674047] using wordTrace_append hprefix tailTrace_4674047
  have hstable : (prefixWord ++ tailWord_4674047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674047).length < 2 ^ (prefixWord ++ tailWord_4674047).sum := by decide
  have hdescent : baseEnd_4674047 < baseStart_4674047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674061 : List Nat := [1, 7, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_4674061 : Nat := 118140960795 + 4674061 * 2 ^ 59
def prefixEnd_4674061 : Nat := 4983230072969 + 3 ^ 40 * 4674061 * 2
def baseEnd_4674061 : Nat := 800013300478247482847297

theorem tailTrace_4674061 : CollatzResearch.WordTrace tailWord_4674061 prefixEnd_4674061 800013300478247482847297 := by
  unfold tailWord_4674061
  simp only [CollatzResearch.WordTrace]
  refine ⟨170477009919682737910702037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113651339946455158607134691 170477009919682737910702037)
  ·
    refine ⟨3995554919992564169782079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 170477009919682737910702037 3995554919992564169782079)
    ·
      refine ⟨5993332379988846254673119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3995554919992564169782079 5993332379988846254673119)
      ·
        refine ⟨8989998569983269382009679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5993332379988846254673119 8989998569983269382009679)
        ·
          refine ⟨13484997854974904073014519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8989998569983269382009679 13484997854974904073014519)
          ·
            refine ⟨20227496782462356109521779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13484997854974904073014519 20227496782462356109521779)
            ·
              refine ⟨30341245173693534164282669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20227496782462356109521779 30341245173693534164282669)
              ·
                refine ⟨11377966940135075311606001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30341245173693534164282669 11377966940135075311606001)
                ·
                  refine ⟨8533475205101306483704501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11377966940135075311606001 8533475205101306483704501)
                  ·
                    refine ⟨800013300478247482847297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8533475205101306483704501 800013300478247482847297)
                    ·
                      rfl

theorem cell23_4674061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_4674061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674061 prefixEnd_4674061 := by exact prefixLift 4674061
  have htrace : WordTrace (prefixWord ++ tailWord_4674061) baseStart_4674061 baseEnd_4674061 := by
    simpa [prefixWord, tailWord_4674061, baseEnd_4674061] using wordTrace_append hprefix tailTrace_4674061
  have hstable : (prefixWord ++ tailWord_4674061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674061).length < 2 ^ (prefixWord ++ tailWord_4674061).sum := by decide
  have hdescent : baseEnd_4674061 < baseStart_4674061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674107 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 2, 9, 2]
def baseStart_4674107 : Nat := 118140960795 + 4674107 * 2 ^ 59
def prefixEnd_4674107 : Nat := 4983230072969 + 3 ^ 40 * 4674107 * 2
def baseEnd_4674107 : Nat := 2400063521544849268566679

theorem tailTrace_4674107 : CollatzResearch.WordTrace tailWord_4674107 prefixEnd_4674107 2400063521544849268566679 := by
  unfold tailWord_4674107
  simp only [CollatzResearch.WordTrace]
  refine ⟨170478687677516087766876575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113652458451677391844584383 170478687677516087766876575)
  ·
    refine ⟨255718031516274131650314863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170478687677516087766876575 255718031516274131650314863)
    ·
      refine ⟨383577047274411197475472295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255718031516274131650314863 383577047274411197475472295)
      ·
        refine ⟨575365570911616796213208443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383577047274411197475472295 575365570911616796213208443)
        ·
          refine ⟨863048356367425194319812665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 575365570911616796213208443 863048356367425194319812665)
          ·
            refine ⟨647286267275568895739859499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 863048356367425194319812665 647286267275568895739859499)
            ·
              refine ⟨970929400913353343609789249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 647286267275568895739859499 970929400913353343609789249)
              ·
                refine ⟨728197050685015007707341937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 970929400913353343609789249 728197050685015007707341937)
                ·
                  refine ⟨546147788013761255780506453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 728197050685015007707341937 546147788013761255780506453)
                  ·
                    refine ⟨3200084695393132358088905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 546147788013761255780506453 3200084695393132358088905)
                    ·
                      refine ⟨2400063521544849268566679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3200084695393132358088905 2400063521544849268566679)
                      ·
                        rfl

theorem cell23_4674107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 9, 2].length) (baseStart_4674107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674107 prefixEnd_4674107 := by exact prefixLift 4674107
  have htrace : WordTrace (prefixWord ++ tailWord_4674107) baseStart_4674107 baseEnd_4674107 := by
    simpa [prefixWord, tailWord_4674107, baseEnd_4674107] using wordTrace_append hprefix tailTrace_4674107
  have hstable : (prefixWord ++ tailWord_4674107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674107).length < 2 ^ (prefixWord ++ tailWord_4674107).sum := by decide
  have hdescent : baseEnd_4674107 < baseStart_4674107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674117 : List Nat := [1, 3, 1, 1, 1, 5, 2, 1, 3, 5]
def baseStart_4674117 : Nat := 118140960795 + 4674117 * 2 ^ 59
def prefixEnd_4674117 : Nat := 4983230072969 + 3 ^ 40 * 4674117 * 2
def baseEnd_4674117 : Nat := 800022885450464743147211

theorem tailTrace_4674117 : CollatzResearch.WordTrace tailWord_4674117 prefixEnd_4674117 800022885450464743147211 := by
  unfold tailWord_4674117
  simp only [CollatzResearch.WordTrace]
  refine ⟨170479052407479859474740605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113652701604986572983160403 170479052407479859474740605)
  ·
    refine ⟨63929644652804947303027727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170479052407479859474740605 63929644652804947303027727)
    ·
      refine ⟨95894466979207420954541591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63929644652804947303027727 95894466979207420954541591)
      ·
        refine ⟨143841700468811131431812387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95894466979207420954541591 143841700468811131431812387)
        ·
          refine ⟨215762550703216697147718581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143841700468811131431812387 215762550703216697147718581)
          ·
            refine ⟨20227739128426565357598617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 215762550703216697147718581 20227739128426565357598617)
            ·
              refine ⟨15170804346319924018198963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20227739128426565357598617 15170804346319924018198963)
              ·
                refine ⟨22756206519479886027298445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15170804346319924018198963 22756206519479886027298445)
                ·
                  refine ⟨8533577444804957260236917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22756206519479886027298445 8533577444804957260236917)
                  ·
                    refine ⟨800022885450464743147211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8533577444804957260236917 800022885450464743147211)
                    ·
                      rfl

theorem cell23_4674117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 5].length) (baseStart_4674117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674117 prefixEnd_4674117 := by exact prefixLift 4674117
  have htrace : WordTrace (prefixWord ++ tailWord_4674117) baseStart_4674117 baseEnd_4674117 := by
    simpa [prefixWord, tailWord_4674117, baseEnd_4674117] using wordTrace_append hprefix tailTrace_4674117
  have hstable : (prefixWord ++ tailWord_4674117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674117).length < 2 ^ (prefixWord ++ tailWord_4674117).sum := by decide
  have hdescent : baseEnd_4674117 < baseStart_4674117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674118 : List Nat := [6, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3]
def baseStart_4674118 : Nat := 118140960795 + 4674118 * 2 ^ 59
def prefixEnd_4674118 : Nat := 4983230072969 + 3 ^ 40 * 4674118 * 2
def baseEnd_4674118 : Nat := 2400069169832048725529129

theorem tailTrace_4674118 : CollatzResearch.WordTrace tailWord_4674118 prefixEnd_4674118 2400069169832048725529129 := by
  unfold tailWord_4674118
  simp only [CollatzResearch.WordTrace]
  refine ⟨5327471527514882395172719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 113652725920317491097018005 5327471527514882395172719)
  ·
    refine ⟨7991207291272323592759079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5327471527514882395172719 7991207291272323592759079)
    ·
      refine ⟨11986810936908485389138619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7991207291272323592759079 11986810936908485389138619)
      ·
        refine ⟨17980216405362728083707929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11986810936908485389138619 17980216405362728083707929)
        ·
          refine ⟨13485162304022046062780947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17980216405362728083707929 13485162304022046062780947)
          ·
            refine ⟨20227743456033069094171421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13485162304022046062780947 20227743456033069094171421)
            ·
              refine ⟨7585403796012400910314283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20227743456033069094171421 7585403796012400910314283)
              ·
                refine ⟨11378105694018601365471425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7585403796012400910314283 11378105694018601365471425)
                ·
                  refine ⟨8533579270513951024103569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11378105694018601365471425 8533579270513951024103569)
                  ·
                    refine ⟨6400184452885463268077677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8533579270513951024103569 6400184452885463268077677)
                    ·
                      refine ⟨2400069169832048725529129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6400184452885463268077677 2400069169832048725529129)
                      ·
                        rfl

theorem cell23_4674118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_4674118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674118 prefixEnd_4674118 := by exact prefixLift 4674118
  have htrace : WordTrace (prefixWord ++ tailWord_4674118) baseStart_4674118 baseEnd_4674118 := by
    simpa [prefixWord, tailWord_4674118, baseEnd_4674118] using wordTrace_append hprefix tailTrace_4674118
  have hstable : (prefixWord ++ tailWord_4674118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674118).length < 2 ^ (prefixWord ++ tailWord_4674118).sum := by decide
  have hdescent : baseEnd_4674118 < baseStart_4674118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674124 : List Nat := [2, 2, 1, 3, 1, 2, 3, 1, 1, 5, 2]
def baseStart_4674124 : Nat := 118140960795 + 4674124 * 2 ^ 59
def prefixEnd_4674124 : Nat := 4983230072969 + 3 ^ 40 * 4674124 * 2
def baseEnd_4674124 : Nat := 2400072250715975702054101

theorem tailTrace_4674124 : CollatzResearch.WordTrace tailWord_4674124 prefixEnd_4674124 2400072250715975702054101 := by
  unfold tailWord_4674124
  simp only [CollatzResearch.WordTrace]
  refine ⟨85239653859227249835122713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113652871812302999780163617 85239653859227249835122713)
  ·
    refine ⟨63929740394420437376342035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85239653859227249835122713 63929740394420437376342035)
    ·
      refine ⟨95894610591630656064513053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63929740394420437376342035 95894610591630656064513053)
      ·
        refine ⟨35960478971861496024192395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95894610591630656064513053 35960478971861496024192395)
        ·
          refine ⟨53940718457792244036288593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35960478971861496024192395 53940718457792244036288593)
          ·
            refine ⟨40455538843344183027216445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53940718457792244036288593 40455538843344183027216445)
            ·
              refine ⟨15170827066254068635206167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40455538843344183027216445 15170827066254068635206167)
              ·
                refine ⟨22756240599381102952809251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15170827066254068635206167 22756240599381102952809251)
                ·
                  refine ⟨34134360899071654429213877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22756240599381102952809251 34134360899071654429213877)
                  ·
                    refine ⟨3200096334287967602738801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34134360899071654429213877 3200096334287967602738801)
                    ·
                      refine ⟨2400072250715975702054101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3200096334287967602738801 2400072250715975702054101)
                      ·
                        rfl

theorem cell23_4674124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_4674124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674124 prefixEnd_4674124 := by exact prefixLift 4674124
  have htrace : WordTrace (prefixWord ++ tailWord_4674124) baseStart_4674124 baseEnd_4674124 := by
    simpa [prefixWord, tailWord_4674124, baseEnd_4674124] using wordTrace_append hprefix tailTrace_4674124
  have hstable : (prefixWord ++ tailWord_4674124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674124).length < 2 ^ (prefixWord ++ tailWord_4674124).sum := by decide
  have hdescent : baseEnd_4674124 < baseStart_4674124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674177 : List Nat := [1, 2, 4, 2, 1, 1, 3, 9]
def baseStart_4674177 : Nat := 118140960795 + 4674177 * 2 ^ 59
def prefixEnd_4674177 : Nat := 4983230072969 + 3 ^ 40 * 4674177 * 2
def baseEnd_4674177 : Nat := 88892572784839407210791

theorem tailTrace_4674177 : CollatzResearch.WordTrace tailWord_4674177 prefixEnd_4674177 88892572784839407210791 := by
  unfold tailWord_4674177
  simp only [CollatzResearch.WordTrace]
  refine ⟨170481240787262489721924785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113654160524841659814616523 170481240787262489721924785)
  ·
    refine ⟨127860930590446867291443589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170481240787262489721924785 127860930590446867291443589)
    ·
      refine ⟨23973924485708787617145673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127860930590446867291443589 23973924485708787617145673)
      ·
        refine ⟨17980443364281590712859255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23973924485708787617145673 17980443364281590712859255)
        ·
          refine ⟨26970665046422386069288883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17980443364281590712859255 26970665046422386069288883)
          ·
            refine ⟨40455997569633579103933325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26970665046422386069288883 40455997569633579103933325)
            ·
              refine ⟨15170999088612592163974997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40455997569633579103933325 15170999088612592163974997)
              ·
                refine ⟨88892572784839407210791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15170999088612592163974997 88892572784839407210791)
                ·
                  rfl

theorem cell23_4674177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 9].length) (baseStart_4674177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674177 prefixEnd_4674177 := by exact prefixLift 4674177
  have htrace : WordTrace (prefixWord ++ tailWord_4674177) baseStart_4674177 baseEnd_4674177 := by
    simpa [prefixWord, tailWord_4674177, baseEnd_4674177] using wordTrace_append hprefix tailTrace_4674177
  have hstable : (prefixWord ++ tailWord_4674177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674177).length < 2 ^ (prefixWord ++ tailWord_4674177).sum := by decide
  have hdescent : baseEnd_4674177 < baseStart_4674177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674188 : List Nat := [2, 2, 1, 2, 1, 1, 2, 7, 1, 2, 2]
def baseStart_4674188 : Nat := 118140960795 + 4674188 * 2 ^ 59
def prefixEnd_4674188 : Nat := 4983230072969 + 3 ^ 40 * 4674188 * 2
def baseEnd_4674188 : Nat := 2400105113477863451653807

theorem tailTrace_4674188 : CollatzResearch.WordTrace tailWord_4674188 prefixEnd_4674188 2400105113477863451653807 := by
  unfold tailWord_4674188
  simp only [CollatzResearch.WordTrace]
  refine ⟨85240820995111319300287609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113654427993481759067050145 85240820995111319300287609)
  ·
    refine ⟨63930615746333489475215707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85240820995111319300287609 63930615746333489475215707)
    ·
      refine ⟨95895923619500234212823561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63930615746333489475215707 95895923619500234212823561)
      ·
        refine ⟨71921942714625175659617671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95895923619500234212823561 71921942714625175659617671)
        ·
          refine ⟨107882914071937763489426507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71921942714625175659617671 107882914071937763489426507)
          ·
            refine ⟨161824371107906645234139761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107882914071937763489426507 161824371107906645234139761)
            ·
              refine ⟨121368278330929983925604821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161824371107906645234139761 121368278330929983925604821)
              ·
                refine ⟨2844569023381171498256363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 121368278330929983925604821 2844569023381171498256363)
                ·
                  refine ⟨4266853535071757247384545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2844569023381171498256363 4266853535071757247384545)
                  ·
                    refine ⟨3200140151303817935538409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4266853535071757247384545 3200140151303817935538409)
                    ·
                      refine ⟨2400105113477863451653807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3200140151303817935538409 2400105113477863451653807)
                      ·
                        rfl

theorem cell23_4674188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 7, 1, 2, 2].length) (baseStart_4674188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674188 prefixEnd_4674188 := by exact prefixLift 4674188
  have htrace : WordTrace (prefixWord ++ tailWord_4674188) baseStart_4674188 baseEnd_4674188 := by
    simpa [prefixWord, tailWord_4674188, baseEnd_4674188] using wordTrace_append hprefix tailTrace_4674188
  have hstable : (prefixWord ++ tailWord_4674188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674188).length < 2 ^ (prefixWord ++ tailWord_4674188).sum := by decide
  have hdescent : baseEnd_4674188 < baseStart_4674188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674194 : List Nat := [3, 2, 3, 1, 2, 3, 9]
def baseStart_4674194 : Nat := 118140960795 + 4674194 * 2 ^ 59
def prefixEnd_4674194 : Nat := 4983230072969 + 3 ^ 40 * 4674194 * 2
def baseEnd_4674194 : Nat := 29630965362491239854059

theorem tailTrace_4674194 : CollatzResearch.WordTrace tailWord_4674194 prefixEnd_4674194 29630965362491239854059 := by
  unfold tailWord_4674194
  simp only [CollatzResearch.WordTrace]
  refine ⟨42620465207050225406323409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113654573885467267750195757 42620465207050225406323409)
  ·
    refine ⟨31965348905287669054742557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42620465207050225406323409 31965348905287669054742557)
    ·
      refine ⟨11987005839482875895528459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31965348905287669054742557 11987005839482875895528459)
      ·
        refine ⟨17980508759224313843292689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11987005839482875895528459 17980508759224313843292689)
        ·
          refine ⟨13485381569418235382469517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17980508759224313843292689 13485381569418235382469517)
          ·
            refine ⟨5057018088531838268426069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13485381569418235382469517 5057018088531838268426069)
            ·
              refine ⟨29630965362491239854059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5057018088531838268426069 29630965362491239854059)
              ·
                rfl

theorem cell23_4674194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 9].length) (baseStart_4674194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674194 prefixEnd_4674194 := by exact prefixLift 4674194
  have htrace : WordTrace (prefixWord ++ tailWord_4674194) baseStart_4674194 baseEnd_4674194 := by
    simpa [prefixWord, tailWord_4674194, baseEnd_4674194] using wordTrace_append hprefix tailTrace_4674194
  have hstable : (prefixWord ++ tailWord_4674194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674194).length < 2 ^ (prefixWord ++ tailWord_4674194).sum := by decide
  have hdescent : baseEnd_4674194 < baseStart_4674194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674225 : List Nat := [1, 2, 2, 6, 1, 2, 1, 2, 1, 2, 3]
def baseStart_4674225 : Nat := 118140960795 + 4674225 * 2 ^ 59
def prefixEnd_4674225 : Nat := 4983230072969 + 3 ^ 40 * 4674225 * 2
def baseEnd_4674225 : Nat := 2400124112262079806891137

theorem tailTrace_4674225 : CollatzResearch.WordTrace tailWord_4674225 prefixEnd_4674225 2400124112262079806891137 := by
  unfold tailWord_4674225
  simp only [CollatzResearch.WordTrace]
  refine ⟨170482991491088593919672129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113655327660725729279781419 170482991491088593919672129)
  ·
    refine ⟨127862243618316445439754097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170482991491088593919672129 127862243618316445439754097)
    ·
      refine ⟨95896682713737334079815573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127862243618316445439754097 95896682713737334079815573)
      ·
        refine ⟨4495157002206437534991355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 95896682713737334079815573 4495157002206437534991355)
        ·
          refine ⟨6742735503309656302487033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4495157002206437534991355 6742735503309656302487033)
          ·
            refine ⟨5057051627482242226865275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6742735503309656302487033 5057051627482242226865275)
            ·
              refine ⟨7585577441223363340297913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5057051627482242226865275 7585577441223363340297913)
              ·
                refine ⟨5689183080917522505223435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7585577441223363340297913 5689183080917522505223435)
                ·
                  refine ⟨8533774621376283757835153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5689183080917522505223435 8533774621376283757835153)
                  ·
                    refine ⟨6400330966032212818376365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8533774621376283757835153 6400330966032212818376365)
                    ·
                      refine ⟨2400124112262079806891137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6400330966032212818376365 2400124112262079806891137)
                      ·
                        rfl

theorem cell23_4674225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_4674225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674225 prefixEnd_4674225 := by exact prefixLift 4674225
  have htrace : WordTrace (prefixWord ++ tailWord_4674225) baseStart_4674225 baseEnd_4674225 := by
    simpa [prefixWord, tailWord_4674225, baseEnd_4674225] using wordTrace_append hprefix tailTrace_4674225
  have hstable : (prefixWord ++ tailWord_4674225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674225).length < 2 ^ (prefixWord ++ tailWord_4674225).sum := by decide
  have hdescent : baseEnd_4674225 < baseStart_4674225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674247 : List Nat := [1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 5]
def baseStart_4674247 : Nat := 118140960795 + 4674247 * 2 ^ 59
def prefixEnd_4674247 : Nat := 4983230072969 + 3 ^ 40 * 4674247 * 2
def baseEnd_4674247 : Nat := 2400135408836478720816035

theorem tailTrace_4674247 : CollatzResearch.WordTrace tailWord_4674247 prefixEnd_4674247 2400135408836478720816035 := by
  unfold tailWord_4674247
  simp only [CollatzResearch.WordTrace]
  refine ⟨170483793897008891676972995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113655862598005927784648663 170483793897008891676972995)
  ·
    refine ⟨255725690845513337515459493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170483793897008891676972995 255725690845513337515459493)
    ·
      refine ⟨47948567033533750784148655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 255725690845513337515459493 47948567033533750784148655)
      ·
        refine ⟨71922850550300626176222983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47948567033533750784148655 71922850550300626176222983)
        ·
          refine ⟨107884275825450939264334475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71922850550300626176222983 107884275825450939264334475)
          ·
            refine ⟨161826413738176408896501713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107884275825450939264334475 161826413738176408896501713)
            ·
              refine ⟨121369810303632306672376285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161826413738176408896501713 121369810303632306672376285)
              ·
                refine ⟨45513678863862115002141107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121369810303632306672376285 45513678863862115002141107)
                ·
                  refine ⟨68270518295793172503211661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45513678863862115002141107 68270518295793172503211661)
                  ·
                    refine ⟨25601444360922439688704373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68270518295793172503211661 25601444360922439688704373)
                    ·
                      refine ⟨2400135408836478720816035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25601444360922439688704373 2400135408836478720816035)
                      ·
                        rfl

theorem cell23_4674247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_4674247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674247 prefixEnd_4674247 := by exact prefixLift 4674247
  have htrace : WordTrace (prefixWord ++ tailWord_4674247) baseStart_4674247 baseEnd_4674247 := by
    simpa [prefixWord, tailWord_4674247, baseEnd_4674247] using wordTrace_append hprefix tailTrace_4674247
  have hstable : (prefixWord ++ tailWord_4674247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674247).length < 2 ^ (prefixWord ++ tailWord_4674247).sum := by decide
  have hdescent : baseEnd_4674247 < baseStart_4674247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674264 : List Nat := [2, 1, 2, 2, 3, 2, 1, 1, 2, 4, 3]
def baseStart_4674264 : Nat := 118140960795 + 4674264 * 2 ^ 59
def prefixEnd_4674264 : Nat := 4983230072969 + 3 ^ 40 * 4674264 * 2
def baseEnd_4674264 : Nat := 2400144138007605154303457

theorem tailTrace_4674264 : CollatzResearch.WordTrace tailWord_4674264 prefixEnd_4674264 2400144138007605154303457 := by
  unfold tailWord_4674264
  simp only [CollatzResearch.WordTrace]
  refine ⟨85242206968973651790170923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113656275958631535720227897 85242206968973651790170923)
  ·
    refine ⟨127863310453460477685256385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85242206968973651790170923 127863310453460477685256385)
    ·
      refine ⟨95897482840095358263942289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127863310453460477685256385 95897482840095358263942289)
      ·
        refine ⟨71923112130071518697956717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95897482840095358263942289 71923112130071518697956717)
        ·
          refine ⟨26971167048776819511733769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71923112130071518697956717 26971167048776819511733769)
          ·
            refine ⟨20228375286582614633800327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26971167048776819511733769 20228375286582614633800327)
            ·
              refine ⟨30342562929873921950700491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20228375286582614633800327 30342562929873921950700491)
              ·
                refine ⟨45513844394810882926050737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30342562929873921950700491 45513844394810882926050737)
                ·
                  refine ⟨34135383296108162194538053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45513844394810882926050737 34135383296108162194538053)
                  ·
                    refine ⟨6400384368020280411475885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34135383296108162194538053 6400384368020280411475885)
                    ·
                      refine ⟨2400144138007605154303457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6400384368020280411475885 2400144138007605154303457)
                      ·
                        rfl

theorem cell23_4674264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_4674264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674264 prefixEnd_4674264 := by exact prefixLift 4674264
  have htrace : WordTrace (prefixWord ++ tailWord_4674264) baseStart_4674264 baseEnd_4674264 := by
    simpa [prefixWord, tailWord_4674264, baseEnd_4674264] using wordTrace_append hprefix tailTrace_4674264
  have hstable : (prefixWord ++ tailWord_4674264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674264).length < 2 ^ (prefixWord ++ tailWord_4674264).sum := by decide
  have hdescent : baseEnd_4674264 < baseStart_4674264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674301 : List Nat := [1, 4, 1, 1, 1, 1, 6, 3, 5]
def baseStart_4674301 : Nat := 118140960795 + 4674301 * 2 ^ 59
def prefixEnd_4674301 : Nat := 4983230072969 + 3 ^ 40 * 4674301 * 2
def baseEnd_4674301 : Nat := 266684792976869056615643

theorem tailTrace_4674301 : CollatzResearch.WordTrace tailWord_4674301 prefixEnd_4674301 266684792976869056615643 := by
  unfold tailWord_4674301
  simp only [CollatzResearch.WordTrace]
  refine ⟨170485763438813258899438757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113657175625875505932959171 170485763438813258899438757)
  ·
    refine ⟨31966080644777486043644767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170485763438813258899438757 31966080644777486043644767)
    ·
      refine ⟨47949120967166229065467151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31966080644777486043644767 47949120967166229065467151)
      ·
        refine ⟨71923681450749343598200727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47949120967166229065467151 71923681450749343598200727)
        ·
          refine ⟨107885522176124015397301091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71923681450749343598200727 107885522176124015397301091)
          ·
            refine ⟨161828283264186023095951637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107885522176124015397301091 161828283264186023095951637)
            ·
              refine ⟨7585700778008719832622733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 161828283264186023095951637 7585700778008719832622733)
              ·
                refine ⟨2844637791753269937233525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7585700778008719832622733 2844637791753269937233525)
                ·
                  refine ⟨266684792976869056615643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2844637791753269937233525 266684792976869056615643)
                  ·
                    rfl

theorem cell23_4674301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 3, 5].length) (baseStart_4674301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674301 prefixEnd_4674301 := by exact prefixLift 4674301
  have htrace : WordTrace (prefixWord ++ tailWord_4674301) baseStart_4674301 baseEnd_4674301 := by
    simpa [prefixWord, tailWord_4674301, baseEnd_4674301] using wordTrace_append hprefix tailTrace_4674301
  have hstable : (prefixWord ++ tailWord_4674301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674301).length < 2 ^ (prefixWord ++ tailWord_4674301).sum := by decide
  have hdescent : baseEnd_4674301 < baseStart_4674301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674311 : List Nat := [1, 1, 4, 4, 1, 1, 1, 2, 2, 3, 3]
def baseStart_4674311 : Nat := 118140960795 + 4674311 * 2 ^ 59
def prefixEnd_4674311 : Nat := 4983230072969 + 3 ^ 40 * 4674311 * 2
def baseEnd_4674311 : Nat := 2400168271598366470415741

theorem tailTrace_4674311 : CollatzResearch.WordTrace tailWord_4674311 prefixEnd_4674311 2400168271598366470415741 := by
  unfold tailWord_4674311
  simp only [CollatzResearch.WordTrace]
  refine ⟨170486128168777030607302787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113657418779184687071535191 170486128168777030607302787)
  ·
    refine ⟨255729192253165545910954181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170486128168777030607302787 255729192253165545910954181)
    ·
      refine ⟨47949223547468539858303909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 255729192253165545910954181 47949223547468539858303909)
      ·
        refine ⟨8990479415150351223431983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47949223547468539858303909 8990479415150351223431983)
        ·
          refine ⟨13485719122725526835147975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8990479415150351223431983 13485719122725526835147975)
          ·
            refine ⟨20228578684088290252721963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13485719122725526835147975 20228578684088290252721963)
            ·
              refine ⟨30342868026132435379082945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20228578684088290252721963 30342868026132435379082945)
              ·
                refine ⟨22757151019599326534312209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30342868026132435379082945 22757151019599326534312209)
                ·
                  refine ⟨17067863264699494900734157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22757151019599326534312209 17067863264699494900734157)
                  ·
                    refine ⟨6400448724262310587775309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17067863264699494900734157 6400448724262310587775309)
                    ·
                      refine ⟨2400168271598366470415741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6400448724262310587775309 2400168271598366470415741)
                      ·
                        rfl

theorem cell23_4674311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_4674311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674311 prefixEnd_4674311 := by exact prefixLift 4674311
  have htrace : WordTrace (prefixWord ++ tailWord_4674311) baseStart_4674311 baseEnd_4674311 := by
    simpa [prefixWord, tailWord_4674311, baseEnd_4674311] using wordTrace_append hprefix tailTrace_4674311
  have hstable : (prefixWord ++ tailWord_4674311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674311).length < 2 ^ (prefixWord ++ tailWord_4674311).sum := by decide
  have hdescent : baseEnd_4674311 < baseStart_4674311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674314 : List Nat := [3, 1, 2, 2, 1, 2, 2, 1, 4, 5]
def baseStart_4674314 : Nat := 118140960795 + 4674314 * 2 ^ 59
def prefixEnd_4674314 : Nat := 4983230072969 + 3 ^ 40 * 4674314 * 2
def baseEnd_4674314 : Nat := 800056604013443319559409

theorem tailTrace_4674314 : CollatzResearch.WordTrace tailWord_4674314 prefixEnd_4674314 800056604013443319559409 := by
  unfold tailWord_4674314
  simp only [CollatzResearch.WordTrace]
  refine ⟨42621559396941540529915499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113657491725177441413107997 42621559396941540529915499)
  ·
    refine ⟨63932339095412310794873249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42621559396941540529915499 63932339095412310794873249)
    ·
      refine ⟨47949254321559233096154937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63932339095412310794873249 47949254321559233096154937)
      ·
        refine ⟨35961940741169424822116203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47949254321559233096154937 35961940741169424822116203)
        ·
          refine ⟨53942911111754137233174305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35961940741169424822116203 53942911111754137233174305)
          ·
            refine ⟨40457183333815602924880729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53942911111754137233174305 40457183333815602924880729)
            ·
              refine ⟨30342887500361702193660547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40457183333815602924880729 30342887500361702193660547)
              ·
                refine ⟨45514331250542553290490821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30342887500361702193660547 45514331250542553290490821)
                ·
                  refine ⟨8533937109476728741967029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45514331250542553290490821 8533937109476728741967029)
                  ·
                    refine ⟨800056604013443319559409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8533937109476728741967029 800056604013443319559409)
                    ·
                      rfl

theorem cell23_4674314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_4674314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674314 prefixEnd_4674314 := by exact prefixLift 4674314
  have htrace : WordTrace (prefixWord ++ tailWord_4674314) baseStart_4674314 baseEnd_4674314 := by
    simpa [prefixWord, tailWord_4674314, baseEnd_4674314] using wordTrace_append hprefix tailTrace_4674314
  have hstable : (prefixWord ++ tailWord_4674314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674314).length < 2 ^ (prefixWord ++ tailWord_4674314).sum := by decide
  have hdescent : baseEnd_4674314 < baseStart_4674314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674344 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 2, 8]
def baseStart_4674344 : Nat := 118140960795 + 4674344 * 2 ^ 59
def prefixEnd_4674344 : Nat := 4983230072969 + 3 ^ 40 * 4674344 * 2
def baseEnd_4674344 : Nat := 800061738819988280434363

theorem tailTrace_4674344 : CollatzResearch.WordTrace tailWord_4674344 prefixEnd_4674344 800061738819988280434363 := by
  unfold tailWord_4674344
  simp only [CollatzResearch.WordTrace]
  refine ⟨85243665888828738621627043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113658221185104984828836057 85243665888828738621627043)
  ·
    refine ⟨127865498833243107932440565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85243665888828738621627043 127865498833243107932440565)
    ·
      refine ⟨11987390515616541368666303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 127865498833243107932440565 11987390515616541368666303)
      ·
        refine ⟨17981085773424812052999455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11987390515616541368666303 17981085773424812052999455)
        ·
          refine ⟨26971628660137218079499183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17981085773424812052999455 26971628660137218079499183)
          ·
            refine ⟨40457442990205827119248775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26971628660137218079499183 40457442990205827119248775)
            ·
              refine ⟨60686164485308740678873163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40457442990205827119248775 60686164485308740678873163)
              ·
                refine ⟨91029246727963111018309745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60686164485308740678873163 91029246727963111018309745)
                ·
                  refine ⟨68271935045972333263732309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91029246727963111018309745 68271935045972333263732309)
                  ·
                    refine ⟨800061738819988280434363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68271935045972333263732309 800061738819988280434363)
                    ·
                      rfl

theorem cell23_4674344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_4674344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674344 prefixEnd_4674344 := by exact prefixLift 4674344
  have htrace : WordTrace (prefixWord ++ tailWord_4674344) baseStart_4674344 baseEnd_4674344 := by
    simpa [prefixWord, tailWord_4674344, baseEnd_4674344] using wordTrace_append hprefix tailTrace_4674344
  have hstable : (prefixWord ++ tailWord_4674344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674344).length < 2 ^ (prefixWord ++ tailWord_4674344).sum := by decide
  have hdescent : baseEnd_4674344 < baseStart_4674344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674371 : List Nat := [1, 1, 1, 3, 1, 4, 3, 2, 2, 2, 3]
def baseStart_4674371 : Nat := 118140960795 + 4674371 * 2 ^ 59
def prefixEnd_4674371 : Nat := 4983230072969 + 3 ^ 40 * 4674371 * 2
def baseEnd_4674371 : Nat := 2400199080437636235665465

theorem tailTrace_4674371 : CollatzResearch.WordTrace tailWord_4674371 prefixEnd_4674371 2400199080437636235665465 := by
  unfold tailWord_4674371
  simp only [CollatzResearch.WordTrace]
  refine ⟨170488316548559660854486967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113658877699039773902991311 170488316548559660854486967)
  ·
    refine ⟨255732474822839491281730451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170488316548559660854486967 255732474822839491281730451)
    ·
      refine ⟨383598712234259236922595677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255732474822839491281730451 383598712234259236922595677)
      ·
        refine ⟨143849517087847213845973379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 383598712234259236922595677 143849517087847213845973379)
        ·
          refine ⟨215774275631770820768960069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143849517087847213845973379 215774275631770820768960069)
          ·
            refine ⟨40457676680957028894180013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 215774275631770820768960069 40457676680957028894180013)
            ·
              refine ⟨15171628755358885835317505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40457676680957028894180013 15171628755358885835317505)
              ·
                refine ⟨11378721566519164376488129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15171628755358885835317505 11378721566519164376488129)
                ·
                  refine ⟨8534041174889373282366097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11378721566519164376488129 8534041174889373282366097)
                  ·
                    refine ⟨6400530881167029961774573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8534041174889373282366097 6400530881167029961774573)
                    ·
                      refine ⟨2400199080437636235665465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6400530881167029961774573 2400199080437636235665465)
                      ·
                        rfl

theorem cell23_4674371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 2, 3].length) (baseStart_4674371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674371 prefixEnd_4674371 := by exact prefixLift 4674371
  have htrace : WordTrace (prefixWord ++ tailWord_4674371) baseStart_4674371 baseEnd_4674371 := by
    simpa [prefixWord, tailWord_4674371, baseEnd_4674371] using wordTrace_append hprefix tailTrace_4674371
  have hstable : (prefixWord ++ tailWord_4674371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674371).length < 2 ^ (prefixWord ++ tailWord_4674371).sum := by decide
  have hdescent : baseEnd_4674371 < baseStart_4674371 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674391 : List Nat := [1, 1, 3, 2, 4, 2, 1, 3, 6]
def baseStart_4674391 : Nat := 118140960795 + 4674391 * 2 ^ 59
def prefixEnd_4674391 : Nat := 4983230072969 + 3 ^ 40 * 4674391 * 2
def baseEnd_4674391 : Nat := 266689927783414017490597

theorem tailTrace_4674391 : CollatzResearch.WordTrace tailWord_4674391 prefixEnd_4674391 266689927783414017490597 := by
  unfold tailWord_4674391
  simp only [CollatzResearch.WordTrace]
  refine ⟨170489046008487204270215027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113659364005658136180143351 170489046008487204270215027)
  ·
    refine ⟨255733569012730806405322541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170489046008487204270215027 255733569012730806405322541)
    ·
      refine ⟨95900088379774052401995953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255733569012730806405322541 95900088379774052401995953)
      ·
        refine ⟨71925066284830539301496965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95900088379774052401995953 71925066284830539301496965)
        ·
          refine ⟨13485949928405726119030681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71925066284830539301496965 13485949928405726119030681)
          ·
            refine ⟨10114462446304294589273011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13485949928405726119030681 10114462446304294589273011)
            ·
              refine ⟨15171693669456441883909517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10114462446304294589273011 15171693669456441883909517)
              ·
                refine ⟨5689385126046165706466069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15171693669456441883909517 5689385126046165706466069)
                ·
                  refine ⟨266689927783414017490597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5689385126046165706466069 266689927783414017490597)
                  ·
                    rfl

theorem cell23_4674391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 6].length) (baseStart_4674391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674391 prefixEnd_4674391 := by exact prefixLift 4674391
  have htrace : WordTrace (prefixWord ++ tailWord_4674391) baseStart_4674391 baseEnd_4674391 := by
    simpa [prefixWord, tailWord_4674391, baseEnd_4674391] using wordTrace_append hprefix tailTrace_4674391
  have hstable : (prefixWord ++ tailWord_4674391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674391).length < 2 ^ (prefixWord ++ tailWord_4674391).sum := by decide
  have hdescent : baseEnd_4674391 < baseStart_4674391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674411 : List Nat := [1, 1, 1, 1, 2, 2, 4, 3, 1, 5, 2]
def baseStart_4674411 : Nat := 118140960795 + 4674411 * 2 ^ 59
def prefixEnd_4674411 : Nat := 4983230072969 + 3 ^ 40 * 4674411 * 2
def baseEnd_4674411 : Nat := 2400219619663816079165281

theorem tailTrace_4674411 : CollatzResearch.WordTrace tailWord_4674411 prefixEnd_4674411 2400219619663816079165281 := by
  unfold tailWord_4674411
  simp only [CollatzResearch.WordTrace]
  refine ⟨170489775468414747685943087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113659850312276498457295391 170489775468414747685943087)
  ·
    refine ⟨255734663202622121528914631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170489775468414747685943087 255734663202622121528914631)
    ·
      refine ⟨383601994803933182293371947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255734663202622121528914631 383601994803933182293371947)
      ·
        refine ⟨575402992205899773440057921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383601994803933182293371947 575402992205899773440057921)
        ·
          refine ⟨431552244154424830080043441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 575402992205899773440057921 431552244154424830080043441)
          ·
            refine ⟨323664183115818622560032581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 431552244154424830080043441 323664183115818622560032581)
            ·
              refine ⟨60687034334215991730006109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 323664183115818622560032581 60687034334215991730006109)
              ·
                refine ⟨22757637875330996898752291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60687034334215991730006109 22757637875330996898752291)
                ·
                  refine ⟨34136456812996495348128437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22757637875330996898752291 34136456812996495348128437)
                  ·
                    refine ⟨3200292826218421438887041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34136456812996495348128437 3200292826218421438887041)
                    ·
                      refine ⟨2400219619663816079165281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3200292826218421438887041 2400219619663816079165281)
                      ·
                        rfl

theorem cell23_4674411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 5, 2].length) (baseStart_4674411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674411 prefixEnd_4674411 := by exact prefixLift 4674411
  have htrace : WordTrace (prefixWord ++ tailWord_4674411) baseStart_4674411 baseEnd_4674411 := by
    simpa [prefixWord, tailWord_4674411, baseEnd_4674411] using wordTrace_append hprefix tailTrace_4674411
  have hstable : (prefixWord ++ tailWord_4674411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674411).length < 2 ^ (prefixWord ++ tailWord_4674411).sum := by decide
  have hdescent : baseEnd_4674411 < baseStart_4674411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674435 : List Nat := [1, 1, 1, 3, 4, 1, 3, 4, 1, 1, 3]
def baseStart_4674435 : Nat := 118140960795 + 4674435 * 2 ^ 59
def prefixEnd_4674435 : Nat := 4983230072969 + 3 ^ 40 * 4674435 * 2
def baseEnd_4674435 : Nat := 2400231943199523985265171

theorem tailTrace_4674435 : CollatzResearch.WordTrace tailWord_4674435 prefixEnd_4674435 2400231943199523985265171 := by
  unfold tailWord_4674435
  simp only [CollatzResearch.WordTrace]
  refine ⟨170490650820327799784816759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113660433880218533189877839 170490650820327799784816759)
  ·
    refine ⟨255735976230491699677225139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170490650820327799784816759 255735976230491699677225139)
    ·
      refine ⟨383603964345737549515837709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255735976230491699677225139 383603964345737549515837709)
      ·
        refine ⟨143851486629651581068439141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 383603964345737549515837709 143851486629651581068439141)
        ·
          refine ⟨26972153743059671450332339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143851486629651581068439141 26972153743059671450332339)
          ·
            refine ⟨40458230614589507175498509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26972153743059671450332339 40458230614589507175498509)
            ·
              refine ⟨15171836480471065190811941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40458230614589507175498509 15171836480471065190811941)
              ·
                refine ⟨2844719340088324723277239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15171836480471065190811941 2844719340088324723277239)
                ·
                  refine ⟨4267079010132487084915859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2844719340088324723277239 4267079010132487084915859)
                  ·
                    refine ⟨6400618515198730627373789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4267079010132487084915859 6400618515198730627373789)
                    ·
                      refine ⟨2400231943199523985265171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6400618515198730627373789 2400231943199523985265171)
                      ·
                        rfl

theorem cell23_4674435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 4, 1, 1, 3].length) (baseStart_4674435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674435 prefixEnd_4674435 := by exact prefixLift 4674435
  have htrace : WordTrace (prefixWord ++ tailWord_4674435) baseStart_4674435 baseEnd_4674435 := by
    simpa [prefixWord, tailWord_4674435, baseEnd_4674435] using wordTrace_append hprefix tailTrace_4674435
  have hstable : (prefixWord ++ tailWord_4674435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674435).length < 2 ^ (prefixWord ++ tailWord_4674435).sum := by decide
  have hdescent : baseEnd_4674435 < baseStart_4674435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674441 : List Nat := [1, 2, 1, 1, 5, 2, 1, 2, 3, 1, 4]
def baseStart_4674441 : Nat := 118140960795 + 4674441 * 2 ^ 59
def prefixEnd_4674441 : Nat := 4983230072969 + 3 ^ 40 * 4674441 * 2
def baseEnd_4674441 : Nat := 2400235024083450961790143

theorem tailTrace_4674441 : CollatzResearch.WordTrace tailWord_4674441 prefixEnd_4674441 2400235024083450961790143 := by
  unfold tailWord_4674441
  simp only [CollatzResearch.WordTrace]
  refine ⟨170490869658306062809535177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113660579772204041873023451 170490869658306062809535177)
  ·
    refine ⟨127868152243729547107151383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170490869658306062809535177 127868152243729547107151383)
    ·
      refine ⟨191802228365594320660727075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127868152243729547107151383 191802228365594320660727075)
      ·
        refine ⟨287703342548391480991090613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191802228365594320660727075 287703342548391480991090613)
        ·
          refine ⟨26972188363911701342914745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 287703342548391480991090613 26972188363911701342914745)
          ·
            refine ⟨20229141272933776007186059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26972188363911701342914745 20229141272933776007186059)
            ·
              refine ⟨30343711909400664010779089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20229141272933776007186059 30343711909400664010779089)
              ·
                refine ⟨22757783932050498008084317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30343711909400664010779089 22757783932050498008084317)
                ·
                  refine ⟨8534168974518936753031619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22757783932050498008084317 8534168974518936753031619)
                  ·
                    refine ⟨12801253461778405129547429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8534168974518936753031619 12801253461778405129547429)
                    ·
                      refine ⟨2400235024083450961790143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12801253461778405129547429 2400235024083450961790143)
                      ·
                        rfl

theorem cell23_4674441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 1, 4].length) (baseStart_4674441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674441 prefixEnd_4674441 := by exact prefixLift 4674441
  have htrace : WordTrace (prefixWord ++ tailWord_4674441) baseStart_4674441 baseEnd_4674441 := by
    simpa [prefixWord, tailWord_4674441, baseEnd_4674441] using wordTrace_append hprefix tailTrace_4674441
  have hstable : (prefixWord ++ tailWord_4674441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674441).length < 2 ^ (prefixWord ++ tailWord_4674441).sum := by decide
  have hdescent : baseEnd_4674441 < baseStart_4674441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674464 : List Nat := [2, 1, 1, 4, 1, 1, 2, 11]
def baseStart_4674464 : Nat := 118140960795 + 4674464 * 2 ^ 59
def prefixEnd_4674464 : Nat := 4983230072969 + 3 ^ 40 * 4674464 * 2
def baseEnd_4674464 : Nat := 88898030894018680437131

theorem tailTrace_4674464 : CollatzResearch.WordTrace tailWord_4674464 prefixEnd_4674464 88898030894018680437131 := by
  unfold tailWord_4674464
  simp only [CollatzResearch.WordTrace]
  refine ⟨85245854268611368868811223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113661139024815158491748297 85245854268611368868811223)
  ·
    refine ⟨127868781402917053303216835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85245854268611368868811223 127868781402917053303216835)
    ·
      refine ⟨191803172104375579954825253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127868781402917053303216835 191803172104375579954825253)
      ·
        refine ⟨35963094769570421241529735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 191803172104375579954825253 35963094769570421241529735)
        ·
          refine ⟨53944642154355631862294603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35963094769570421241529735 53944642154355631862294603)
          ·
            refine ⟨80916963231533447793441905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53944642154355631862294603 80916963231533447793441905)
            ·
              refine ⟨60687722423650085845081429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80916963231533447793441905 60687722423650085845081429)
              ·
                refine ⟨88898030894018680437131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 60687722423650085845081429 88898030894018680437131)
                ·
                  rfl

theorem cell23_4674464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 11].length) (baseStart_4674464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674464 prefixEnd_4674464 := by exact prefixLift 4674464
  have htrace : WordTrace (prefixWord ++ tailWord_4674464) baseStart_4674464 baseEnd_4674464 := by
    simpa [prefixWord, tailWord_4674464, baseEnd_4674464] using wordTrace_append hprefix tailTrace_4674464
  have hstable : (prefixWord ++ tailWord_4674464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674464).length < 2 ^ (prefixWord ++ tailWord_4674464).sum := by decide
  have hdescent : baseEnd_4674464 < baseStart_4674464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674481 : List Nat := [1, 2, 2, 4, 3, 1, 10]
def baseStart_4674481 : Nat := 118140960795 + 4674481 * 2 ^ 59
def prefixEnd_4674481 : Nat := 4983230072969 + 3 ^ 40 * 4674481 * 2
def baseEnd_4674481 : Nat := 29632784732217664262839

theorem tailTrace_4674481 : CollatzResearch.WordTrace tailWord_4674481 prefixEnd_4674481 29632784732217664262839 := by
  unfold tailWord_4674481
  simp only [CollatzResearch.WordTrace]
  refine ⟨170492328578161149640991297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113661552385440766427327531 170492328578161149640991297)
  ·
    refine ⟨127869246433620862230743473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170492328578161149640991297 127869246433620862230743473)
    ·
      refine ⟨95901934825215646673057605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127869246433620862230743473 95901934825215646673057605)
      ·
        refine ⟨17981612779727933751198301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95901934825215646673057605 17981612779727933751198301)
        ·
          refine ⟨6743104792397975156699363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17981612779727933751198301 6743104792397975156699363)
          ·
            refine ⟨10114657188596962735049045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6743104792397975156699363 10114657188596962735049045)
            ·
              refine ⟨29632784732217664262839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10114657188596962735049045 29632784732217664262839)
              ·
                rfl

theorem cell23_4674481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 10].length) (baseStart_4674481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674481 prefixEnd_4674481 := by exact prefixLift 4674481
  have htrace : WordTrace (prefixWord ++ tailWord_4674481) baseStart_4674481 baseEnd_4674481 := by
    simpa [prefixWord, tailWord_4674481, baseEnd_4674481] using wordTrace_append hprefix tailTrace_4674481
  have hstable : (prefixWord ++ tailWord_4674481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674481).length < 2 ^ (prefixWord ++ tailWord_4674481).sum := by decide
  have hdescent : baseEnd_4674481 < baseStart_4674481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674486 : List Nat := [5, 1, 4, 1, 1, 1, 2, 1, 3, 1, 3]
def baseStart_4674486 : Nat := 118140960795 + 4674486 * 2 ^ 59
def prefixEnd_4674486 : Nat := 4983230072969 + 3 ^ 40 * 4674486 * 2
def baseEnd_4674486 : Nat := 2400258130712903285727437

theorem tailTrace_4674486 : CollatzResearch.WordTrace tailWord_4674486 prefixEnd_4674486 2400258130712903285727437 := by
  unfold tailWord_4674486
  simp only [CollatzResearch.WordTrace]
  refine ⟨10655781933946439718432707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113661673962095356996615541 10655781933946439718432707)
  ·
    refine ⟨15983672900919659577649061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10655781933946439718432707 15983672900919659577649061)
    ·
      refine ⟨2996938668922436170809199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15983672900919659577649061 2996938668922436170809199)
      ·
        refine ⟨4495408003383654256213799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2996938668922436170809199 4495408003383654256213799)
        ·
          refine ⟨6743112005075481384320699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4495408003383654256213799 6743112005075481384320699)
          ·
            refine ⟨10114668007613222076481049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6743112005075481384320699 10114668007613222076481049)
            ·
              refine ⟨7586001005709916557360787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10114668007613222076481049 7586001005709916557360787)
              ·
                refine ⟨11379001508564874836041181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7586001005709916557360787 11379001508564874836041181)
                ·
                  refine ⟨4267125565711828063515443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11379001508564874836041181 4267125565711828063515443)
                  ·
                    refine ⟨6400688348567742095273165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4267125565711828063515443 6400688348567742095273165)
                    ·
                      refine ⟨2400258130712903285727437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6400688348567742095273165 2400258130712903285727437)
                      ·
                        rfl

theorem cell23_4674486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_4674486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674486 prefixEnd_4674486 := by exact prefixLift 4674486
  have htrace : WordTrace (prefixWord ++ tailWord_4674486) baseStart_4674486 baseEnd_4674486 := by
    simpa [prefixWord, tailWord_4674486, baseEnd_4674486] using wordTrace_append hprefix tailTrace_4674486
  have hstable : (prefixWord ++ tailWord_4674486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674486).length < 2 ^ (prefixWord ++ tailWord_4674486).sum := by decide
  have hdescent : baseEnd_4674486 < baseStart_4674486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674521 : List Nat := [1, 2, 1, 2, 5, 1, 1, 1, 2, 2, 5]
def baseStart_4674521 : Nat := 118140960795 + 4674521 * 2 ^ 59
def prefixEnd_4674521 : Nat := 4983230072969 + 3 ^ 40 * 4674521 * 2
def baseEnd_4674521 : Nat := 2400276102535810648789775

theorem tailTrace_4674521 : CollatzResearch.WordTrace tailWord_4674521 prefixEnd_4674521 2400276102535810648789775 := by
  unfold tailWord_4674521
  simp only [CollatzResearch.WordTrace]
  refine ⟨170493787498016236472447417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113662524998677490981631611 170493787498016236472447417)
  ·
    refine ⟨127870340623512177354335563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170493787498016236472447417 127870340623512177354335563)
    ·
      refine ⟨191805510935268266031503345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127870340623512177354335563 191805510935268266031503345)
      ·
        refine ⟨143854133201451199523627509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191805510935268266031503345 143854133201451199523627509)
        ·
          refine ⟨13486324987636049955340079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 143854133201451199523627509 13486324987636049955340079)
          ·
            refine ⟨20229487481454074933010119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13486324987636049955340079 20229487481454074933010119)
            ·
              refine ⟨30344231222181112399515179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20229487481454074933010119 30344231222181112399515179)
              ·
                refine ⟨45516346833271668599272769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30344231222181112399515179 45516346833271668599272769)
                ·
                  refine ⟨34137260124953751449454577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45516346833271668599272769 34137260124953751449454577)
                  ·
                    refine ⟨25602945093715313587090933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34137260124953751449454577 25602945093715313587090933)
                    ·
                      refine ⟨2400276102535810648789775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25602945093715313587090933 2400276102535810648789775)
                      ·
                        rfl

theorem cell23_4674521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_4674521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674521 prefixEnd_4674521 := by exact prefixLift 4674521
  have htrace : WordTrace (prefixWord ++ tailWord_4674521) baseStart_4674521 baseEnd_4674521 := by
    simpa [prefixWord, tailWord_4674521, baseEnd_4674521] using wordTrace_append hprefix tailTrace_4674521
  have hstable : (prefixWord ++ tailWord_4674521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674521).length < 2 ^ (prefixWord ++ tailWord_4674521).sum := by decide
  have hdescent : baseEnd_4674521 < baseStart_4674521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674525 : List Nat := [1, 4, 3, 1, 2, 1, 1, 2, 4, 1, 3]
def baseStart_4674525 : Nat := 118140960795 + 4674525 * 2 ^ 59
def prefixEnd_4674525 : Nat := 4983230072969 + 3 ^ 40 * 4674525 * 2
def baseEnd_4674525 : Nat := 2400278156458428633139757

theorem tailTrace_4674525 : CollatzResearch.WordTrace tailWord_4674525 prefixEnd_4674525 2400278156458428633139757 := by
  unfold tailWord_4674525
  simp only [CollatzResearch.WordTrace]
  refine ⟨170493933390001745155593029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113662622260001163437062019 170493933390001745155593029)
  ·
    refine ⟨31967612510625327216673693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170493933390001745155593029 31967612510625327216673693)
    ·
      refine ⟨11987854691484497706252635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31967612510625327216673693 11987854691484497706252635)
      ·
        refine ⟨17981782037226746559378953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11987854691484497706252635 17981782037226746559378953)
        ·
          refine ⟨13486336527920059919534215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17981782037226746559378953 13486336527920059919534215)
          ·
            refine ⟨20229504791880089879301323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13486336527920059919534215 20229504791880089879301323)
            ·
              refine ⟨30344257187820134818951985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20229504791880089879301323 30344257187820134818951985)
              ·
                refine ⟨22758192890865101114213989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30344257187820134818951985 22758192890865101114213989)
                ·
                  refine ⟨4267161167037206458915123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22758192890865101114213989 4267161167037206458915123)
                  ·
                    refine ⟨6400741750555809688372685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4267161167037206458915123 6400741750555809688372685)
                    ·
                      refine ⟨2400278156458428633139757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6400741750555809688372685 2400278156458428633139757)
                      ·
                        rfl

theorem cell23_4674525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_4674525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674525 prefixEnd_4674525 := by exact prefixLift 4674525
  have htrace : WordTrace (prefixWord ++ tailWord_4674525) baseStart_4674525 baseEnd_4674525 := by
    simpa [prefixWord, tailWord_4674525, baseEnd_4674525] using wordTrace_append hprefix tailTrace_4674525
  have hstable : (prefixWord ++ tailWord_4674525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674525).length < 2 ^ (prefixWord ++ tailWord_4674525).sum := by decide
  have hdescent : baseEnd_4674525 < baseStart_4674525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674599 : List Nat := [1, 1, 7, 1, 1, 1, 1, 4, 2, 2, 2]
def baseStart_4674599 : Nat := 118140960795 + 4674599 * 2 ^ 59
def prefixEnd_4674599 : Nat := 4983230072969 + 3 ^ 40 * 4674599 * 2
def baseEnd_4674599 : Nat := 2400316154026861343614417

theorem tailTrace_4674599 : CollatzResearch.WordTrace tailWord_4674599 prefixEnd_4674599 2400316154026861343614417 := by
  unfold tailWord_4674599
  simp only [CollatzResearch.WordTrace]
  refine ⟨170496632391733655793786851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113664421594489103862524567 170496632391733655793786851)
  ·
    refine ⟨255744948587600483690680277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170496632391733655793786851 255744948587600483690680277)
    ·
      refine ⟨5994022232521886336500319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 255744948587600483690680277 5994022232521886336500319)
      ·
        refine ⟨8991033348782829504750479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5994022232521886336500319 8991033348782829504750479)
        ·
          refine ⟨13486550023174244257125719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8991033348782829504750479 13486550023174244257125719)
          ·
            refine ⟨20229825034761366385688579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13486550023174244257125719 20229825034761366385688579)
            ·
              refine ⟨30344737552142049578532869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20229825034761366385688579 30344737552142049578532869)
              ·
                refine ⟨5689638291026634295974913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30344737552142049578532869 5689638291026634295974913)
                ·
                  refine ⟨4267228718269975721981185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5689638291026634295974913 4267228718269975721981185)
                  ·
                    refine ⟨3200421538702481791485889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4267228718269975721981185 3200421538702481791485889)
                    ·
                      refine ⟨2400316154026861343614417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3200421538702481791485889 2400316154026861343614417)
                      ·
                        rfl

theorem cell23_4674599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_4674599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674599 prefixEnd_4674599 := by exact prefixLift 4674599
  have htrace : WordTrace (prefixWord ++ tailWord_4674599) baseStart_4674599 baseEnd_4674599 := by
    simpa [prefixWord, tailWord_4674599, baseEnd_4674599] using wordTrace_append hprefix tailTrace_4674599
  have hstable : (prefixWord ++ tailWord_4674599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674599).length < 2 ^ (prefixWord ++ tailWord_4674599).sum := by decide
  have hdescent : baseEnd_4674599 < baseStart_4674599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674608 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 1, 7, 2]
def baseStart_4674608 : Nat := 118140960795 + 4674608 * 2 ^ 59
def prefixEnd_4674608 : Nat := 4983230072969 + 3 ^ 40 * 4674608 * 2
def baseEnd_4674608 : Nat := 2400320775352751808401875

theorem tailTrace_4674608 : CollatzResearch.WordTrace tailWord_4674608 prefixEnd_4674608 2400320775352751808401875 := by
  unfold tailWord_4674608
  simp only [CollatzResearch.WordTrace]
  refine ⟨85248480324350525165432239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113664640432467366887242985 85248480324350525165432239)
  ·
    refine ⟨127872720486525787748148359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85248480324350525165432239 127872720486525787748148359)
    ·
      refine ⟨191809080729788681622222539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127872720486525787748148359 191809080729788681622222539)
      ·
        refine ⟨287713621094683022433333809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191809080729788681622222539 287713621094683022433333809)
        ·
          refine ⟨215785215821012266825000357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287713621094683022433333809 215785215821012266825000357)
          ·
            refine ⟨40459727966439800029687567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 215785215821012266825000357 40459727966439800029687567)
            ·
              refine ⟨60689591949659700044531351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40459727966439800029687567 60689591949659700044531351)
              ·
                refine ⟨91034387924489550066797027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60689591949659700044531351 91034387924489550066797027)
                ·
                  refine ⟨136551581886734325100195541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91034387924489550066797027 136551581886734325100195541)
                  ·
                    refine ⟨3200427700470335744535833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 136551581886734325100195541 3200427700470335744535833)
                    ·
                      refine ⟨2400320775352751808401875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3200427700470335744535833 2400320775352751808401875)
                      ·
                        rfl

theorem cell23_4674608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 1, 7, 2].length) (baseStart_4674608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674608 prefixEnd_4674608 := by exact prefixLift 4674608
  have htrace : WordTrace (prefixWord ++ tailWord_4674608) baseStart_4674608 baseEnd_4674608 := by
    simpa [prefixWord, tailWord_4674608, baseEnd_4674608] using wordTrace_append hprefix tailTrace_4674608
  have hstable : (prefixWord ++ tailWord_4674608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674608).length < 2 ^ (prefixWord ++ tailWord_4674608).sum := by decide
  have hdescent : baseEnd_4674608 < baseStart_4674608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674638 : List Nat := [4, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4]
def baseStart_4674638 : Nat := 118140960795 + 4674638 * 2 ^ 59
def prefixEnd_4674638 : Nat := 4983230072969 + 3 ^ 40 * 4674638 * 2
def baseEnd_4674638 : Nat := 2400336179772386691026737

theorem tailTrace_4674638 : CollatzResearch.WordTrace tailWord_4674638 prefixEnd_4674638 2400336179772386691026737 := by
  unfold tailWord_4674638
  simp only [CollatzResearch.WordTrace]
  refine ⟨21312256854824045681807071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113665369892394910302971045 21312256854824045681807071)
  ·
    refine ⟨31968385282236068522710607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21312256854824045681807071 31968385282236068522710607)
    ·
      refine ⟨47952577923354102784065911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31968385282236068522710607 47952577923354102784065911)
      ·
        refine ⟨71928866885031154176098867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47952577923354102784065911 71928866885031154176098867)
        ·
          refine ⟨107893300327546731264148301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71928866885031154176098867 107893300327546731264148301)
          ·
            refine ⟨40459987622830024224055613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107893300327546731264148301 40459987622830024224055613)
            ·
              refine ⟨15172495358561259084020855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40459987622830024224055613 15172495358561259084020855)
              ·
                refine ⟨22758743037841888626031283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15172495358561259084020855 22758743037841888626031283)
                ·
                  refine ⟨34138114556762832939046925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22758743037841888626031283 34138114556762832939046925)
                  ·
                    refine ⟨12801792958786062352142597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34138114556762832939046925 12801792958786062352142597)
                    ·
                      refine ⟨2400336179772386691026737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12801792958786062352142597 2400336179772386691026737)
                      ·
                        rfl

theorem cell23_4674638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_4674638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674638 prefixEnd_4674638 := by exact prefixLift 4674638
  have htrace : WordTrace (prefixWord ++ tailWord_4674638) baseStart_4674638 baseEnd_4674638 := by
    simpa [prefixWord, tailWord_4674638, baseEnd_4674638] using wordTrace_append hprefix tailTrace_4674638
  have hstable : (prefixWord ++ tailWord_4674638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674638).length < 2 ^ (prefixWord ++ tailWord_4674638).sum := by decide
  have hdescent : baseEnd_4674638 < baseStart_4674638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674648 : List Nat := [2, 1, 2, 2, 1, 3, 1, 2, 5, 4]
def baseStart_4674648 : Nat := 118140960795 + 4674648 * 2 ^ 59
def prefixEnd_4674648 : Nat := 4983230072969 + 3 ^ 40 * 4674648 * 2
def baseEnd_4674648 : Nat := 800113771526310550633897

theorem tailTrace_4674648 : CollatzResearch.WordTrace tailWord_4674648 prefixEnd_4674648 800113771526310550633897 := by
  unfold tailWord_4674648
  simp only [CollatzResearch.WordTrace]
  refine ⟨85249209784278068581160299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113665613045704091441547065 85249209784278068581160299)
  ·
    refine ⟨127873814676417102871740449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85249209784278068581160299 127873814676417102871740449)
    ·
      refine ⟨95905361007312827153805337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127873814676417102871740449 95905361007312827153805337)
      ·
        refine ⟨71929020755484620365354003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95905361007312827153805337 71929020755484620365354003)
        ·
          refine ⟨107893531133226930548031005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71929020755484620365354003 107893531133226930548031005)
          ·
            refine ⟨40460074174960098955511627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107893531133226930548031005 40460074174960098955511627)
            ·
              refine ⟨60690111262440148433267441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40460074174960098955511627 60690111262440148433267441)
              ·
                refine ⟨45517583446830111324950581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60690111262440148433267441 45517583446830111324950581)
                ·
                  refine ⟨4267273448140322936714117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45517583446830111324950581 4267273448140322936714117)
                  ·
                    refine ⟨800113771526310550633897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4267273448140322936714117 800113771526310550633897)
                    ·
                      rfl

theorem cell23_4674648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 5, 4].length) (baseStart_4674648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674648 prefixEnd_4674648 := by exact prefixLift 4674648
  have htrace : WordTrace (prefixWord ++ tailWord_4674648) baseStart_4674648 baseEnd_4674648 := by
    simpa [prefixWord, tailWord_4674648, baseEnd_4674648] using wordTrace_append hprefix tailTrace_4674648
  have hstable : (prefixWord ++ tailWord_4674648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674648).length < 2 ^ (prefixWord ++ tailWord_4674648).sum := by decide
  have hdescent : baseEnd_4674648 < baseStart_4674648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674665 : List Nat := [1, 2, 1, 1, 1, 7, 2, 1, 3, 4]
def baseStart_4674665 : Nat := 118140960795 + 4674665 * 2 ^ 59
def prefixEnd_4674665 : Nat := 4983230072969 + 3 ^ 40 * 4674665 * 2
def baseEnd_4674665 : Nat := 800116681250019361796371

theorem tailTrace_4674665 : CollatzResearch.WordTrace tailWord_4674665 prefixEnd_4674665 800116681250019361796371 := by
  unfold tailWord_4674665
  simp only [CollatzResearch.WordTrace]
  refine ⟨170499039609494549065689449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113666026406329699377126299 170499039609494549065689449)
  ·
    refine ⟨127874279707120911799267087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170499039609494549065689449 127874279707120911799267087)
    ·
      refine ⟨191811419560681367698900631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127874279707120911799267087 191811419560681367698900631)
      ·
        refine ⟨287717129341022051548350947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191811419560681367698900631 287717129341022051548350947)
        ·
          refine ⟨431575694011533077322526421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287717129341022051548350947 431575694011533077322526421)
          ·
            refine ⟨10115055328395306499746713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 431575694011533077322526421 10115055328395306499746713)
            ·
              refine ⟨7586291496296479874810035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10115055328395306499746713 7586291496296479874810035)
              ·
                refine ⟨11379437244444719812215053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7586291496296479874810035 11379437244444719812215053)
                ·
                  refine ⟨4267288966666769929580645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11379437244444719812215053 4267288966666769929580645)
                  ·
                    refine ⟨800116681250019361796371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4267288966666769929580645 800116681250019361796371)
                    ·
                      rfl

theorem cell23_4674665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 3, 4].length) (baseStart_4674665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674665 prefixEnd_4674665 := by exact prefixLift 4674665
  have htrace : WordTrace (prefixWord ++ tailWord_4674665) baseStart_4674665 baseEnd_4674665 := by
    simpa [prefixWord, tailWord_4674665, baseEnd_4674665] using wordTrace_append hprefix tailTrace_4674665
  have hstable : (prefixWord ++ tailWord_4674665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674665).length < 2 ^ (prefixWord ++ tailWord_4674665).sum := by decide
  have hdescent : baseEnd_4674665 < baseStart_4674665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674745 : List Nat := [1, 2, 1, 4, 1, 4, 1, 1, 3, 1, 4]
def baseStart_4674745 : Nat := 118140960795 + 4674745 * 2 ^ 59
def prefixEnd_4674745 : Nat := 4983230072969 + 3 ^ 40 * 4674745 * 2
def baseEnd_4674745 : Nat := 2400391122202417772388745

theorem tailTrace_4674745 : CollatzResearch.WordTrace tailWord_4674745 prefixEnd_4674745 2400391122202417772388745 := by
  unfold tailWord_4674745
  simp only [CollatzResearch.WordTrace]
  refine ⟨170501957449204722728601689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113667971632803148485734459 170501957449204722728601689)
  ·
    refine ⟨127876468086903542046451267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170501957449204722728601689 127876468086903542046451267)
    ·
      refine ⟨191814702130355313069676901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127876468086903542046451267 191814702130355313069676901)
      ·
        refine ⟨35965256649441621200564419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 191814702130355313069676901 35965256649441621200564419)
        ·
          refine ⟨53947884974162431800846629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35965256649441621200564419 53947884974162431800846629)
          ·
            refine ⟨10115228432655455962658743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53947884974162431800846629 10115228432655455962658743)
            ·
              refine ⟨15172842648983183943988115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10115228432655455962658743 15172842648983183943988115)
              ·
                refine ⟨22759263973474775915982173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15172842648983183943988115 22759263973474775915982173)
                ·
                  refine ⟨8534723990053040968493315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22759263973474775915982173 8534723990053040968493315)
                  ·
                    refine ⟨12802085985079561452739973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8534723990053040968493315 12802085985079561452739973)
                    ·
                      refine ⟨2400391122202417772388745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12802085985079561452739973 2400391122202417772388745)
                      ·
                        rfl

theorem cell23_4674745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_4674745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674745 prefixEnd_4674745 := by exact prefixLift 4674745
  have htrace : WordTrace (prefixWord ++ tailWord_4674745) baseStart_4674745 baseEnd_4674745 := by
    simpa [prefixWord, tailWord_4674745, baseEnd_4674745] using wordTrace_append hprefix tailTrace_4674745
  have hstable : (prefixWord ++ tailWord_4674745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674745).length < 2 ^ (prefixWord ++ tailWord_4674745).sum := by decide
  have hdescent : baseEnd_4674745 < baseStart_4674745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674773 : List Nat := [1, 3, 2, 4, 1, 3, 2, 2, 1, 1, 3]
def baseStart_4674773 : Nat := 118140960795 + 4674773 * 2 ^ 59
def prefixEnd_4674773 : Nat := 4983230072969 + 3 ^ 40 * 4674773 * 2
def baseEnd_4674773 : Nat := 2400405499660743662838617

theorem tailTrace_4674773 : CollatzResearch.WordTrace tailWord_4674773 prefixEnd_4674773 2400405499660743662838617 := by
  unfold tailWord_4674773
  simp only [CollatzResearch.WordTrace]
  refine ⟨170502978693103283510620973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113668652462068855673747315 170502978693103283510620973)
  ·
    refine ⟨63938617009913731316482865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170502978693103283510620973 63938617009913731316482865)
    ·
      refine ⟨47953962757435298487362149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63938617009913731316482865 47953962757435298487362149)
      ·
        refine ⟨8991368017019118466380403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47953962757435298487362149 8991368017019118466380403)
        ·
          refine ⟨13487052025528677699570605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8991368017019118466380403 13487052025528677699570605)
          ·
            refine ⟨5057644509573254137338977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13487052025528677699570605 5057644509573254137338977)
            ·
              refine ⟨3793233382179940603004233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5057644509573254137338977 3793233382179940603004233)
              ·
                refine ⟨2844925036634955452253175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3793233382179940603004233 2844925036634955452253175)
                ·
                  refine ⟨4267387554952433178379763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2844925036634955452253175 4267387554952433178379763)
                  ·
                    refine ⟨6401081332428649767569645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4267387554952433178379763 6401081332428649767569645)
                    ·
                      refine ⟨2400405499660743662838617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6401081332428649767569645 2400405499660743662838617)
                      ·
                        rfl

theorem cell23_4674773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_4674773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674773 prefixEnd_4674773 := by exact prefixLift 4674773
  have htrace : WordTrace (prefixWord ++ tailWord_4674773) baseStart_4674773 baseEnd_4674773 := by
    simpa [prefixWord, tailWord_4674773, baseEnd_4674773] using wordTrace_append hprefix tailTrace_4674773
  have hstable : (prefixWord ++ tailWord_4674773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674773).length < 2 ^ (prefixWord ++ tailWord_4674773).sum := by decide
  have hdescent : baseEnd_4674773 < baseStart_4674773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674785 : List Nat := [1, 2, 3, 1, 3, 4, 1, 8]
def baseStart_4674785 : Nat := 118140960795 + 4674785 * 2 ^ 59
def prefixEnd_4674785 : Nat := 4983230072969 + 3 ^ 40 * 4674785 * 2
def baseEnd_4674785 : Nat := 88904135608466578366243

theorem tailTrace_4674785 : CollatzResearch.WordTrace tailWord_4674785 prefixEnd_4674785 88904135608466578366243 := by
  unfold tailWord_4674785
  simp only [CollatzResearch.WordTrace]
  refine ⟨170503416369059809560057809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113668944246039873040038539 170503416369059809560057809)
  ·
    refine ⟨127877562276794857170043357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170503416369059809560057809 127877562276794857170043357)
    ·
      refine ⟨47954085853798071438766259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127877562276794857170043357 47954085853798071438766259)
      ·
        refine ⟨71931128780697107158149389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47954085853798071438766259 71931128780697107158149389)
        ·
          refine ⟨26974173292761415184306021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71931128780697107158149389 26974173292761415184306021)
          ·
            refine ⟨5057657492392765347057379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26974173292761415184306021 5057657492392765347057379)
            ·
              refine ⟨7586486238589148020586069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5057657492392765347057379 7586486238589148020586069)
              ·
                refine ⟨88904135608466578366243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7586486238589148020586069 88904135608466578366243)
                ·
                  rfl

theorem cell23_4674785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 8].length) (baseStart_4674785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674785 prefixEnd_4674785 := by exact prefixLift 4674785
  have htrace : WordTrace (prefixWord ++ tailWord_4674785) baseStart_4674785 baseEnd_4674785 := by
    simpa [prefixWord, tailWord_4674785, baseEnd_4674785] using wordTrace_append hprefix tailTrace_4674785
  have hstable : (prefixWord ++ tailWord_4674785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674785).length < 2 ^ (prefixWord ++ tailWord_4674785).sum := by decide
  have hdescent : baseEnd_4674785 < baseStart_4674785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674788 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 2, 2, 6]
def baseStart_4674788 : Nat := 118140960795 + 4674788 * 2 ^ 59
def prefixEnd_4674788 : Nat := 4983230072969 + 3 ^ 40 * 4674788 * 2
def baseEnd_4674788 : Nat := 2400413201870561104151047

theorem tailTrace_4674788 : CollatzResearch.WordTrace tailWord_4674788 prefixEnd_4674788 2400413201870561104151047 := by
  unfold tailWord_4674788
  simp only [CollatzResearch.WordTrace]
  refine ⟨85251762894024470536208509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113669017192032627381611345 85251762894024470536208509)
  ·
    refine ⟨31969411085259176451078191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85251762894024470536208509 31969411085259176451078191)
    ·
      refine ⟨47954116627888764676617287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31969411085259176451078191 47954116627888764676617287)
      ·
        refine ⟨71931174941833147014925931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47954116627888764676617287 71931174941833147014925931)
        ·
          refine ⟨107896762412749720522388897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71931174941833147014925931 107896762412749720522388897)
          ·
            refine ⟨80922571809562290391791673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107896762412749720522388897 80922571809562290391791673)
            ·
              refine ⟨60691928857171717793843755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80922571809562290391791673 60691928857171717793843755)
              ·
                refine ⟨91037893285757576690765633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60691928857171717793843755 91037893285757576690765633)
                ·
                  refine ⟨68278419964318182518074225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91037893285757576690765633 68278419964318182518074225)
                  ·
                    refine ⟨51208814973238636888555669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68278419964318182518074225 51208814973238636888555669)
                    ·
                      refine ⟨2400413201870561104151047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51208814973238636888555669 2400413201870561104151047)
                      ·
                        rfl

theorem cell23_4674788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_4674788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674788 prefixEnd_4674788 := by exact prefixLift 4674788
  have htrace : WordTrace (prefixWord ++ tailWord_4674788) baseStart_4674788 baseEnd_4674788 := by
    simpa [prefixWord, tailWord_4674788, baseEnd_4674788] using wordTrace_append hprefix tailTrace_4674788
  have hstable : (prefixWord ++ tailWord_4674788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674788).length < 2 ^ (prefixWord ++ tailWord_4674788).sum := by decide
  have hdescent : baseEnd_4674788 < baseStart_4674788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674795 : List Nat := [1, 1, 1, 1, 2, 6, 1, 3, 1, 3, 3]
def baseStart_4674795 : Nat := 118140960795 + 4674795 * 2 ^ 59
def prefixEnd_4674795 : Nat := 4983230072969 + 3 ^ 40 * 4674795 * 2
def baseEnd_4674795 : Nat := 2400416796235142576763515

theorem tailTrace_4674795 : CollatzResearch.WordTrace tailWord_4674795 prefixEnd_4674795 2400416796235142576763515 := by
  unfold tailWord_4674795
  simp only [CollatzResearch.WordTrace]
  refine ⟨170503781099023581267921839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113669187399349054178614559 170503781099023581267921839)
  ·
    refine ⟨255755671648535371901882759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170503781099023581267921839 255755671648535371901882759)
    ·
      refine ⟨383633507472803057852824139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255755671648535371901882759 383633507472803057852824139)
      ·
        refine ⟨575450261209204586779236209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383633507472803057852824139 575450261209204586779236209)
        ·
          refine ⟨431587695906903440084427157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 575450261209204586779236209 431587695906903440084427157)
          ·
            refine ⟨20230673245636098753957523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 431587695906903440084427157 20230673245636098753957523)
            ·
              refine ⟨30346009868454148130936285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20230673245636098753957523 30346009868454148130936285)
              ·
                refine ⟨11379753700670305549101107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30346009868454148130936285 11379753700670305549101107)
                ·
                  refine ⟨17069630551005458323651661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11379753700670305549101107 17069630551005458323651661)
                  ·
                    refine ⟨6401111456627046871369373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17069630551005458323651661 6401111456627046871369373)
                    ·
                      refine ⟨2400416796235142576763515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6401111456627046871369373 2400416796235142576763515)
                      ·
                        rfl

theorem cell23_4674795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 3, 3].length) (baseStart_4674795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674795 prefixEnd_4674795 := by exact prefixLift 4674795
  have htrace : WordTrace (prefixWord ++ tailWord_4674795) baseStart_4674795 baseEnd_4674795 := by
    simpa [prefixWord, tailWord_4674795, baseEnd_4674795] using wordTrace_append hprefix tailTrace_4674795
  have hstable : (prefixWord ++ tailWord_4674795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674795).length < 2 ^ (prefixWord ++ tailWord_4674795).sum := by decide
  have hdescent : baseEnd_4674795 < baseStart_4674795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674802 : List Nat := [3, 2, 1, 3, 3, 1, 3, 7]
def baseStart_4674802 : Nat := 118140960795 + 4674802 * 2 ^ 59
def prefixEnd_4674802 : Nat := 4983230072969 + 3 ^ 40 * 4674802 * 2
def baseEnd_4674802 : Nat := 88904458911100890717629

theorem tailTrace_4674802 : CollatzResearch.WordTrace tailWord_4674802 prefixEnd_4674802 88904458911100890717629 := by
  unfold tailWord_4674802
  simp only [CollatzResearch.WordTrace]
  refine ⟨42626009102499555365856665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113669357606665480975617773 42626009102499555365856665)
  ·
    refine ⟨31969506826874666524392499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42626009102499555365856665 31969506826874666524392499)
    ·
      refine ⟨47954260240311999786588749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31969506826874666524392499 47954260240311999786588749)
      ·
        refine ⟨17982847590116999919970781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47954260240311999786588749 17982847590116999919970781)
        ·
          refine ⟨6743567846293874969989043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17982847590116999919970781 6743567846293874969989043)
          ·
            refine ⟨10115351769440812454983565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6743567846293874969989043 10115351769440812454983565)
            ·
              refine ⟨3793256913540304670618837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10115351769440812454983565 3793256913540304670618837)
              ·
                refine ⟨88904458911100890717629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3793256913540304670618837 88904458911100890717629)
                ·
                  rfl

theorem cell23_4674802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 7].length) (baseStart_4674802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674802 prefixEnd_4674802 := by exact prefixLift 4674802
  have htrace : WordTrace (prefixWord ++ tailWord_4674802) baseStart_4674802 baseEnd_4674802 := by
    simpa [prefixWord, tailWord_4674802, baseEnd_4674802] using wordTrace_append hprefix tailTrace_4674802
  have hstable : (prefixWord ++ tailWord_4674802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674802).length < 2 ^ (prefixWord ++ tailWord_4674802).sum := by decide
  have hdescent : baseEnd_4674802 < baseStart_4674802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674835 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 2, 8, 2]
def baseStart_4674835 : Nat := 118140960795 + 4674835 * 2 ^ 59
def prefixEnd_4674835 : Nat := 4983230072969 + 3 ^ 40 * 4674835 * 2
def baseEnd_4674835 : Nat := 2400437335461322420263331

theorem tailTrace_4674835 : CollatzResearch.WordTrace tailWord_4674835 prefixEnd_4674835 2400437335461322420263331 := by
  unfold tailWord_4674835
  simp only [CollatzResearch.WordTrace]
  refine ⟨170505240018878668099377959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113670160012585778732918639 170505240018878668099377959)
  ·
    refine ⟨255757860028318002149066939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170505240018878668099377959 255757860028318002149066939)
    ·
      refine ⟨383636790042477003223600409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255757860028318002149066939 383636790042477003223600409)
      ·
        refine ⟨287727592531857752417700307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 383636790042477003223600409 287727592531857752417700307)
        ·
          refine ⟨431591388797786628626550461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287727592531857752417700307 431591388797786628626550461)
          ·
            refine ⟨161846770799169985734956423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 431591388797786628626550461 161846770799169985734956423)
            ·
              refine ⟨242770156198754978602434635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161846770799169985734956423 242770156198754978602434635)
              ·
                refine ⟨364155234298132467903651953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 242770156198754978602434635 364155234298132467903651953)
                ·
                  refine ⟨273116425723599350927738965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 364155234298132467903651953 273116425723599350927738965)
                  ·
                    refine ⟨3200583113948429893684441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 273116425723599350927738965 3200583113948429893684441)
                    ·
                      refine ⟨2400437335461322420263331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3200583113948429893684441 2400437335461322420263331)
                      ·
                        rfl

theorem cell23_4674835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 8, 2].length) (baseStart_4674835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674835 prefixEnd_4674835 := by exact prefixLift 4674835
  have htrace : WordTrace (prefixWord ++ tailWord_4674835) baseStart_4674835 baseEnd_4674835 := by
    simpa [prefixWord, tailWord_4674835, baseEnd_4674835] using wordTrace_append hprefix tailTrace_4674835
  have hstable : (prefixWord ++ tailWord_4674835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674835).length < 2 ^ (prefixWord ++ tailWord_4674835).sum := by decide
  have hdescent : baseEnd_4674835 < baseStart_4674835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674856 : List Nat := [2, 1, 5, 1, 2, 2, 2, 2, 1, 3, 2]
def baseStart_4674856 : Nat := 118140960795 + 4674856 * 2 ^ 59
def prefixEnd_4674856 : Nat := 4983230072969 + 3 ^ 40 * 4674856 * 2
def baseEnd_4674856 : Nat := 2400448118555066838100735

theorem tailTrace_4674856 : CollatzResearch.WordTrace tailWord_4674856 prefixEnd_4674856 2400448118555066838100735 := by
  unfold tailWord_4674856
  simp only [CollatzResearch.WordTrace]
  refine ⟨85253002975901294342946211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113670670634535059123928281 85253002975901294342946211)
  ·
    refine ⟨127879504463851941514419317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85253002975901294342946211 127879504463851941514419317)
    ·
      refine ⟨11988703543486119516976811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 127879504463851941514419317 11988703543486119516976811)
      ·
        refine ⟨17983055315229179275465217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11988703543486119516976811 17983055315229179275465217)
        ·
          refine ⟨13487291486421884456598913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17983055315229179275465217 13487291486421884456598913)
          ·
            refine ⟨10115468614816413342449185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13487291486421884456598913 10115468614816413342449185)
            ·
              refine ⟨7586601461112310006836889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10115468614816413342449185 7586601461112310006836889)
              ·
                refine ⟨5689951095834232505127667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7586601461112310006836889 5689951095834232505127667)
                ·
                  refine ⟨8534926643751348757691501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5689951095834232505127667 8534926643751348757691501)
                  ·
                    refine ⟨3200597491406755784134313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8534926643751348757691501 3200597491406755784134313)
                    ·
                      refine ⟨2400448118555066838100735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3200597491406755784134313 2400448118555066838100735)
                      ·
                        rfl

theorem cell23_4674856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_4674856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674856 prefixEnd_4674856 := by exact prefixLift 4674856
  have htrace : WordTrace (prefixWord ++ tailWord_4674856) baseStart_4674856 baseEnd_4674856 := by
    simpa [prefixWord, tailWord_4674856, baseEnd_4674856] using wordTrace_append hprefix tailTrace_4674856
  have hstable : (prefixWord ++ tailWord_4674856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674856).length < 2 ^ (prefixWord ++ tailWord_4674856).sum := by decide
  have hdescent : baseEnd_4674856 < baseStart_4674856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674869 : List Nat := [1, 3, 3, 1, 2, 2, 1, 2, 4, 2, 2]
def baseStart_4674869 : Nat := 118140960795 + 4674869 * 2 ^ 59
def prefixEnd_4674869 : Nat := 4983230072969 + 3 ^ 40 * 4674869 * 2
def baseEnd_4674869 : Nat := 2400454793803575287238175

theorem tailTrace_4674869 : CollatzResearch.WordTrace tailWord_4674869 prefixEnd_4674869 2400454793803575287238175 := by
  unfold tailWord_4674869
  simp only [CollatzResearch.WordTrace]
  refine ⟨170506480100755491906115661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113670986733836994604077107 170506480100755491906115661)
  ·
    refine ⟨63939930037783309464793373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170506480100755491906115661 63939930037783309464793373)
    ·
      refine ⟨23977473764168741049297515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63939930037783309464793373 23977473764168741049297515)
      ·
        refine ⟨35966210646253111573946273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23977473764168741049297515 35966210646253111573946273)
        ·
          refine ⟨26974657984689833680459705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35966210646253111573946273 26974657984689833680459705)
          ·
            refine ⟨20230993488517375260344779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26974657984689833680459705 20230993488517375260344779)
            ·
              refine ⟨30346490232776062890517169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20230993488517375260344779 30346490232776062890517169)
              ·
                refine ⟨22759867674582047167887877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30346490232776062890517169 22759867674582047167887877)
                ·
                  refine ⟨4267475188984133843978977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22759867674582047167887877 4267475188984133843978977)
                  ·
                    refine ⟨3200606391738100382984233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4267475188984133843978977 3200606391738100382984233)
                    ·
                      refine ⟨2400454793803575287238175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3200606391738100382984233 2400454793803575287238175)
                      ·
                        rfl

theorem cell23_4674869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_4674869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674869 prefixEnd_4674869 := by exact prefixLift 4674869
  have htrace : WordTrace (prefixWord ++ tailWord_4674869) baseStart_4674869 baseEnd_4674869 := by
    simpa [prefixWord, tailWord_4674869, baseEnd_4674869] using wordTrace_append hprefix tailTrace_4674869
  have hstable : (prefixWord ++ tailWord_4674869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674869).length < 2 ^ (prefixWord ++ tailWord_4674869).sum := by decide
  have hdescent : baseEnd_4674869 < baseStart_4674869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674885 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 4, 3, 3]
def baseStart_4674885 : Nat := 118140960795 + 4674885 * 2 ^ 59
def prefixEnd_4674885 : Nat := 4983230072969 + 3 ^ 40 * 4674885 * 2
def baseEnd_4674885 : Nat := 2400463009494047224638101

theorem tailTrace_4674885 : CollatzResearch.WordTrace tailWord_4674885 prefixEnd_4674885 2400463009494047224638101 := by
  unfold tailWord_4674885
  simp only [CollatzResearch.WordTrace]
  refine ⟨170507063668697526638698109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113671375779131684425798739 170507063668697526638698109)
  ·
    refine ⟨63940148875761572489511791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170507063668697526638698109 63940148875761572489511791)
    ·
      refine ⟨95910223313642358734267687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63940148875761572489511791 95910223313642358734267687)
      ·
        refine ⟨143865334970463538101401531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95910223313642358734267687 143865334970463538101401531)
        ·
          refine ⟨215798002455695307152102297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143865334970463538101401531 215798002455695307152102297)
          ·
            refine ⟨161848501841771480364076723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215798002455695307152102297 161848501841771480364076723)
            ·
              refine ⟨242772752762657220546115085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161848501841771480364076723 242772752762657220546115085)
              ·
                refine ⟨91039782285996457704793157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 242772752762657220546115085 91039782285996457704793157)
                ·
                  refine ⟨17069959178624335819648717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91039782285996457704793157 17069959178624335819648717)
                  ·
                    refine ⟨6401234691984125932368269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17069959178624335819648717 6401234691984125932368269)
                    ·
                      refine ⟨2400463009494047224638101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6401234691984125932368269 2400463009494047224638101)
                      ·
                        rfl

theorem cell23_4674885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 3, 3].length) (baseStart_4674885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674885 prefixEnd_4674885 := by exact prefixLift 4674885
  have htrace : WordTrace (prefixWord ++ tailWord_4674885) baseStart_4674885 baseEnd_4674885 := by
    simpa [prefixWord, tailWord_4674885, baseEnd_4674885] using wordTrace_append hprefix tailTrace_4674885
  have hstable : (prefixWord ++ tailWord_4674885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674885).length < 2 ^ (prefixWord ++ tailWord_4674885).sum := by decide
  have hdescent : baseEnd_4674885 < baseStart_4674885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674892 : List Nat := [2, 2, 1, 3, 2, 4, 1, 1, 7]
def baseStart_4674892 : Nat := 118140960795 + 4674892 * 2 ^ 59
def prefixEnd_4674892 : Nat := 4983230072969 + 3 ^ 40 * 4674892 * 2
def baseEnd_4674892 : Nat := 266718511539847633027841

theorem tailTrace_4674892 : CollatzResearch.WordTrace tailWord_4674892 prefixEnd_4674892 266718511539847633027841 := by
  unfold tailWord_4674892
  simp only [CollatzResearch.WordTrace]
  refine ⟨85253659489836083417101465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113671545986448111222801953 85253659489836083417101465)
  ·
    refine ⟨63940244617377062562826099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85253659489836083417101465 63940244617377062562826099)
    ·
      refine ⟨95910366926065593844239149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63940244617377062562826099 95910366926065593844239149)
      ·
        refine ⟨35966387597274597691589681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95910366926065593844239149 35966387597274597691589681)
        ·
          refine ⟨26974790697955948268692261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35966387597274597691589681 26974790697955948268692261)
          ·
            refine ⟨5057773255866740300379799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26974790697955948268692261 5057773255866740300379799)
            ·
              refine ⟨7586659883800110450569699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5057773255866740300379799 7586659883800110450569699)
              ·
                refine ⟨11379989825700165675854549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7586659883800110450569699 11379989825700165675854549)
                ·
                  refine ⟨266718511539847633027841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11379989825700165675854549 266718511539847633027841)
                  ·
                    rfl

theorem cell23_4674892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 7].length) (baseStart_4674892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674892 prefixEnd_4674892 := by exact prefixLift 4674892
  have htrace : WordTrace (prefixWord ++ tailWord_4674892) baseStart_4674892 baseEnd_4674892 := by
    simpa [prefixWord, tailWord_4674892, baseEnd_4674892] using wordTrace_append hprefix tailTrace_4674892
  have hstable : (prefixWord ++ tailWord_4674892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674892).length < 2 ^ (prefixWord ++ tailWord_4674892).sum := by decide
  have hdescent : baseEnd_4674892 < baseStart_4674892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674903 : List Nat := [1, 1, 3, 2, 3, 4, 2, 1, 2, 2, 2]
def baseStart_4674903 : Nat := 118140960795 + 4674903 * 2 ^ 59
def prefixEnd_4674903 : Nat := 4983230072969 + 3 ^ 40 * 4674903 * 2
def baseEnd_4674903 : Nat := 2400472252145828154213019

theorem tailTrace_4674903 : CollatzResearch.WordTrace tailWord_4674903 prefixEnd_4674903 2400472252145828154213019 := by
  unfold tailWord_4674903
  simp only [CollatzResearch.WordTrace]
  refine ⟨170507720182632315712853363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113671813455088210475235575 170507720182632315712853363)
  ·
    refine ⟨255761580273948473569280045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170507720182632315712853363 255761580273948473569280045)
    ·
      refine ⟨95910592602730677588480017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255761580273948473569280045 95910592602730677588480017)
      ·
        refine ⟨71932944452048008191360013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95910592602730677588480017 71932944452048008191360013)
        ·
          refine ⟨26974854169518003071760005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71932944452048008191360013 26974854169518003071760005)
          ·
            refine ⟨5057785156784625575955001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26974854169518003071760005 5057785156784625575955001)
            ·
              refine ⟨3793338867588469181966251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5057785156784625575955001 3793338867588469181966251)
              ·
                refine ⟨5690008301382703772949377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3793338867588469181966251 5690008301382703772949377)
                ·
                  refine ⟨4267506226037027829712033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5690008301382703772949377 4267506226037027829712033)
                  ·
                    refine ⟨3200629669527770872284025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4267506226037027829712033 3200629669527770872284025)
                    ·
                      refine ⟨2400472252145828154213019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3200629669527770872284025 2400472252145828154213019)
                      ·
                        rfl

theorem cell23_4674903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 2, 2, 2].length) (baseStart_4674903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674903 prefixEnd_4674903 := by exact prefixLift 4674903
  have htrace : WordTrace (prefixWord ++ tailWord_4674903) baseStart_4674903 baseEnd_4674903 := by
    simpa [prefixWord, tailWord_4674903, baseEnd_4674903] using wordTrace_append hprefix tailTrace_4674903
  have hstable : (prefixWord ++ tailWord_4674903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674903).length < 2 ^ (prefixWord ++ tailWord_4674903).sum := by decide
  have hdescent : baseEnd_4674903 < baseStart_4674903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4674946 : List Nat := [3, 4, 2, 1, 1, 1, 1, 1, 2, 5, 2]
def baseStart_4674946 : Nat := 118140960795 + 4674946 * 2 ^ 59
def prefixEnd_4674946 : Nat := 4983230072969 + 3 ^ 40 * 4674946 * 2
def baseEnd_4674946 : Nat := 2400494331813971485975321

theorem tailTrace_4674946 : CollatzResearch.WordTrace tailWord_4674946 prefixEnd_4674946 2400494331813971485975321 := by
  unfold tailWord_4674946
  simp only [CollatzResearch.WordTrace]
  refine ⟨42627322130369133514167173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113672859014317689371112461 42627322130369133514167173)
  ·
    refine ⟨7992622899444212533906345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42627322130369133514167173 7992622899444212533906345)
    ·
      refine ⟨5994467174583159400429759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7992622899444212533906345 5994467174583159400429759)
      ·
        refine ⟨8991700761874739100644639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5994467174583159400429759 8991700761874739100644639)
        ·
          refine ⟨13487551142812108650966959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8991700761874739100644639 13487551142812108650966959)
          ·
            refine ⟨20231326714218162976450439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13487551142812108650966959 20231326714218162976450439)
            ·
              refine ⟨30346990071327244464675659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20231326714218162976450439 30346990071327244464675659)
              ·
                refine ⟨45520485106990866697013489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30346990071327244464675659 45520485106990866697013489)
                ·
                  refine ⟨34140363830243150022760117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45520485106990866697013489 34140363830243150022760117)
                  ·
                    refine ⟨3200659109085295314633761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34140363830243150022760117 3200659109085295314633761)
                    ·
                      refine ⟨2400494331813971485975321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3200659109085295314633761 2400494331813971485975321)
                      ·
                        rfl

theorem cell23_4674946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_4674946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4674946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4674946 prefixEnd_4674946 := by exact prefixLift 4674946
  have htrace : WordTrace (prefixWord ++ tailWord_4674946) baseStart_4674946 baseEnd_4674946 := by
    simpa [prefixWord, tailWord_4674946, baseEnd_4674946] using wordTrace_append hprefix tailTrace_4674946
  have hstable : (prefixWord ++ tailWord_4674946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4674946).length < 2 ^ (prefixWord ++ tailWord_4674946).sum := by decide
  have hdescent : baseEnd_4674946 < baseStart_4674946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4674946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675029 : List Nat := [1, 3, 2, 3, 1, 1, 4, 2, 1, 5]
def baseStart_4675029 : Nat := 118140960795 + 4675029 * 2 ^ 59
def prefixEnd_4675029 : Nat := 4983230072969 + 3 ^ 40 * 4675029 * 2
def baseEnd_4675029 : Nat := 800178983569431553745813

theorem tailTrace_4675029 : CollatzResearch.WordTrace tailWord_4675029 prefixEnd_4675029 800178983569431553745813 := by
  unfold tailWord_4675029
  simp only [CollatzResearch.WordTrace]
  refine ⟨170512315780175839231940141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113674877186783892821293427 170512315780175839231940141)
  ·
    refine ⟨63942118417565939711977553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170512315780175839231940141 63942118417565939711977553)
    ·
      refine ⟨47956588813174454783983165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63942118417565939711977553 47956588813174454783983165)
      ·
        refine ⟨17983720804940420543993687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47956588813174454783983165 17983720804940420543993687)
        ·
          refine ⟨26975581207410630815990531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17983720804940420543993687 26975581207410630815990531)
          ·
            refine ⟨40463371811115946223985797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26975581207410630815990531 40463371811115946223985797)
            ·
              refine ⟨7586882214584239916997337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40463371811115946223985797 7586882214584239916997337)
              ·
                refine ⟨5690161660938179937748003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7586882214584239916997337 5690161660938179937748003)
                ·
                  refine ⟨8535242491407269906622005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5690161660938179937748003 8535242491407269906622005)
                  ·
                    refine ⟨800178983569431553745813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8535242491407269906622005 800178983569431553745813)
                    ·
                      rfl

theorem cell23_4675029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_4675029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675029 prefixEnd_4675029 := by exact prefixLift 4675029
  have htrace : WordTrace (prefixWord ++ tailWord_4675029) baseStart_4675029 baseEnd_4675029 := by
    simpa [prefixWord, tailWord_4675029, baseEnd_4675029] using wordTrace_append hprefix tailTrace_4675029
  have hstable : (prefixWord ++ tailWord_4675029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675029).length < 2 ^ (prefixWord ++ tailWord_4675029).sum := by decide
  have hdescent : baseEnd_4675029 < baseStart_4675029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675032 : List Nat := [2, 1, 2, 2, 2, 1, 2, 3, 3, 1, 4]
def baseStart_4675032 : Nat := 118140960795 + 4675032 * 2 ^ 59
def prefixEnd_4675032 : Nat := 4983230072969 + 3 ^ 40 * 4675032 * 2
def baseEnd_4675032 : Nat := 2400538491150258149499925

theorem tailTrace_4675032 : CollatzResearch.WordTrace tailWord_4675032 prefixEnd_4675032 2400538491150258149499925 := by
  unfold tailWord_4675032
  simp only [CollatzResearch.WordTrace]
  refine ⟨85256212599582485372149675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113674950132776647162866233 85256212599582485372149675)
  ·
    refine ⟨127884318899373728058224513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85256212599582485372149675 127884318899373728058224513)
    ·
      refine ⟨95913239174530296043668385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127884318899373728058224513 95913239174530296043668385)
      ·
        refine ⟨71934929380897722032751289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95913239174530296043668385 71934929380897722032751289)
        ·
          refine ⟨53951197035673291524563467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71934929380897722032751289 53951197035673291524563467)
          ·
            refine ⟨80926795553509937286845201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53951197035673291524563467 80926795553509937286845201)
            ·
              refine ⟨60695096665132452965133901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80926795553509937286845201 60695096665132452965133901)
              ·
                refine ⟨22760661249424669861925213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60695096665132452965133901 22760661249424669861925213)
                ·
                  refine ⟨8535247968534251198221955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22760661249424669861925213 8535247968534251198221955)
                  ·
                    refine ⟨12802871952801376797332933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8535247968534251198221955 12802871952801376797332933)
                    ·
                      refine ⟨2400538491150258149499925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12802871952801376797332933 2400538491150258149499925)
                      ·
                        rfl

theorem cell23_4675032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_4675032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675032 prefixEnd_4675032 := by exact prefixLift 4675032
  have htrace : WordTrace (prefixWord ++ tailWord_4675032) baseStart_4675032 baseEnd_4675032 := by
    simpa [prefixWord, tailWord_4675032, baseEnd_4675032] using wordTrace_append hprefix tailTrace_4675032
  have hstable : (prefixWord ++ tailWord_4675032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675032).length < 2 ^ (prefixWord ++ tailWord_4675032).sum := by decide
  have hdescent : baseEnd_4675032 < baseStart_4675032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675043 : List Nat := [1, 1, 1, 6, 2, 1, 3, 3, 1, 1, 3]
def baseStart_4675043 : Nat := 118140960795 + 4675043 * 2 ^ 59
def prefixEnd_4675043 : Nat := 4983230072969 + 3 ^ 40 * 4675043 * 2
def baseEnd_4675043 : Nat := 2400544139437457606462375

theorem tailTrace_4675043 : CollatzResearch.WordTrace tailWord_4675043 prefixEnd_4675043 2400544139437457606462375 := by
  unfold tailWord_4675043
  simp only [CollatzResearch.WordTrace]
  refine ⟨170512826402125119622949783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113675217601416746415299855 170512826402125119622949783)
  ·
    refine ⟨255769239603187679434424675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170512826402125119622949783 255769239603187679434424675)
    ·
      refine ⟨383653859404781519151637013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255769239603187679434424675 383653859404781519151637013)
      ·
        refine ⟨17983774659599133710232985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 383653859404781519151637013 17983774659599133710232985)
        ·
          refine ⟨13487830994699350282674739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17983774659599133710232985 13487830994699350282674739)
          ·
            refine ⟨20231746492049025424012109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13487830994699350282674739 20231746492049025424012109)
            ·
              refine ⟨7586904934518384534004541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20231746492049025424012109 7586904934518384534004541)
              ·
                refine ⟨2845089350444394200251703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7586904934518384534004541 2845089350444394200251703)
                ·
                  refine ⟨4267634025666591300377555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2845089350444394200251703 4267634025666591300377555)
                  ·
                    refine ⟨6401451038499886950566333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4267634025666591300377555 6401451038499886950566333)
                    ·
                      refine ⟨2400544139437457606462375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6401451038499886950566333 2400544139437457606462375)
                      ·
                        rfl

theorem cell23_4675043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_4675043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675043 prefixEnd_4675043 := by exact prefixLift 4675043
  have htrace : WordTrace (prefixWord ++ tailWord_4675043) baseStart_4675043 baseEnd_4675043 := by
    simpa [prefixWord, tailWord_4675043, baseEnd_4675043] using wordTrace_append hprefix tailTrace_4675043
  have hstable : (prefixWord ++ tailWord_4675043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675043).length < 2 ^ (prefixWord ++ tailWord_4675043).sum := by decide
  have hdescent : baseEnd_4675043 < baseStart_4675043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675053 : List Nat := [1, 5, 1, 3, 2, 1, 1, 2, 2, 3, 2]
def baseStart_4675053 : Nat := 118140960795 + 4675053 * 2 ^ 59
def prefixEnd_4675053 : Nat := 4983230072969 + 3 ^ 40 * 4675053 * 2
def baseEnd_4675053 : Nat := 2400549274244002567337329

theorem tailTrace_4675053 : CollatzResearch.WordTrace tailWord_4675053 prefixEnd_4675053 2400549274244002567337329 := by
  unfold tailWord_4675053
  simp only [CollatzResearch.WordTrace]
  refine ⟨170513191132088891330813813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113675460754725927553875875 170513191132088891330813813)
  ·
    refine ⟨15985611668633333562263795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 170513191132088891330813813 15985611668633333562263795)
    ·
      refine ⟨23978417502950000343395693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15985611668633333562263795 23978417502950000343395693)
      ·
        refine ⟨8991906563606250128773385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23978417502950000343395693 8991906563606250128773385)
        ·
          refine ⟨6743929922704687596580039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8991906563606250128773385 6743929922704687596580039)
          ·
            refine ⟨10115894884057031394870059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6743929922704687596580039 10115894884057031394870059)
            ·
              refine ⟨15173842326085547092305089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10115894884057031394870059 15173842326085547092305089)
              ·
                refine ⟨11380381744564160319228817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15173842326085547092305089 11380381744564160319228817)
                ·
                  refine ⟨8535286308423120239421613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11380381744564160319228817 8535286308423120239421613)
                  ·
                    refine ⟨3200732365658670089783105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8535286308423120239421613 3200732365658670089783105)
                    ·
                      refine ⟨2400549274244002567337329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3200732365658670089783105 2400549274244002567337329)
                      ·
                        rfl

theorem cell23_4675053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_4675053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675053 prefixEnd_4675053 := by exact prefixLift 4675053
  have htrace : WordTrace (prefixWord ++ tailWord_4675053) baseStart_4675053 baseEnd_4675053 := by
    simpa [prefixWord, tailWord_4675053, baseEnd_4675053] using wordTrace_append hprefix tailTrace_4675053
  have hstable : (prefixWord ++ tailWord_4675053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675053).length < 2 ^ (prefixWord ++ tailWord_4675053).sum := by decide
  have hdescent : baseEnd_4675053 < baseStart_4675053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675055 : List Nat := [1, 1, 2, 1, 4, 1, 13]
def baseStart_4675055 : Nat := 118140960795 + 4675055 * 2 ^ 59
def prefixEnd_4675055 : Nat := 4983230072969 + 3 ^ 40 * 4675055 * 2
def baseEnd_4675055 : Nat := 29636423471670513080399

theorem tailTrace_4675055 : CollatzResearch.WordTrace tailWord_4675055 prefixEnd_4675055 29636423471670513080399 := by
  unfold tailWord_4675055
  simp only [CollatzResearch.WordTrace]
  refine ⟨170513264078081645672386619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113675509385387763781591079 170513264078081645672386619)
  ·
    refine ⟨255769896117122468508579929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170513264078081645672386619 255769896117122468508579929)
    ·
      refine ⟨191827422087841851381434947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255769896117122468508579929 191827422087841851381434947)
      ·
        refine ⟨287741133131762777072152421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191827422087841851381434947 287741133131762777072152421)
        ·
          refine ⟨53951462462205520701028579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 287741133131762777072152421 53951462462205520701028579)
          ·
            refine ⟨80927193693308281051542869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53951462462205520701028579 80927193693308281051542869)
            ·
              refine ⟨29636423471670513080399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 80927193693308281051542869 29636423471670513080399)
              ·
                rfl

theorem cell23_4675055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 13].length) (baseStart_4675055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675055 prefixEnd_4675055 := by exact prefixLift 4675055
  have htrace : WordTrace (prefixWord ++ tailWord_4675055) baseStart_4675055 baseEnd_4675055 := by
    simpa [prefixWord, tailWord_4675055, baseEnd_4675055] using wordTrace_append hprefix tailTrace_4675055
  have hstable : (prefixWord ++ tailWord_4675055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675055).length < 2 ^ (prefixWord ++ tailWord_4675055).sum := by decide
  have hdescent : baseEnd_4675055 < baseStart_4675055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675083 : List Nat := [1, 1, 1, 1, 9, 1, 1, 2, 1, 1, 4]
def baseStart_4675083 : Nat := 118140960795 + 4675083 * 2 ^ 59
def prefixEnd_4675083 : Nat := 4983230072969 + 3 ^ 40 * 4675083 * 2
def baseEnd_4675083 : Nat := 2400564678663637449962191

theorem tailTrace_4675083 : CollatzResearch.WordTrace tailWord_4675083 prefixEnd_4675083 2400564678663637449962191 := by
  unfold tailWord_4675083
  simp only [CollatzResearch.WordTrace]
  refine ⟨170514285321980206454405903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113676190214653470969603935 170514285321980206454405903)
  ·
    refine ⟨255771427982970309681608855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170514285321980206454405903 255771427982970309681608855)
    ·
      refine ⟨383657141974455464522413283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255771427982970309681608855 383657141974455464522413283)
      ·
        refine ⟨575485712961683196783619925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383657141974455464522413283 575485712961683196783619925)
        ·
          refine ⟨3371986599384862481154023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 575485712961683196783619925 3371986599384862481154023)
          ·
            refine ⟨5057979899077293721731035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3371986599384862481154023 5057979899077293721731035)
            ·
              refine ⟨7586969848615940582596553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5057979899077293721731035 7586969848615940582596553)
              ·
                refine ⟨5690227386461955436947415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7586969848615940582596553 5690227386461955436947415)
                ·
                  refine ⟨8535341079692933155421123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5690227386461955436947415 8535341079692933155421123)
                  ·
                    refine ⟨12803011619539399733131685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8535341079692933155421123 12803011619539399733131685)
                    ·
                      refine ⟨2400564678663637449962191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12803011619539399733131685 2400564678663637449962191)
                      ·
                        rfl

theorem cell23_4675083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 1, 1, 4].length) (baseStart_4675083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675083 prefixEnd_4675083 := by exact prefixLift 4675083
  have htrace : WordTrace (prefixWord ++ tailWord_4675083) baseStart_4675083 baseEnd_4675083 := by
    simpa [prefixWord, tailWord_4675083, baseEnd_4675083] using wordTrace_append hprefix tailTrace_4675083
  have hstable : (prefixWord ++ tailWord_4675083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675083).length < 2 ^ (prefixWord ++ tailWord_4675083).sum := by decide
  have hdescent : baseEnd_4675083 < baseStart_4675083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675086 : List Nat := [4, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3]
def baseStart_4675086 : Nat := 118140960795 + 4675086 * 2 ^ 59
def prefixEnd_4675086 : Nat := 4983230072969 + 3 ^ 40 * 4675086 * 2
def baseEnd_4675086 : Nat := 2400566219105600938224677

theorem tailTrace_4675086 : CollatzResearch.WordTrace tailWord_4675086 prefixEnd_4675086 2400566219105600938224677 := by
  unfold tailWord_4675086
  simp only [CollatzResearch.WordTrace]
  refine ⟨21314299342621167245845639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113676263160646225311176741 21314299342621167245845639)
  ·
    refine ⟨31971449013931750868768459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21314299342621167245845639 31971449013931750868768459)
    ·
      refine ⟨47957173520897626303152689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31971449013931750868768459 47957173520897626303152689)
      ·
        refine ⟨35967880140673219727364517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47957173520897626303152689 35967880140673219727364517)
        ·
          refine ⟨6743977526376228698880847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35967880140673219727364517 6743977526376228698880847)
          ·
            refine ⟨10115966289564343048321271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6743977526376228698880847 10115966289564343048321271)
            ·
              refine ⟨15173949434346514572481907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10115966289564343048321271 15173949434346514572481907)
              ·
                refine ⟨22760924151519771858722861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15173949434346514572481907 22760924151519771858722861)
                ·
                  refine ⟨8535346556819914447021073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22760924151519771858722861 8535346556819914447021073)
                  ·
                    refine ⟨6401509917614935835265805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8535346556819914447021073 6401509917614935835265805)
                    ·
                      refine ⟨2400566219105600938224677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6401509917614935835265805 2400566219105600938224677)
                      ·
                        rfl

theorem cell23_4675086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_4675086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675086 prefixEnd_4675086 := by exact prefixLift 4675086
  have htrace : WordTrace (prefixWord ++ tailWord_4675086) baseStart_4675086 baseEnd_4675086 := by
    simpa [prefixWord, tailWord_4675086, baseEnd_4675086] using wordTrace_append hprefix tailTrace_4675086
  have hstable : (prefixWord ++ tailWord_4675086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675086).length < 2 ^ (prefixWord ++ tailWord_4675086).sum := by decide
  have hdescent : baseEnd_4675086 < baseStart_4675086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675152 : List Nat := [2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 4]
def baseStart_4675152 : Nat := 118140960795 + 4675152 * 2 ^ 59
def prefixEnd_4675152 : Nat := 4983230072969 + 3 ^ 40 * 4675152 * 2
def baseEnd_4675152 : Nat := 2400600108828797679999373

theorem tailTrace_4675152 : CollatzResearch.WordTrace tailWord_4675152 prefixEnd_4675152 2400600108828797679999373 := by
  unfold tailWord_4675152
  simp only [CollatzResearch.WordTrace]
  refine ⟨85258400979365115619333855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113677867972486820825778473 85258400979365115619333855)
  ·
    refine ⟨127887601469047673429000783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85258400979365115619333855 127887601469047673429000783)
    ·
      refine ⟨191831402203571510143501175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127887601469047673429000783 191831402203571510143501175)
      ·
        refine ⟨287747103305357265215251763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191831402203571510143501175 287747103305357265215251763)
        ·
          refine ⟨431620654958035897822877645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287747103305357265215251763 431620654958035897822877645)
          ·
            refine ⟨161857745609263461683579117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 431620654958035897822877645 161857745609263461683579117)
            ·
              refine ⟨60696654603473798131342169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161857745609263461683579117 60696654603473798131342169)
              ·
                refine ⟨45522490952605348598506627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60696654603473798131342169 45522490952605348598506627)
                ·
                  refine ⟨68283736428908022897759941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45522490952605348598506627 68283736428908022897759941)
                  ·
                    refine ⟨12803200580420254293329989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68283736428908022897759941 12803200580420254293329989)
                    ·
                      refine ⟨2400600108828797679999373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12803200580420254293329989 2400600108828797679999373)
                      ·
                        rfl

theorem cell23_4675152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 4].length) (baseStart_4675152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675152 prefixEnd_4675152 := by exact prefixLift 4675152
  have htrace : WordTrace (prefixWord ++ tailWord_4675152) baseStart_4675152 baseEnd_4675152 := by
    simpa [prefixWord, tailWord_4675152, baseEnd_4675152] using wordTrace_append hprefix tailTrace_4675152
  have hstable : (prefixWord ++ tailWord_4675152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675152).length < 2 ^ (prefixWord ++ tailWord_4675152).sum := by decide
  have hdescent : baseEnd_4675152 < baseStart_4675152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675156 : List Nat := [2, 4, 1, 1, 1, 2, 1, 4, 1, 4, 2]
def baseStart_4675156 : Nat := 118140960795 + 4675156 * 2 ^ 59
def prefixEnd_4675156 : Nat := 4983230072969 + 3 ^ 40 * 4675156 * 2
def baseEnd_4675156 : Nat := 2400602162751415664349355

theorem tailTrace_4675156 : CollatzResearch.WordTrace tailWord_4675156 prefixEnd_4675156 2400602162751415664349355 := by
  unfold tailWord_4675156
  simp only [CollatzResearch.WordTrace]
  refine ⟨85258473925357869960906661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113677965233810493281208881 85258473925357869960906661)
  ·
    refine ⟨15985963861004600617669999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85258473925357869960906661 15985963861004600617669999)
    ·
      refine ⟨23978945791506900926504999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15985963861004600617669999 23978945791506900926504999)
      ·
        refine ⟨35968418687260351389757499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23978945791506900926504999 35968418687260351389757499)
        ·
          refine ⟨53952628030890527084636249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35968418687260351389757499 53952628030890527084636249)
          ·
            refine ⟨40464471023167895313477187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53952628030890527084636249 40464471023167895313477187)
            ·
              refine ⟨60696706534751842970215781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40464471023167895313477187 60696706534751842970215781)
              ·
                refine ⟨11380632475265970556915459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60696706534751842970215781 11380632475265970556915459)
                ·
                  refine ⟨17070948712898955835373189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11380632475265970556915459 17070948712898955835373189)
                  ·
                    refine ⟨3200802883668554219132473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17070948712898955835373189 3200802883668554219132473)
                    ·
                      refine ⟨2400602162751415664349355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3200802883668554219132473 2400602162751415664349355)
                      ·
                        rfl

theorem cell23_4675156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_4675156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675156 prefixEnd_4675156 := by exact prefixLift 4675156
  have htrace : WordTrace (prefixWord ++ tailWord_4675156) baseStart_4675156 baseEnd_4675156 := by
    simpa [prefixWord, tailWord_4675156, baseEnd_4675156] using wordTrace_append hprefix tailTrace_4675156
  have hstable : (prefixWord ++ tailWord_4675156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675156).length < 2 ^ (prefixWord ++ tailWord_4675156).sum := by decide
  have hdescent : baseEnd_4675156 < baseStart_4675156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675173 : List Nat := [1, 3, 1, 3, 3, 2, 1, 1, 4, 2, 2]
def baseStart_4675173 : Nat := 118140960795 + 4675173 * 2 ^ 59
def prefixEnd_4675173 : Nat := 4983230072969 + 3 ^ 40 * 4675173 * 2
def baseEnd_4675173 : Nat := 2400610891922542097836777

theorem tailTrace_4675173 : CollatzResearch.WordTrace tailWord_4675173 prefixEnd_4675173 2400610891922542097836777 := by
  unfold tailWord_4675173
  simp only [CollatzResearch.WordTrace]
  refine ⟨170517567891654151825182173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113678378594436101216788115 170517567891654151825182173)
  ·
    refine ⟨63944087959370306934443315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170517567891654151825182173 63944087959370306934443315)
    ·
      refine ⟨95916131939055460401664973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63944087959370306934443315 95916131939055460401664973)
      ·
        refine ⟨35968549477145797650624365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95916131939055460401664973 35968549477145797650624365)
        ·
          refine ⟨13488206053929674118984137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35968549477145797650624365 13488206053929674118984137)
          ·
            refine ⟨10116154540447255589238103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13488206053929674118984137 10116154540447255589238103)
            ·
              refine ⟨15174231810670883383857155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10116154540447255589238103 15174231810670883383857155)
              ·
                refine ⟨22761347716006325075785733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15174231810670883383857155 22761347716006325075785733)
                ·
                  refine ⟨4267752696751185951709825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22761347716006325075785733 4267752696751185951709825)
                  ·
                    refine ⟨3200814522563389463782369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4267752696751185951709825 3200814522563389463782369)
                    ·
                      refine ⟨2400610891922542097836777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3200814522563389463782369 2400610891922542097836777)
                      ·
                        rfl

theorem cell23_4675173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_4675173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675173 prefixEnd_4675173 := by exact prefixLift 4675173
  have htrace : WordTrace (prefixWord ++ tailWord_4675173) baseStart_4675173 baseEnd_4675173 := by
    simpa [prefixWord, tailWord_4675173, baseEnd_4675173] using wordTrace_append hprefix tailTrace_4675173
  have hstable : (prefixWord ++ tailWord_4675173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675173).length < 2 ^ (prefixWord ++ tailWord_4675173).sum := by decide
  have hdescent : baseEnd_4675173 < baseStart_4675173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675190 : List Nat := [5, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2]
def baseStart_4675190 : Nat := 118140960795 + 4675190 * 2 ^ 59
def prefixEnd_4675190 : Nat := 4983230072969 + 3 ^ 40 * 4675190 * 2
def baseEnd_4675190 : Nat := 2400619621093668531324199

theorem tailTrace_4675190 : CollatzResearch.WordTrace tailWord_4675190 prefixEnd_4675190 2400619621093668531324199 := by
  unfold tailWord_4675190
  simp only [CollatzResearch.WordTrace]
  refine ⟨10657386745787035233034439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113678791955061709152367349 10657386745787035233034439)
  ·
    refine ⟨15986080118680552849551659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10657386745787035233034439 15986080118680552849551659)
    ·
      refine ⟨23979120178020829274327489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15986080118680552849551659 23979120178020829274327489)
      ·
        refine ⟨17984340133515621955745617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23979120178020829274327489 17984340133515621955745617)
        ·
          refine ⟨13488255100136716466809213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17984340133515621955745617 13488255100136716466809213)
          ·
            refine ⟨5058095662551268675053455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13488255100136716466809213 5058095662551268675053455)
            ·
              refine ⟨7587143493826903012580183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5058095662551268675053455 7587143493826903012580183)
              ·
                refine ⟨11380715240740354518870275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7587143493826903012580183 11380715240740354518870275)
                ·
                  refine ⟨17071072861110531778305413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11380715240740354518870275 17071072861110531778305413)
                  ·
                    refine ⟨3200826161458224708432265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17071072861110531778305413 3200826161458224708432265)
                    ·
                      refine ⟨2400619621093668531324199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3200826161458224708432265 2400619621093668531324199)
                      ·
                        rfl

theorem cell23_4675190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_4675190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675190 prefixEnd_4675190 := by exact prefixLift 4675190
  have htrace : WordTrace (prefixWord ++ tailWord_4675190) baseStart_4675190 baseEnd_4675190 := by
    simpa [prefixWord, tailWord_4675190, baseEnd_4675190] using wordTrace_append hprefix tailTrace_4675190
  have hstable : (prefixWord ++ tailWord_4675190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675190).length < 2 ^ (prefixWord ++ tailWord_4675190).sum := by decide
  have hdescent : baseEnd_4675190 < baseStart_4675190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675199 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 3, 7, 2]
def baseStart_4675199 : Nat := 118140960795 + 4675199 * 2 ^ 59
def prefixEnd_4675199 : Nat := 4983230072969 + 3 ^ 40 * 4675199 * 2
def baseEnd_4675199 : Nat := 2400624242419558996111657

theorem tailTrace_4675199 : CollatzResearch.WordTrace tailWord_4675199 prefixEnd_4675199 2400624242419558996111657 := by
  unfold tailWord_4675199
  simp only [CollatzResearch.WordTrace]
  refine ⟨170518516189559958265628651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113679010793039972177085767 170518516189559958265628651)
  ·
    refine ⟨255777774284339937398442977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170518516189559958265628651 255777774284339937398442977)
    ·
      refine ⟨191833330713254953048832233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255777774284339937398442977 191833330713254953048832233)
      ·
        refine ⟨143874998034941214786624175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191833330713254953048832233 143874998034941214786624175)
        ·
          refine ⟨215812497052411822179936263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143874998034941214786624175 215812497052411822179936263)
          ·
            refine ⟨323718745578617733269904395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215812497052411822179936263 323718745578617733269904395)
            ·
              refine ⟨485578118367926599904856593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323718745578617733269904395 485578118367926599904856593)
              ·
                refine ⟨364183588775944949928642445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 485578118367926599904856593 364183588775944949928642445)
                ·
                  refine ⟨136568845790979356223240917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 364183588775944949928642445 136568845790979356223240917)
                  ·
                    refine ⟨3200832323226078661482209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 136568845790979356223240917 3200832323226078661482209)
                    ·
                      refine ⟨2400624242419558996111657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3200832323226078661482209 2400624242419558996111657)
                      ·
                        rfl

theorem cell23_4675199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 7, 2].length) (baseStart_4675199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675199 prefixEnd_4675199 := by exact prefixLift 4675199
  have htrace : WordTrace (prefixWord ++ tailWord_4675199) baseStart_4675199 baseEnd_4675199 := by
    simpa [prefixWord, tailWord_4675199, baseEnd_4675199] using wordTrace_append hprefix tailTrace_4675199
  have hstable : (prefixWord ++ tailWord_4675199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675199).length < 2 ^ (prefixWord ++ tailWord_4675199).sum := by decide
  have hdescent : baseEnd_4675199 < baseStart_4675199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675230 : List Nat := [4, 3, 1, 1, 1, 3, 3, 2, 5]
def baseStart_4675230 : Nat := 118140960795 + 4675230 * 2 ^ 59
def prefixEnd_4675230 : Nat := 4983230072969 + 3 ^ 40 * 4675230 * 2
def baseEnd_4675230 : Nat := 266737795591094263869335

theorem tailTrace_4675230 : CollatzResearch.WordTrace tailWord_4675230 prefixEnd_4675230 266737795591094263869335 := by
  unfold tailWord_4675230
  simp only [CollatzResearch.WordTrace]
  refine ⟨21314955856555956320000893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113679764568298433706671429 21314955856555956320000893)
  ·
    refine ⟨7993108446208483620000335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21314955856555956320000893 7993108446208483620000335)
    ·
      refine ⟨11989662669312725430000503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7993108446208483620000335 11989662669312725430000503)
      ·
        refine ⟨17984494003969088145000755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11989662669312725430000503 17984494003969088145000755)
        ·
          refine ⟨26976741005953632217501133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17984494003969088145000755 26976741005953632217501133)
          ·
            refine ⟨10116277877232612081562925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26976741005953632217501133 10116277877232612081562925)
            ·
              refine ⟨3793604203962229530586097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10116277877232612081562925 3793604203962229530586097)
              ·
                refine ⟨2845203152971672147939573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3793604203962229530586097 2845203152971672147939573)
                ·
                  refine ⟨266737795591094263869335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2845203152971672147939573 266737795591094263869335)
                  ·
                    rfl

theorem cell23_4675230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_4675230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675230 prefixEnd_4675230 := by exact prefixLift 4675230
  have htrace : WordTrace (prefixWord ++ tailWord_4675230) baseStart_4675230 baseEnd_4675230 := by
    simpa [prefixWord, tailWord_4675230, baseEnd_4675230] using wordTrace_append hprefix tailTrace_4675230
  have hstable : (prefixWord ++ tailWord_4675230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675230).length < 2 ^ (prefixWord ++ tailWord_4675230).sum := by decide
  have hdescent : baseEnd_4675230 < baseStart_4675230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675290 : List Nat := [3, 1, 1, 2, 2, 3, 4, 2, 1, 4]
def baseStart_4675290 : Nat := 118140960795 + 4675290 * 2 ^ 59
def prefixEnd_4675290 : Nat := 4983230072969 + 3 ^ 40 * 4675290 * 2
def baseEnd_4675290 : Nat := 800223656386372713357913

theorem tailTrace_4675290 : CollatzResearch.WordTrace tailWord_4675290 prefixEnd_4675290 800223656386372713357913 := by
  unfold tailWord_4675290
  simp only [CollatzResearch.WordTrace]
  refine ⟨42630458808057570201797831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113681223488153520538127549 42630458808057570201797831)
  ·
    refine ⟨63945688212086355302696747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42630458808057570201797831 63945688212086355302696747)
    ·
      refine ⟨95918532318129532954045121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63945688212086355302696747 95918532318129532954045121)
      ·
        refine ⟨71938899238597149715533841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95918532318129532954045121 71938899238597149715533841)
        ·
          refine ⟨53954174428947862286650381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71938899238597149715533841 53954174428947862286650381)
          ·
            refine ⟨20232815410855448357493893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53954174428947862286650381 20232815410855448357493893)
            ·
              refine ⟨3793652889535396567030105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20232815410855448357493893 3793652889535396567030105)
              ·
                refine ⟨2845239667151547425272579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3793652889535396567030105 2845239667151547425272579)
                ·
                  refine ⟨4267859500727321137908869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2845239667151547425272579 4267859500727321137908869)
                  ·
                    refine ⟨800223656386372713357913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4267859500727321137908869 800223656386372713357913)
                    ·
                      rfl

theorem cell23_4675290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 2, 1, 4].length) (baseStart_4675290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675290 prefixEnd_4675290 := by exact prefixLift 4675290
  have htrace : WordTrace (prefixWord ++ tailWord_4675290) baseStart_4675290 baseEnd_4675290 := by
    simpa [prefixWord, tailWord_4675290, baseEnd_4675290] using wordTrace_append hprefix tailTrace_4675290
  have hstable : (prefixWord ++ tailWord_4675290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675290).length < 2 ^ (prefixWord ++ tailWord_4675290).sum := by decide
  have hdescent : baseEnd_4675290 < baseStart_4675290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675313 : List Nat := [1, 2, 2, 2, 2, 4, 1, 2, 3, 1, 3]
def baseStart_4675313 : Nat := 118140960795 + 4675313 * 2 ^ 59
def prefixEnd_4675313 : Nat := 4983230072969 + 3 ^ 40 * 4675313 * 2
def baseEnd_4675313 : Nat := 2400682779214171550086133

theorem tailTrace_4675313 : CollatzResearch.WordTrace tailWord_4675313 prefixEnd_4675313 2400682779214171550086133 := by
  unfold tailWord_4675313
  simp only [CollatzResearch.WordTrace]
  refine ⟨170522674111146955735278593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113681782740764637156852395 170522674111146955735278593)
  ·
    refine ⟨127892005583360216801458945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170522674111146955735278593 127892005583360216801458945)
    ·
      refine ⟨95919004187520162601094209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127892005583360216801458945 95919004187520162601094209)
      ·
        refine ⟨71939253140640121950820657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95919004187520162601094209 71939253140640121950820657)
        ·
          refine ⟨53954439855480091463115493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71939253140640121950820657 53954439855480091463115493)
          ·
            refine ⟨10116457472902517149334155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53954439855480091463115493 10116457472902517149334155)
            ·
              refine ⟨15174686209353775724001233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10116457472902517149334155 15174686209353775724001233)
              ·
                refine ⟨11381014657015331793000925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15174686209353775724001233 11381014657015331793000925)
                ·
                  refine ⟨4267880496380749422375347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11381014657015331793000925 4267880496380749422375347)
                  ·
                    refine ⟨6401820744571124133563021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4267880496380749422375347 6401820744571124133563021)
                    ·
                      refine ⟨2400682779214171550086133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6401820744571124133563021 2400682779214171550086133)
                      ·
                        rfl

theorem cell23_4675313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 3, 1, 3].length) (baseStart_4675313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675313 prefixEnd_4675313 := by exact prefixLift 4675313
  have htrace : WordTrace (prefixWord ++ tailWord_4675313) baseStart_4675313 baseEnd_4675313 := by
    simpa [prefixWord, tailWord_4675313, baseEnd_4675313] using wordTrace_append hprefix tailTrace_4675313
  have hstable : (prefixWord ++ tailWord_4675313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675313).length < 2 ^ (prefixWord ++ tailWord_4675313).sum := by decide
  have hdescent : baseEnd_4675313 < baseStart_4675313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675356 : List Nat := [2, 2, 3, 1, 1, 2, 3, 2, 1, 1, 5]
def baseStart_4675356 : Nat := 118140960795 + 4675356 * 2 ^ 59
def prefixEnd_4675356 : Nat := 4983230072969 + 3 ^ 40 * 4675356 * 2
def baseEnd_4675356 : Nat := 2400704858882314881848435

theorem tailTrace_4675356 : CollatzResearch.WordTrace tailWord_4675356 prefixEnd_4675356 2400704858882314881848435 := by
  unfold tailWord_4675356
  simp only [CollatzResearch.WordTrace]
  refine ⟨85262121224995587039546961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113682828299994116052729281 85262121224995587039546961)
  ·
    refine ⟨63946590918746690279660221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85262121224995587039546961 63946590918746690279660221)
    ·
      refine ⟨23979971594530008854872583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63946590918746690279660221 23979971594530008854872583)
      ·
        refine ⟨35969957391795013282308875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23979971594530008854872583 35969957391795013282308875)
        ·
          refine ⟨53954936087692519923463313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35969957391795013282308875 53954936087692519923463313)
          ·
            refine ⟨40466202065769389942597485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53954936087692519923463313 40466202065769389942597485)
            ·
              refine ⟨15174825774663521228474057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40466202065769389942597485 15174825774663521228474057)
              ·
                refine ⟨11381119330997640921355543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15174825774663521228474057 11381119330997640921355543)
                ·
                  refine ⟨17071678996496461382033315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11381119330997640921355543 17071678996496461382033315)
                  ·
                    refine ⟨25607518494744692073049973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17071678996496461382033315 25607518494744692073049973)
                    ·
                      refine ⟨2400704858882314881848435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25607518494744692073049973 2400704858882314881848435)
                      ·
                        rfl

theorem cell23_4675356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_4675356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675356 prefixEnd_4675356 := by exact prefixLift 4675356
  have htrace : WordTrace (prefixWord ++ tailWord_4675356) baseStart_4675356 baseEnd_4675356 := by
    simpa [prefixWord, tailWord_4675356, baseEnd_4675356] using wordTrace_append hprefix tailTrace_4675356
  have hstable : (prefixWord ++ tailWord_4675356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675356).length < 2 ^ (prefixWord ++ tailWord_4675356).sum := by decide
  have hdescent : baseEnd_4675356 < baseStart_4675356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675359 : List Nat := [1, 1, 2, 4, 2, 1, 2, 10]
def baseStart_4675359 : Nat := 118140960795 + 4675359 * 2 ^ 59
def prefixEnd_4675359 : Nat := 4983230072969 + 3 ^ 40 * 4675359 * 2
def baseEnd_4675359 : Nat := 88915051826825124818923

theorem tailTrace_4675359 : CollatzResearch.WordTrace tailWord_4675359 prefixEnd_4675359 88915051826825124818923 := by
  unfold tailWord_4675359
  simp only [CollatzResearch.WordTrace]
  refine ⟨170524351868980305591453131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113682901245986870394302087 170524351868980305591453131)
  ·
    refine ⟨255786527803470458387179697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170524351868980305591453131 255786527803470458387179697)
    ·
      refine ⟨191839895852602843790384773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255786527803470458387179697 191839895852602843790384773)
      ·
        refine ⟨35969980472363033210697145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 191839895852602843790384773 35969980472363033210697145)
        ·
          refine ⟨26977485354272274908022859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35969980472363033210697145 26977485354272274908022859)
          ·
            refine ⟨40466228031408412362034289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26977485354272274908022859 40466228031408412362034289)
            ·
              refine ⟨30349671023556309271525717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40466228031408412362034289 30349671023556309271525717)
              ·
                refine ⟨88915051826825124818923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 30349671023556309271525717 88915051826825124818923)
                ·
                  rfl

theorem cell23_4675359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 10].length) (baseStart_4675359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675359 prefixEnd_4675359 := by exact prefixLift 4675359
  have htrace : WordTrace (prefixWord ++ tailWord_4675359) baseStart_4675359 baseEnd_4675359 := by
    simpa [prefixWord, tailWord_4675359, baseEnd_4675359] using wordTrace_append hprefix tailTrace_4675359
  have hstable : (prefixWord ++ tailWord_4675359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675359).length < 2 ^ (prefixWord ++ tailWord_4675359).sum := by decide
  have hdescent : baseEnd_4675359 < baseStart_4675359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675390 : List Nat := [4, 2, 1, 2, 2, 1, 2, 3, 1, 2, 3]
def baseStart_4675390 : Nat := 118140960795 + 4675390 * 2 ^ 59
def prefixEnd_4675390 : Nat := 4983230072969 + 3 ^ 40 * 4675390 * 2
def baseEnd_4675390 : Nat := 2400722317224567748823279

theorem tailTrace_4675390 : CollatzResearch.WordTrace tailWord_4675390 prefixEnd_4675390 2400722317224567748823279 := by
  unfold tailWord_4675390
  simp only [CollatzResearch.WordTrace]
  refine ⟨21315685316483499735728953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113683655021245331923887749 21315685316483499735728953)
  ·
    refine ⟨15986763987362624801796715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21315685316483499735728953 15986763987362624801796715)
    ·
      refine ⟨23980145981043937202695073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15986763987362624801796715 23980145981043937202695073)
      ·
        refine ⟨17985109485782952902021305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23980145981043937202695073 17985109485782952902021305)
        ·
          refine ⟨13488832114337214676515979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17985109485782952902021305 13488832114337214676515979)
          ·
            refine ⟨20233248171505822014773969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13488832114337214676515979 20233248171505822014773969)
            ·
              refine ⟨15174936128629366511080477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20233248171505822014773969 15174936128629366511080477)
              ·
                refine ⟨5690601048236012441655179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15174936128629366511080477 5690601048236012441655179)
                ·
                  refine ⟨8535901572354018662482769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5690601048236012441655179 8535901572354018662482769)
                  ·
                    refine ⟨6401926179265513996862077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8535901572354018662482769 6401926179265513996862077)
                    ·
                      refine ⟨2400722317224567748823279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6401926179265513996862077 2400722317224567748823279)
                      ·
                        rfl

theorem cell23_4675390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_4675390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675390 prefixEnd_4675390 := by exact prefixLift 4675390
  have htrace : WordTrace (prefixWord ++ tailWord_4675390) baseStart_4675390 baseEnd_4675390 := by
    simpa [prefixWord, tailWord_4675390, baseEnd_4675390] using wordTrace_append hprefix tailTrace_4675390
  have hstable : (prefixWord ++ tailWord_4675390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675390).length < 2 ^ (prefixWord ++ tailWord_4675390).sum := by decide
  have hdescent : baseEnd_4675390 < baseStart_4675390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675404 : List Nat := [2, 2, 1, 3, 5, 1, 1, 1, 3, 2, 2]
def baseStart_4675404 : Nat := 118140960795 + 4675404 * 2 ^ 59
def prefixEnd_4675404 : Nat := 4983230072969 + 3 ^ 40 * 4675404 * 2
def baseEnd_4675404 : Nat := 2400729505953730694048215

theorem tailTrace_4675404 : CollatzResearch.WordTrace tailWord_4675404 prefixEnd_4675404 2400729505953730694048215 := by
  unfold tailWord_4675404
  simp only [CollatzResearch.WordTrace]
  refine ⟨85262996576908639138420633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113683995435878185517894177 85262996576908639138420633)
  ·
    refine ⟨63947247432681479353815475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85262996576908639138420633 63947247432681479353815475)
    ·
      refine ⟨95920871149022219030723213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63947247432681479353815475 95920871149022219030723213)
      ·
        refine ⟨35970326680883332136521205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95920871149022219030723213 35970326680883332136521205)
        ·
          refine ⟨3372218126332812387798863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35970326680883332136521205 3372218126332812387798863)
          ·
            refine ⟨5058327189499218581698295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3372218126332812387798863 5058327189499218581698295)
            ·
              refine ⟨7587490784248827872547443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5058327189499218581698295 7587490784248827872547443)
              ·
                refine ⟨11381236176373241808821165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7587490784248827872547443 11381236176373241808821165)
                ·
                  refine ⟨4267963566139965678307937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11381236176373241808821165 4267963566139965678307937)
                  ·
                    refine ⟨3200972674604974258730953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4267963566139965678307937 3200972674604974258730953)
                    ·
                      refine ⟨2400729505953730694048215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3200972674604974258730953 2400729505953730694048215)
                      ·
                        rfl

theorem cell23_4675404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_4675404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675404 prefixEnd_4675404 := by exact prefixLift 4675404
  have htrace : WordTrace (prefixWord ++ tailWord_4675404) baseStart_4675404 baseEnd_4675404 := by
    simpa [prefixWord, tailWord_4675404, baseEnd_4675404] using wordTrace_append hprefix tailTrace_4675404
  have hstable : (prefixWord ++ tailWord_4675404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675404).length < 2 ^ (prefixWord ++ tailWord_4675404).sum := by decide
  have hdescent : baseEnd_4675404 < baseStart_4675404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675454 : List Nat := [4, 2, 3, 1, 1, 2, 2, 2, 2, 1, 3]
def baseStart_4675454 : Nat := 118140960795 + 4675454 * 2 ^ 59
def prefixEnd_4675454 : Nat := 4983230072969 + 3 ^ 40 * 4675454 * 2
def baseEnd_4675454 : Nat := 2400755179986455498422985

theorem tailTrace_4675454 : CollatzResearch.WordTrace tailWord_4675454 prefixEnd_4675454 2400755179986455498422985 := by
  unfold tailWord_4675454
  simp only [CollatzResearch.WordTrace]
  refine ⟨21315977100454517102020177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113685211202424091210774277 21315977100454517102020177)
  ·
    refine ⟨15986982825340887826515133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21315977100454517102020177 15986982825340887826515133)
    ·
      refine ⟨5995118559502832934943175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15986982825340887826515133 5995118559502832934943175)
      ·
        refine ⟨8992677839254249402414763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5995118559502832934943175 8992677839254249402414763)
        ·
          refine ⟨13489016758881374103622145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8992677839254249402414763 13489016758881374103622145)
          ·
            refine ⟨10116762569161030577716609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13489016758881374103622145 10116762569161030577716609)
            ·
              refine ⟨7587571926870772933287457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10116762569161030577716609 7587571926870772933287457)
              ·
                refine ⟨5690678945153079699965593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7587571926870772933287457 5690678945153079699965593)
                ·
                  refine ⟨4268009208864809774974195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5690678945153079699965593 4268009208864809774974195)
                  ·
                    refine ⟨6402013813297214662461293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4268009208864809774974195 6402013813297214662461293)
                    ·
                      refine ⟨2400755179986455498422985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6402013813297214662461293 2400755179986455498422985)
                      ·
                        rfl

theorem cell23_4675454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_4675454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675454 prefixEnd_4675454 := by exact prefixLift 4675454
  have htrace : WordTrace (prefixWord ++ tailWord_4675454) baseStart_4675454 baseEnd_4675454 := by
    simpa [prefixWord, tailWord_4675454, baseEnd_4675454] using wordTrace_append hprefix tailTrace_4675454
  have hstable : (prefixWord ++ tailWord_4675454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675454).length < 2 ^ (prefixWord ++ tailWord_4675454).sum := by decide
  have hdescent : baseEnd_4675454 < baseStart_4675454 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675456 : List Nat := [2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 4]
def baseStart_4675456 : Nat := 118140960795 + 4675456 * 2 ^ 59
def prefixEnd_4675456 : Nat := 4983230072969 + 3 ^ 40 * 4675456 * 2
def baseEnd_4675456 : Nat := 2400756206947764490597975

theorem tailTrace_4675456 : CollatzResearch.WordTrace tailWord_4675456 prefixEnd_4675456 2400756206947764490597975 := by
  unfold tailWord_4675456
  simp only [CollatzResearch.WordTrace]
  refine ⟨85263944874814445578867111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113685259833085927438489481 85263944874814445578867111)
  ·
    refine ⟨127895917312221668368300667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85263944874814445578867111 127895917312221668368300667)
    ·
      refine ⟨191843875968332502552451001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127895917312221668368300667 191843875968332502552451001)
      ·
        refine ⟨143882906976249376914338251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191843875968332502552451001 143882906976249376914338251)
        ·
          refine ⟨215824360464374065371507377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143882906976249376914338251 215824360464374065371507377)
          ·
            refine ⟨161868270348280549028630533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215824360464374065371507377 161868270348280549028630533)
            ·
              refine ⟨30350300690302602942868225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 161868270348280549028630533 30350300690302602942868225)
              ·
                refine ⟨22762725517726952207151169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30350300690302602942868225 22762725517726952207151169)
                ·
                  refine ⟨17072044138295214155363377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22762725517726952207151169 17072044138295214155363377)
                  ·
                    refine ⟨12804033103721410616522533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17072044138295214155363377 12804033103721410616522533)
                    ·
                      refine ⟨2400756206947764490597975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12804033103721410616522533 2400756206947764490597975)
                      ·
                        rfl

theorem cell23_4675456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_4675456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675456 prefixEnd_4675456 := by exact prefixLift 4675456
  have htrace : WordTrace (prefixWord ++ tailWord_4675456) baseStart_4675456 baseEnd_4675456 := by
    simpa [prefixWord, tailWord_4675456, baseEnd_4675456] using wordTrace_append hprefix tailTrace_4675456
  have hstable : (prefixWord ++ tailWord_4675456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675456).length < 2 ^ (prefixWord ++ tailWord_4675456).sum := by decide
  have hdescent : baseEnd_4675456 < baseStart_4675456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675460 : List Nat := [2, 3, 2, 1, 1, 1, 2, 3, 4, 2, 2]
def baseStart_4675460 : Nat := 118140960795 + 4675460 * 2 ^ 59
def prefixEnd_4675460 : Nat := 4983230072969 + 3 ^ 40 * 4675460 * 2
def baseEnd_4675460 : Nat := 2400758260870382474947957

theorem tailTrace_4675460 : CollatzResearch.WordTrace tailWord_4675460 prefixEnd_4675460 2400758260870382474947957 := by
  unfold tailWord_4675460
  simp only [CollatzResearch.WordTrace]
  refine ⟨85264017820807199920439917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113685357094409599893919889 85264017820807199920439917)
  ·
    refine ⟨31974006682802699970164969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85264017820807199920439917 31974006682802699970164969)
    ·
      refine ⟨23980505012102024977623727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31974006682802699970164969 23980505012102024977623727)
      ·
        refine ⟨35970757518153037466435591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23980505012102024977623727 35970757518153037466435591)
        ·
          refine ⟨53956136277229556199653387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35970757518153037466435591 53956136277229556199653387)
          ·
            refine ⟨80934204415844334299480081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53956136277229556199653387 80934204415844334299480081)
            ·
              refine ⟨60700653311883250724610061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80934204415844334299480081 60700653311883250724610061)
              ·
                refine ⟨22762744991956219021728773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60700653311883250724610061 22762744991956219021728773)
                ·
                  refine ⟨4268014685991791066574145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22762744991956219021728773 4268014685991791066574145)
                  ·
                    refine ⟨3201011014493843299930609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4268014685991791066574145 3201011014493843299930609)
                    ·
                      refine ⟨2400758260870382474947957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3201011014493843299930609 2400758260870382474947957)
                      ·
                        rfl

theorem cell23_4675460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_4675460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675460 prefixEnd_4675460 := by exact prefixLift 4675460
  have htrace : WordTrace (prefixWord ++ tailWord_4675460) baseStart_4675460 baseEnd_4675460 := by
    simpa [prefixWord, tailWord_4675460, baseEnd_4675460] using wordTrace_append hprefix tailTrace_4675460
  have hstable : (prefixWord ++ tailWord_4675460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675460).length < 2 ^ (prefixWord ++ tailWord_4675460).sum := by decide
  have hdescent : baseEnd_4675460 < baseStart_4675460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675470 : List Nat := [4, 1, 1, 5, 1, 1, 1, 1, 2, 6]
def baseStart_4675470 : Nat := 118140960795 + 4675470 * 2 ^ 59
def prefixEnd_4675470 : Nat := 4983230072969 + 3 ^ 40 * 4675470 * 2
def baseEnd_4675470 : Nat := 800254465225642478607637

theorem tailTrace_4675470 : CollatzResearch.WordTrace tailWord_4675470 prefixEnd_4675470 800254465225642478607637 := by
  unfold tailWord_4675470
  simp only [CollatzResearch.WordTrace]
  refine ⟨21316050046447271443592983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113685600247718781032495909 21316050046447271443592983)
  ·
    refine ⟨31974075069670907165389475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21316050046447271443592983 31974075069670907165389475)
    ·
      refine ⟨47961112604506360748084213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31974075069670907165389475 47961112604506360748084213)
      ·
        refine ⟨4496354306672471320132895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47961112604506360748084213 4496354306672471320132895)
        ·
          refine ⟨6744531460008706980199343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4496354306672471320132895 6744531460008706980199343)
          ·
            refine ⟨10116797190013060470299015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6744531460008706980199343 10116797190013060470299015)
            ·
              refine ⟨15175195785019590705448523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10116797190013060470299015 15175195785019590705448523)
              ·
                refine ⟨22762793677529386058172785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15175195785019590705448523 22762793677529386058172785)
                ·
                  refine ⟨17072095258147039543629589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22762793677529386058172785 17072095258147039543629589)
                  ·
                    refine ⟨800254465225642478607637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17072095258147039543629589 800254465225642478607637)
                    ·
                      rfl

theorem cell23_4675470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_4675470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675470 prefixEnd_4675470 := by exact prefixLift 4675470
  have htrace : WordTrace (prefixWord ++ tailWord_4675470) baseStart_4675470 baseEnd_4675470 := by
    simpa [prefixWord, tailWord_4675470, baseEnd_4675470] using wordTrace_append hprefix tailTrace_4675470
  have hstable : (prefixWord ++ tailWord_4675470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675470).length < 2 ^ (prefixWord ++ tailWord_4675470).sum := by decide
  have hdescent : baseEnd_4675470 < baseStart_4675470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675506 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5]
def baseStart_4675506 : Nat := 118140960795 + 4675506 * 2 ^ 59
def prefixEnd_4675506 : Nat := 4983230072969 + 3 ^ 40 * 4675506 * 2
def baseEnd_4675506 : Nat := 2400781880980489294972745

theorem tailTrace_4675506 : CollatzResearch.WordTrace tailWord_4675506 prefixEnd_4675506 2400781880980489294972745 := by
  unfold tailWord_4675506
  simp only [CollatzResearch.WordTrace]
  refine ⟨42632428349861937424263593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113686475599631833131369581 42632428349861937424263593)
  ·
    refine ⟨31974321262396453068197695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42632428349861937424263593 31974321262396453068197695)
    ·
      refine ⟨47961481893594679602296543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31974321262396453068197695 47961481893594679602296543)
      ·
        refine ⟨71942222840392019403444815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47961481893594679602296543 71942222840392019403444815)
        ·
          refine ⟨107913334260588029105167223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71942222840392019403444815 107913334260588029105167223)
          ·
            refine ⟨161870001390882043657750835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107913334260588029105167223 161870001390882043657750835)
            ·
              refine ⟨242805002086323065486626253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161870001390882043657750835 242805002086323065486626253)
              ·
                refine ⟨91051875782371149557484845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 242805002086323065486626253 91051875782371149557484845)
                ·
                  refine ⟨34144453418389181084056817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91051875782371149557484845 34144453418389181084056817)
                  ·
                    refine ⟨25608340063791885813042613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34144453418389181084056817 25608340063791885813042613)
                    ·
                      refine ⟨2400781880980489294972745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25608340063791885813042613 2400781880980489294972745)
                      ·
                        rfl

theorem cell23_4675506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_4675506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675506 prefixEnd_4675506 := by exact prefixLift 4675506
  have htrace : WordTrace (prefixWord ++ tailWord_4675506) baseStart_4675506 baseEnd_4675506 := by
    simpa [prefixWord, tailWord_4675506, baseEnd_4675506] using wordTrace_append hprefix tailTrace_4675506
  have hstable : (prefixWord ++ tailWord_4675506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675506).length < 2 ^ (prefixWord ++ tailWord_4675506).sum := by decide
  have hdescent : baseEnd_4675506 < baseStart_4675506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675543 : List Nat := [1, 1, 3, 2, 1, 1, 3, 4, 3, 4]
def baseStart_4675543 : Nat := 118140960795 + 4675543 * 2 ^ 59
def prefixEnd_4675543 : Nat := 4983230072969 + 3 ^ 40 * 4675543 * 2
def baseEnd_4675543 : Nat := 800266959921568550070025

theorem tailTrace_4675543 : CollatzResearch.WordTrace tailWord_4675543 prefixEnd_4675543 800266959921568550070025 := by
  unfold tailWord_4675543
  simp only [CollatzResearch.WordTrace]
  refine ⟨170531062900313705016151283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113687375266875803344100855 170531062900313705016151283)
  ·
    refine ⟨255796594350470557524226925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170531062900313705016151283 255796594350470557524226925)
    ·
      refine ⟨95923722881426459071585097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255796594350470557524226925 95923722881426459071585097)
      ·
        refine ⟨71942792161069844303688823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95923722881426459071585097 71942792161069844303688823)
        ·
          refine ⟨107914188241604766455533235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71942792161069844303688823 107914188241604766455533235)
          ·
            refine ⟨161871282362407149683299853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107914188241604766455533235 161871282362407149683299853)
            ·
              refine ⟨60701730885902681131237445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161871282362407149683299853 60701730885902681131237445)
              ·
                refine ⟨11381574541106752712107021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60701730885902681131237445 11381574541106752712107021)
                ·
                  refine ⟨4268090452915032267040133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11381574541106752712107021 4268090452915032267040133)
                  ·
                    refine ⟨800266959921568550070025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4268090452915032267040133 800266959921568550070025)
                    ·
                      rfl

theorem cell23_4675543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 3, 4].length) (baseStart_4675543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675543 prefixEnd_4675543 := by exact prefixLift 4675543
  have htrace : WordTrace (prefixWord ++ tailWord_4675543) baseStart_4675543 baseEnd_4675543 := by
    simpa [prefixWord, tailWord_4675543, baseEnd_4675543] using wordTrace_append hprefix tailTrace_4675543
  have hstable : (prefixWord ++ tailWord_4675543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675543).length < 2 ^ (prefixWord ++ tailWord_4675543).sum := by decide
  have hdescent : baseEnd_4675543 < baseStart_4675543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675553 : List Nat := [1, 2, 3, 1, 2, 1, 4, 1, 1, 4, 3]
def baseStart_4675553 : Nat := 118140960795 + 4675553 * 2 ^ 59
def prefixEnd_4675553 : Nat := 4983230072969 + 3 ^ 40 * 4675553 * 2
def baseEnd_4675553 : Nat := 2400806014571250611085029

theorem tailTrace_4675553 : CollatzResearch.WordTrace tailWord_4675553 prefixEnd_4675553 2400806014571250611085029 := by
  unfold tailWord_4675553
  simp only [CollatzResearch.WordTrace]
  refine ⟨170531427630277476724015313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113687618420184984482676875 170531427630277476724015313)
  ·
    refine ⟨127898570722708107543011485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170531427630277476724015313 127898570722708107543011485)
    ·
      refine ⟨47961964021015540328629307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127898570722708107543011485 47961964021015540328629307)
      ·
        refine ⟨71942946031523310492943961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47961964021015540328629307 71942946031523310492943961)
        ·
          refine ⟨53957209523642482869707971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71942946031523310492943961 53957209523642482869707971)
          ·
            refine ⟨80935814285463724304561957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53957209523642482869707971 80935814285463724304561957)
            ·
              refine ⟨15175465178524448307105367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80935814285463724304561957 15175465178524448307105367)
              ·
                refine ⟨22763197767786672460658051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15175465178524448307105367 22763197767786672460658051)
                ·
                  refine ⟨34144796651680008690987077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22763197767786672460658051 34144796651680008690987077)
                  ·
                    refine ⟨6402149372190001629560077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34144796651680008690987077 6402149372190001629560077)
                    ·
                      refine ⟨2400806014571250611085029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6402149372190001629560077 2400806014571250611085029)
                      ·
                        rfl

theorem cell23_4675553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_4675553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675553 prefixEnd_4675553 := by exact prefixLift 4675553
  have htrace : WordTrace (prefixWord ++ tailWord_4675553) baseStart_4675553 baseEnd_4675553 := by
    simpa [prefixWord, tailWord_4675553, baseEnd_4675553] using wordTrace_append hprefix tailTrace_4675553
  have hstable : (prefixWord ++ tailWord_4675553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675553).length < 2 ^ (prefixWord ++ tailWord_4675553).sum := by decide
  have hdescent : baseEnd_4675553 < baseStart_4675553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675556 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 10]
def baseStart_4675556 : Nat := 118140960795 + 4675556 * 2 ^ 59
def prefixEnd_4675556 : Nat := 4983230072969 + 3 ^ 40 * 4675556 * 2
def baseEnd_4675556 : Nat := 266756395001468233260835

theorem tailTrace_4675556 : CollatzResearch.WordTrace tailWord_4675556 prefixEnd_4675556 266756395001468233260835 := by
  unfold tailWord_4675556
  simp only [CollatzResearch.WordTrace]
  refine ⟨85265768524633304118187261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113687691366177738824249681 85265768524633304118187261)
  ·
    refine ⟨31974663196737489044320223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85265768524633304118187261 31974663196737489044320223)
    ·
      refine ⟨47961994795106233566480335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31974663196737489044320223 47961994795106233566480335)
      ·
        refine ⟨71942992192659350349720503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47961994795106233566480335 71942992192659350349720503)
        ·
          refine ⟨107914488288989025524580755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71942992192659350349720503 107914488288989025524580755)
          ·
            refine ⟨161871732433483538286871133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107914488288989025524580755 161871732433483538286871133)
            ·
              refine ⟨60701899662556326857576675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161871732433483538286871133 60701899662556326857576675)
              ·
                refine ⟨91052849493834490286365013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60701899662556326857576675 91052849493834490286365013)
                ·
                  refine ⟨266756395001468233260835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 91052849493834490286365013 266756395001468233260835)
                  ·
                    rfl

theorem cell23_4675556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 10].length) (baseStart_4675556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675556 prefixEnd_4675556 := by exact prefixLift 4675556
  have htrace : WordTrace (prefixWord ++ tailWord_4675556) baseStart_4675556 baseEnd_4675556 := by
    simpa [prefixWord, tailWord_4675556, baseEnd_4675556] using wordTrace_append hprefix tailTrace_4675556
  have hstable : (prefixWord ++ tailWord_4675556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675556).length < 2 ^ (prefixWord ++ tailWord_4675556).sum := by decide
  have hdescent : baseEnd_4675556 < baseStart_4675556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675576 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 1, 1, 8]
def baseStart_4675576 : Nat := 118140960795 + 4675576 * 2 ^ 59
def prefixEnd_4675576 : Nat := 4983230072969 + 3 ^ 40 * 4675576 * 2
def baseEnd_4675576 : Nat := 2400817824626304021097423

theorem tailTrace_4675576 : CollatzResearch.WordTrace tailWord_4675576 prefixEnd_4675576 2400817824626304021097423 := by
  unfold tailWord_4675576
  simp only [CollatzResearch.WordTrace]
  refine ⟨85266133254597075826051291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113688177672796101101401721 85266133254597075826051291)
  ·
    refine ⟨127899199881895613739076937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85266133254597075826051291 127899199881895613739076937)
    ·
      refine ⟨95924399911421710304307703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127899199881895613739076937 95924399911421710304307703)
      ·
        refine ⟨143886599867132565456461555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95924399911421710304307703 143886599867132565456461555)
        ·
          refine ⟨215829899800698848184692333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143886599867132565456461555 215829899800698848184692333)
          ·
            refine ⟨80936212425262068069259625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 215829899800698848184692333 80936212425262068069259625)
            ·
              refine ⟨60702159318946551051944719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80936212425262068069259625 60702159318946551051944719)
              ·
                refine ⟨91053238978419826577917079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60702159318946551051944719 91053238978419826577917079)
                ·
                  refine ⟨136579858467629739866875619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91053238978419826577917079 136579858467629739866875619)
                  ·
                    refine ⟨204869787701444609800313429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 136579858467629739866875619 204869787701444609800313429)
                    ·
                      refine ⟨2400817824626304021097423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 204869787701444609800313429 2400817824626304021097423)
                      ·
                        rfl

theorem cell23_4675576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_4675576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675576 prefixEnd_4675576 := by exact prefixLift 4675576
  have htrace : WordTrace (prefixWord ++ tailWord_4675576) baseStart_4675576 baseEnd_4675576 := by
    simpa [prefixWord, tailWord_4675576, baseEnd_4675576] using wordTrace_append hprefix tailTrace_4675576
  have hstable : (prefixWord ++ tailWord_4675576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675576).length < 2 ^ (prefixWord ++ tailWord_4675576).sum := by decide
  have hdescent : baseEnd_4675576 < baseStart_4675576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675634 : List Nat := [3, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3]
def baseStart_4675634 : Nat := 118140960795 + 4675634 * 2 ^ 59
def prefixEnd_4675634 : Nat := 4983230072969 + 3 ^ 40 * 4675634 * 2
def baseEnd_4675634 : Nat := 2400847606504264794172157

theorem tailTrace_4675634 : CollatzResearch.WordTrace tailWord_4675634 prefixEnd_4675634 2400847606504264794172157 := by
  unfold tailWord_4675634
  simp only [CollatzResearch.WordTrace]
  refine ⟨42633595485746006889428489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113689587961989351705142637 42633595485746006889428489)
  ·
    refine ⟨31975196614309505167071367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42633595485746006889428489 31975196614309505167071367)
    ·
      refine ⟨47962794921464257750607051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31975196614309505167071367 47962794921464257750607051)
      ·
        refine ⟨71944192382196386625910577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47962794921464257750607051 71944192382196386625910577)
        ·
          refine ⟨53958144286647289969432933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71944192382196386625910577 53958144286647289969432933)
          ·
            refine ⟨10117152053746366869268675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53958144286647289969432933 10117152053746366869268675)
            ·
              refine ⟨15175728080619550303903013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10117152053746366869268675 15175728080619550303903013)
              ·
                refine ⟨2845449015116165681981815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15175728080619550303903013 2845449015116165681981815)
                ·
                  refine ⟨4268173522674248522972723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2845449015116165681981815 4268173522674248522972723)
                  ·
                    refine ⟨6402260284011372784459085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4268173522674248522972723 6402260284011372784459085)
                    ·
                      refine ⟨2400847606504264794172157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6402260284011372784459085 2400847606504264794172157)
                      ·
                        rfl

theorem cell23_4675634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3].length) (baseStart_4675634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675634 prefixEnd_4675634 := by exact prefixLift 4675634
  have htrace : WordTrace (prefixWord ++ tailWord_4675634) baseStart_4675634 baseEnd_4675634 := by
    simpa [prefixWord, tailWord_4675634, baseEnd_4675634] using wordTrace_append hprefix tailTrace_4675634
  have hstable : (prefixWord ++ tailWord_4675634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675634).length < 2 ^ (prefixWord ++ tailWord_4675634).sum := by decide
  have hdescent : baseEnd_4675634 < baseStart_4675634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675657 : List Nat := [1, 2, 1, 1, 2, 2, 5, 2, 3, 2, 2]
def baseStart_4675657 : Nat := 118140960795 + 4675657 * 2 ^ 59
def prefixEnd_4675657 : Nat := 4983230072969 + 3 ^ 40 * 4675657 * 2
def baseEnd_4675657 : Nat := 2400859416559318204184551

theorem tailTrace_4675657 : CollatzResearch.WordTrace tailWord_4675657 prefixEnd_4675657 2400859416559318204184551 := by
  unfold tailWord_4675657
  simp only [CollatzResearch.WordTrace]
  refine ⟨170535220821900702485801225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113690147214600468323867483 170535220821900702485801225)
  ·
    refine ⟨127901415616425526864350919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170535220821900702485801225 127901415616425526864350919)
    ·
      refine ⟨191852123424638290296526379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127901415616425526864350919 191852123424638290296526379)
      ·
        refine ⟨287778185136957435444789569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191852123424638290296526379 287778185136957435444789569)
        ·
          refine ⟨215833638852718076583592177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287778185136957435444789569 215833638852718076583592177)
          ·
            refine ⟨161875229139538557437694133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215833638852718076583592177 161875229139538557437694133)
            ·
              refine ⟨15175802731831739759783825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 161875229139538557437694133 15175802731831739759783825)
              ·
                refine ⟨11381852048873804819837869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15175802731831739759783825 11381852048873804819837869)
                ·
                  refine ⟨4268194518327676807439201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11381852048873804819837869 4268194518327676807439201)
                  ·
                    refine ⟨3201145888745757605579401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4268194518327676807439201 3201145888745757605579401)
                    ·
                      refine ⟨2400859416559318204184551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3201145888745757605579401 2400859416559318204184551)
                      ·
                        rfl

theorem cell23_4675657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 3, 2, 2].length) (baseStart_4675657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675657 prefixEnd_4675657 := by exact prefixLift 4675657
  have htrace : WordTrace (prefixWord ++ tailWord_4675657) baseStart_4675657 baseEnd_4675657 := by
    simpa [prefixWord, tailWord_4675657, baseEnd_4675657] using wordTrace_append hprefix tailTrace_4675657
  have hstable : (prefixWord ++ tailWord_4675657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675657).length < 2 ^ (prefixWord ++ tailWord_4675657).sum := by decide
  have hdescent : baseEnd_4675657 < baseStart_4675657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675660 : List Nat := [2, 2, 1, 3, 1, 1, 4, 1, 3, 2, 3]
def baseStart_4675660 : Nat := 118140960795 + 4675660 * 2 ^ 59
def prefixEnd_4675660 : Nat := 4983230072969 + 3 ^ 40 * 4675660 * 2
def baseEnd_4675660 : Nat := 2400860957001281692447037

theorem tailTrace_4675660 : CollatzResearch.WordTrace tailWord_4675660 prefixEnd_4675660 2400860957001281692447037 := by
  unfold tailWord_4675660
  simp only [CollatzResearch.WordTrace]
  refine ⟨85267665120444916999080217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113690220160593222665440289 85267665120444916999080217)
  ·
    refine ⟨63950748840333687749310163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85267665120444916999080217 63950748840333687749310163)
    ·
      refine ⟨95926123260500531623965245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63950748840333687749310163 95926123260500531623965245)
      ·
        refine ⟨35972296222687699358986967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95926123260500531623965245 35972296222687699358986967)
        ·
          refine ⟨53958444334031549038480451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35972296222687699358986967 53958444334031549038480451)
          ·
            refine ⟨80937666501047323557720677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53958444334031549038480451 80937666501047323557720677)
            ·
              refine ⟨15175812468946373167072627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80937666501047323557720677 15175812468946373167072627)
              ·
                refine ⟨22763718703419559750608941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15175812468946373167072627 22763718703419559750608941)
                ·
                  refine ⟨8536394513782334906478353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22763718703419559750608941 8536394513782334906478353)
                  ·
                    refine ⟨6402295885336751179858765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8536394513782334906478353 6402295885336751179858765)
                    ·
                      refine ⟨2400860957001281692447037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6402295885336751179858765 2400860957001281692447037)
                      ·
                        rfl

theorem cell23_4675660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_4675660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675660 prefixEnd_4675660 := by exact prefixLift 4675660
  have htrace : WordTrace (prefixWord ++ tailWord_4675660) baseStart_4675660 baseEnd_4675660 := by
    simpa [prefixWord, tailWord_4675660, baseEnd_4675660] using wordTrace_append hprefix tailTrace_4675660
  have hstable : (prefixWord ++ tailWord_4675660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675660).length < 2 ^ (prefixWord ++ tailWord_4675660).sum := by decide
  have hdescent : baseEnd_4675660 < baseStart_4675660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675720 : List Nat := [2, 1, 3, 4, 1, 1, 1, 1, 2, 2, 5]
def baseStart_4675720 : Nat := 118140960795 + 4675720 * 2 ^ 59
def prefixEnd_4675720 : Nat := 4983230072969 + 3 ^ 40 * 4675720 * 2
def baseEnd_4675720 : Nat := 2400891765840551457696761

theorem tailTrace_4675720 : CollatzResearch.WordTrace tailWord_4675720 prefixEnd_4675720 2400891765840551457696761 := by
  unfold tailWord_4675720
  simp only [CollatzResearch.WordTrace]
  refine ⟨85268759310336232122672307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113691679080448309496896409 85268759310336232122672307)
  ·
    refine ⟨127903138965504348184008461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85268759310336232122672307 127903138965504348184008461)
    ·
      refine ⟨47963677112064130569003173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127903138965504348184008461 47963677112064130569003173)
      ·
        refine ⟨8993189458512024481688095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47963677112064130569003173 8993189458512024481688095)
        ·
          refine ⟨13489784187768036722532143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8993189458512024481688095 13489784187768036722532143)
          ·
            refine ⟨20234676281652055083798215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13489784187768036722532143 20234676281652055083798215)
            ·
              refine ⟨30352014422478082625697323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20234676281652055083798215 30352014422478082625697323)
              ·
                refine ⟨45528021633717123938545985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30352014422478082625697323 45528021633717123938545985)
                ·
                  refine ⟨34146016225287842953909489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45528021633717123938545985 34146016225287842953909489)
                  ·
                    refine ⟨25609512168965882215432117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34146016225287842953909489 25609512168965882215432117)
                    ·
                      refine ⟨2400891765840551457696761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25609512168965882215432117 2400891765840551457696761)
                      ·
                        rfl

theorem cell23_4675720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_4675720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675720 prefixEnd_4675720 := by exact prefixLift 4675720
  have htrace : WordTrace (prefixWord ++ tailWord_4675720) baseStart_4675720 baseEnd_4675720 := by
    simpa [prefixWord, tailWord_4675720, baseEnd_4675720] using wordTrace_append hprefix tailTrace_4675720
  have hstable : (prefixWord ++ tailWord_4675720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675720).length < 2 ^ (prefixWord ++ tailWord_4675720).sum := by decide
  have hdescent : baseEnd_4675720 < baseStart_4675720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675758 : List Nat := [4, 1, 4, 2, 1, 1, 1, 3, 2, 1, 3]
def baseStart_4675758 : Nat := 118140960795 + 4675758 * 2 ^ 59
def prefixEnd_4675758 : Nat := 4983230072969 + 3 ^ 40 * 4675758 * 2
def baseEnd_4675758 : Nat := 2400911278105422309021587

theorem tailTrace_4675758 : CollatzResearch.WordTrace tailWord_4675758 prefixEnd_4675758 2400911278105422309021587 := by
  unfold tailWord_4675758
  simp only [CollatzResearch.WordTrace]
  refine ⟨21317363074316849591903491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113692603063023197823485285 21317363074316849591903491)
  ·
    refine ⟨31976044611475274387855237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21317363074316849591903491 31976044611475274387855237)
    ·
      refine ⟨5995508364651613947722857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31976044611475274387855237 5995508364651613947722857)
      ·
        refine ⟨4496631273488710460792143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5995508364651613947722857 4496631273488710460792143)
        ·
          refine ⟨6744946910233065691188215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4496631273488710460792143 6744946910233065691188215)
          ·
            refine ⟨10117420365349598536782323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6744946910233065691188215 10117420365349598536782323)
            ·
              refine ⟨15176130548024397805173485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10117420365349598536782323 15176130548024397805173485)
              ·
                refine ⟨5691048955509149176940057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15176130548024397805173485 5691048955509149176940057)
                ·
                  refine ⟨4268286716631861882705043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5691048955509149176940057 4268286716631861882705043)
                  ·
                    refine ⟨6402430074947792824057565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4268286716631861882705043 6402430074947792824057565)
                    ·
                      refine ⟨2400911278105422309021587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6402430074947792824057565 2400911278105422309021587)
                      ·
                        rfl

theorem cell23_4675758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_4675758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675758 prefixEnd_4675758 := by exact prefixLift 4675758
  have htrace : WordTrace (prefixWord ++ tailWord_4675758) baseStart_4675758 baseEnd_4675758 := by
    simpa [prefixWord, tailWord_4675758, baseEnd_4675758] using wordTrace_append hprefix tailTrace_4675758
  have hstable : (prefixWord ++ tailWord_4675758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675758).length < 2 ^ (prefixWord ++ tailWord_4675758).sum := by decide
  have hdescent : baseEnd_4675758 < baseStart_4675758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675798 : List Nat := [5, 2, 1, 2, 1, 1, 1, 4, 2, 2, 2]
def baseStart_4675798 : Nat := 118140960795 + 4675798 * 2 ^ 59
def prefixEnd_4675798 : Nat := 4983230072969 + 3 ^ 40 * 4675798 * 2
def baseEnd_4675798 : Nat := 2400931817331602152521403

theorem tailTrace_4675798 : CollatzResearch.WordTrace tailWord_4675798 prefixEnd_4675798 2400931817331602152521403 := by
  unfold tailWord_4675798
  simp only [CollatzResearch.WordTrace]
  refine ⟨10658772719649367722917753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113693575676259922377789365 10658772719649367722917753)
  ·
    refine ⟨7994079539737025792188315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10658772719649367722917753 7994079539737025792188315)
    ·
      refine ⟨11991119309605538688282473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7994079539737025792188315 11991119309605538688282473)
      ·
        refine ⟨8993339482204154016211855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11991119309605538688282473 8993339482204154016211855)
        ·
          refine ⟨13490009223306231024317783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8993339482204154016211855 13490009223306231024317783)
          ·
            refine ⟨20235013834959346536476675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13490009223306231024317783 20235013834959346536476675)
            ·
              refine ⟨30352520752439019804715013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20235013834959346536476675 30352520752439019804715013)
              ·
                refine ⟨5691097641082316213384065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30352520752439019804715013 5691097641082316213384065)
                ·
                  refine ⟨4268323230811737160038049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5691097641082316213384065 4268323230811737160038049)
                  ·
                    refine ⟨3201242423108802870028537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4268323230811737160038049 3201242423108802870028537)
                    ·
                      refine ⟨2400931817331602152521403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3201242423108802870028537 2400931817331602152521403)
                      ·
                        rfl

theorem cell23_4675798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_4675798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675798 prefixEnd_4675798 := by exact prefixLift 4675798
  have htrace : WordTrace (prefixWord ++ tailWord_4675798) baseStart_4675798 baseEnd_4675798 := by
    simpa [prefixWord, tailWord_4675798, baseEnd_4675798] using wordTrace_append hprefix tailTrace_4675798
  have hstable : (prefixWord ++ tailWord_4675798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675798).length < 2 ^ (prefixWord ++ tailWord_4675798).sum := by decide
  have hdescent : baseEnd_4675798 < baseStart_4675798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675820 : List Nat := [2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 4]
def baseStart_4675820 : Nat := 118140960795 + 4675820 * 2 ^ 59
def prefixEnd_4675820 : Nat := 4983230072969 + 3 ^ 40 * 4675820 * 2
def baseEnd_4675820 : Nat := 2400943113906001066446301

theorem tailTrace_4675820 : CollatzResearch.WordTrace tailWord_4675820 prefixEnd_4675820 2400943113906001066446301 := by
  unfold tailWord_4675820
  simp only [CollatzResearch.WordTrace]
  refine ⟨85270582960155090661992457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113694110613540120882656609 85270582960155090661992457)
  ·
    refine ⟨63952937220116317996494343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85270582960155090661992457 63952937220116317996494343)
    ·
      refine ⟨95929405830174476994741515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63952937220116317996494343 95929405830174476994741515)
      ·
        refine ⟨143894108745261715492112273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95929405830174476994741515 143894108745261715492112273)
        ·
          refine ⟨107920581558946286619084205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143894108745261715492112273 107920581558946286619084205)
          ·
            refine ⟨40470218084604857482156577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107920581558946286619084205 40470218084604857482156577)
            ·
              refine ⟨30352663563453643111617433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40470218084604857482156577 30352663563453643111617433)
              ·
                refine ⟨22764497672590232333713075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30352663563453643111617433 22764497672590232333713075)
                ·
                  refine ⟨34146746508885348500569613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22764497672590232333713075 34146746508885348500569613)
                  ·
                    refine ⟨12805029940832005687713605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34146746508885348500569613 12805029940832005687713605)
                    ·
                      refine ⟨2400943113906001066446301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12805029940832005687713605 2400943113906001066446301)
                      ·
                        rfl

theorem cell23_4675820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_4675820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675820 prefixEnd_4675820 := by exact prefixLift 4675820
  have htrace : WordTrace (prefixWord ++ tailWord_4675820) baseStart_4675820 baseEnd_4675820 := by
    simpa [prefixWord, tailWord_4675820, baseEnd_4675820] using wordTrace_append hprefix tailTrace_4675820
  have hstable : (prefixWord ++ tailWord_4675820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675820).length < 2 ^ (prefixWord ++ tailWord_4675820).sum := by decide
  have hdescent : baseEnd_4675820 < baseStart_4675820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675850 : List Nat := [3, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6]
def baseStart_4675850 : Nat := 118140960795 + 4675850 * 2 ^ 59
def prefixEnd_4675850 : Nat := 4983230072969 + 3 ^ 40 * 4675850 * 2
def baseEnd_4675850 : Nat := 2400958518325635949071163

theorem tailTrace_4675850 : CollatzResearch.WordTrace tailWord_4675850 prefixEnd_4675850 2400958518325635949071163 := by
  unfold tailWord_4675850
  simp only [CollatzResearch.WordTrace]
  refine ⟨42635565027550374111894251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113694840073467664298384669 42635565027550374111894251)
  ·
    refine ⟨63953347541325561167841377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42635565027550374111894251 63953347541325561167841377)
    ·
      refine ⟨47965010655994170875881033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63953347541325561167841377 47965010655994170875881033)
      ·
        refine ⟨35973757991995628156910775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47965010655994170875881033 35973757991995628156910775)
        ·
          refine ⟨53960636987993442235366163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35973757991995628156910775 53960636987993442235366163)
          ·
            refine ⟨80940955481990163353049245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53960636987993442235366163 80940955481990163353049245)
            ·
              refine ⟨30352858305746311257393467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80940955481990163353049245 30352858305746311257393467)
              ·
                refine ⟨45529287458619466886090201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30352858305746311257393467 45529287458619466886090201)
                ·
                  refine ⟨34146965593964600164567651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45529287458619466886090201 34146965593964600164567651)
                  ·
                    refine ⟨51220448390946900246851477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34146965593964600164567651 51220448390946900246851477)
                    ·
                      refine ⟨2400958518325635949071163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51220448390946900246851477 2400958518325635949071163)
                      ·
                        rfl

theorem cell23_4675850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_4675850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675850 prefixEnd_4675850 := by exact prefixLift 4675850
  have htrace : WordTrace (prefixWord ++ tailWord_4675850) baseStart_4675850 baseEnd_4675850 := by
    simpa [prefixWord, tailWord_4675850, baseEnd_4675850] using wordTrace_append hprefix tailTrace_4675850
  have hstable : (prefixWord ++ tailWord_4675850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675850).length < 2 ^ (prefixWord ++ tailWord_4675850).sum := by decide
  have hdescent : baseEnd_4675850 < baseStart_4675850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675864 : List Nat := [2, 1, 2, 3, 1, 2, 1, 6, 1, 4]
def baseStart_4675864 : Nat := 118140960795 + 4675864 * 2 ^ 59
def prefixEnd_4675864 : Nat := 4983230072969 + 3 ^ 40 * 4675864 * 2
def baseEnd_4675864 : Nat := 800321902351599631432033

theorem tailTrace_4675864 : CollatzResearch.WordTrace tailWord_4675864 prefixEnd_4675864 800321902351599631432033 := by
  unfold tailWord_4675864
  simp only [CollatzResearch.WordTrace]
  refine ⟨85271385366075388419293323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113695180488100517892391097 85271385366075388419293323)
  ·
    refine ⟨127907078049113082628939985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85271385366075388419293323 127907078049113082628939985)
    ·
      refine ⟨95930308536834811971704989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127907078049113082628939985 95930308536834811971704989)
      ·
        refine ⟨35973865701313054489389371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95930308536834811971704989 35973865701313054489389371)
        ·
          refine ⟨53960798551969581734084057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35973865701313054489389371 53960798551969581734084057)
          ·
            refine ⟨40470598913977186300563043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53960798551969581734084057 40470598913977186300563043)
            ·
              refine ⟨60705898370965779450844565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40470598913977186300563043 60705898370965779450844565)
              ·
                refine ⟨2845588986139020911758339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60705898370965779450844565 2845588986139020911758339)
                ·
                  refine ⟨4268383479208531367637509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2845588986139020911758339 4268383479208531367637509)
                  ·
                    refine ⟨800321902351599631432033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4268383479208531367637509 800321902351599631432033)
                    ·
                      rfl

theorem cell23_4675864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 6, 1, 4].length) (baseStart_4675864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675864 prefixEnd_4675864 := by exact prefixLift 4675864
  have htrace : WordTrace (prefixWord ++ tailWord_4675864) baseStart_4675864 baseEnd_4675864 := by
    simpa [prefixWord, tailWord_4675864, baseEnd_4675864] using wordTrace_append hprefix tailTrace_4675864
  have hstable : (prefixWord ++ tailWord_4675864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675864).length < 2 ^ (prefixWord ++ tailWord_4675864).sum := by decide
  have hdescent : baseEnd_4675864 < baseStart_4675864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675907 : List Nat := [1, 1, 1, 3, 1, 3, 4, 3, 1, 5]
def baseStart_4675907 : Nat := 118140960795 + 4675907 * 2 ^ 59
def prefixEnd_4675907 : Nat := 4983230072969 + 3 ^ 40 * 4675907 * 2
def baseEnd_4675907 : Nat := 800329262240980742019467

theorem tailTrace_4675907 : CollatzResearch.WordTrace tailWord_4675907 prefixEnd_4675907 800329262240980742019467 := by
  unfold tailWord_4675907
  simp only [CollatzResearch.WordTrace]
  refine ⟨170544339070994995182401975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113696226047329996788267983 170544339070994995182401975)
  ·
    refine ⟨255816508606492492773602963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170544339070994995182401975 255816508606492492773602963)
    ·
      refine ⟨383724762909738739160404445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255816508606492492773602963 383724762909738739160404445)
      ·
        refine ⟨143896786091152027185151667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 383724762909738739160404445 143896786091152027185151667)
        ·
          refine ⟨215845179136728040777727501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143896786091152027185151667 215845179136728040777727501)
          ·
            refine ⟨80941942176273015291647813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 215845179136728040777727501 80941942176273015291647813)
            ·
              refine ⟨15176614158051190367183965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80941942176273015291647813 15176614158051190367183965)
              ·
                refine ⟨5691230309269196387693987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15176614158051190367183965 5691230309269196387693987)
                ·
                  refine ⟨8536845463903794581540981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5691230309269196387693987 8536845463903794581540981)
                  ·
                    refine ⟨800329262240980742019467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8536845463903794581540981 800329262240980742019467)
                    ·
                      rfl

theorem cell23_4675907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 5].length) (baseStart_4675907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675907 prefixEnd_4675907 := by exact prefixLift 4675907
  have htrace : WordTrace (prefixWord ++ tailWord_4675907) baseStart_4675907 baseEnd_4675907 := by
    simpa [prefixWord, tailWord_4675907, baseEnd_4675907] using wordTrace_append hprefix tailTrace_4675907
  have hstable : (prefixWord ++ tailWord_4675907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675907).length < 2 ^ (prefixWord ++ tailWord_4675907).sum := by decide
  have hdescent : baseEnd_4675907 < baseStart_4675907 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675921 : List Nat := [1, 2, 2, 1, 4, 4, 1, 1, 3, 1, 3]
def baseStart_4675921 : Nat := 118140960795 + 4675921 * 2 ^ 59
def prefixEnd_4675921 : Nat := 4983230072969 + 3 ^ 40 * 4675921 * 2
def baseEnd_4675921 : Nat := 2400994975452105171283337

theorem tailTrace_4675921 : CollatzResearch.WordTrace tailWord_4675921 prefixEnd_4675921 2400994975452105171283337 := by
  unfold tailWord_4675921
  simp only [CollatzResearch.WordTrace]
  refine ⟨170544849692944275573411617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113696566461962850382274411 170544849692944275573411617)
  ·
    refine ⟨127908637269708206680058713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170544849692944275573411617 127908637269708206680058713)
    ·
      refine ⟨95931477952281155010044035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127908637269708206680058713 95931477952281155010044035)
      ·
        refine ⟨143897216928421732515066053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95931477952281155010044035 143897216928421732515066053)
        ·
          refine ⟨26980728174079074846574885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143897216928421732515066053 26980728174079074846574885)
          ·
            refine ⟨5058886532639826533732791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26980728174079074846574885 5058886532639826533732791)
            ·
              refine ⟨7588329798959739800599187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5058886532639826533732791 7588329798959739800599187)
              ·
                refine ⟨11382494698439609700898781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7588329798959739800599187 11382494698439609700898781)
                ·
                  refine ⟨4268435511914853637837043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11382494698439609700898781 4268435511914853637837043)
                  ·
                    refine ⟨6402653267872280456755565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4268435511914853637837043 6402653267872280456755565)
                    ·
                      refine ⟨2400994975452105171283337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6402653267872280456755565 2400994975452105171283337)
                      ·
                        rfl

theorem cell23_4675921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 3, 1, 3].length) (baseStart_4675921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675921 prefixEnd_4675921 := by exact prefixLift 4675921
  have htrace : WordTrace (prefixWord ++ tailWord_4675921) baseStart_4675921 baseEnd_4675921 := by
    simpa [prefixWord, tailWord_4675921, baseEnd_4675921] using wordTrace_append hprefix tailTrace_4675921
  have hstable : (prefixWord ++ tailWord_4675921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675921).length < 2 ^ (prefixWord ++ tailWord_4675921).sum := by decide
  have hdescent : baseEnd_4675921 < baseStart_4675921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675927 : List Nat := [1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 4]
def baseStart_4675927 : Nat := 118140960795 + 4675927 * 2 ^ 59
def prefixEnd_4675927 : Nat := 4983230072969 + 3 ^ 40 * 4675927 * 2
def baseEnd_4675927 : Nat := 2400998056336032147808309

theorem tailTrace_4675927 : CollatzResearch.WordTrace tailWord_4675927 prefixEnd_4675927 2400998056336032147808309 := by
  unfold tailWord_4675927
  simp only [CollatzResearch.WordTrace]
  refine ⟨170545068530922538598130035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113696712353948359065420023 170545068530922538598130035)
  ·
    refine ⟨255817602796383807897195053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170545068530922538598130035 255817602796383807897195053)
    ·
      refine ⟨95931601048643927961448145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255817602796383807897195053 95931601048643927961448145)
      ·
        refine ⟨71948700786482945971086109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95931601048643927961448145 71948700786482945971086109)
        ·
          refine ⟨26980762794931104739157291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71948700786482945971086109 26980762794931104739157291)
          ·
            refine ⟨40471144192396657108735937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26980762794931104739157291 40471144192396657108735937)
            ·
              refine ⟨30353358144297492831551953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40471144192396657108735937 30353358144297492831551953)
              ·
                refine ⟨22765018608223119623663965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30353358144297492831551953 22765018608223119623663965)
                ·
                  refine ⟨8536881978083669858873987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22765018608223119623663965 8536881978083669858873987)
                  ·
                    refine ⟨12805322967125504788310981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8536881978083669858873987 12805322967125504788310981)
                    ·
                      refine ⟨2400998056336032147808309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12805322967125504788310981 2400998056336032147808309)
                      ·
                        rfl

theorem cell23_4675927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_4675927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675927 prefixEnd_4675927 := by exact prefixLift 4675927
  have htrace : WordTrace (prefixWord ++ tailWord_4675927) baseStart_4675927 baseEnd_4675927 := by
    simpa [prefixWord, tailWord_4675927, baseEnd_4675927] using wordTrace_append hprefix tailTrace_4675927
  have hstable : (prefixWord ++ tailWord_4675927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675927).length < 2 ^ (prefixWord ++ tailWord_4675927).sum := by decide
  have hdescent : baseEnd_4675927 < baseStart_4675927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675944 : List Nat := [2, 1, 4, 2, 2, 2, 1, 1, 3, 1, 4]
def baseStart_4675944 : Nat := 118140960795 + 4675944 * 2 ^ 59
def prefixEnd_4675944 : Nat := 4983230072969 + 3 ^ 40 * 4675944 * 2
def baseEnd_4675944 : Nat := 2401006785507158581295731

theorem tailTrace_4675944 : CollatzResearch.WordTrace tailWord_4675944 prefixEnd_4675944 2401006785507158581295731 := by
  unfold tailWord_4675944
  simp only [CollatzResearch.WordTrace]
  refine ⟨85272844285930475250749443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113697125714573967000999257 85272844285930475250749443)
  ·
    refine ⟨127909266428895712876124165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85272844285930475250749443 127909266428895712876124165)
    ·
      refine ⟨23982987455417946164273281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127909266428895712876124165 23982987455417946164273281)
      ·
        refine ⟨17987240591563459623204961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23982987455417946164273281 17987240591563459623204961)
        ·
          refine ⟨13490430443672594717403721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17987240591563459623204961 13490430443672594717403721)
          ·
            refine ⟨10117822832754446038052791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13490430443672594717403721 10117822832754446038052791)
            ·
              refine ⟨15176734249131669057079187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10117822832754446038052791 15176734249131669057079187)
              ·
                refine ⟨22765101373697503585618781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15176734249131669057079187 22765101373697503585618781)
                ·
                  refine ⟨8536913015136563844607043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22765101373697503585618781 8536913015136563844607043)
                  ·
                    refine ⟨12805369522704845766910565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8536913015136563844607043 12805369522704845766910565)
                    ·
                      refine ⟨2401006785507158581295731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12805369522704845766910565 2401006785507158581295731)
                      ·
                        rfl

theorem cell23_4675944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_4675944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675944 prefixEnd_4675944 := by exact prefixLift 4675944
  have htrace : WordTrace (prefixWord ++ tailWord_4675944) baseStart_4675944 baseEnd_4675944 := by
    simpa [prefixWord, tailWord_4675944, baseEnd_4675944] using wordTrace_append hprefix tailTrace_4675944
  have hstable : (prefixWord ++ tailWord_4675944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675944).length < 2 ^ (prefixWord ++ tailWord_4675944).sum := by decide
  have hdescent : baseEnd_4675944 < baseStart_4675944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675947 : List Nat := [1, 1, 1, 1, 2, 2, 2, 5, 3, 2, 3]
def baseStart_4675947 : Nat := 118140960795 + 4675947 * 2 ^ 59
def prefixEnd_4675947 : Nat := 4983230072969 + 3 ^ 40 * 4675947 * 2
def baseEnd_4675947 : Nat := 2401008325949122069558217

theorem tailTrace_4675947 : CollatzResearch.WordTrace tailWord_4675947 prefixEnd_4675947 2401008325949122069558217 := by
  unfold tailWord_4675947
  simp only [CollatzResearch.WordTrace]
  refine ⟨170545797990850082013858095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113697198660566721342572063 170545797990850082013858095)
  ·
    refine ⟨255818696986275123020787143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170545797990850082013858095 255818696986275123020787143)
    ·
      refine ⟨383728045479412684531180715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255818696986275123020787143 383728045479412684531180715)
      ·
        refine ⟨575592068219119026796771073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383728045479412684531180715 575592068219119026796771073)
        ·
          refine ⟨431694051164339270097578305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 575592068219119026796771073 431694051164339270097578305)
          ·
            refine ⟨323770538373254452573183729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 431694051164339270097578305 323770538373254452573183729)
            ·
              refine ⟨242827903779940839429887797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 323770538373254452573183729 242827903779940839429887797)
              ·
                refine ⟨22765115979369453696551981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 242827903779940839429887797 22765115979369453696551981)
                ·
                  refine ⟨8536918492263545136206993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22765115979369453696551981 8536918492263545136206993)
                  ·
                    refine ⟨6402688869197658852155245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8536918492263545136206993 6402688869197658852155245)
                    ·
                      refine ⟨2401008325949122069558217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6402688869197658852155245 2401008325949122069558217)
                      ·
                        rfl

theorem cell23_4675947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 2, 3].length) (baseStart_4675947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675947 prefixEnd_4675947 := by exact prefixLift 4675947
  have htrace : WordTrace (prefixWord ++ tailWord_4675947) baseStart_4675947 baseEnd_4675947 := by
    simpa [prefixWord, tailWord_4675947, baseEnd_4675947] using wordTrace_append hprefix tailTrace_4675947
  have hstable : (prefixWord ++ tailWord_4675947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675947).length < 2 ^ (prefixWord ++ tailWord_4675947).sum := by decide
  have hdescent : baseEnd_4675947 < baseStart_4675947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675971 : List Nat := [1, 1, 1, 3, 6, 1, 2, 2, 2, 4]
def baseStart_4675971 : Nat := 118140960795 + 4675971 * 2 ^ 59
def prefixEnd_4675971 : Nat := 4983230072969 + 3 ^ 40 * 4675971 * 2
def baseEnd_4675971 : Nat := 800340216494943325219369

theorem tailTrace_4675971 : CollatzResearch.WordTrace tailWord_4675971 prefixEnd_4675971 800340216494943325219369 := by
  unfold tailWord_4675971
  simp only [CollatzResearch.WordTrace]
  refine ⟨170546673342763134112731767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113697782228508756075154511 170546673342763134112731767)
  ·
    refine ⟨255820010014144701169097651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170546673342763134112731767 255820010014144701169097651)
    ·
      refine ⟨383730015021217051753646477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255820010014144701169097651 383730015021217051753646477)
      ·
        refine ⟨143898755632956394407617429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 383730015021217051753646477 143898755632956394407617429)
        ·
          refine ⟨6745254170294830987857067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 143898755632956394407617429 6745254170294830987857067)
          ·
            refine ⟨10117881255442246481785601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6745254170294830987857067 10117881255442246481785601)
            ·
              refine ⟨7588410941581684861339201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10117881255442246481785601 7588410941581684861339201)
              ·
                refine ⟨5691308206186263646004401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7588410941581684861339201 5691308206186263646004401)
                ·
                  refine ⟨4268481154639697734503301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5691308206186263646004401 4268481154639697734503301)
                  ·
                    refine ⟨800340216494943325219369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4268481154639697734503301 800340216494943325219369)
                    ·
                      rfl

theorem cell23_4675971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 2, 4].length) (baseStart_4675971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675971 prefixEnd_4675971 := by exact prefixLift 4675971
  have htrace : WordTrace (prefixWord ++ tailWord_4675971) baseStart_4675971 baseEnd_4675971 := by
    simpa [prefixWord, tailWord_4675971, baseEnd_4675971] using wordTrace_append hprefix tailTrace_4675971
  have hstable : (prefixWord ++ tailWord_4675971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675971).length < 2 ^ (prefixWord ++ tailWord_4675971).sum := by decide
  have hdescent : baseEnd_4675971 < baseStart_4675971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4675994 : List Nat := [3, 1, 1, 4, 1, 2, 1, 3, 1, 3, 3]
def baseStart_4675994 : Nat := 118140960795 + 4675994 * 2 ^ 59
def prefixEnd_4675994 : Nat := 4983230072969 + 3 ^ 40 * 4675994 * 2
def baseEnd_4675994 : Nat := 2401032459539883385670501

theorem tailTrace_4675994 : CollatzResearch.WordTrace tailWord_4675994 prefixEnd_4675994 2401032459539883385670501 := by
  unfold tailWord_4675994
  simp only [CollatzResearch.WordTrace]
  refine ⟨42636878055419952260204759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113698341481119872693879357 42636878055419952260204759)
  ·
    refine ⟨63955317083129928390307139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42636878055419952260204759 63955317083129928390307139)
    ·
      refine ⟨95932975624694892585460709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63955317083129928390307139 95932975624694892585460709)
      ·
        refine ⟨17987432929630292359773883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95932975624694892585460709 17987432929630292359773883)
        ·
          refine ⟨26981149394445438539660825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17987432929630292359773883 26981149394445438539660825)
          ·
            refine ⟨20235862045834078904745619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26981149394445438539660825 20235862045834078904745619)
            ·
              refine ⟨30353793068751118357118429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20235862045834078904745619 30353793068751118357118429)
              ·
                refine ⟨11382672400781669383919411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30353793068751118357118429 11382672400781669383919411)
                ·
                  refine ⟨17074008601172504075879117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11382672400781669383919411 17074008601172504075879117)
                  ·
                    refine ⟨6402753225439689028454669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17074008601172504075879117 6402753225439689028454669)
                    ·
                      refine ⟨2401032459539883385670501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6402753225439689028454669 2401032459539883385670501)
                      ·
                        rfl

theorem cell23_4675994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_4675994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4675994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4675994 prefixEnd_4675994 := by exact prefixLift 4675994
  have htrace : WordTrace (prefixWord ++ tailWord_4675994) baseStart_4675994 baseEnd_4675994 := by
    simpa [prefixWord, tailWord_4675994, baseEnd_4675994] using wordTrace_append hprefix tailTrace_4675994
  have hstable : (prefixWord ++ tailWord_4675994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4675994).length < 2 ^ (prefixWord ++ tailWord_4675994).sum := by decide
  have hdescent : baseEnd_4675994 < baseStart_4675994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4675994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676001 : List Nat := [1, 2, 3, 5, 1, 1, 3, 7]
def baseStart_4676001 : Nat := 118140960795 + 4676001 * 2 ^ 59
def prefixEnd_4676001 : Nat := 4983230072969 + 3 ^ 40 * 4676001 * 2
def baseEnd_4676001 : Nat := 88927261255720920677147

theorem tailTrace_4676001 : CollatzResearch.WordTrace tailWord_4676001 prefixEnd_4676001 88927261255720920677147 := by
  unfold tailWord_4676001
  simp only [CollatzResearch.WordTrace]
  refine ⟨170547767532654449236323857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113698511688436299490882571 170547767532654449236323857)
  ·
    refine ⟨127910825649490836927242893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170547767532654449236323857 127910825649490836927242893)
    ·
      refine ⟨47966559618559063847716085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127910825649490836927242893 47966559618559063847716085)
      ·
        refine ⟨4496864964239912235723383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47966559618559063847716085 4496864964239912235723383)
        ·
          refine ⟨6745297446359868353585075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4496864964239912235723383 6745297446359868353585075)
          ·
            refine ⟨10117946169539802530377613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6745297446359868353585075 10117946169539802530377613)
            ·
              refine ⟨3794229813577425948891605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10117946169539802530377613 3794229813577425948891605)
              ·
                refine ⟨88927261255720920677147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3794229813577425948891605 88927261255720920677147)
                ·
                  rfl

theorem cell23_4676001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 7].length) (baseStart_4676001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676001 prefixEnd_4676001 := by exact prefixLift 4676001
  have htrace : WordTrace (prefixWord ++ tailWord_4676001) baseStart_4676001 baseEnd_4676001 := by
    simpa [prefixWord, tailWord_4676001, baseEnd_4676001] using wordTrace_append hprefix tailTrace_4676001
  have hstable : (prefixWord ++ tailWord_4676001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676001).length < 2 ^ (prefixWord ++ tailWord_4676001).sum := by decide
  have hdescent : baseEnd_4676001 < baseStart_4676001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676028 : List Nat := [2, 2, 2, 4, 1, 1, 3, 2, 2, 1, 3]
def baseStart_4676028 : Nat := 118140960795 + 4676028 * 2 ^ 59
def prefixEnd_4676028 : Nat := 4983230072969 + 3 ^ 40 * 4676028 * 2
def baseEnd_4676028 : Nat := 2401049917882136252645345

theorem tailTrace_4676028 : CollatzResearch.WordTrace tailWord_4676028 prefixEnd_4676028 2401049917882136252645345 := by
  unfold tailWord_4676028
  simp only [CollatzResearch.WordTrace]
  refine ⟨85274376151778316423778369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113699168202371088565037825 85274376151778316423778369)
  ·
    refine ⟨63955782113833737317833777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85274376151778316423778369 63955782113833737317833777)
    ·
      refine ⟨47966836585375302988375333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63955782113833737317833777 47966836585375302988375333)
      ·
        refine ⟨8993781859757869310320375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47966836585375302988375333 8993781859757869310320375)
        ·
          refine ⟨13490672789636803965480563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8993781859757869310320375 13490672789636803965480563)
          ·
            refine ⟨20236009184455205948220845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13490672789636803965480563 20236009184455205948220845)
            ·
              refine ⟨7588503444170702230582817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20236009184455205948220845 7588503444170702230582817)
              ·
                refine ⟨5691377583128026672937113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7588503444170702230582817 5691377583128026672937113)
                ·
                  refine ⟨4268533187346020004702835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5691377583128026672937113 4268533187346020004702835)
                  ·
                    refine ⟨6402799781019030007054253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4268533187346020004702835 6402799781019030007054253)
                    ·
                      refine ⟨2401049917882136252645345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6402799781019030007054253 2401049917882136252645345)
                      ·
                        rfl

theorem cell23_4676028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_4676028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676028 prefixEnd_4676028 := by exact prefixLift 4676028
  have htrace : WordTrace (prefixWord ++ tailWord_4676028) baseStart_4676028 baseEnd_4676028 := by
    simpa [prefixWord, tailWord_4676028, baseEnd_4676028] using wordTrace_append hprefix tailTrace_4676028
  have hstable : (prefixWord ++ tailWord_4676028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676028).length < 2 ^ (prefixWord ++ tailWord_4676028).sum := by decide
  have hdescent : baseEnd_4676028 < baseStart_4676028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676057 : List Nat := [1, 2, 1, 2, 4, 1, 1, 4, 7]
def baseStart_4676057 : Nat := 118140960795 + 4676057 * 2 ^ 59
def prefixEnd_4676057 : Nat := 4983230072969 + 3 ^ 40 * 4676057 * 2
def baseEnd_4676057 : Nat := 266784978757901848798079

theorem tailTrace_4676057 : CollatzResearch.WordTrace tailWord_4676057 prefixEnd_4676057 266784978757901848798079 := by
  unfold tailWord_4676057
  simp only [CollatzResearch.WordTrace]
  refine ⟨170549810020451570800362425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113699873346967713866908283 170549810020451570800362425)
  ·
    refine ⟨127912357515338678100271819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170549810020451570800362425 127912357515338678100271819)
    ·
      refine ⟨191868536273008017150407729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127912357515338678100271819 191868536273008017150407729)
      ·
        refine ⟨143901402204756012862805797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191868536273008017150407729 143901402204756012862805797)
        ·
          refine ⟨26981512913391752411776087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143901402204756012862805797 26981512913391752411776087)
          ·
            refine ⟨40472269370087628617664131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26981512913391752411776087 40472269370087628617664131)
            ·
              refine ⟨60708404055131442926496197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40472269370087628617664131 60708404055131442926496197)
              ·
                refine ⟨11382825760337145548718037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60708404055131442926496197 11382825760337145548718037)
                ·
                  refine ⟨266784978757901848798079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11382825760337145548718037 266784978757901848798079)
                  ·
                    rfl

theorem cell23_4676057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 7].length) (baseStart_4676057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676057 prefixEnd_4676057 := by exact prefixLift 4676057
  have htrace : WordTrace (prefixWord ++ tailWord_4676057) baseStart_4676057 baseEnd_4676057 := by
    simpa [prefixWord, tailWord_4676057, baseEnd_4676057] using wordTrace_append hprefix tailTrace_4676057
  have hstable : (prefixWord ++ tailWord_4676057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676057).length < 2 ^ (prefixWord ++ tailWord_4676057).sum := by decide
  have hdescent : baseEnd_4676057 < baseStart_4676057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676142 : List Nat := [4, 1, 3, 1, 4, 1, 2, 2, 5]
def baseStart_4676142 : Nat := 118140960795 + 4676142 * 2 ^ 59
def prefixEnd_4676142 : Nat := 4983230072969 + 3 ^ 40 * 4676142 * 2
def baseEnd_4676142 : Nat := 266789828297416534068869

theorem tailTrace_4676142 : CollatzResearch.WordTrace tailWord_4676142 prefixEnd_4676142 266789828297416534068869 := by
  unfold tailWord_4676142
  simp only [CollatzResearch.WordTrace]
  refine ⟨21319113778142953789650835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113701940150095753544804453 21319113778142953789650835)
  ·
    refine ⟨31978670667214430684476253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21319113778142953789650835 31978670667214430684476253)
    ·
      refine ⟨11992001500205411506678595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31978670667214430684476253 11992001500205411506678595)
      ·
        refine ⟨17988002250308117260017893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11992001500205411506678595 17988002250308117260017893)
        ·
          refine ⟨3372750421932771986253355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17988002250308117260017893 3372750421932771986253355)
          ·
            refine ⟨5059125632899157979380033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3372750421932771986253355 5059125632899157979380033)
            ·
              refine ⟨3794344224674368484535025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5059125632899157979380033 3794344224674368484535025)
              ·
                refine ⟨2845758168505776363401269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3794344224674368484535025 2845758168505776363401269)
                ·
                  refine ⟨266789828297416534068869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2845758168505776363401269 266789828297416534068869)
                  ·
                    rfl

theorem cell23_4676142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 2, 5].length) (baseStart_4676142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676142 prefixEnd_4676142 := by exact prefixLift 4676142
  have htrace : WordTrace (prefixWord ++ tailWord_4676142) baseStart_4676142 baseEnd_4676142 := by
    simpa [prefixWord, tailWord_4676142, baseEnd_4676142] using wordTrace_append hprefix tailTrace_4676142
  have hstable : (prefixWord ++ tailWord_4676142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676142).length < 2 ^ (prefixWord ++ tailWord_4676142).sum := by decide
  have hdescent : baseEnd_4676142 < baseStart_4676142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676201 : List Nat := [1, 2, 1, 1, 1, 4, 1, 3, 4, 3, 2]
def baseStart_4676201 : Nat := 118140960795 + 4676201 * 2 ^ 59
def prefixEnd_4676201 : Nat := 4983230072969 + 3 ^ 40 * 4676201 * 2
def baseEnd_4676201 : Nat := 2401138750035364075782049

theorem tailTrace_4676201 : CollatzResearch.WordTrace tailWord_4676201 prefixEnd_4676201 2401138750035364075782049 := by
  unfold tailWord_4676201
  simp only [CollatzResearch.WordTrace]
  refine ⟨170555062131929883393604457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113703374754619922262402971 170555062131929883393604457)
  ·
    refine ⟨127916296598947412545203343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170555062131929883393604457 127916296598947412545203343)
    ·
      refine ⟨191874444898421118817805015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127916296598947412545203343 191874444898421118817805015)
      ·
        refine ⟨287811667347631678226707523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191874444898421118817805015 287811667347631678226707523)
        ·
          refine ⟨431717501021447517340061285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287811667347631678226707523 431717501021447517340061285)
          ·
            refine ⟨80947031441521409501261491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 431717501021447517340061285 80947031441521409501261491)
            ·
              refine ⟨121420547162282114251892237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80947031441521409501261491 121420547162282114251892237)
              ·
                refine ⟨45532705185855792844459589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121420547162282114251892237 45532705185855792844459589)
                ·
                  refine ⟨8537382222347961158336173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45532705185855792844459589 8537382222347961158336173)
                  ·
                    refine ⟨3201518333380485434376065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8537382222347961158336173 3201518333380485434376065)
                    ·
                      refine ⟨2401138750035364075782049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3201518333380485434376065 2401138750035364075782049)
                      ·
                        rfl

theorem cell23_4676201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 3, 2].length) (baseStart_4676201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676201 prefixEnd_4676201 := by exact prefixLift 4676201
  have htrace : WordTrace (prefixWord ++ tailWord_4676201) baseStart_4676201 baseEnd_4676201 := by
    simpa [prefixWord, tailWord_4676201, baseEnd_4676201] using wordTrace_append hprefix tailTrace_4676201
  have hstable : (prefixWord ++ tailWord_4676201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676201).length < 2 ^ (prefixWord ++ tailWord_4676201).sum := by decide
  have hdescent : baseEnd_4676201 < baseStart_4676201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676228 : List Nat := [2, 3, 2, 1, 3, 2, 2, 2, 1, 5]
def baseStart_4676228 : Nat := 118140960795 + 4676228 * 2 ^ 59
def prefixEnd_4676228 : Nat := 4983230072969 + 3 ^ 40 * 4676228 * 2
def baseEnd_4676228 : Nat := 800384204671011823381475

theorem tailTrace_4676228 : CollatzResearch.WordTrace tailWord_4676228 prefixEnd_4676228 800384204671011823381475 := by
  unfold tailWord_4676228
  simp only [CollatzResearch.WordTrace]
  refine ⟨85278023451416033502418669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113704031268554711336558225 85278023451416033502418669)
  ·
    refine ⟨31979258794281012563407001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85278023451416033502418669 31979258794281012563407001)
    ·
      refine ⟨23984444095710759422555251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31979258794281012563407001 23984444095710759422555251)
      ·
        refine ⟨35976666143566139133832877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23984444095710759422555251 35976666143566139133832877)
        ·
          refine ⟨13491249803837302175187329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35976666143566139133832877 13491249803837302175187329)
          ·
            refine ⟨10118437352877976631390497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13491249803837302175187329 10118437352877976631390497)
            ·
              refine ⟨7588828014658482473542873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10118437352877976631390497 7588828014658482473542873)
              ·
                refine ⟨5691621010993861855157155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7588828014658482473542873 5691621010993861855157155)
                ·
                  refine ⟨8537431516490792782735733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5691621010993861855157155 8537431516490792782735733)
                  ·
                    refine ⟨800384204671011823381475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8537431516490792782735733 800384204671011823381475)
                    ·
                      rfl

theorem cell23_4676228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_4676228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676228 prefixEnd_4676228 := by exact prefixLift 4676228
  have htrace : WordTrace (prefixWord ++ tailWord_4676228) baseStart_4676228 baseEnd_4676228 := by
    simpa [prefixWord, tailWord_4676228, baseEnd_4676228] using wordTrace_append hprefix tailTrace_4676228
  have hstable : (prefixWord ++ tailWord_4676228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676228).length < 2 ^ (prefixWord ++ tailWord_4676228).sum := by decide
  have hdescent : baseEnd_4676228 < baseStart_4676228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676231 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 2, 6, 2]
def baseStart_4676231 : Nat := 118140960795 + 4676231 * 2 ^ 59
def prefixEnd_4676231 : Nat := 4983230072969 + 3 ^ 40 * 4676231 * 2
def baseEnd_4676231 : Nat := 2401154154454998958406911

theorem tailTrace_4676231 : CollatzResearch.WordTrace tailWord_4676231 prefixEnd_4676231 2401154154454998958406911 := by
  unfold tailWord_4676231
  simp only [CollatzResearch.WordTrace]
  refine ⟨170556156321821198517196547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113704104214547465678131031 170556156321821198517196547)
  ·
    refine ⟨255834234482731797775794821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170556156321821198517196547 255834234482731797775794821)
    ·
      refine ⟨47968918965512212082961529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 255834234482731797775794821 47968918965512212082961529)
      ·
        refine ⟨35976689224134159062221147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47968918965512212082961529 35976689224134159062221147)
        ·
          refine ⟨53965033836201238593331721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35976689224134159062221147 53965033836201238593331721)
          ·
            refine ⟨40473775377150928944998791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53965033836201238593331721 40473775377150928944998791)
            ·
              refine ⟨60710663065726393417498187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40473775377150928944998791 60710663065726393417498187)
              ·
                refine ⟨91065994598589590126247281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60710663065726393417498187 91065994598589590126247281)
                ·
                  refine ⟨68299495948942192594685461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91065994598589590126247281 68299495948942192594685461)
                  ·
                    refine ⟨3201538872606665277875881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 68299495948942192594685461 3201538872606665277875881)
                    ·
                      refine ⟨2401154154454998958406911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3201538872606665277875881 2401154154454998958406911)
                      ·
                        rfl

theorem cell23_4676231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_4676231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676231 prefixEnd_4676231 := by exact prefixLift 4676231
  have htrace : WordTrace (prefixWord ++ tailWord_4676231) baseStart_4676231 baseEnd_4676231 := by
    simpa [prefixWord, tailWord_4676231, baseEnd_4676231] using wordTrace_append hprefix tailTrace_4676231
  have hstable : (prefixWord ++ tailWord_4676231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676231).length < 2 ^ (prefixWord ++ tailWord_4676231).sum := by decide
  have hdescent : baseEnd_4676231 < baseStart_4676231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676242 : List Nat := [3, 2, 3, 1, 2, 1, 3, 3, 1, 1, 3]
def baseStart_4676242 : Nat := 118140960795 + 4676242 * 2 ^ 59
def prefixEnd_4676242 : Nat := 4983230072969 + 3 ^ 40 * 4676242 * 2
def baseEnd_4676242 : Nat := 2401159802742198415369361

theorem tailTrace_4676242 : CollatzResearch.WordTrace tailWord_4676242 prefixEnd_4676242 2401159802742198415369361 := by
  unfold tailWord_4676242
  simp only [CollatzResearch.WordTrace]
  refine ⟨42639139381195336848961745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113704371683187564930564653 42639139381195336848961745)
  ·
    refine ⟨31979354535896502636721309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42639139381195336848961745 31979354535896502636721309)
    ·
      refine ⟨11992257950961188488770491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31979354535896502636721309 11992257950961188488770491)
      ·
        refine ⟨17988386926441782733155737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11992257950961188488770491 17988386926441782733155737)
        ·
          refine ⟨13491290194831337049866803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17988386926441782733155737 13491290194831337049866803)
          ·
            refine ⟨20236935292247005574800205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13491290194831337049866803 20236935292247005574800205)
            ·
              refine ⟨7588850734592627090550077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20236935292247005574800205 7588850734592627090550077)
              ·
                refine ⟨2845819025472235158956279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7588850734592627090550077 2845819025472235158956279)
                ·
                  refine ⟨4268728538208352738434419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2845819025472235158956279 4268728538208352738434419)
                  ·
                    refine ⟨6403092807312529107651629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4268728538208352738434419 6403092807312529107651629)
                    ·
                      refine ⟨2401159802742198415369361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6403092807312529107651629 2401159802742198415369361)
                      ·
                        rfl

theorem cell23_4676242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_4676242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676242 prefixEnd_4676242 := by exact prefixLift 4676242
  have htrace : WordTrace (prefixWord ++ tailWord_4676242) baseStart_4676242 baseEnd_4676242 := by
    simpa [prefixWord, tailWord_4676242, baseEnd_4676242] using wordTrace_append hprefix tailTrace_4676242
  have hstable : (prefixWord ++ tailWord_4676242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676242).length < 2 ^ (prefixWord ++ tailWord_4676242).sum := by decide
  have hdescent : baseEnd_4676242 < baseStart_4676242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676274 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6]
def baseStart_4676274 : Nat := 118140960795 + 4676274 * 2 ^ 59
def prefixEnd_4676274 : Nat := 4983230072969 + 3 ^ 40 * 4676274 * 2
def baseEnd_4676274 : Nat := 2401176234123142290169213

theorem tailTrace_4676274 : CollatzResearch.WordTrace tailWord_4676274 prefixEnd_4676274 2401176234123142290169213 := by
  unfold tailWord_4676274
  simp only [CollatzResearch.WordTrace]
  refine ⟨42639431165166354215252969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113705149773776944574007917 42639431165166354215252969)
  ·
    refine ⟨31979573373874765661439727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42639431165166354215252969 31979573373874765661439727)
    ·
      refine ⟨47969360060812148492159591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31979573373874765661439727 47969360060812148492159591)
      ·
        refine ⟨71954040091218222738239387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47969360060812148492159591 71954040091218222738239387)
        ·
          refine ⟨107931060136827334107359081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71954040091218222738239387 107931060136827334107359081)
          ·
            refine ⟨80948295102620500580519311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107931060136827334107359081 80948295102620500580519311)
            ·
              refine ⟨121422442653930750870778967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80948295102620500580519311 121422442653930750870778967)
              ·
                refine ⟨182133663980896126306168451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121422442653930750870778967 182133663980896126306168451)
                ·
                  refine ⟨273200495971344189459252677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 182133663980896126306168451 273200495971344189459252677)
                  ·
                    refine ⟨51225092994627035523609877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 273200495971344189459252677 51225092994627035523609877)
                    ·
                      refine ⟨2401176234123142290169213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51225092994627035523609877 2401176234123142290169213)
                      ·
                        rfl

theorem cell23_4676274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_4676274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676274 prefixEnd_4676274 := by exact prefixLift 4676274
  have htrace : WordTrace (prefixWord ++ tailWord_4676274) baseStart_4676274 baseEnd_4676274 := by
    simpa [prefixWord, tailWord_4676274, baseEnd_4676274] using wordTrace_append hprefix tailTrace_4676274
  have hstable : (prefixWord ++ tailWord_4676274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676274).length < 2 ^ (prefixWord ++ tailWord_4676274).sum := by decide
  have hdescent : baseEnd_4676274 < baseStart_4676274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676275 : List Nat := [1, 1, 1, 2, 3, 6, 2, 1, 2, 4]
def baseStart_4676275 : Nat := 118140960795 + 4676275 * 2 ^ 59
def prefixEnd_4676275 : Nat := 4983230072969 + 3 ^ 40 * 4676275 * 2
def baseEnd_4676275 : Nat := 800392249201265595418903

theorem tailTrace_4676275 : CollatzResearch.WordTrace tailWord_4676275 prefixEnd_4676275 800392249201265595418903 := by
  unfold tailWord_4676275
  simp only [CollatzResearch.WordTrace]
  refine ⟨170557761133661794031798279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113705174089107862687865519 170557761133661794031798279)
  ·
    refine ⟨255836641700492691047697419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170557761133661794031798279 255836641700492691047697419)
    ·
      refine ⟨383754962550739036571546129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255836641700492691047697419 383754962550739036571546129)
      ·
        refine ⟨287816221913054277428659597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 383754962550739036571546129 287816221913054277428659597)
        ·
          refine ⟨107931083217395354035747349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 287816221913054277428659597 107931083217395354035747349)
          ·
            refine ⟨5059269525815407220425657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 107931083217395354035747349 5059269525815407220425657)
            ·
              refine ⟨3794452144361555415319243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5059269525815407220425657 3794452144361555415319243)
              ·
                refine ⟨5691678216542333122978865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3794452144361555415319243 5691678216542333122978865)
                ·
                  refine ⟨4268758662406749842234149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5691678216542333122978865 4268758662406749842234149)
                  ·
                    refine ⟨800392249201265595418903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4268758662406749842234149 800392249201265595418903)
                    ·
                      rfl

theorem cell23_4676275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 2, 4].length) (baseStart_4676275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676275 prefixEnd_4676275 := by exact prefixLift 4676275
  have htrace : WordTrace (prefixWord ++ tailWord_4676275) baseStart_4676275 baseEnd_4676275 := by
    simpa [prefixWord, tailWord_4676275, baseEnd_4676275] using wordTrace_append hprefix tailTrace_4676275
  have hstable : (prefixWord ++ tailWord_4676275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676275).length < 2 ^ (prefixWord ++ tailWord_4676275).sum := by decide
  have hdescent : baseEnd_4676275 < baseStart_4676275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676281 : List Nat := [1, 2, 1, 4, 1, 1, 1, 5, 1, 3, 3]
def baseStart_4676281 : Nat := 118140960795 + 4676281 * 2 ^ 59
def prefixEnd_4676281 : Nat := 4983230072969 + 3 ^ 40 * 4676281 * 2
def baseEnd_4676281 : Nat := 2401179828487723762781681

theorem tailTrace_4676281 : CollatzResearch.WordTrace tailWord_4676281 prefixEnd_4676281 2401179828487723762781681 := by
  unfold tailWord_4676281
  simp only [CollatzResearch.WordTrace]
  refine ⟨170557979971640057056516697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113705319981093371371011131 170557979971640057056516697)
  ·
    refine ⟨127918484978730042792387523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170557979971640057056516697 127918484978730042792387523)
    ·
      refine ⟨191877727468095064188581285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127918484978730042792387523 191877727468095064188581285)
      ·
        refine ⟨35977073900267824535358991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 191877727468095064188581285 35977073900267824535358991)
        ·
          refine ⟨53965610850401736803038487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35977073900267824535358991 53965610850401736803038487)
          ·
            refine ⟨80948416275602605204557731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53965610850401736803038487 80948416275602605204557731)
            ·
              refine ⟨121422624413403907806836597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80948416275602605204557731 121422624413403907806836597)
              ·
                refine ⟨11383371038756616356890931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 121422624413403907806836597 11383371038756616356890931)
                ·
                  refine ⟨17075056558134924535336397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11383371038756616356890931 17075056558134924535336397)
                  ·
                    refine ⟨6403146209300596700751149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17075056558134924535336397 6403146209300596700751149)
                    ·
                      refine ⟨2401179828487723762781681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6403146209300596700751149 2401179828487723762781681)
                      ·
                        rfl

theorem cell23_4676281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_4676281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676281 prefixEnd_4676281 := by exact prefixLift 4676281
  have htrace : WordTrace (prefixWord ++ tailWord_4676281) baseStart_4676281 baseEnd_4676281 := by
    simpa [prefixWord, tailWord_4676281, baseEnd_4676281] using wordTrace_append hprefix tailTrace_4676281
  have hstable : (prefixWord ++ tailWord_4676281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676281).length < 2 ^ (prefixWord ++ tailWord_4676281).sum := by decide
  have hdescent : baseEnd_4676281 < baseStart_4676281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676285 : List Nat := [1, 4, 1, 2, 1, 5, 1, 2, 1, 2, 3]
def baseStart_4676285 : Nat := 118140960795 + 4676285 * 2 ^ 59
def prefixEnd_4676285 : Nat := 4983230072969 + 3 ^ 40 * 4676285 * 2
def baseEnd_4676285 : Nat := 2401181882410341747131663

theorem tailTrace_4676285 : CollatzResearch.WordTrace tailWord_4676285 prefixEnd_4676285 2401181882410341747131663 := by
  unfold tailWord_4676285
  simp only [CollatzResearch.WordTrace]
  refine ⟨170558125863625565739662309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113705417242417043826441539 170558125863625565739662309)
  ·
    refine ⟨31979648599429793576186683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170558125863625565739662309 31979648599429793576186683)
    ·
      refine ⟨47969472899144690364280025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31979648599429793576186683 47969472899144690364280025)
      ·
        refine ⟨35977104674358517773210019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47969472899144690364280025 35977104674358517773210019)
        ·
          refine ⟨53965657011537776659815029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35977104674358517773210019 53965657011537776659815029)
          ·
            refine ⟨5059280344831666561857659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53965657011537776659815029 5059280344831666561857659)
            ·
              refine ⟨7588920517247499842786489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5059280344831666561857659 7588920517247499842786489)
              ·
                refine ⟨5691690387935624882089867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7588920517247499842786489 5691690387935624882089867)
                ·
                  refine ⟨8537535581903437323134801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5691690387935624882089867 8537535581903437323134801)
                  ·
                    refine ⟨6403151686427577992351101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8537535581903437323134801 6403151686427577992351101)
                    ·
                      refine ⟨2401181882410341747131663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6403151686427577992351101 2401181882410341747131663)
                      ·
                        rfl

theorem cell23_4676285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_4676285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676285 prefixEnd_4676285 := by exact prefixLift 4676285
  have htrace : WordTrace (prefixWord ++ tailWord_4676285) baseStart_4676285 baseEnd_4676285 := by
    simpa [prefixWord, tailWord_4676285, baseEnd_4676285] using wordTrace_append hprefix tailTrace_4676285
  have hstable : (prefixWord ++ tailWord_4676285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676285).length < 2 ^ (prefixWord ++ tailWord_4676285).sum := by decide
  have hdescent : baseEnd_4676285 < baseStart_4676285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676298 : List Nat := [3, 1, 2, 1, 4, 2, 1, 2, 1, 3, 3]
def baseStart_4676298 : Nat := 118140960795 + 4676298 * 2 ^ 59
def prefixEnd_4676298 : Nat := 4983230072969 + 3 ^ 40 * 4676298 * 2
def baseEnd_4676298 : Nat := 2401188557658850196269103

theorem tailTrace_4676298 : CollatzResearch.WordTrace tailWord_4676298 prefixEnd_4676298 2401188557658850196269103 := by
  unfold tailWord_4676298
  simp only [CollatzResearch.WordTrace]
  refine ⟨42639650003144617239971387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113705733341718979306590365 42639650003144617239971387)
  ·
    refine ⟨63959475004716925859957081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42639650003144617239971387 63959475004716925859957081)
    ·
      refine ⟨47969606253537694394967811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63959475004716925859957081 47969606253537694394967811)
      ·
        refine ⟨71954409380306541592451717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47969606253537694394967811 71954409380306541592451717)
        ·
          refine ⟨13491451758807476548584697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71954409380306541592451717 13491451758807476548584697)
          ·
            refine ⟨10118588819105607411438523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13491451758807476548584697 10118588819105607411438523)
            ·
              refine ⟨15177883228658411117157785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10118588819105607411438523 15177883228658411117157785)
              ·
                refine ⟨11383412421493808337868339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15177883228658411117157785 11383412421493808337868339)
                ·
                  refine ⟨17075118632240712506802509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11383412421493808337868339 17075118632240712506802509)
                  ·
                    refine ⟨6403169487090267190050941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17075118632240712506802509 6403169487090267190050941)
                    ·
                      refine ⟨2401188557658850196269103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6403169487090267190050941 2401188557658850196269103)
                      ·
                        rfl

theorem cell23_4676298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_4676298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676298 prefixEnd_4676298 := by exact prefixLift 4676298
  have htrace : WordTrace (prefixWord ++ tailWord_4676298) baseStart_4676298 baseEnd_4676298 := by
    simpa [prefixWord, tailWord_4676298, baseEnd_4676298] using wordTrace_append hprefix tailTrace_4676298
  have hstable : (prefixWord ++ tailWord_4676298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676298).length < 2 ^ (prefixWord ++ tailWord_4676298).sum := by decide
  have hdescent : baseEnd_4676298 < baseStart_4676298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676316 : List Nat := [2, 2, 5, 1, 1, 1, 4, 2, 1, 2, 2]
def baseStart_4676316 : Nat := 118140960795 + 4676316 * 2 ^ 59
def prefixEnd_4676316 : Nat := 4983230072969 + 3 ^ 40 * 4676316 * 2
def baseEnd_4676316 : Nat := 2401197800310631125844021

theorem tailTrace_4676316 : CollatzResearch.WordTrace tailWord_4676316 prefixEnd_4676316 2401197800310631125844021 := by
  unfold tailWord_4676316
  simp only [CollatzResearch.WordTrace]
  refine ⟨85279628263256629017020401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113706171017675505356027201 85279628263256629017020401)
  ·
    refine ⟨63959721197442471762765301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85279628263256629017020401 63959721197442471762765301)
    ·
      refine ⟨5996223862260231727759247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63959721197442471762765301 5996223862260231727759247)
      ·
        refine ⟨8994335793390347591638871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5996223862260231727759247 8994335793390347591638871)
        ·
          refine ⟨13491503690085521387458307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8994335793390347591638871 13491503690085521387458307)
          ·
            refine ⟨20237255535128282081187461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13491503690085521387458307 20237255535128282081187461)
            ·
              refine ⟨3794485412836552890222649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20237255535128282081187461 3794485412836552890222649)
              ·
                refine ⟨2845864059627414667666987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3794485412836552890222649 2845864059627414667666987)
                ·
                  refine ⟨4268796089441122001500481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2845864059627414667666987 4268796089441122001500481)
                  ·
                    refine ⟨3201597067080841501125361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4268796089441122001500481 3201597067080841501125361)
                    ·
                      refine ⟨2401197800310631125844021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3201597067080841501125361 2401197800310631125844021)
                      ·
                        rfl

theorem cell23_4676316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_4676316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676316 prefixEnd_4676316 := by exact prefixLift 4676316
  have htrace : WordTrace (prefixWord ++ tailWord_4676316) baseStart_4676316 baseEnd_4676316 := by
    simpa [prefixWord, tailWord_4676316, baseEnd_4676316] using wordTrace_append hprefix tailTrace_4676316
  have hstable : (prefixWord ++ tailWord_4676316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676316).length < 2 ^ (prefixWord ++ tailWord_4676316).sum := by decide
  have hdescent : baseEnd_4676316 < baseStart_4676316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676321 : List Nat := [1, 2, 3, 1, 4, 1, 1, 1, 2, 3, 4]
def baseStart_4676321 : Nat := 118140960795 + 4676321 * 2 ^ 59
def prefixEnd_4676321 : Nat := 4983230072969 + 3 ^ 40 * 4676321 * 2
def baseEnd_4676321 : Nat := 2401200367713903606281497

theorem tailTrace_4676321 : CollatzResearch.WordTrace tailWord_4676321 prefixEnd_4676321 2401200367713903606281497 := by
  unfold tailWord_4676321
  simp only [CollatzResearch.WordTrace]
  refine ⟨170559438891495143887972817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113706292594330095925315211 170559438891495143887972817)
  ·
    refine ⟨127919579168621357915979613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170559438891495143887972817 127919579168621357915979613)
    ·
      refine ⟨47969842188233009218492355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127919579168621357915979613 47969842188233009218492355)
      ·
        refine ⟨71954763282349513827738533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47969842188233009218492355 71954763282349513827738533)
        ·
          refine ⟨13491518115440533842700975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71954763282349513827738533 13491518115440533842700975)
          ·
            refine ⟨20237277173160800764051463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13491518115440533842700975 20237277173160800764051463)
            ·
              refine ⟨30355915759741201146077195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20237277173160800764051463 30355915759741201146077195)
              ·
                refine ⟨45533873639611801719115793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30355915759741201146077195 45533873639611801719115793)
                ·
                  refine ⟨34150405229708851289336845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45533873639611801719115793 34150405229708851289336845)
                  ·
                    refine ⟨12806401961140819233501317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34150405229708851289336845 12806401961140819233501317)
                    ·
                      refine ⟨2401200367713903606281497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12806401961140819233501317 2401200367713903606281497)
                      ·
                        rfl

theorem cell23_4676321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_4676321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676321 prefixEnd_4676321 := by exact prefixLift 4676321
  have htrace : WordTrace (prefixWord ++ tailWord_4676321) baseStart_4676321 baseEnd_4676321 := by
    simpa [prefixWord, tailWord_4676321, baseEnd_4676321] using wordTrace_append hprefix tailTrace_4676321
  have hstable : (prefixWord ++ tailWord_4676321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676321).length < 2 ^ (prefixWord ++ tailWord_4676321).sum := by decide
  have hdescent : baseEnd_4676321 < baseStart_4676321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676359 : List Nat := [1, 1, 4, 4, 1, 3, 2, 1, 1, 3, 2]
def baseStart_4676359 : Nat := 118140960795 + 4676359 * 2 ^ 59
def prefixEnd_4676359 : Nat := 4983230072969 + 3 ^ 40 * 4676359 * 2
def baseEnd_4676359 : Nat := 2401219879978774457606323

theorem tailTrace_4676359 : CollatzResearch.WordTrace tailWord_4676359 prefixEnd_4676359 2401219879978774457606323 := by
  unfold tailWord_4676359
  simp only [CollatzResearch.WordTrace]
  refine ⟨170560824865357476377856131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113707216576904984251904087 170560824865357476377856131)
  ·
    refine ⟨255841237298036214566784197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170560824865357476377856131 255841237298036214566784197)
    ·
      refine ⟨47970231993381790231272037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 255841237298036214566784197 47970231993381790231272037)
      ·
        refine ⟨8994418498759085668363507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47970231993381790231272037 8994418498759085668363507)
        ·
          refine ⟨13491627748138628502545261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8994418498759085668363507 13491627748138628502545261)
          ·
            refine ⟨5059360405551985688454473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13491627748138628502545261 5059360405551985688454473)
            ·
              refine ⟨3794520304163989266340855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5059360405551985688454473 3794520304163989266340855)
              ·
                refine ⟨5691780456245983899511283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3794520304163989266340855 5691780456245983899511283)
                ·
                  refine ⟨8537670684368975849266925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5691780456245983899511283 8537670684368975849266925)
                  ·
                    refine ⟨3201626506638365943475097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8537670684368975849266925 3201626506638365943475097)
                    ·
                      refine ⟨2401219879978774457606323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3201626506638365943475097 2401219879978774457606323)
                      ·
                        rfl

theorem cell23_4676359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_4676359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676359 prefixEnd_4676359 := by exact prefixLift 4676359
  have htrace : WordTrace (prefixWord ++ tailWord_4676359) baseStart_4676359 baseEnd_4676359 := by
    simpa [prefixWord, tailWord_4676359, baseEnd_4676359] using wordTrace_append hprefix tailTrace_4676359
  have hstable : (prefixWord ++ tailWord_4676359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676359).length < 2 ^ (prefixWord ++ tailWord_4676359).sum := by decide
  have hdescent : baseEnd_4676359 < baseStart_4676359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676371 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 4, 3, 3]
def baseStart_4676371 : Nat := 118140960795 + 4676371 * 2 ^ 59
def prefixEnd_4676371 : Nat := 4983230072969 + 3 ^ 40 * 4676371 * 2
def baseEnd_4676371 : Nat := 2401226041746628410656267

theorem tailTrace_4676371 : CollatzResearch.WordTrace tailWord_4676371 prefixEnd_4676371 2401226041746628410656267 := by
  unfold tailWord_4676371
  simp only [CollatzResearch.WordTrace]
  refine ⟨170561262541314002427292967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113707508360876001618195311 170561262541314002427292967)
  ·
    refine ⟨255841893811971003640939451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170561262541314002427292967 255841893811971003640939451)
    ·
      refine ⟨383762840717956505461409177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255841893811971003640939451 383762840717956505461409177)
      ·
        refine ⟨287822130538467379096056883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 383762840717956505461409177 287822130538467379096056883)
        ·
          refine ⟨431733195807701068644085325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287822130538467379096056883 431733195807701068644085325)
          ·
            refine ⟨161899948427887900741531997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 431733195807701068644085325 161899948427887900741531997)
            ·
              refine ⟨60712480660457962778074499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161899948427887900741531997 60712480660457962778074499)
              ·
                refine ⟨91068720990686944167111749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60712480660457962778074499 91068720990686944167111749)
                ·
                  refine ⟨17075385185753802031333453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91068720990686944167111749 17075385185753802031333453)
                  ·
                    refine ⟨6403269444657675761750045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17075385185753802031333453 6403269444657675761750045)
                    ·
                      refine ⟨2401226041746628410656267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6403269444657675761750045 2401226041746628410656267)
                      ·
                        rfl

theorem cell23_4676371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 3, 3].length) (baseStart_4676371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676371 prefixEnd_4676371 := by exact prefixLift 4676371
  have htrace : WordTrace (prefixWord ++ tailWord_4676371) baseStart_4676371 baseEnd_4676371 := by
    simpa [prefixWord, tailWord_4676371, baseEnd_4676371] using wordTrace_append hprefix tailTrace_4676371
  have hstable : (prefixWord ++ tailWord_4676371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676371).length < 2 ^ (prefixWord ++ tailWord_4676371).sum := by decide
  have hdescent : baseEnd_4676371 < baseStart_4676371 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676378 : List Nat := [3, 1, 1, 3, 2, 1, 1, 6, 5]
def baseStart_4676378 : Nat := 118140960795 + 4676378 * 2 ^ 59
def prefixEnd_4676378 : Nat := 4983230072969 + 3 ^ 40 * 4676378 * 2
def baseEnd_4676378 : Nat := 266803292901245542585415

theorem tailTrace_4676378 : CollatzResearch.WordTrace tailWord_4676378 prefixEnd_4676378 266803292901245542585415 := by
  unfold tailWord_4676378
  simp only [CollatzResearch.WordTrace]
  refine ⟨42640379463072160655699447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113707678568192428415198525 42640379463072160655699447)
  ·
    refine ⟨63960569194608240983549171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42640379463072160655699447 63960569194608240983549171)
    ·
      refine ⟨95940853791912361475323757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63960569194608240983549171 95940853791912361475323757)
      ·
        refine ⟨35977820171967135553246409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95940853791912361475323757 35977820171967135553246409)
        ·
          refine ⟨26983365128975351664934807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35977820171967135553246409 26983365128975351664934807)
          ·
            refine ⟨40475047693463027497402211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26983365128975351664934807 40475047693463027497402211)
            ·
              refine ⟨60712571540194541246103317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40475047693463027497402211 60712571540194541246103317)
              ·
                refine ⟨2845901790946619120911093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60712571540194541246103317 2845901790946619120911093)
                ·
                  refine ⟨266803292901245542585415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2845901790946619120911093 266803292901245542585415)
                  ·
                    rfl

theorem cell23_4676378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 6, 5].length) (baseStart_4676378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676378 prefixEnd_4676378 := by exact prefixLift 4676378
  have htrace : WordTrace (prefixWord ++ tailWord_4676378) baseStart_4676378 baseEnd_4676378 := by
    simpa [prefixWord, tailWord_4676378, baseEnd_4676378] using wordTrace_append hprefix tailTrace_4676378
  have hstable : (prefixWord ++ tailWord_4676378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676378).length < 2 ^ (prefixWord ++ tailWord_4676378).sum := by decide
  have hdescent : baseEnd_4676378 < baseStart_4676378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676428 : List Nat := [2, 2, 1, 3, 3, 1, 1, 1, 4, 1, 4]
def baseStart_4676428 : Nat := 118140960795 + 4676428 * 2 ^ 59
def prefixEnd_4676428 : Nat := 4983230072969 + 3 ^ 40 * 4676428 * 2
def baseEnd_4676428 : Nat := 2401255310143934687643505

theorem tailTrace_4676428 : CollatzResearch.WordTrace tailWord_4676428 prefixEnd_4676428 2401255310143934687643505 := by
  unfold tailWord_4676428
  simp only [CollatzResearch.WordTrace]
  refine ⟨85281670751053750581058969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113708894334738334108078625 85281670751053750581058969)
  ·
    refine ⟨63961253063290312935794227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85281670751053750581058969 63961253063290312935794227)
    ·
      refine ⟨95941879594935469403691341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63961253063290312935794227 95941879594935469403691341)
      ·
        refine ⟨35978204848100801026384253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95941879594935469403691341 35978204848100801026384253)
        ·
          refine ⟨13491826818037800384894095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35978204848100801026384253 13491826818037800384894095)
          ·
            refine ⟨20237740227056700577341143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13491826818037800384894095 20237740227056700577341143)
            ·
              refine ⟨30356610340585050866011715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20237740227056700577341143 30356610340585050866011715)
              ·
                refine ⟨45534915510877576299017573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30356610340585050866011715 45534915510877576299017573)
                ·
                  refine ⟨8537796658289545556065795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45534915510877576299017573 8537796658289545556065795)
                  ·
                    refine ⟨12806694987434318334098693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8537796658289545556065795 12806694987434318334098693)
                    ·
                      refine ⟨2401255310143934687643505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12806694987434318334098693 2401255310143934687643505)
                      ·
                        rfl

theorem cell23_4676428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_4676428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676428 prefixEnd_4676428 := by exact prefixLift 4676428
  have htrace : WordTrace (prefixWord ++ tailWord_4676428) baseStart_4676428 baseEnd_4676428 := by
    simpa [prefixWord, tailWord_4676428, baseEnd_4676428] using wordTrace_append hprefix tailTrace_4676428
  have hstable : (prefixWord ++ tailWord_4676428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676428).length < 2 ^ (prefixWord ++ tailWord_4676428).sum := by decide
  have hdescent : baseEnd_4676428 < baseStart_4676428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676429 : List Nat := [1, 6, 1, 2, 2, 1, 3, 2, 5]
def baseStart_4676429 : Nat := 118140960795 + 4676429 * 2 ^ 59
def prefixEnd_4676429 : Nat := 4983230072969 + 3 ^ 40 * 4676429 * 2
def baseEnd_4676429 : Nat := 266806202624954353747889

theorem tailTrace_4676429 : CollatzResearch.WordTrace tailWord_4676429 prefixEnd_4676429 266806202624954353747889 := by
  unfold tailWord_4676429
  simp only [CollatzResearch.WordTrace]
  refine ⟨170563377975103878332904341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113708918650069252221936227 170563377975103878332904341)
  ·
    refine ⟨7995158342582994296854891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 170563377975103878332904341 7995158342582994296854891)
    ·
      refine ⟨11992737513874491445282337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7995158342582994296854891 11992737513874491445282337)
      ·
        refine ⟨8994553135405868583961753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11992737513874491445282337 8994553135405868583961753)
        ·
          refine ⟨6745914851554401437971315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8994553135405868583961753 6745914851554401437971315)
          ·
            refine ⟨10118872277331602156956973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6745914851554401437971315 10118872277331602156956973)
            ·
              refine ⟨3794577103999350808858865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10118872277331602156956973 3794577103999350808858865)
              ·
                refine ⟨2845932827999513106644149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3794577103999350808858865 2845932827999513106644149)
                ·
                  refine ⟨266806202624954353747889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2845932827999513106644149 266806202624954353747889)
                  ·
                    rfl

theorem cell23_4676429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_4676429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676429 prefixEnd_4676429 := by exact prefixLift 4676429
  have htrace : WordTrace (prefixWord ++ tailWord_4676429) baseStart_4676429 baseEnd_4676429 := by
    simpa [prefixWord, tailWord_4676429, baseEnd_4676429] using wordTrace_append hprefix tailTrace_4676429
  have hstable : (prefixWord ++ tailWord_4676429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676429).length < 2 ^ (prefixWord ++ tailWord_4676429).sum := by decide
  have hdescent : baseEnd_4676429 < baseStart_4676429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676431 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 2, 8, 3]
def baseStart_4676431 : Nat := 118140960795 + 4676431 * 2 ^ 59
def prefixEnd_4676431 : Nat := 4983230072969 + 3 ^ 40 * 4676431 * 2
def baseEnd_4676431 : Nat := 2401256850585898175905991

theorem tailTrace_4676431 : CollatzResearch.WordTrace tailWord_4676431 prefixEnd_4676431 2401256850585898175905991 := by
  unfold tailWord_4676431
  simp only [CollatzResearch.WordTrace]
  refine ⟨170563450921096632674477147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113708967280731088449651431 170563450921096632674477147)
  ·
    refine ⟨255845176381644949011715721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170563450921096632674477147 255845176381644949011715721)
    ·
      refine ⟨191883882286233711758786791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255845176381644949011715721 191883882286233711758786791)
      ·
        refine ⟨287825823429350567638180187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191883882286233711758786791 287825823429350567638180187)
        ·
          refine ⟨431738735144025851457270281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287825823429350567638180187 431738735144025851457270281)
          ·
            refine ⟨323804051358019388592952711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 431738735144025851457270281 323804051358019388592952711)
            ·
              refine ⟨485706077037029082889429067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323804051358019388592952711 485706077037029082889429067)
              ·
                refine ⟨728559115555543624334143601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 485706077037029082889429067 728559115555543624334143601)
                ·
                  refine ⟨546419336666657718250607701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 728559115555543624334143601 546419336666657718250607701)
                  ·
                    refine ⟨6403351601562395135749309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 546419336666657718250607701 6403351601562395135749309)
                    ·
                      refine ⟨2401256850585898175905991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6403351601562395135749309 2401256850585898175905991)
                      ·
                        rfl

theorem cell23_4676431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 8, 3].length) (baseStart_4676431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676431 prefixEnd_4676431 := by exact prefixLift 4676431
  have htrace : WordTrace (prefixWord ++ tailWord_4676431) baseStart_4676431 baseEnd_4676431 := by
    simpa [prefixWord, tailWord_4676431, baseEnd_4676431] using wordTrace_append hprefix tailTrace_4676431
  have hstable : (prefixWord ++ tailWord_4676431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676431).length < 2 ^ (prefixWord ++ tailWord_4676431).sum := by decide
  have hdescent : baseEnd_4676431 < baseStart_4676431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676448 : List Nat := [2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 3]
def baseStart_4676448 : Nat := 118140960795 + 4676448 * 2 ^ 59
def prefixEnd_4676448 : Nat := 4983230072969 + 3 ^ 40 * 4676448 * 2
def baseEnd_4676448 : Nat := 2401265579757024609393413

theorem tailTrace_4676448 : CollatzResearch.WordTrace tailWord_4676448 prefixEnd_4676448 2401265579757024609393413 := by
  unfold tailWord_4676448
  simp only [CollatzResearch.WordTrace]
  refine ⟨85282035481017522288922999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113709380641356696385230665 85282035481017522288922999)
  ·
    refine ⟨127923053221526283433384499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85282035481017522288922999 127923053221526283433384499)
    ·
      refine ⟨191884579832289425150076749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127923053221526283433384499 191884579832289425150076749)
      ·
        refine ⟨71956717437108534431278781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191884579832289425150076749 71956717437108534431278781)
        ·
          refine ⟨26983769038915700411729543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71956717437108534431278781 26983769038915700411729543)
          ·
            refine ⟨40475653558373550617594315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26983769038915700411729543 40475653558373550617594315)
            ·
              refine ⟨60713480337560325926391473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40475653558373550617594315 60713480337560325926391473)
              ·
                refine ⟨45535110253170244444793605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60713480337560325926391473 45535110253170244444793605)
                ·
                  refine ⟨8537833172469420833398801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45535110253170244444793605 8537833172469420833398801)
                  ·
                    refine ⟨6403374879352065625049101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8537833172469420833398801 6403374879352065625049101)
                    ·
                      refine ⟨2401265579757024609393413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6403374879352065625049101 2401265579757024609393413)
                      ·
                        rfl

theorem cell23_4676448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_4676448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676448 prefixEnd_4676448 := by exact prefixLift 4676448
  have htrace : WordTrace (prefixWord ++ tailWord_4676448) baseStart_4676448 baseEnd_4676448 := by
    simpa [prefixWord, tailWord_4676448, baseEnd_4676448] using wordTrace_append hprefix tailTrace_4676448
  have hstable : (prefixWord ++ tailWord_4676448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676448).length < 2 ^ (prefixWord ++ tailWord_4676448).sum := by decide
  have hdescent : baseEnd_4676448 < baseStart_4676448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676462 : List Nat := [4, 1, 2, 3, 2, 1, 2, 1, 2, 1, 4]
def baseStart_4676462 : Nat := 118140960795 + 4676462 * 2 ^ 59
def prefixEnd_4676462 : Nat := 4983230072969 + 3 ^ 40 * 4676462 * 2
def baseEnd_4676462 : Nat := 2401272768486187554618349

theorem tailTrace_4676462 : CollatzResearch.WordTrace tailWord_4676462 prefixEnd_4676462 2401272768486187554618349 := by
  unfold tailWord_4676462
  simp only [CollatzResearch.WordTrace]
  refine ⟨21320572697998040621106955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113709721055989549979237093 21320572697998040621106955)
  ·
    refine ⟨31980859046997060931660433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21320572697998040621106955 31980859046997060931660433)
    ·
      refine ⟨23985644285247795698745325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31980859046997060931660433 23985644285247795698745325)
      ·
        refine ⟨8994616606967923387029497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23985644285247795698745325 8994616606967923387029497)
        ·
          refine ⟨6745962455225942540272123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8994616606967923387029497 6745962455225942540272123)
          ·
            refine ⟨10118943682838913810408185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6745962455225942540272123 10118943682838913810408185)
            ·
              refine ⟨7589207762129185357806139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10118943682838913810408185 7589207762129185357806139)
              ·
                refine ⟨11383811643193778036709209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7589207762129185357806139 11383811643193778036709209)
                ·
                  refine ⟨8537858732395333527531907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11383811643193778036709209 8537858732395333527531907)
                  ·
                    refine ⟨12806788098593000291297861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8537858732395333527531907 12806788098593000291297861)
                    ·
                      refine ⟨2401272768486187554618349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12806788098593000291297861 2401272768486187554618349)
                      ·
                        rfl

theorem cell23_4676462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_4676462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676462 prefixEnd_4676462 := by exact prefixLift 4676462
  have htrace : WordTrace (prefixWord ++ tailWord_4676462) baseStart_4676462 baseEnd_4676462 := by
    simpa [prefixWord, tailWord_4676462, baseEnd_4676462] using wordTrace_append hprefix tailTrace_4676462
  have hstable : (prefixWord ++ tailWord_4676462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676462).length < 2 ^ (prefixWord ++ tailWord_4676462).sum := by decide
  have hdescent : baseEnd_4676462 < baseStart_4676462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676465 : List Nat := [1, 2, 2, 2, 1, 5, 2, 1, 2, 2, 3]
def baseStart_4676465 : Nat := 118140960795 + 4676465 * 2 ^ 59
def prefixEnd_4676465 : Nat := 4983230072969 + 3 ^ 40 * 4676465 * 2
def baseEnd_4676465 : Nat := 2401274308928151042880835

theorem tailTrace_4676465 : CollatzResearch.WordTrace tailWord_4676465 prefixEnd_4676465 2401274308928151042880835 := by
  unfold tailWord_4676465
  simp only [CollatzResearch.WordTrace]
  refine ⟨170564691002973456481214849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113709794001982304320809899 170564691002973456481214849)
  ·
    refine ⟨127923518252230092360911137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170564691002973456481214849 127923518252230092360911137)
    ·
      refine ⟨95942638689172569270683353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127923518252230092360911137 95942638689172569270683353)
      ·
        refine ⟨71956979016879426953012515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95942638689172569270683353 71956979016879426953012515)
        ·
          refine ⟨107935468525319140429518773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71956979016879426953012515 107935468525319140429518773)
          ·
            refine ⟨10118950174248669415267385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 107935468525319140429518773 10118950174248669415267385)
            ·
              refine ⟨7589212630686502061450539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10118950174248669415267385 7589212630686502061450539)
              ·
                refine ⟨11383818946029753092175809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7589212630686502061450539 11383818946029753092175809)
                ·
                  refine ⟨8537864209522314819131857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11383818946029753092175809 8537864209522314819131857)
                  ·
                    refine ⟨6403398157141736114348893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8537864209522314819131857 6403398157141736114348893)
                    ·
                      refine ⟨2401274308928151042880835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6403398157141736114348893 2401274308928151042880835)
                      ·
                        rfl

theorem cell23_4676465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_4676465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676465 prefixEnd_4676465 := by exact prefixLift 4676465
  have htrace : WordTrace (prefixWord ++ tailWord_4676465) baseStart_4676465 baseEnd_4676465 := by
    simpa [prefixWord, tailWord_4676465, baseEnd_4676465] using wordTrace_append hprefix tailTrace_4676465
  have hstable : (prefixWord ++ tailWord_4676465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676465).length < 2 ^ (prefixWord ++ tailWord_4676465).sum := by decide
  have hdescent : baseEnd_4676465 < baseStart_4676465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676489 : List Nat := [1, 2, 1, 1, 5, 4, 2, 2, 1, 4]
def baseStart_4676489 : Nat := 118140960795 + 4676489 * 2 ^ 59
def prefixEnd_4676489 : Nat := 4983230072969 + 3 ^ 40 * 4676489 * 2
def baseEnd_4676489 : Nat := 800428877487952982993575

theorem tailTrace_4676489 : CollatzResearch.WordTrace tailWord_4676489 prefixEnd_4676489 800428877487952982993575 := by
  unfold tailWord_4676489
  simp only [CollatzResearch.WordTrace]
  refine ⟨170565566354886508580088521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113710377569924339053392347 170565566354886508580088521)
  ·
    refine ⟨127924174766164881435066391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170565566354886508580088521 127924174766164881435066391)
    ·
      refine ⟨191886262149247322152599587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127924174766164881435066391 191886262149247322152599587)
      ·
        refine ⟨287829393223870983228899381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191886262149247322152599587 287829393223870983228899381)
        ·
          refine ⟨26984005614737904677709317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 287829393223870983228899381 26984005614737904677709317)
          ·
            refine ⟨5059501052763357127070497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26984005614737904677709317 5059501052763357127070497)
            ·
              refine ⟨3794625789572517845302873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5059501052763357127070497 3794625789572517845302873)
              ·
                refine ⟨2845969342179388383977155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3794625789572517845302873 2845969342179388383977155)
                ·
                  refine ⟨4268954013269082575965733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2845969342179388383977155 4268954013269082575965733)
                  ·
                    refine ⟨800428877487952982993575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4268954013269082575965733 800428877487952982993575)
                    ·
                      rfl

theorem cell23_4676489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 2, 1, 4].length) (baseStart_4676489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676489 prefixEnd_4676489 := by exact prefixLift 4676489
  have htrace : WordTrace (prefixWord ++ tailWord_4676489) baseStart_4676489 baseEnd_4676489 := by
    simpa [prefixWord, tailWord_4676489, baseEnd_4676489] using wordTrace_append hprefix tailTrace_4676489
  have hstable : (prefixWord ++ tailWord_4676489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676489).length < 2 ^ (prefixWord ++ tailWord_4676489).sum := by decide
  have hdescent : baseEnd_4676489 < baseStart_4676489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676538 : List Nat := [3, 1, 1, 1, 2, 1, 4, 3, 1, 1, 5]
def baseStart_4676538 : Nat := 118140960795 + 4676538 * 2 ^ 59
def prefixEnd_4676538 : Nat := 4983230072969 + 3 ^ 40 * 4676538 * 2
def baseEnd_4676538 : Nat := 2401311793015929257267999

theorem tailTrace_4676538 : CollatzResearch.WordTrace tailWord_4676538 prefixEnd_4676538 2401311793015929257267999 := by
  unfold tailWord_4676538
  simp only [CollatzResearch.WordTrace]
  refine ⟨42641838382927247487155567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113711569021139326632414845 42641838382927247487155567)
  ·
    refine ⟨63962757574390871230733351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42641838382927247487155567 63962757574390871230733351)
    ·
      refine ⟨95944136361586306846100027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63962757574390871230733351 95944136361586306846100027)
      ·
        refine ⟨143916204542379460269150041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95944136361586306846100027 143916204542379460269150041)
        ·
          refine ⟨107937153406784595201862531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143916204542379460269150041 107937153406784595201862531)
          ·
            refine ⟨161905730110176892802793797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107937153406784595201862531 161905730110176892802793797)
            ·
              refine ⟨30357324395658167400523837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 161905730110176892802793797 30357324395658167400523837)
              ·
                refine ⟨11383996648371812775196439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30357324395658167400523837 11383996648371812775196439)
                ·
                  refine ⟨17075994972557719162794659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11383996648371812775196439 17075994972557719162794659)
                  ·
                    refine ⟨25613992458836578744191989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17075994972557719162794659 25613992458836578744191989)
                    ·
                      refine ⟨2401311793015929257267999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25613992458836578744191989 2401311793015929257267999)
                      ·
                        rfl

theorem cell23_4676538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 1, 1, 5].length) (baseStart_4676538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676538 prefixEnd_4676538 := by exact prefixLift 4676538
  have htrace : WordTrace (prefixWord ++ tailWord_4676538) baseStart_4676538 baseEnd_4676538 := by
    simpa [prefixWord, tailWord_4676538, baseEnd_4676538] using wordTrace_append hprefix tailTrace_4676538
  have hstable : (prefixWord ++ tailWord_4676538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676538).length < 2 ^ (prefixWord ++ tailWord_4676538).sum := by decide
  have hdescent : baseEnd_4676538 < baseStart_4676538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676562 : List Nat := [3, 2, 2, 3, 1, 3, 1, 1, 1, 6]
def baseStart_4676562 : Nat := 118140960795 + 4676562 * 2 ^ 59
def prefixEnd_4676562 : Nat := 4983230072969 + 3 ^ 40 * 4676562 * 2
def baseEnd_4676562 : Nat := 800441372183879054455963

theorem tailTrace_4676562 : CollatzResearch.WordTrace tailWord_4676562 prefixEnd_4676562 800441372183879054455963 := by
  unfold tailWord_4676562
  simp only [CollatzResearch.WordTrace]
  refine ⟨42642057220905510511873985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113712152589081361364997293 42642057220905510511873985)
  ·
    refine ⟨31981542915679132883905489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42642057220905510511873985 31981542915679132883905489)
    ·
      refine ⟨23986157186759349662929117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31981542915679132883905489 23986157186759349662929117)
      ·
        refine ⟨8994808945034756123598419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23986157186759349662929117 8994808945034756123598419)
        ·
          refine ⟨13492213417552134185397629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8994808945034756123598419 13492213417552134185397629)
          ·
            refine ⟨5059580031582050319524111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13492213417552134185397629 5059580031582050319524111)
            ·
              refine ⟨7589370047373075479286167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5059580031582050319524111 7589370047373075479286167)
              ·
                refine ⟨11384055071059613218929251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7589370047373075479286167 11384055071059613218929251)
                ·
                  refine ⟨17076082606589419828393877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11384055071059613218929251 17076082606589419828393877)
                  ·
                    refine ⟨800441372183879054455963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17076082606589419828393877 800441372183879054455963)
                    ·
                      rfl

theorem cell23_4676562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_4676562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676562 prefixEnd_4676562 := by exact prefixLift 4676562
  have htrace : WordTrace (prefixWord ++ tailWord_4676562) baseStart_4676562 baseEnd_4676562 := by
    simpa [prefixWord, tailWord_4676562, baseEnd_4676562] using wordTrace_append hprefix tailTrace_4676562
  have hstable : (prefixWord ++ tailWord_4676562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676562).length < 2 ^ (prefixWord ++ tailWord_4676562).sum := by decide
  have hdescent : baseEnd_4676562 < baseStart_4676562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676565 : List Nat := [1, 3, 2, 3, 3, 1, 1, 1, 1, 1, 6]
def baseStart_4676565 : Nat := 118140960795 + 4676565 * 2 ^ 59
def prefixEnd_4676565 : Nat := 4983230072969 + 3 ^ 40 * 4676565 * 2
def baseEnd_4676565 : Nat := 2401325656993600651630375

theorem tailTrace_4676565 : CollatzResearch.WordTrace tailWord_4676565 prefixEnd_4676565 2401325656993600651630375 := by
  unfold tailWord_4676565
  simp only [CollatzResearch.WordTrace]
  refine ⟨170568338302611173559855149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113712225535074115706570099 170568338302611173559855149)
  ·
    refine ⟨63963126863479190084945681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170568338302611173559855149 63963126863479190084945681)
    ·
      refine ⟨47972345147609392563709261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63963126863479190084945681 47972345147609392563709261)
      ·
        refine ⟨17989629430353522211390973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47972345147609392563709261 17989629430353522211390973)
        ·
          refine ⟨6746111036382570829271615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17989629430353522211390973 6746111036382570829271615)
          ·
            refine ⟨10119166554573856243907423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6746111036382570829271615 10119166554573856243907423)
            ·
              refine ⟨15178749831860784365861135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10119166554573856243907423 15178749831860784365861135)
              ·
                refine ⟨22768124747791176548791703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15178749831860784365861135 22768124747791176548791703)
                ·
                  refine ⟨34152187121686764823187555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22768124747791176548791703 34152187121686764823187555)
                  ·
                    refine ⟨51228280682530147234781333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34152187121686764823187555 51228280682530147234781333)
                    ·
                      refine ⟨2401325656993600651630375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51228280682530147234781333 2401325656993600651630375)
                      ·
                        rfl

theorem cell23_4676565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_4676565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676565 prefixEnd_4676565 := by exact prefixLift 4676565
  have htrace : WordTrace (prefixWord ++ tailWord_4676565) baseStart_4676565 baseEnd_4676565 := by
    simpa [prefixWord, tailWord_4676565, baseEnd_4676565] using wordTrace_append hprefix tailTrace_4676565
  have hstable : (prefixWord ++ tailWord_4676565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676565).length < 2 ^ (prefixWord ++ tailWord_4676565).sum := by decide
  have hdescent : baseEnd_4676565 < baseStart_4676565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676586 : List Nat := [3, 1, 3, 1, 2, 2, 3, 3, 1, 2, 2]
def baseStart_4676586 : Nat := 118140960795 + 4676586 * 2 ^ 59
def prefixEnd_4676586 : Nat := 4983230072969 + 3 ^ 40 * 4676586 * 2
def baseEnd_4676586 : Nat := 2401336440087345069467779

theorem tailTrace_4676586 : CollatzResearch.WordTrace tailWord_4676586 prefixEnd_4676586 2401336440087345069467779 := by
  unfold tailWord_4676586
  simp only [CollatzResearch.WordTrace]
  refine ⟨42642276058883773536592403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113712736157023396097579741 42642276058883773536592403)
  ·
    refine ⟨63963414088325660304888605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42642276058883773536592403 63963414088325660304888605)
    ·
      refine ⟨23986280283122122614333227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63963414088325660304888605 23986280283122122614333227)
      ·
        refine ⟨35979420424683183921499841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23986280283122122614333227 35979420424683183921499841)
        ·
          refine ⟨26984565318512387941124881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35979420424683183921499841 26984565318512387941124881)
          ·
            refine ⟨20238423988884290955843661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26984565318512387941124881 20238423988884290955843661)
            ·
              refine ⟨7589408995831609108441373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20238423988884290955843661 7589408995831609108441373)
              ·
                refine ⟨2846028373436853415665515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7589408995831609108441373 2846028373436853415665515)
                ·
                  refine ⟨4269042560155280123498273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2846028373436853415665515 4269042560155280123498273)
                  ·
                    refine ⟨3201781920116460092623705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4269042560155280123498273 3201781920116460092623705)
                    ·
                      refine ⟨2401336440087345069467779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3201781920116460092623705 2401336440087345069467779)
                      ·
                        rfl

theorem cell23_4676586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_4676586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676586 prefixEnd_4676586 := by exact prefixLift 4676586
  have htrace : WordTrace (prefixWord ++ tailWord_4676586) baseStart_4676586 baseEnd_4676586 := by
    simpa [prefixWord, tailWord_4676586, baseEnd_4676586] using wordTrace_append hprefix tailTrace_4676586
  have hstable : (prefixWord ++ tailWord_4676586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676586).length < 2 ^ (prefixWord ++ tailWord_4676586).sum := by decide
  have hdescent : baseEnd_4676586 < baseStart_4676586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676595 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 7, 3, 2]
def baseStart_4676595 : Nat := 118140960795 + 4676595 * 2 ^ 59
def prefixEnd_4676595 : Nat := 4983230072969 + 3 ^ 40 * 4676595 * 2
def baseEnd_4676595 : Nat := 2401341061413235534255237

theorem tailTrace_4676595 : CollatzResearch.WordTrace tailWord_4676595 prefixEnd_4676595 2401341061413235534255237 := by
  unfold tailWord_4676595
  simp only [CollatzResearch.WordTrace]
  refine ⟨170569432492502488683447239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113712954995001659122298159 170569432492502488683447239)
  ·
    refine ⟨255854148738753733025170859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170569432492502488683447239 255854148738753733025170859)
    ·
      refine ⟨383781223108130599537756289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255854148738753733025170859 383781223108130599537756289)
      ·
        refine ⟨287835917331097949653317217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 383781223108130599537756289 287835917331097949653317217)
        ·
          refine ⟨215876937998323462239987913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287835917331097949653317217 215876937998323462239987913)
          ·
            refine ⟨161907703498742596679990935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215876937998323462239987913 161907703498742596679990935)
            ·
              refine ⟨242861555248113895019986403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161907703498742596679990935 242861555248113895019986403)
              ·
                refine ⟨364292332872170842529979605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 242861555248113895019986403 364292332872170842529979605)
                ·
                  refine ⟨8538101551691504121796397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 364292332872170842529979605 8538101551691504121796397)
                  ·
                    refine ⟨3201788081884314045673649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8538101551691504121796397 3201788081884314045673649)
                    ·
                      refine ⟨2401341061413235534255237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3201788081884314045673649 2401341061413235534255237)
                      ·
                        rfl

theorem cell23_4676595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 3, 2].length) (baseStart_4676595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676595 prefixEnd_4676595 := by exact prefixLift 4676595
  have htrace : WordTrace (prefixWord ++ tailWord_4676595) baseStart_4676595 baseEnd_4676595 := by
    simpa [prefixWord, tailWord_4676595, baseEnd_4676595] using wordTrace_append hprefix tailTrace_4676595
  have hstable : (prefixWord ++ tailWord_4676595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676595).length < 2 ^ (prefixWord ++ tailWord_4676595).sum := by decide
  have hdescent : baseEnd_4676595 < baseStart_4676595 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676619 : List Nat := [1, 1, 1, 1, 6, 2, 4, 1, 2, 1, 3]
def baseStart_4676619 : Nat := 118140960795 + 4676619 * 2 ^ 59
def prefixEnd_4676619 : Nat := 4983230072969 + 3 ^ 40 * 4676619 * 2
def baseEnd_4676619 : Nat := 2401353384948943440355127

theorem tailTrace_4676619 : CollatzResearch.WordTrace tailWord_4676619 prefixEnd_4676619 2401353384948943440355127 := by
  unfold tailWord_4676619
  simp only [CollatzResearch.WordTrace]
  refine ⟨170570307844415540782320911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113713538562943693854880607 170570307844415540782320911)
  ·
    refine ⟨255855461766623311173481367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170570307844415540782320911 255855461766623311173481367)
    ·
      refine ⟨383783192649934966760222051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255855461766623311173481367 383783192649934966760222051)
      ·
        refine ⟨575674788974902450140333077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383783192649934966760222051 575674788974902450140333077)
        ·
          refine ⟨26984755733198552350328113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 575674788974902450140333077 26984755733198552350328113)
          ·
            refine ⟨20238566799898914262746085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26984755733198552350328113 20238566799898914262746085)
            ·
              refine ⟨3794731274981046424264891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20238566799898914262746085 3794731274981046424264891)
              ·
                refine ⟨5692096912471569636397337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3794731274981046424264891 5692096912471569636397337)
                ·
                  refine ⟨4269072684353677227298003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5692096912471569636397337 4269072684353677227298003)
                  ·
                    refine ⟨6403609026530515840947005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4269072684353677227298003 6403609026530515840947005)
                    ·
                      refine ⟨2401353384948943440355127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6403609026530515840947005 2401353384948943440355127)
                      ·
                        rfl

theorem cell23_4676619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 2, 1, 3].length) (baseStart_4676619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676619 prefixEnd_4676619 := by exact prefixLift 4676619
  have htrace : WordTrace (prefixWord ++ tailWord_4676619) baseStart_4676619 baseEnd_4676619 := by
    simpa [prefixWord, tailWord_4676619, baseEnd_4676619] using wordTrace_append hprefix tailTrace_4676619
  have hstable : (prefixWord ++ tailWord_4676619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676619).length < 2 ^ (prefixWord ++ tailWord_4676619).sum := by decide
  have hdescent : baseEnd_4676619 < baseStart_4676619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676625 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 5, 4, 2]
def baseStart_4676625 : Nat := 118140960795 + 4676625 * 2 ^ 59
def prefixEnd_4676625 : Nat := 4983230072969 + 3 ^ 40 * 4676625 * 2
def baseEnd_4676625 : Nat := 2401356465832870416880099

theorem tailTrace_4676625 : CollatzResearch.WordTrace tailWord_4676625 prefixEnd_4676625 2401356465832870416880099 := by
  unfold tailWord_4676625
  simp only [CollatzResearch.WordTrace]
  refine ⟨170570526682393803807039329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113713684454929202538026219 170570526682393803807039329)
  ·
    refine ⟨127927895011795352855279497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170570526682393803807039329 127927895011795352855279497)
    ·
      refine ⟨95945921258846514641459623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127927895011795352855279497 95945921258846514641459623)
      ·
        refine ⟨143918881888269771962189435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95945921258846514641459623 143918881888269771962189435)
        ·
          refine ⟨215878322832404657943284153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143918881888269771962189435 215878322832404657943284153)
          ·
            refine ⟨161908742124303493457463115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215878322832404657943284153 161908742124303493457463115)
            ·
              refine ⟨242863113186455240186194673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161908742124303493457463115 242863113186455240186194673)
              ·
                refine ⟨182147334889841430139646005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 242863113186455240186194673 182147334889841430139646005)
                ·
                  refine ⟨17076312645922634075591813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 182147334889841430139646005 17076312645922634075591813)
                  ·
                    refine ⟨3201808621110493889173465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17076312645922634075591813 3201808621110493889173465)
                    ·
                      refine ⟨2401356465832870416880099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3201808621110493889173465 2401356465832870416880099)
                      ·
                        rfl

theorem cell23_4676625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 4, 2].length) (baseStart_4676625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676625 prefixEnd_4676625 := by exact prefixLift 4676625
  have htrace : WordTrace (prefixWord ++ tailWord_4676625) baseStart_4676625 baseEnd_4676625 := by
    simpa [prefixWord, tailWord_4676625, baseEnd_4676625] using wordTrace_append hprefix tailTrace_4676625
  have hstable : (prefixWord ++ tailWord_4676625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676625).length < 2 ^ (prefixWord ++ tailWord_4676625).sum := by decide
  have hdescent : baseEnd_4676625 < baseStart_4676625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676629 : List Nat := [1, 3, 2, 1, 4, 1, 3, 2, 1, 3, 2]
def baseStart_4676629 : Nat := 118140960795 + 4676629 * 2 ^ 59
def prefixEnd_4676629 : Nat := 4983230072969 + 3 ^ 40 * 4676629 * 2
def baseEnd_4676629 : Nat := 2401358519755488401230081

theorem tailTrace_4676629 : CollatzResearch.WordTrace tailWord_4676629 prefixEnd_4676629 2401358519755488401230081 := by
  unfold tailWord_4676629
  simp only [CollatzResearch.WordTrace]
  refine ⟨170570672574379312490184941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113713781716252874993456627 170570672574379312490184941)
  ·
    refine ⟨63964002215392242183819353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170570672574379312490184941 63964002215392242183819353)
    ·
      refine ⟨47973001661544181637864515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63964002215392242183819353 47973001661544181637864515)
      ·
        refine ⟨71959502492316272456796773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47973001661544181637864515 71959502492316272456796773)
        ·
          refine ⟨13492406717309301085649395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71959502492316272456796773 13492406717309301085649395)
          ·
            refine ⟨20238610075963951628474093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13492406717309301085649395 20238610075963951628474093)
            ·
              refine ⟨7589478778486481860677785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20238610075963951628474093 7589478778486481860677785)
              ·
                refine ⟨5692109083864861395508339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7589478778486481860677785 5692109083864861395508339)
                ·
                  refine ⟨8538163625797292093262509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5692109083864861395508339 8538163625797292093262509)
                  ·
                    refine ⟨3201811359673984534973441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8538163625797292093262509 3201811359673984534973441)
                    ·
                      refine ⟨2401358519755488401230081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3201811359673984534973441 2401358519755488401230081)
                      ·
                        rfl

theorem cell23_4676629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 3, 2].length) (baseStart_4676629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676629 prefixEnd_4676629 := by exact prefixLift 4676629
  have htrace : WordTrace (prefixWord ++ tailWord_4676629) baseStart_4676629 baseEnd_4676629 := by
    simpa [prefixWord, tailWord_4676629, baseEnd_4676629] using wordTrace_append hprefix tailTrace_4676629
  have hstable : (prefixWord ++ tailWord_4676629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676629).length < 2 ^ (prefixWord ++ tailWord_4676629).sum := by decide
  have hdescent : baseEnd_4676629 < baseStart_4676629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676642 : List Nat := [3, 3, 1, 1, 1, 3, 1, 1, 3, 4, 2]
def baseStart_4676642 : Nat := 118140960795 + 4676642 * 2 ^ 59
def prefixEnd_4676642 : Nat := 4983230072969 + 3 ^ 40 * 4676642 * 2
def baseEnd_4676642 : Nat := 2401365195003996850367521

theorem tailTrace_4676642 : CollatzResearch.WordTrace tailWord_4676642 prefixEnd_4676642 2401365195003996850367521 := by
  unfold tailWord_4676642
  simp only [CollatzResearch.WordTrace]
  refine ⟨42642786680833053927602045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113714097815554810473605453 42642786680833053927602045)
  ·
    refine ⟨15991045005312395222850767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42642786680833053927602045 15991045005312395222850767)
    ·
      refine ⟨23986567507968592834276151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15991045005312395222850767 23986567507968592834276151)
      ·
        refine ⟨35979851261952889251414227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23986567507968592834276151 35979851261952889251414227)
        ·
          refine ⟨53969776892929333877121341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35979851261952889251414227 53969776892929333877121341)
          ·
            refine ⟨20238666334848500203920503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53969776892929333877121341 20238666334848500203920503)
            ·
              refine ⟨30357999502272750305880755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20238666334848500203920503 30357999502272750305880755)
              ·
                refine ⟨45536999253409125458821133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30357999502272750305880755 45536999253409125458821133)
                ·
                  refine ⟨17076374720028422047057925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45536999253409125458821133 17076374720028422047057925)
                  ·
                    refine ⟨3201820260005329133823361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17076374720028422047057925 3201820260005329133823361)
                    ·
                      refine ⟨2401365195003996850367521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3201820260005329133823361 2401365195003996850367521)
                      ·
                        rfl

theorem cell23_4676642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_4676642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676642 prefixEnd_4676642 := by exact prefixLift 4676642
  have htrace : WordTrace (prefixWord ++ tailWord_4676642) baseStart_4676642 baseEnd_4676642 := by
    simpa [prefixWord, tailWord_4676642, baseEnd_4676642] using wordTrace_append hprefix tailTrace_4676642
  have hstable : (prefixWord ++ tailWord_4676642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676642).length < 2 ^ (prefixWord ++ tailWord_4676642).sum := by decide
  have hdescent : baseEnd_4676642 < baseStart_4676642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676662 : List Nat := [5, 1, 2, 1, 1, 2, 1, 1, 2, 4, 3]
def baseStart_4676662 : Nat := 118140960795 + 4676662 * 2 ^ 59
def prefixEnd_4676662 : Nat := 4983230072969 + 3 ^ 40 * 4676662 * 2
def baseEnd_4676662 : Nat := 2401375464617086772117429

theorem tailTrace_4676662 : CollatzResearch.WordTrace tailWord_4676662 prefixEnd_4676662 2401375464617086772117429 := by
  unfold tailWord_4676662
  simp only [CollatzResearch.WordTrace]
  refine ⟨10660742261453734945383515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 113714584122173172750757493 10660742261453734945383515)
  ·
    refine ⟨15991113392180602418075273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10660742261453734945383515 15991113392180602418075273)
    ·
      refine ⟨11993335044135451813556455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15991113392180602418075273 11993335044135451813556455)
      ·
        refine ⟨17990002566203177720334683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11993335044135451813556455 17990002566203177720334683)
        ·
          refine ⟨26985003849304766580502025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17990002566203177720334683 26985003849304766580502025)
          ·
            refine ⟨20238752886978574935376519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26985003849304766580502025 20238752886978574935376519)
            ·
              refine ⟨30358129330467862403064779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20238752886978574935376519 30358129330467862403064779)
              ·
                refine ⟨45537193995701793604597169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30358129330467862403064779 45537193995701793604597169)
                ·
                  refine ⟨34152895496776345203447877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45537193995701793604597169 34152895496776345203447877)
                  ·
                    refine ⟨6403667905645564725646477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34152895496776345203447877 6403667905645564725646477)
                    ·
                      refine ⟨2401375464617086772117429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6403667905645564725646477 2401375464617086772117429)
                      ·
                        rfl

theorem cell23_4676662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_4676662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676662 prefixEnd_4676662 := by exact prefixLift 4676662
  have htrace : WordTrace (prefixWord ++ tailWord_4676662) baseStart_4676662 baseEnd_4676662 := by
    simpa [prefixWord, tailWord_4676662, baseEnd_4676662] using wordTrace_append hprefix tailTrace_4676662
  have hstable : (prefixWord ++ tailWord_4676662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676662).length < 2 ^ (prefixWord ++ tailWord_4676662).sum := by decide
  have hdescent : baseEnd_4676662 < baseStart_4676662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676675 : List Nat := [1, 1, 1, 3, 1, 2, 5, 1, 2, 3, 3]
def baseStart_4676675 : Nat := 118140960795 + 4676675 * 2 ^ 59
def prefixEnd_4676675 : Nat := 4983230072969 + 3 ^ 40 * 4676675 * 2
def baseEnd_4676675 : Nat := 2401382139865595221254869

theorem tailTrace_4676675 : CollatzResearch.WordTrace tailWord_4676675 prefixEnd_4676675 2401382139865595221254869 := by
  unfold tailWord_4676675
  simp only [CollatzResearch.WordTrace]
  refine ⟨170572350332212662346359479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113714900221475108230906319 170572350332212662346359479)
  ·
    refine ⟨255858525498318993519539219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170572350332212662346359479 255858525498318993519539219)
    ·
      refine ⟨383787788247478490279308829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255858525498318993519539219 383787788247478490279308829)
      ·
        refine ⟨143920420592804433854740811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 383787788247478490279308829 143920420592804433854740811)
        ·
          refine ⟨215880630889206650782111217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143920420592804433854740811 215880630889206650782111217)
          ·
            refine ⟨161910473166904988086583413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215880630889206650782111217 161910473166904988086583413)
            ·
              refine ⟨15179106859397342633117195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 161910473166904988086583413 15179106859397342633117195)
              ·
                refine ⟨22768660289096013949675793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15179106859397342633117195 22768660289096013949675793)
                ·
                  refine ⟨17076495216822010462256845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22768660289096013949675793 17076495216822010462256845)
                  ·
                    refine ⟨6403685706308253923346317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17076495216822010462256845 6403685706308253923346317)
                    ·
                      refine ⟨2401382139865595221254869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6403685706308253923346317 2401382139865595221254869)
                      ·
                        rfl

theorem cell23_4676675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 3, 3].length) (baseStart_4676675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676675 prefixEnd_4676675 := by exact prefixLift 4676675
  have htrace : WordTrace (prefixWord ++ tailWord_4676675) baseStart_4676675 baseEnd_4676675 := by
    simpa [prefixWord, tailWord_4676675, baseEnd_4676675] using wordTrace_append hprefix tailTrace_4676675
  have hstable : (prefixWord ++ tailWord_4676675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676675).length < 2 ^ (prefixWord ++ tailWord_4676675).sum := by decide
  have hdescent : baseEnd_4676675 < baseStart_4676675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676688 : List Nat := [2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 7]
def baseStart_4676688 : Nat := 118140960795 + 4676688 * 2 ^ 59
def prefixEnd_4676688 : Nat := 4983230072969 + 3 ^ 40 * 4676688 * 2
def baseEnd_4676688 : Nat := 2401388815114103670392309

theorem tailTrace_4676688 : CollatzResearch.WordTrace tailWord_4676688 prefixEnd_4676688 2401388815114103670392309 := by
  unfold tailWord_4676688
  simp only [CollatzResearch.WordTrace]
  refine ⟨85286412240582782783291359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113715216320777043711055145 85286412240582782783291359)
  ·
    refine ⟨127929618360874174174937039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85286412240582782783291359 127929618360874174174937039)
    ·
      refine ⟨191894427541311261262405559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127929618360874174174937039 191894427541311261262405559)
      ·
        refine ⟨287841641311966891893608339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191894427541311261262405559 287841641311966891893608339)
        ·
          refine ⟨431762461967950337840412509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287841641311966891893608339 431762461967950337840412509)
          ·
            refine ⟨161910923237981376690154691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 431762461967950337840412509 161910923237981376690154691)
            ·
              refine ⟨242866384856972065035232037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161910923237981376690154691 242866384856972065035232037)
              ·
                refine ⟨45537447160682262194106007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 242866384856972065035232037 45537447160682262194106007)
                ·
                  refine ⟨68306170741023393291159011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45537447160682262194106007 68306170741023393291159011)
                  ·
                    refine ⟨102459256111535089936738517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68306170741023393291159011 102459256111535089936738517)
                    ·
                      refine ⟨2401388815114103670392309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 102459256111535089936738517 2401388815114103670392309)
                      ·
                        rfl

theorem cell23_4676688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 7].length) (baseStart_4676688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676688 prefixEnd_4676688 := by exact prefixLift 4676688
  have htrace : WordTrace (prefixWord ++ tailWord_4676688) baseStart_4676688 baseEnd_4676688 := by
    simpa [prefixWord, tailWord_4676688, baseEnd_4676688] using wordTrace_append hprefix tailTrace_4676688
  have hstable : (prefixWord ++ tailWord_4676688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676688).length < 2 ^ (prefixWord ++ tailWord_4676688).sum := by decide
  have hdescent : baseEnd_4676688 < baseStart_4676688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676732 : List Nat := [2, 2, 2, 1, 1, 3, 1, 3, 2, 4, 2]
def baseStart_4676732 : Nat := 118140960795 + 4676732 * 2 ^ 59
def prefixEnd_4676732 : Nat := 4983230072969 + 3 ^ 40 * 4676732 * 2
def baseEnd_4676732 : Nat := 2401411408262901498242107

theorem tailTrace_4676732 : CollatzResearch.WordTrace tailWord_4676732 prefixEnd_4676732 2401411408262901498242107 := by
  unfold tailWord_4676732
  simp only [CollatzResearch.WordTrace]
  refine ⟨85287214646503080540592225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113716286195337440720789633 85287214646503080540592225)
  ·
    refine ⟨63965410984877310405444169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85287214646503080540592225 63965410984877310405444169)
    ·
      refine ⟨47974058238657982804083127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63965410984877310405444169 47974058238657982804083127)
      ·
        refine ⟨71961087357986974206124691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47974058238657982804083127 71961087357986974206124691)
        ·
          refine ⟨107941631036980461309187037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71961087357986974206124691 107941631036980461309187037)
          ·
            refine ⟨40478111638867672990945139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107941631036980461309187037 40478111638867672990945139)
            ·
              refine ⟨60717167458301509486417709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40478111638867672990945139 60717167458301509486417709)
              ·
                refine ⟨22768937796863066057406641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60717167458301509486417709 22768937796863066057406641)
                ·
                  refine ⟨17076703347647299543054981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22768937796863066057406641 17076703347647299543054981)
                  ·
                    refine ⟨3201881877683868664322809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17076703347647299543054981 3201881877683868664322809)
                    ·
                      refine ⟨2401411408262901498242107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3201881877683868664322809 2401411408262901498242107)
                      ·
                        rfl

theorem cell23_4676732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 2, 4, 2].length) (baseStart_4676732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676732 prefixEnd_4676732 := by exact prefixLift 4676732
  have htrace : WordTrace (prefixWord ++ tailWord_4676732) baseStart_4676732 baseEnd_4676732 := by
    simpa [prefixWord, tailWord_4676732, baseEnd_4676732] using wordTrace_append hprefix tailTrace_4676732
  have hstable : (prefixWord ++ tailWord_4676732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676732).length < 2 ^ (prefixWord ++ tailWord_4676732).sum := by decide
  have hdescent : baseEnd_4676732 < baseStart_4676732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676792 : List Nat := [2, 1, 2, 1, 2, 1, 2, 4, 1, 5, 2]
def baseStart_4676792 : Nat := 118140960795 + 4676792 * 2 ^ 59
def prefixEnd_4676792 : Nat := 4983230072969 + 3 ^ 40 * 4676792 * 2
def baseEnd_4676792 : Nat := 2401442217102171263491831

theorem tailTrace_4676792 : CollatzResearch.WordTrace tailWord_4676792 prefixEnd_4676792 2401442217102171263491831 := by
  unfold tailWord_4676792
  simp only [CollatzResearch.WordTrace]
  refine ⟨85288308836394395664184315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113717745115192527552245753 85288308836394395664184315)
  ·
    refine ⟨127932463254591593496276473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85288308836394395664184315 127932463254591593496276473)
    ·
      refine ⟨95949347440943695122207355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127932463254591593496276473 95949347440943695122207355)
      ·
        refine ⟨143924021161415542683311033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95949347440943695122207355 143924021161415542683311033)
        ·
          refine ⟨107943015871061657012483275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143924021161415542683311033 107943015871061657012483275)
          ·
            refine ⟨161914523806592485518724913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107943015871061657012483275 161914523806592485518724913)
            ·
              refine ⟨121435892854944364139043685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161914523806592485518724913 121435892854944364139043685)
              ·
                refine ⟨22769229910302068276070691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 121435892854944364139043685 22769229910302068276070691)
                ·
                  refine ⟨34153844865453102414106037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22769229910302068276070691 34153844865453102414106037)
                  ·
                    refine ⟨3201922956136228351322441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34153844865453102414106037 3201922956136228351322441)
                    ·
                      refine ⟨2401442217102171263491831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3201922956136228351322441 2401442217102171263491831)
                      ·
                        rfl

theorem cell23_4676792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 1, 5, 2].length) (baseStart_4676792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676792 prefixEnd_4676792 := by exact prefixLift 4676792
  have htrace : WordTrace (prefixWord ++ tailWord_4676792) baseStart_4676792 baseEnd_4676792 := by
    simpa [prefixWord, tailWord_4676792, baseEnd_4676792] using wordTrace_append hprefix tailTrace_4676792
  have hstable : (prefixWord ++ tailWord_4676792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676792).length < 2 ^ (prefixWord ++ tailWord_4676792).sum := by decide
  have hdescent : baseEnd_4676792 < baseStart_4676792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676833 : List Nat := [1, 2, 3, 1, 3, 2, 4, 2, 1, 1, 3]
def baseStart_4676833 : Nat := 118140960795 + 4676833 * 2 ^ 59
def prefixEnd_4676833 : Nat := 4983230072969 + 3 ^ 40 * 4676833 * 2
def baseEnd_4676833 : Nat := 2401463269809005603079143

theorem tailTrace_4676833 : CollatzResearch.WordTrace tailWord_4676833 prefixEnd_4676833 2401463269809005603079143 := by
  unfold tailWord_4676833
  simp only [CollatzResearch.WordTrace]
  refine ⟨170578113065640255330611153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113718742043760170220407435 170578113065640255330611153)
  ·
    refine ⟨127933584799230191497958365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170578113065640255330611153 127933584799230191497958365)
    ·
      refine ⟨47975094299711321811734387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127933584799230191497958365 47975094299711321811734387)
      ·
        refine ⟨71962641449566982717601581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47975094299711321811734387 71962641449566982717601581)
        ·
          refine ⟨26985990543587618519100593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71962641449566982717601581 26985990543587618519100593)
          ·
            refine ⟨20239492907690713889325445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26985990543587618519100593 20239492907690713889325445)
            ·
              refine ⟨3794904920192008854248521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20239492907690713889325445 3794904920192008854248521)
              ·
                refine ⟨2846178690144006640686391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3794904920192008854248521 2846178690144006640686391)
                ·
                  refine ⟨4269268035216009961029587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2846178690144006640686391 4269268035216009961029587)
                  ·
                    refine ⟨6403902052824014941544381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4269268035216009961029587 6403902052824014941544381)
                    ·
                      refine ⟨2401463269809005603079143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6403902052824014941544381 2401463269809005603079143)
                      ·
                        rfl

theorem cell23_4676833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 2, 1, 1, 3].length) (baseStart_4676833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676833 prefixEnd_4676833 := by exact prefixLift 4676833
  have htrace : WordTrace (prefixWord ++ tailWord_4676833) baseStart_4676833 baseEnd_4676833 := by
    simpa [prefixWord, tailWord_4676833, baseEnd_4676833] using wordTrace_append hprefix tailTrace_4676833
  have hstable : (prefixWord ++ tailWord_4676833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676833).length < 2 ^ (prefixWord ++ tailWord_4676833).sum := by decide
  have hdescent : baseEnd_4676833 < baseStart_4676833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676873 : List Nat := [1, 2, 1, 1, 3, 3, 4, 3, 1, 2, 2]
def baseStart_4676873 : Nat := 118140960795 + 4676873 * 2 ^ 59
def prefixEnd_4676873 : Nat := 4983230072969 + 3 ^ 40 * 4676873 * 2
def baseEnd_4676873 : Nat := 2401483809035185446578959

theorem tailTrace_4676873 : CollatzResearch.WordTrace tailWord_4676873 prefixEnd_4676873 2401483809035185446578959 := by
  unfold tailWord_4676873
  simp only [CollatzResearch.WordTrace]
  refine ⟨170579571985495342162067273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113719714656996894774711515 170579571985495342162067273)
  ·
    refine ⟨127934678989121506621550455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170579571985495342162067273 127934678989121506621550455)
    ·
      refine ⟨191902018483682259932325683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127934678989121506621550455 191902018483682259932325683)
      ·
        refine ⟨287853027725523389898488525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191902018483682259932325683 287853027725523389898488525)
        ·
          refine ⟨107944885397071271211933197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 287853027725523389898488525 107944885397071271211933197)
          ·
            refine ⟨40479332023901726704474949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107944885397071271211933197 40479332023901726704474949)
            ·
              refine ⟨7589874754481573757089053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40479332023901726704474949 7589874754481573757089053)
              ·
                refine ⟨2846203032930590158908395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7589874754481573757089053 2846203032930590158908395)
                ·
                  refine ⟨4269304549395885238362593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2846203032930590158908395 4269304549395885238362593)
                  ·
                    refine ⟨3201978412046913928771945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4269304549395885238362593 3201978412046913928771945)
                    ·
                      refine ⟨2401483809035185446578959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3201978412046913928771945 2401483809035185446578959)
                      ·
                        rfl

theorem cell23_4676873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 3, 1, 2, 2].length) (baseStart_4676873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676873 prefixEnd_4676873 := by exact prefixLift 4676873
  have htrace : WordTrace (prefixWord ++ tailWord_4676873) baseStart_4676873 baseEnd_4676873 := by
    simpa [prefixWord, tailWord_4676873, baseEnd_4676873] using wordTrace_append hprefix tailTrace_4676873
  have hstable : (prefixWord ++ tailWord_4676873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676873).length < 2 ^ (prefixWord ++ tailWord_4676873).sum := by decide
  have hdescent : baseEnd_4676873 < baseStart_4676873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676876 : List Nat := [2, 2, 1, 2, 2, 3, 4, 1, 1, 2, 3]
def baseStart_4676876 : Nat := 118140960795 + 4676876 * 2 ^ 59
def prefixEnd_4676876 : Nat := 4983230072969 + 3 ^ 40 * 4676876 * 2
def baseEnd_4676876 : Nat := 2401485349477148934841445

theorem tailTrace_4676876 : CollatzResearch.WordTrace tailWord_4676876 prefixEnd_4676876 2401485349477148934841445 := by
  unfold tailWord_4676876
  simp only [CollatzResearch.WordTrace]
  refine ⟨85289840702242236837213241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113719787602989649116284321 85289840702242236837213241)
  ·
    refine ⟨63967380526681677627909931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85289840702242236837213241 63967380526681677627909931)
    ·
      refine ⟨95951070790022516441864897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63967380526681677627909931 95951070790022516441864897)
      ·
        refine ⟨71963303092516887331398673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95951070790022516441864897 71963303092516887331398673)
        ·
          refine ⟨53972477319387665498549005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71963303092516887331398673 53972477319387665498549005)
          ·
            refine ⟨20239678994770374561955877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53972477319387665498549005 20239678994770374561955877)
            ·
              refine ⟨3794939811519445230366727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20239678994770374561955877 3794939811519445230366727)
              ·
                refine ⟨5692409717279167845550091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3794939811519445230366727 5692409717279167845550091)
                ·
                  refine ⟨8538614575918751768325137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5692409717279167845550091 8538614575918751768325137)
                  ·
                    refine ⟨6403960931939063826243853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8538614575918751768325137 6403960931939063826243853)
                    ·
                      refine ⟨2401485349477148934841445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6403960931939063826243853 2401485349477148934841445)
                      ·
                        rfl

theorem cell23_4676876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 1, 2, 3].length) (baseStart_4676876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676876 prefixEnd_4676876 := by exact prefixLift 4676876
  have htrace : WordTrace (prefixWord ++ tailWord_4676876) baseStart_4676876 baseEnd_4676876 := by
    simpa [prefixWord, tailWord_4676876, baseEnd_4676876] using wordTrace_append hprefix tailTrace_4676876
  have hstable : (prefixWord ++ tailWord_4676876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676876).length < 2 ^ (prefixWord ++ tailWord_4676876).sum := by decide
  have hdescent : baseEnd_4676876 < baseStart_4676876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676905 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 5, 8]
def baseStart_4676905 : Nat := 118140960795 + 4676905 * 2 ^ 59
def prefixEnd_4676905 : Nat := 4983230072969 + 3 ^ 40 * 4676905 * 2
def baseEnd_4676905 : Nat := 800500080138709773792937

theorem tailTrace_4676905 : CollatzResearch.WordTrace tailWord_4676905 prefixEnd_4676905 800500080138709773792937 := by
  unfold tailWord_4676905
  simp only [CollatzResearch.WordTrace]
  refine ⟨170580739121379411627232169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113720492747586274418154779 170580739121379411627232169)
  ·
    refine ⟨127935554341034558720424127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170580739121379411627232169 127935554341034558720424127)
    ·
      refine ⟨191903331511551838080636191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127935554341034558720424127 191903331511551838080636191)
      ·
        refine ⟨287854997267327757120954287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191903331511551838080636191 287854997267327757120954287)
        ·
          refine ⟨431782495900991635681431431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287854997267327757120954287 431782495900991635681431431)
          ·
            refine ⟨647673743851487453522147147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431782495900991635681431431 647673743851487453522147147)
            ·
              refine ⟨971510615777231180283220721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 647673743851487453522147147 971510615777231180283220721)
              ·
                refine ⟨728632961832923385212415541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 971510615777231180283220721 728632961832923385212415541)
                ·
                  refine ⟨68309340171836567363663957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 728632961832923385212415541 68309340171836567363663957)
                  ·
                    refine ⟨800500080138709773792937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68309340171836567363663957 800500080138709773792937)
                    ·
                      rfl

theorem cell23_4676905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 8].length) (baseStart_4676905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676905 prefixEnd_4676905 := by exact prefixLift 4676905
  have htrace : WordTrace (prefixWord ++ tailWord_4676905) baseStart_4676905 baseEnd_4676905 := by
    simpa [prefixWord, tailWord_4676905, baseEnd_4676905] using wordTrace_append hprefix tailTrace_4676905
  have hstable : (prefixWord ++ tailWord_4676905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676905).length < 2 ^ (prefixWord ++ tailWord_4676905).sum := by decide
  have hdescent : baseEnd_4676905 < baseStart_4676905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676906 : List Nat := [3, 1, 4, 2, 1, 1, 3, 1, 1, 3, 3]
def baseStart_4676906 : Nat := 118140960795 + 4676906 * 2 ^ 59
def prefixEnd_4676906 : Nat := 4983230072969 + 3 ^ 40 * 4676906 * 2
def baseEnd_4676906 : Nat := 2401500753896783817466307

theorem tailTrace_4676906 : CollatzResearch.WordTrace tailWord_4676906 prefixEnd_4676906 2401500753896783817466307 := by
  unfold tailWord_4676906
  simp only [CollatzResearch.WordTrace]
  refine ⟨42645193898593947199504643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113720517062917192532012381 42645193898593947199504643)
  ·
    refine ⟨63967790847890920799256965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42645193898593947199504643 63967790847890920799256965)
    ·
      refine ⟨11993960783979547649860681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63967790847890920799256965 11993960783979547649860681)
      ·
        refine ⟨8995470587984660737395511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11993960783979547649860681 8995470587984660737395511)
        ·
          refine ⟨13493205881976991106093267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8995470587984660737395511 13493205881976991106093267)
          ·
            refine ⟨20239808822965486659139901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13493205881976991106093267 20239808822965486659139901)
            ·
              refine ⟨7589928308612057497177463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20239808822965486659139901 7589928308612057497177463)
              ·
                refine ⟨11384892462918086245766195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7589928308612057497177463 11384892462918086245766195)
                ·
                  refine ⟨17077338694377129368649293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11384892462918086245766195 17077338694377129368649293)
                  ·
                    refine ⟨6404002010391423513243485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17077338694377129368649293 6404002010391423513243485)
                    ·
                      refine ⟨2401500753896783817466307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6404002010391423513243485 2401500753896783817466307)
                      ·
                        rfl

theorem cell23_4676906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_4676906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676906 prefixEnd_4676906 := by exact prefixLift 4676906
  have htrace : WordTrace (prefixWord ++ tailWord_4676906) baseStart_4676906 baseEnd_4676906 := by
    simpa [prefixWord, tailWord_4676906, baseEnd_4676906] using wordTrace_append hprefix tailTrace_4676906
  have hstable : (prefixWord ++ tailWord_4676906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676906).length < 2 ^ (prefixWord ++ tailWord_4676906).sum := by decide
  have hdescent : baseEnd_4676906 < baseStart_4676906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676957 : List Nat := [1, 4, 5, 1, 1, 1, 1, 3, 2, 1, 3]
def baseStart_4676957 : Nat := 118140960795 + 4676957 * 2 ^ 59
def prefixEnd_4676957 : Nat := 4983230072969 + 3 ^ 40 * 4676957 * 2
def baseEnd_4676957 : Nat := 2401526941410163117928573

theorem tailTrace_4676957 : CollatzResearch.WordTrace tailWord_4676957 prefixEnd_4676957 2401526941410163117928573 := by
  unfold tailWord_4676957
  simp only [CollatzResearch.WordTrace]
  refine ⟨170582635717191024508125125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113721757144794016338750083 170582635717191024508125125)
  ·
    refine ⟨31984244196973317095273461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170582635717191024508125125 31984244196973317095273461)
    ·
      refine ⟨2998522893466248477681887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31984244196973317095273461 2998522893466248477681887)
      ·
        refine ⟨4497784340199372716522831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2998522893466248477681887 4497784340199372716522831)
        ·
          refine ⟨6746676510299059074784247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4497784340199372716522831 6746676510299059074784247)
          ·
            refine ⟨10120014765448588612176371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6746676510299059074784247 10120014765448588612176371)
            ·
              refine ⟨15180022148172882918264557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10120014765448588612176371 15180022148172882918264557)
              ·
                refine ⟨5692508305564831094349209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15180022148172882918264557 5692508305564831094349209)
                ·
                  refine ⟨4269381229173623320761907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5692508305564831094349209 4269381229173623320761907)
                  ·
                    refine ⟨6404071843760434981142861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4269381229173623320761907 6404071843760434981142861)
                    ·
                      refine ⟨2401526941410163117928573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6404071843760434981142861 2401526941410163117928573)
                      ·
                        rfl

theorem cell23_4676957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_4676957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676957 prefixEnd_4676957 := by exact prefixLift 4676957
  have htrace : WordTrace (prefixWord ++ tailWord_4676957) baseStart_4676957 baseEnd_4676957 := by
    simpa [prefixWord, tailWord_4676957, baseEnd_4676957] using wordTrace_append hprefix tailTrace_4676957
  have hstable : (prefixWord ++ tailWord_4676957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676957).length < 2 ^ (prefixWord ++ tailWord_4676957).sum := by decide
  have hdescent : baseEnd_4676957 < baseStart_4676957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676963 : List Nat := [1, 1, 1, 5, 2, 3, 1, 3, 2, 2, 2]
def baseStart_4676963 : Nat := 118140960795 + 4676963 * 2 ^ 59
def prefixEnd_4676963 : Nat := 4983230072969 + 3 ^ 40 * 4676963 * 2
def baseEnd_4676963 : Nat := 2401530022294090094453545

theorem tailTrace_4676963 : CollatzResearch.WordTrace tailWord_4676963 prefixEnd_4676963 2401530022294090094453545 := by
  unfold tailWord_4676963
  simp only [CollatzResearch.WordTrace]
  refine ⟨170582854555169287532843543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113721903036779525021895695 170582854555169287532843543)
  ·
    refine ⟨255874281832753931299265315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170582854555169287532843543 255874281832753931299265315)
    ·
      refine ⟨383811422749130896948897973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255874281832753931299265315 383811422749130896948897973)
      ·
        refine ⟨35982320882731021588959185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 383811422749130896948897973 35982320882731021588959185)
        ·
          refine ⟨26986740662048266191719389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35982320882731021588959185 26986740662048266191719389)
          ·
            refine ⟨10120027748268099821894771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26986740662048266191719389 10120027748268099821894771)
            ·
              refine ⟨15180041622402149732842157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10120027748268099821894771 15180041622402149732842157)
              ·
                refine ⟨5692515608400806149815809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15180041622402149732842157 5692515608400806149815809)
                ·
                  refine ⟨4269386706300604612361857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5692515608400806149815809 4269386706300604612361857)
                  ·
                    refine ⟨3202040029725453459271393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4269386706300604612361857 3202040029725453459271393)
                    ·
                      refine ⟨2401530022294090094453545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3202040029725453459271393 2401530022294090094453545)
                      ·
                        rfl

theorem cell23_4676963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_4676963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676963 prefixEnd_4676963 := by exact prefixLift 4676963
  have htrace : WordTrace (prefixWord ++ tailWord_4676963) baseStart_4676963 baseEnd_4676963 := by
    simpa [prefixWord, tailWord_4676963, baseEnd_4676963] using wordTrace_append hprefix tailTrace_4676963
  have hstable : (prefixWord ++ tailWord_4676963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676963).length < 2 ^ (prefixWord ++ tailWord_4676963).sum := by decide
  have hdescent : baseEnd_4676963 < baseStart_4676963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4676999 : List Nat := [1, 1, 4, 2, 2, 2, 2, 2, 2, 5]
def baseStart_4676999 : Nat := 118140960795 + 4676999 * 2 ^ 59
def prefixEnd_4676999 : Nat := 4983230072969 + 3 ^ 40 * 4676999 * 2
def baseEnd_4676999 : Nat := 800516169199217317867793

theorem tailTrace_4676999 : CollatzResearch.WordTrace tailWord_4676999 prefixEnd_4676999 800516169199217317867793 := by
  unfold tailWord_4676999
  simp only [CollatzResearch.WordTrace]
  refine ⟨170584167583038865681154051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113722778388692577120769367 170584167583038865681154051)
  ·
    refine ⟨255876251374558298521731077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170584167583038865681154051 255876251374558298521731077)
    ·
      refine ⟨47976797132729680972824577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 255876251374558298521731077 47976797132729680972824577)
      ·
        refine ⟨35982597849547260729618433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47976797132729680972824577 35982597849547260729618433)
        ·
          refine ⟨26986948387160445547213825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35982597849547260729618433 26986948387160445547213825)
          ·
            refine ⟨20240211290370334160410369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26986948387160445547213825 20240211290370334160410369)
            ·
              refine ⟨15180158467777750620307777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20240211290370334160410369 15180158467777750620307777)
              ·
                refine ⟨11385118850833312965230833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15180158467777750620307777 11385118850833312965230833)
                ·
                  refine ⟨8538839138124984723923125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11385118850833312965230833 8538839138124984723923125)
                  ·
                    refine ⟨800516169199217317867793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8538839138124984723923125 800516169199217317867793)
                    ·
                      rfl

theorem cell23_4676999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_4676999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4676999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4676999 prefixEnd_4676999 := by exact prefixLift 4676999
  have htrace : WordTrace (prefixWord ++ tailWord_4676999) baseStart_4676999 baseEnd_4676999 := by
    simpa [prefixWord, tailWord_4676999, baseEnd_4676999] using wordTrace_append hprefix tailTrace_4676999
  have hstable : (prefixWord ++ tailWord_4676999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4676999).length < 2 ^ (prefixWord ++ tailWord_4676999).sum := by decide
  have hdescent : baseEnd_4676999 < baseStart_4676999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4676999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677019 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 8, 4, 2]
def baseStart_4677019 : Nat := 118140960795 + 4677019 * 2 ^ 59
def prefixEnd_4677019 : Nat := 4983230072969 + 3 ^ 40 * 4677019 * 2
def baseEnd_4677019 : Nat := 2401558777210741875353287

theorem tailTrace_4677019 : CollatzResearch.WordTrace tailWord_4677019 prefixEnd_4677019 2401558777210741875353287 := by
  unfold tailWord_4677019
  simp only [CollatzResearch.WordTrace]
  refine ⟨170584897042966409096882111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113723264695310939397921407 170584897042966409096882111)
  ·
    refine ⟨255877345564449613645323167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170584897042966409096882111 255877345564449613645323167)
    ·
      refine ⟨383816018346674420467984751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255877345564449613645323167 383816018346674420467984751)
      ·
        refine ⟨575724027520011630701977127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383816018346674420467984751 575724027520011630701977127)
        ·
          refine ⟨863586041280017446052965691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 575724027520011630701977127 863586041280017446052965691)
          ·
            refine ⟨1295379061920026169079448537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 863586041280017446052965691 1295379061920026169079448537)
            ·
              refine ⟨971534296440019626809586403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1295379061920026169079448537 971534296440019626809586403)
              ·
                refine ⟨1457301444660029440214379605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 971534296440019626809586403 1457301444660029440214379605)
                ·
                  refine ⟨17077751304609720002512261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1457301444660029440214379605 17077751304609720002512261)
                  ·
                    refine ⟨3202078369614322500471049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17077751304609720002512261 3202078369614322500471049)
                    ·
                      refine ⟨2401558777210741875353287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3202078369614322500471049 2401558777210741875353287)
                      ·
                        rfl

theorem cell23_4677019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 4, 2].length) (baseStart_4677019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677019 prefixEnd_4677019 := by exact prefixLift 4677019
  have htrace : WordTrace (prefixWord ++ tailWord_4677019) baseStart_4677019 baseEnd_4677019 := by
    simpa [prefixWord, tailWord_4677019, baseEnd_4677019] using wordTrace_append hprefix tailTrace_4677019
  have hstable : (prefixWord ++ tailWord_4677019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677019).length < 2 ^ (prefixWord ++ tailWord_4677019).sum := by decide
  have hdescent : baseEnd_4677019 < baseStart_4677019 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677059 : List Nat := [1, 1, 1, 3, 1, 1, 7, 2, 6]
def baseStart_4677059 : Nat := 118140960795 + 4677059 * 2 ^ 59
def prefixEnd_4677059 : Nat := 4983230072969 + 3 ^ 40 * 4677059 * 2
def baseEnd_4677059 : Nat := 266842146270769079872567

theorem tailTrace_4677059 : CollatzResearch.WordTrace tailWord_4677059 prefixEnd_4677059 266842146270769079872567 := by
  unfold tailWord_4677059
  simp only [CollatzResearch.WordTrace]
  refine ⟨170586355962821495928338231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113724237308547663952225487 170586355962821495928338231)
  ·
    refine ⟨255879533944232243892507347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170586355962821495928338231 255879533944232243892507347)
    ·
      refine ⟨383819300916348365838761021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255879533944232243892507347 383819300916348365838761021)
      ·
        refine ⟨143932237843630637189535383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 383819300916348365838761021 143932237843630637189535383)
        ·
          refine ⟨215898356765445955784303075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143932237843630637189535383 215898356765445955784303075)
          ·
            refine ⟨323847535148168933676454613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215898356765445955784303075 323847535148168933676454613)
            ·
              refine ⟨7590176605035209383041905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 323847535148168933676454613 7590176605035209383041905)
              ·
                refine ⟨5692632453776407037281429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7590176605035209383041905 5692632453776407037281429)
                ·
                  refine ⟨266842146270769079872567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5692632453776407037281429 266842146270769079872567)
                  ·
                    rfl

theorem cell23_4677059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 6].length) (baseStart_4677059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677059 prefixEnd_4677059 := by exact prefixLift 4677059
  have htrace : WordTrace (prefixWord ++ tailWord_4677059) baseStart_4677059 baseEnd_4677059 := by
    simpa [prefixWord, tailWord_4677059, baseEnd_4677059] using wordTrace_append hprefix tailTrace_4677059
  have hstable : (prefixWord ++ tailWord_4677059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677059).length < 2 ^ (prefixWord ++ tailWord_4677059).sum := by decide
  have hdescent : baseEnd_4677059 < baseStart_4677059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677096 : List Nat := [2, 1, 4, 1, 1, 2, 1, 3, 1, 5, 2]
def baseStart_4677096 : Nat := 118140960795 + 4677096 * 2 ^ 59
def prefixEnd_4677096 : Nat := 4983230072969 + 3 ^ 40 * 4677096 * 2
def baseEnd_4677096 : Nat := 2401598315221138074090433

theorem tailTrace_4677096 : CollatzResearch.WordTrace tailWord_4677096 prefixEnd_4677096 2401598315221138074090433 := by
  unfold tailWord_4677096
  simp only [CollatzResearch.WordTrace]
  refine ⟨85293852731843725623717571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113725136975791634164956761 85293852731843725623717571)
  ·
    refine ⟨127940779097765588435576357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85293852731843725623717571 127940779097765588435576357)
    ·
      refine ⟨23988896080831047831670567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127940779097765588435576357 23988896080831047831670567)
      ·
        refine ⟨35983344121246571747505851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23988896080831047831670567 35983344121246571747505851)
        ·
          refine ⟨53975016181869857621258777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35983344121246571747505851 53975016181869857621258777)
          ·
            refine ⟨40481262136402393215944083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53975016181869857621258777 40481262136402393215944083)
            ·
              refine ⟨60721893204603589823916125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40481262136402393215944083 60721893204603589823916125)
              ·
                refine ⟨22770709951726346183968547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60721893204603589823916125 22770709951726346183968547)
                ·
                  refine ⟨34156064927589519275952821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22770709951726346183968547 34156064927589519275952821)
                  ·
                    refine ⟨3202131086961517432120577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34156064927589519275952821 3202131086961517432120577)
                    ·
                      refine ⟨2401598315221138074090433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3202131086961517432120577 2401598315221138074090433)
                      ·
                        rfl

theorem cell23_4677096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_4677096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677096 prefixEnd_4677096 := by exact prefixLift 4677096
  have htrace : WordTrace (prefixWord ++ tailWord_4677096) baseStart_4677096 baseEnd_4677096 := by
    simpa [prefixWord, tailWord_4677096, baseEnd_4677096] using wordTrace_append hprefix tailTrace_4677096
  have hstable : (prefixWord ++ tailWord_4677096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677096).length < 2 ^ (prefixWord ++ tailWord_4677096).sum := by decide
  have hdescent : baseEnd_4677096 < baseStart_4677096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677129 : List Nat := [1, 2, 1, 1, 3, 1, 3, 4, 1, 1, 5]
def baseStart_4677129 : Nat := 118140960795 + 4677129 * 2 ^ 59
def prefixEnd_4677129 : Nat := 4983230072969 + 3 ^ 40 * 4677129 * 2
def baseEnd_4677129 : Nat := 2401615260082736444977781

theorem tailTrace_4677129 : CollatzResearch.WordTrace tailWord_4677129 prefixEnd_4677129 2401615260082736444977781 := by
  unfold tailWord_4677129
  simp only [CollatzResearch.WordTrace]
  refine ⟨170588909072567897883386441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113725939381711931922257627 170588909072567897883386441)
  ·
    refine ⟨127941681804425923412539831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170588909072567897883386441 127941681804425923412539831)
    ·
      refine ⟨191912522706638885118809747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127941681804425923412539831 191912522706638885118809747)
      ·
        refine ⟨287868784059958327678214621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191912522706638885118809747 287868784059958327678214621)
        ·
          refine ⟨107950794022484372879330483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 287868784059958327678214621 107950794022484372879330483)
          ·
            refine ⟨161926191033726559318995725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107950794022484372879330483 161926191033726559318995725)
            ·
              refine ⟨60722321637647459744623397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161926191033726559318995725 60722321637647459744623397)
              ·
                refine ⟨11385435307058898702116887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60722321637647459744623397 11385435307058898702116887)
                ·
                  refine ⟨17078152960588348053175331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11385435307058898702116887 17078152960588348053175331)
                  ·
                    refine ⟨25617229440882522079762997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17078152960588348053175331 25617229440882522079762997)
                    ·
                      refine ⟨2401615260082736444977781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25617229440882522079762997 2401615260082736444977781)
                      ·
                        rfl

theorem cell23_4677129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 1, 5].length) (baseStart_4677129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677129 prefixEnd_4677129 := by exact prefixLift 4677129
  have htrace : WordTrace (prefixWord ++ tailWord_4677129) baseStart_4677129 baseEnd_4677129 := by
    simpa [prefixWord, tailWord_4677129, baseEnd_4677129] using wordTrace_append hprefix tailTrace_4677129
  have hstable : (prefixWord ++ tailWord_4677129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677129).length < 2 ^ (prefixWord ++ tailWord_4677129).sum := by decide
  have hdescent : baseEnd_4677129 < baseStart_4677129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677139 : List Nat := [1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 6]
def baseStart_4677139 : Nat := 118140960795 + 4677139 * 2 ^ 59
def prefixEnd_4677139 : Nat := 4983230072969 + 3 ^ 40 * 4677139 * 2
def baseEnd_4677139 : Nat := 2401620394889281405852735

theorem tailTrace_4677139 : CollatzResearch.WordTrace tailWord_4677139 prefixEnd_4677139 2401620394889281405852735 := by
  unfold tailWord_4677139
  simp only [CollatzResearch.WordTrace]
  refine ⟨170589273802531669591250471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113726182535021113060833647 170589273802531669591250471)
  ·
    refine ⟨255883910703797504386875707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170589273802531669591250471 255883910703797504386875707)
    ·
      refine ⟨383825866055696256580313561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255883910703797504386875707 383825866055696256580313561)
      ·
        refine ⟨287869399541772192435235171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 383825866055696256580313561 287869399541772192435235171)
        ·
          refine ⟨431804099312658288652852757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287869399541772192435235171 431804099312658288652852757)
          ·
            refine ⟨20240817155280857280602473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 431804099312658288652852757 20240817155280857280602473)
            ·
              refine ⟨15180612866460642960451855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20240817155280857280602473 15180612866460642960451855)
              ·
                refine ⟨22770919299690964440677783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15180612866460642960451855 22770919299690964440677783)
                ·
                  refine ⟨34156378949536446661016675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22770919299690964440677783 34156378949536446661016675)
                  ·
                    refine ⟨51234568424304669991525013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34156378949536446661016675 51234568424304669991525013)
                    ·
                      refine ⟨2401620394889281405852735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51234568424304669991525013 2401620394889281405852735)
                      ·
                        rfl

theorem cell23_4677139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 6].length) (baseStart_4677139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677139 prefixEnd_4677139 := by exact prefixLift 4677139
  have htrace : WordTrace (prefixWord ++ tailWord_4677139) baseStart_4677139 baseEnd_4677139 := by
    simpa [prefixWord, tailWord_4677139, baseEnd_4677139] using wordTrace_append hprefix tailTrace_4677139
  have hstable : (prefixWord ++ tailWord_4677139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677139).length < 2 ^ (prefixWord ++ tailWord_4677139).sum := by decide
  have hdescent : baseEnd_4677139 < baseStart_4677139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677149 : List Nat := [1, 4, 2, 2, 1, 1, 1, 11]
def baseStart_4677149 : Nat := 118140960795 + 4677149 * 2 ^ 59
def prefixEnd_4677149 : Nat := 4983230072969 + 3 ^ 40 * 4677149 * 2
def baseEnd_4677149 : Nat := 88949093692438013582507

theorem tailTrace_4677149 : CollatzResearch.WordTrace tailWord_4677149 prefixEnd_4677149 88949093692438013582507 := by
  unfold tailWord_4677149
  simp only [CollatzResearch.WordTrace]
  refine ⟨170589638532495441299114501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113726425688330294199409667 170589638532495441299114501)
  ·
    refine ⟨31985557224842895243583969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170589638532495441299114501 31985557224842895243583969)
    ·
      refine ⟨23989167918632171432687977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31985557224842895243583969 23989167918632171432687977)
      ·
        refine ⟨17991875938974128574515983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23989167918632171432687977 17991875938974128574515983)
        ·
          refine ⟨26987813908461192861773975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17991875938974128574515983 26987813908461192861773975)
          ·
            refine ⟨40481720862691789292660963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26987813908461192861773975 40481720862691789292660963)
            ·
              refine ⟨60722581294037683938991445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40481720862691789292660963 60722581294037683938991445)
              ·
                refine ⟨88949093692438013582507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 60722581294037683938991445 88949093692438013582507)
                ·
                  rfl

theorem cell23_4677149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 11].length) (baseStart_4677149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677149 prefixEnd_4677149 := by exact prefixLift 4677149
  have htrace : WordTrace (prefixWord ++ tailWord_4677149) baseStart_4677149 baseEnd_4677149 := by
    simpa [prefixWord, tailWord_4677149, baseEnd_4677149] using wordTrace_append hprefix tailTrace_4677149
  have hstable : (prefixWord ++ tailWord_4677149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677149).length < 2 ^ (prefixWord ++ tailWord_4677149).sum := by decide
  have hdescent : baseEnd_4677149 < baseStart_4677149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677177 : List Nat := [1, 2, 1, 5, 1, 3, 1, 4, 1, 2, 2]
def baseStart_4677177 : Nat := 118140960795 + 4677177 * 2 ^ 59
def prefixEnd_4677177 : Nat := 4983230072969 + 3 ^ 40 * 4677177 * 2
def baseEnd_4677177 : Nat := 2401639907154152257177561

theorem tailTrace_4677177 : CollatzResearch.WordTrace tailWord_4677177 prefixEnd_4677177 2401639907154152257177561 := by
  unfold tailWord_4677177
  simp only [CollatzResearch.WordTrace]
  refine ⟨170590659776394002081133785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113727106517596001387422523 170590659776394002081133785)
  ·
    refine ⟨127942994832295501560850339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170590659776394002081133785 127942994832295501560850339)
    ·
      refine ⟨191914492248443252341275509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127942994832295501560850339 191914492248443252341275509)
      ·
        refine ⟨17991983648291554906994579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 191914492248443252341275509 17991983648291554906994579)
        ·
          refine ⟨26987975472437332360491869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17991983648291554906994579 26987975472437332360491869)
          ·
            refine ⟨10120490802163999635184451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26987975472437332360491869 10120490802163999635184451)
            ·
              refine ⟨15180736203245999452776677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10120490802163999635184451 15180736203245999452776677)
              ·
                refine ⟨2846388038108624897395627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15180736203245999452776677 2846388038108624897395627)
                ·
                  refine ⟨4269582057162937346093441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2846388038108624897395627 4269582057162937346093441)
                  ·
                    refine ⟨3202186542872203009570081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4269582057162937346093441 3202186542872203009570081)
                    ·
                      refine ⟨2401639907154152257177561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3202186542872203009570081 2401639907154152257177561)
                      ·
                        rfl

theorem cell23_4677177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_4677177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677177 prefixEnd_4677177 := by exact prefixLift 4677177
  have htrace : WordTrace (prefixWord ++ tailWord_4677177) baseStart_4677177 baseEnd_4677177 := by
    simpa [prefixWord, tailWord_4677177, baseEnd_4677177] using wordTrace_append hprefix tailTrace_4677177
  have hstable : (prefixWord ++ tailWord_4677177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677177).length < 2 ^ (prefixWord ++ tailWord_4677177).sum := by decide
  have hdescent : baseEnd_4677177 < baseStart_4677177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677199 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 4]
def baseStart_4677199 : Nat := 118140960795 + 4677199 * 2 ^ 59
def prefixEnd_4677199 : Nat := 4983230072969 + 3 ^ 40 * 4677199 * 2
def baseEnd_4677199 : Nat := 2401651203728551171102459

theorem tailTrace_4677199 : CollatzResearch.WordTrace tailWord_4677199 prefixEnd_4677199 2401651203728551171102459 := by
  unfold tailWord_4677199
  simp only [CollatzResearch.WordTrace]
  refine ⟨170591462182314299838434651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113727641454876199892289767 170591462182314299838434651)
  ·
    refine ⟨255887193273471449757651977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170591462182314299838434651 255887193273471449757651977)
    ·
      refine ⟨191915394955103587318238983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255887193273471449757651977 191915394955103587318238983)
      ·
        refine ⟨287873092432655380977358475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191915394955103587318238983 287873092432655380977358475)
        ·
          refine ⟨431809638648983071466037713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287873092432655380977358475 431809638648983071466037713)
          ·
            refine ⟨323857228986737303599528285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 431809638648983071466037713 323857228986737303599528285)
            ·
              refine ⟨121446460870026488849823107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 323857228986737303599528285 121446460870026488849823107)
              ·
                refine ⟨182169691305039733274734661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121446460870026488849823107 182169691305039733274734661)
                ·
                  refine ⟨34156817119694949989012749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 182169691305039733274734661 34156817119694949989012749)
                  ·
                    refine ⟨12808806419885606245879781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34156817119694949989012749 12808806419885606245879781)
                    ·
                      refine ⟨2401651203728551171102459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12808806419885606245879781 2401651203728551171102459)
                      ·
                        rfl

theorem cell23_4677199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 4].length) (baseStart_4677199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677199 prefixEnd_4677199 := by exact prefixLift 4677199
  have htrace : WordTrace (prefixWord ++ tailWord_4677199) baseStart_4677199 baseEnd_4677199 := by
    simpa [prefixWord, tailWord_4677199, baseEnd_4677199] using wordTrace_append hprefix tailTrace_4677199
  have hstable : (prefixWord ++ tailWord_4677199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677199).length < 2 ^ (prefixWord ++ tailWord_4677199).sum := by decide
  have hdescent : baseEnd_4677199 < baseStart_4677199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677220 : List Nat := [2, 3, 1, 1, 2, 4, 1, 3, 1, 3, 2]
def baseStart_4677220 : Nat := 118140960795 + 4677220 * 2 ^ 59
def prefixEnd_4677220 : Nat := 4983230072969 + 3 ^ 40 * 4677220 * 2
def baseEnd_4677220 : Nat := 2401661986822295588939863

theorem tailTrace_4677220 : CollatzResearch.WordTrace tailWord_4677220 prefixEnd_4677220 2401661986822295588939863 := by
  unfold tailWord_4677220
  simp only [CollatzResearch.WordTrace]
  refine ⟨85296114057619110212474557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113728152076825480283299409 85296114057619110212474557)
  ·
    refine ⟨31986042771607166329677959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85296114057619110212474557 31986042771607166329677959)
    ·
      refine ⟨47979064157410749494516939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31986042771607166329677959 47979064157410749494516939)
      ·
        refine ⟨71968596236116124241775409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47979064157410749494516939 71968596236116124241775409)
        ·
          refine ⟨53976447177087093181331557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71968596236116124241775409 53976447177087093181331557)
          ·
            refine ⟨10120583845703829971499667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53976447177087093181331557 10120583845703829971499667)
            ·
              refine ⟨15180875768555744957249501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10120583845703829971499667 15180875768555744957249501)
              ·
                refine ⟨5692828413208404358968563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15180875768555744957249501 5692828413208404358968563)
                ·
                  refine ⟨8539242619812606538452845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5692828413208404358968563 8539242619812606538452845)
                  ·
                    refine ⟨3202215982429727451919817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8539242619812606538452845 3202215982429727451919817)
                    ·
                      refine ⟨2401661986822295588939863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3202215982429727451919817 2401661986822295588939863)
                      ·
                        rfl

theorem cell23_4677220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 1, 3, 2].length) (baseStart_4677220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677220 prefixEnd_4677220 := by exact prefixLift 4677220
  have htrace : WordTrace (prefixWord ++ tailWord_4677220) baseStart_4677220 baseEnd_4677220 := by
    simpa [prefixWord, tailWord_4677220, baseEnd_4677220] using wordTrace_append hprefix tailTrace_4677220
  have hstable : (prefixWord ++ tailWord_4677220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677220).length < 2 ^ (prefixWord ++ tailWord_4677220).sum := by decide
  have hdescent : baseEnd_4677220 < baseStart_4677220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677226 : List Nat := [3, 1, 3, 2, 1, 2, 1, 2, 2, 6]
def baseStart_4677226 : Nat := 118140960795 + 4677226 * 2 ^ 59
def prefixEnd_4677226 : Nat := 4983230072969 + 3 ^ 40 * 4677226 * 2
def baseEnd_4677226 : Nat := 800555022568740855154945

theorem tailTrace_4677226 : CollatzResearch.WordTrace tailWord_4677226 prefixEnd_4677226 800555022568740855154945 := by
  unfold tailWord_4677226
  simp only [CollatzResearch.WordTrace]
  refine ⟨42648111738304120862416883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113728297968810988966445021 42648111738304120862416883)
  ·
    refine ⟨63972167607456181293625325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42648111738304120862416883 63972167607456181293625325)
    ·
      refine ⟨23989562852796067985109497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63972167607456181293625325 23989562852796067985109497)
      ·
        refine ⟨17992172139597050988832123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23989562852796067985109497 17992172139597050988832123)
        ·
          refine ⟨26988258209395576483248185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17992172139597050988832123 26988258209395576483248185)
          ·
            refine ⟨20241193657046682362436139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26988258209395576483248185 20241193657046682362436139)
            ·
              refine ⟨30361790485570023543654209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20241193657046682362436139 30361790485570023543654209)
              ·
                refine ⟨22771342864177517657740657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30361790485570023543654209 22771342864177517657740657)
                ·
                  refine ⟨17078507148133138243305493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22771342864177517657740657 17078507148133138243305493)
                  ·
                    refine ⟨800555022568740855154945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17078507148133138243305493 800555022568740855154945)
                    ·
                      rfl

theorem cell23_4677226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_4677226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677226 prefixEnd_4677226 := by exact prefixLift 4677226
  have htrace : WordTrace (prefixWord ++ tailWord_4677226) baseStart_4677226 baseEnd_4677226 := by
    simpa [prefixWord, tailWord_4677226, baseEnd_4677226] using wordTrace_append hprefix tailTrace_4677226
  have hstable : (prefixWord ++ tailWord_4677226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677226).length < 2 ^ (prefixWord ++ tailWord_4677226).sum := by decide
  have hdescent : baseEnd_4677226 < baseStart_4677226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677301 : List Nat := [1, 3, 3, 3, 2, 2, 2, 1, 2, 2, 2]
def baseStart_4677301 : Nat := 118140960795 + 4677301 * 2 ^ 59
def prefixEnd_4677301 : Nat := 4983230072969 + 3 ^ 40 * 4677301 * 2
def baseEnd_4677301 : Nat := 2401703578755309772026991

theorem tailTrace_4677301 : CollatzResearch.WordTrace tailWord_4677301 prefixEnd_4677301 2401703578755309772026991 := by
  unfold tailWord_4677301
  simp only [CollatzResearch.WordTrace]
  refine ⟨170595182427944771258647757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113730121618629847505765171 170595182427944771258647757)
  ·
    refine ⟨63973193410479289221992909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170595182427944771258647757 63973193410479289221992909)
    ·
      refine ⟨23989947528929733458247341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63973193410479289221992909 23989947528929733458247341)
      ·
        refine ⟨8996230323348650046842753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23989947528929733458247341 8996230323348650046842753)
        ·
          refine ⟨6747172742511487535132065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8996230323348650046842753 6747172742511487535132065)
          ·
            refine ⟨5060379556883615651349049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6747172742511487535132065 5060379556883615651349049)
            ·
              refine ⟨3795284667662711738511787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5060379556883615651349049 3795284667662711738511787)
              ·
                refine ⟨5692927001494067607767681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3795284667662711738511787 5692927001494067607767681)
                ·
                  refine ⟨4269695251120550705825761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5692927001494067607767681 4269695251120550705825761)
                  ·
                    refine ⟨3202271438340413029369321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4269695251120550705825761 3202271438340413029369321)
                    ·
                      refine ⟨2401703578755309772026991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3202271438340413029369321 2401703578755309772026991)
                      ·
                        rfl

theorem cell23_4677301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_4677301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677301 prefixEnd_4677301 := by exact prefixLift 4677301
  have htrace : WordTrace (prefixWord ++ tailWord_4677301) baseStart_4677301 baseEnd_4677301 := by
    simpa [prefixWord, tailWord_4677301, baseEnd_4677301] using wordTrace_append hprefix tailTrace_4677301
  have hstable : (prefixWord ++ tailWord_4677301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677301).length < 2 ^ (prefixWord ++ tailWord_4677301).sum := by decide
  have hdescent : baseEnd_4677301 < baseStart_4677301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677336 : List Nat := [2, 1, 2, 2, 3, 1, 2, 1, 2, 1, 6]
def baseStart_4677336 : Nat := 118140960795 + 4677336 * 2 ^ 59
def prefixEnd_4677336 : Nat := 4983230072969 + 3 ^ 40 * 4677336 * 2
def baseEnd_4677336 : Nat := 2401721550578217135089329

theorem tailTrace_4677336 : CollatzResearch.WordTrace tailWord_4677336 prefixEnd_4677336 2401721550578217135089329 := by
  unfold tailWord_4677336
  simp only [CollatzResearch.WordTrace]
  refine ⟨85298229491408986118085931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113730972655211981490781241 85298229491408986118085931)
  ·
    refine ⟨127947344237113479177128897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85298229491408986118085931 127947344237113479177128897)
    ·
      refine ⟨95960508177835109382846673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127947344237113479177128897 95960508177835109382846673)
      ·
        refine ⟨71970381133376332037135005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95960508177835109382846673 71970381133376332037135005)
        ·
          refine ⟨26988892925016124513925627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71970381133376332037135005 26988892925016124513925627)
          ·
            refine ⟨40483339387524186770888441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26988892925016124513925627 40483339387524186770888441)
            ·
              refine ⟨30362504540643140078166331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40483339387524186770888441 30362504540643140078166331)
              ·
                refine ⟨45543756810964710117249497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30362504540643140078166331 45543756810964710117249497)
                ·
                  refine ⟨34157817608223532587937123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45543756810964710117249497 34157817608223532587937123)
                  ·
                    refine ⟨51236726412335298881905685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34157817608223532587937123 51236726412335298881905685)
                    ·
                      refine ⟨2401721550578217135089329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51236726412335298881905685 2401721550578217135089329)
                      ·
                        rfl

theorem cell23_4677336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_4677336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677336 prefixEnd_4677336 := by exact prefixLift 4677336
  have htrace : WordTrace (prefixWord ++ tailWord_4677336) baseStart_4677336 baseEnd_4677336 := by
    simpa [prefixWord, tailWord_4677336, baseEnd_4677336] using wordTrace_append hprefix tailTrace_4677336
  have hstable : (prefixWord ++ tailWord_4677336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677336).length < 2 ^ (prefixWord ++ tailWord_4677336).sum := by decide
  have hdescent : baseEnd_4677336 < baseStart_4677336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677341 : List Nat := [1, 4, 3, 3, 2, 1, 2, 2, 5]
def baseStart_4677341 : Nat := 118140960795 + 4677341 * 2 ^ 59
def prefixEnd_4677341 : Nat := 4983230072969 + 3 ^ 40 * 4677341 * 2
def baseEnd_4677341 : Nat := 266858235331276623947423

theorem tailTrace_4677341 : CollatzResearch.WordTrace tailWord_4677341 prefixEnd_4677341 266858235331276623947423 := by
  unfold tailWord_4677341
  simp only [CollatzResearch.WordTrace]
  refine ⟨170596641347799858090103877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113731094231866572060069251 170596641347799858090103877)
  ·
    refine ⟨31986870252712473391894477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 170596641347799858090103877 31986870252712473391894477)
    ·
      refine ⟨11995076344767177521960429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31986870252712473391894477 11995076344767177521960429)
      ·
        refine ⟨4498153629287691570735161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11995076344767177521960429 4498153629287691570735161)
        ·
          refine ⟨3373615221965768678051371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4498153629287691570735161 3373615221965768678051371)
          ·
            refine ⟨5060422832948653017077057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3373615221965768678051371 5060422832948653017077057)
            ·
              refine ⟨3795317124711489762807793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5060422832948653017077057 3795317124711489762807793)
              ·
                refine ⟨2846487843533617322105845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3795317124711489762807793 2846487843533617322105845)
                ·
                  refine ⟨266858235331276623947423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2846487843533617322105845 266858235331276623947423)
                  ·
                    rfl

theorem cell23_4677341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 2, 5].length) (baseStart_4677341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677341 prefixEnd_4677341 := by exact prefixLift 4677341
  have htrace : WordTrace (prefixWord ++ tailWord_4677341) baseStart_4677341 baseEnd_4677341 := by
    simpa [prefixWord, tailWord_4677341, baseEnd_4677341] using wordTrace_append hprefix tailTrace_4677341
  have hstable : (prefixWord ++ tailWord_4677341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677341).length < 2 ^ (prefixWord ++ tailWord_4677341).sum := by decide
  have hdescent : baseEnd_4677341 < baseStart_4677341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677343 : List Nat := [1, 1, 2, 3, 2, 2, 1, 4, 2, 2, 3]
def baseStart_4677343 : Nat := 118140960795 + 4677343 * 2 ^ 59
def prefixEnd_4677343 : Nat := 4983230072969 + 3 ^ 40 * 4677343 * 2
def baseEnd_4677343 : Nat := 2401725144942798607701797

theorem tailTrace_4677343 : CollatzResearch.WordTrace tailWord_4677343 prefixEnd_4677343 2401725144942798607701797 := by
  unfold tailWord_4677343
  simp only [CollatzResearch.WordTrace]
  refine ⟨170596714293792612431676683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113731142862528408287784455 170596714293792612431676683)
  ·
    refine ⟨255895071440688918647515025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170596714293792612431676683 255895071440688918647515025)
    ·
      refine ⟨191921303580516688985636269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255895071440688918647515025 191921303580516688985636269)
      ·
        refine ⟨71970488842693758369613601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191921303580516688985636269 71970488842693758369613601)
        ·
          refine ⟨53977866632020318777210201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71970488842693758369613601 53977866632020318777210201)
          ·
            refine ⟨40483399974015239082907651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53977866632020318777210201 40483399974015239082907651)
            ·
              refine ⟨60725099961022858624361477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40483399974015239082907651 60725099961022858624361477)
              ·
                refine ⟨11385956242691785992067777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60725099961022858624361477 11385956242691785992067777)
                ·
                  refine ⟨8539467182018839494050833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11385956242691785992067777 8539467182018839494050833)
                  ·
                    refine ⟨6404600386514129620538125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8539467182018839494050833 6404600386514129620538125)
                    ·
                      refine ⟨2401725144942798607701797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6404600386514129620538125 2401725144942798607701797)
                      ·
                        rfl

theorem cell23_4677343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_4677343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677343 prefixEnd_4677343 := by exact prefixLift 4677343
  have htrace : WordTrace (prefixWord ++ tailWord_4677343) baseStart_4677343 baseEnd_4677343 := by
    simpa [prefixWord, tailWord_4677343, baseEnd_4677343] using wordTrace_append hprefix tailTrace_4677343
  have hstable : (prefixWord ++ tailWord_4677343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677343).length < 2 ^ (prefixWord ++ tailWord_4677343).sum := by decide
  have hdescent : baseEnd_4677343 < baseStart_4677343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677374 : List Nat := [4, 2, 2, 1, 4, 1, 1, 1, 2, 1, 4]
def baseStart_4677374 : Nat := 118140960795 + 4677374 * 2 ^ 59
def prefixEnd_4677374 : Nat := 4983230072969 + 3 ^ 40 * 4677374 * 2
def baseEnd_4677374 : Nat := 2401741062843087986414155

theorem tailTrace_4677374 : CollatzResearch.WordTrace tailWord_4677374 prefixEnd_4677374 2401741062843087986414155 := by
  unfold tailWord_4677374
  simp only [CollatzResearch.WordTrace]
  refine ⟨21324730619585038090756897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 113731896637786869817370117 21324730619585038090756897)
  ·
    refine ⟨15993547964688778568067673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21324730619585038090756897 15993547964688778568067673)
    ·
      refine ⟨11995160973516583926050755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15993547964688778568067673 11995160973516583926050755)
      ·
        refine ⟨17992741460274875889076133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11995160973516583926050755 17992741460274875889076133)
        ·
          refine ⟨3373639023801539229201775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17992741460274875889076133 3373639023801539229201775)
          ·
            refine ⟨5060458535702308843802663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3373639023801539229201775 5060458535702308843802663)
            ·
              refine ⟨7590687803553463265703995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5060458535702308843802663 7590687803553463265703995)
              ·
                refine ⟨11386031705330194898555993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7590687803553463265703995 11386031705330194898555993)
                ·
                  refine ⟨8539523778997646173916995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11386031705330194898555993 8539523778997646173916995)
                  ·
                    refine ⟨12809285668496469260875493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8539523778997646173916995 12809285668496469260875493)
                    ·
                      refine ⟨2401741062843087986414155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12809285668496469260875493 2401741062843087986414155)
                      ·
                        rfl

theorem cell23_4677374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_4677374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677374 prefixEnd_4677374 := by exact prefixLift 4677374
  have htrace : WordTrace (prefixWord ++ tailWord_4677374) baseStart_4677374 baseEnd_4677374 := by
    simpa [prefixWord, tailWord_4677374, baseEnd_4677374] using wordTrace_append hprefix tailTrace_4677374
  have hstable : (prefixWord ++ tailWord_4677374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677374).length < 2 ^ (prefixWord ++ tailWord_4677374).sum := by decide
  have hdescent : baseEnd_4677374 < baseStart_4677374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677400 : List Nat := [2, 1, 2, 3, 1, 1, 2, 4, 2, 3, 2]
def baseStart_4677400 : Nat := 118140960795 + 4677400 * 2 ^ 59
def prefixEnd_4677400 : Nat := 4983230072969 + 3 ^ 40 * 4677400 * 2
def baseEnd_4677400 : Nat := 2401754413340104884689035

theorem tailTrace_4677400 : CollatzResearch.WordTrace tailWord_4677400 prefixEnd_4677400 2401754413340104884689035 := by
  unfold tailWord_4677400
  simp only [CollatzResearch.WordTrace]
  refine ⟨85299396627293055583250827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113732528836390740777667769 85299396627293055583250827)
  ·
    refine ⟨127949094940939583374876241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85299396627293055583250827 127949094940939583374876241)
    ·
      refine ⟨95961821205704687531157181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127949094940939583374876241 95961821205704687531157181)
      ·
        refine ⟨35985682952139257824183943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95961821205704687531157181 35985682952139257824183943)
        ·
          refine ⟨53978524428208886736275915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35985682952139257824183943 53978524428208886736275915)
          ·
            refine ⟨80967786642313330104413873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53978524428208886736275915 80967786642313330104413873)
            ·
              refine ⟨60725839981734997578310405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80967786642313330104413873 60725839981734997578310405)
              ·
                refine ⟨11386094996575312045933201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60725839981734997578310405 11386094996575312045933201)
                ·
                  refine ⟨8539571247431484034449901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11386094996575312045933201 8539571247431484034449901)
                  ·
                    refine ⟨3202339217786806512918713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8539571247431484034449901 3202339217786806512918713)
                    ·
                      refine ⟨2401754413340104884689035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3202339217786806512918713 2401754413340104884689035)
                      ·
                        rfl

theorem cell23_4677400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_4677400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677400 prefixEnd_4677400 := by exact prefixLift 4677400
  have htrace : WordTrace (prefixWord ++ tailWord_4677400) baseStart_4677400 baseEnd_4677400 := by
    simpa [prefixWord, tailWord_4677400, baseEnd_4677400] using wordTrace_append hprefix tailTrace_4677400
  have hstable : (prefixWord ++ tailWord_4677400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677400).length < 2 ^ (prefixWord ++ tailWord_4677400).sum := by decide
  have hdescent : baseEnd_4677400 < baseStart_4677400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677407 : List Nat := [1, 1, 2, 4, 2, 1, 1, 6, 1, 1, 3]
def baseStart_4677407 : Nat := 118140960795 + 4677407 * 2 ^ 59
def prefixEnd_4677407 : Nat := 4983230072969 + 3 ^ 40 * 4677407 * 2
def baseEnd_4677407 : Nat := 2401758007704686357301503

theorem tailTrace_4677407 : CollatzResearch.WordTrace tailWord_4677407 prefixEnd_4677407 2401758007704686357301503 := by
  unfold tailWord_4677407
  simp only [CollatzResearch.WordTrace]
  refine ⟨170599048565560751362006475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113732699043707167574670983 170599048565560751362006475)
  ·
    refine ⟨255898572848341127043009713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170599048565560751362006475 255898572848341127043009713)
    ·
      refine ⟨191923929636255845282257285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255898572848341127043009713 191923929636255845282257285)
      ·
        refine ⟨35985736806797970990423241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 191923929636255845282257285 35985736806797970990423241)
        ·
          refine ⟨26989302605098478242817431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35985736806797970990423241 26989302605098478242817431)
          ·
            refine ⟨40483953907647717364226147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26989302605098478242817431 40483953907647717364226147)
            ·
              refine ⟨60725930861471576046339221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40483953907647717364226147 60725930861471576046339221)
              ·
                refine ⟨2846528009131480127172151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60725930861471576046339221 2846528009131480127172151)
                ·
                  refine ⟨4269792013697220190758227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2846528009131480127172151 4269792013697220190758227)
                  ·
                    refine ⟨6404688020545830286137341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4269792013697220190758227 6404688020545830286137341)
                    ·
                      refine ⟨2401758007704686357301503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6404688020545830286137341 2401758007704686357301503)
                      ·
                        rfl

theorem cell23_4677407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_4677407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677407 prefixEnd_4677407 := by exact prefixLift 4677407
  have htrace : WordTrace (prefixWord ++ tailWord_4677407) baseStart_4677407 baseEnd_4677407 := by
    simpa [prefixWord, tailWord_4677407, baseEnd_4677407] using wordTrace_append hprefix tailTrace_4677407
  have hstable : (prefixWord ++ tailWord_4677407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677407).length < 2 ^ (prefixWord ++ tailWord_4677407).sum := by decide
  have hdescent : baseEnd_4677407 < baseStart_4677407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677450 : List Nat := [3, 1, 2, 1, 1, 1, 3, 5, 1, 2, 3]
def baseStart_4677450 : Nat := 118140960795 + 4677450 * 2 ^ 59
def prefixEnd_4677450 : Nat := 4983230072969 + 3 ^ 40 * 4677450 * 2
def baseEnd_4677450 : Nat := 2401780087372829689063805

theorem tailTrace_4677450 : CollatzResearch.WordTrace tailWord_4677450 prefixEnd_4677450 2401780087372829689063805 := by
  unfold tailWord_4677450
  simp only [CollatzResearch.WordTrace]
  refine ⟨42650154226101242426455451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113733744602936646470547869 42650154226101242426455451)
  ·
    refine ⟨63975231339151863639683177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42650154226101242426455451 63975231339151863639683177)
    ·
      refine ⟨47981423504363897729762383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63975231339151863639683177 47981423504363897729762383)
      ·
        refine ⟨71972135256545846594643575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47981423504363897729762383 71972135256545846594643575)
        ·
          refine ⟨107958202884818769891965363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71972135256545846594643575 107958202884818769891965363)
          ·
            refine ⟨161937304327228154837948045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107958202884818769891965363 161937304327228154837948045)
            ·
              refine ⟨60726489122710558064230517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161937304327228154837948045 60726489122710558064230517)
              ·
                refine ⟨5693108355254114818521611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60726489122710558064230517 5693108355254114818521611)
                ·
                  refine ⟨8539662532881172227782417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5693108355254114818521611 8539662532881172227782417)
                  ·
                    refine ⟨6404746899660879170836813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8539662532881172227782417 6404746899660879170836813)
                    ·
                      refine ⟨2401780087372829689063805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6404746899660879170836813 2401780087372829689063805)
                      ·
                        rfl

theorem cell23_4677450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 1, 2, 3].length) (baseStart_4677450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677450 prefixEnd_4677450 := by exact prefixLift 4677450
  have htrace : WordTrace (prefixWord ++ tailWord_4677450) baseStart_4677450 baseEnd_4677450 := by
    simpa [prefixWord, tailWord_4677450, baseEnd_4677450] using wordTrace_append hprefix tailTrace_4677450
  have hstable : (prefixWord ++ tailWord_4677450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677450).length < 2 ^ (prefixWord ++ tailWord_4677450).sum := by decide
  have hdescent : baseEnd_4677450 < baseStart_4677450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677474 : List Nat := [3, 3, 2, 1, 2, 1, 4, 1, 2, 4]
def baseStart_4677474 : Nat := 118140960795 + 4677474 * 2 ^ 59
def prefixEnd_4677474 : Nat := 4983230072969 + 3 ^ 40 * 4677474 * 2
def baseEnd_4677474 : Nat := 800597470302845865054565

theorem tailTrace_4677474 : CollatzResearch.WordTrace tailWord_4677474 prefixEnd_4677474 800597470302845865054565 := by
  unfold tailWord_4677474
  simp only [CollatzResearch.WordTrace]
  refine ⟨42650373064079505451173869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113734328170878681203130317 42650373064079505451173869)
  ·
    refine ⟨15993889899029814544190201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42650373064079505451173869 15993889899029814544190201)
    ·
      refine ⟨11995417424272360908142651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15993889899029814544190201 11995417424272360908142651)
      ·
        refine ⟨17993126136408541362213977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11995417424272360908142651 17993126136408541362213977)
        ·
          refine ⟨13494844602306406021660483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17993126136408541362213977 13494844602306406021660483)
          ·
            refine ⟨20242266903459609032490725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13494844602306406021660483 20242266903459609032490725)
            ·
              refine ⟨3795425044398676693592011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20242266903459609032490725 3795425044398676693592011)
              ·
                refine ⟨5693137566598015040388017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3795425044398676693592011 5693137566598015040388017)
                ·
                  refine ⟨4269853174948511280291013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5693137566598015040388017 4269853174948511280291013)
                  ·
                    refine ⟨800597470302845865054565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4269853174948511280291013 800597470302845865054565)
                    ·
                      rfl

theorem cell23_4677474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_4677474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677474 prefixEnd_4677474 := by exact prefixLift 4677474
  have htrace : WordTrace (prefixWord ++ tailWord_4677474) baseStart_4677474 baseEnd_4677474 := by
    simpa [prefixWord, tailWord_4677474, baseEnd_4677474] using wordTrace_append hprefix tailTrace_4677474
  have hstable : (prefixWord ++ tailWord_4677474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677474).length < 2 ^ (prefixWord ++ tailWord_4677474).sum := by decide
  have hdescent : baseEnd_4677474 < baseStart_4677474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677480 : List Nat := [2, 1, 4, 2, 1, 1, 2, 3, 1, 3, 3]
def baseStart_4677480 : Nat := 118140960795 + 4677480 * 2 ^ 59
def prefixEnd_4677480 : Nat := 4983230072969 + 3 ^ 40 * 4677480 * 2
def baseEnd_4677480 : Nat := 2401795491792464571688667

theorem tailTrace_4677480 : CollatzResearch.WordTrace tailWord_4677480 prefixEnd_4677480 2401795491792464571688667 := by
  unfold tailWord_4677480
  simp only [CollatzResearch.WordTrace]
  refine ⟨85300855547148142414706947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113734474062864189886275929 85300855547148142414706947)
  ·
    refine ⟨127951283320722213622060421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85300855547148142414706947 127951283320722213622060421)
    ·
      refine ⟨23990865622635415054136329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127951283320722213622060421 23990865622635415054136329)
      ·
        refine ⟨17993149216976561290602247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23990865622635415054136329 17993149216976561290602247)
        ·
          refine ⟨26989723825464841935903371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17993149216976561290602247 26989723825464841935903371)
          ·
            refine ⟨40484585738197262903855057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26989723825464841935903371 40484585738197262903855057)
            ·
              refine ⟨30363439303647947177891293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40484585738197262903855057 30363439303647947177891293)
              ·
                refine ⟨11386289738867980191709235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30363439303647947177891293 11386289738867980191709235)
                ·
                  refine ⟨17079434608301970287563853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11386289738867980191709235 17079434608301970287563853)
                  ·
                    refine ⟨6404787978113238857836445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17079434608301970287563853 6404787978113238857836445)
                    ·
                      refine ⟨2401795491792464571688667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6404787978113238857836445 2401795491792464571688667)
                      ·
                        rfl

theorem cell23_4677480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_4677480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677480 prefixEnd_4677480 := by exact prefixLift 4677480
  have htrace : WordTrace (prefixWord ++ tailWord_4677480) baseStart_4677480 baseEnd_4677480 := by
    simpa [prefixWord, tailWord_4677480, baseEnd_4677480] using wordTrace_append hprefix tailTrace_4677480
  have hstable : (prefixWord ++ tailWord_4677480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677480).length < 2 ^ (prefixWord ++ tailWord_4677480).sum := by decide
  have hdescent : baseEnd_4677480 < baseStart_4677480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677513 : List Nat := [1, 2, 1, 1, 5, 1, 2, 2, 2, 6]
def baseStart_4677513 : Nat := 118140960795 + 4677513 * 2 ^ 59
def prefixEnd_4677513 : Nat := 4983230072969 + 3 ^ 40 * 4677513 * 2
def baseEnd_4677513 : Nat := 800604145551354314192005

theorem tailTrace_4677513 : CollatzResearch.WordTrace tailWord_4677513 prefixEnd_4677513 800604145551354314192005 := by
  unfold tailWord_4677513
  simp only [CollatzResearch.WordTrace]
  refine ⟨170602914703176731465365193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113735276468784487643576795 170602914703176731465365193)
  ·
    refine ⟨127952186027382548599023895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170602914703176731465365193 127952186027382548599023895)
    ·
      refine ⟨191928279041073822898535843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127952186027382548599023895 191928279041073822898535843)
      ·
        refine ⟨287892418561610734347803765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191928279041073822898535843 287892418561610734347803765)
        ·
          refine ⟨26989914240151006345106603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 287892418561610734347803765 26989914240151006345106603)
          ·
            refine ⟨40484871360226509517659905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26989914240151006345106603 40484871360226509517659905)
            ·
              refine ⟨30363653520169882138244929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40484871360226509517659905 30363653520169882138244929)
              ·
                refine ⟨22772740140127411603683697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30363653520169882138244929 22772740140127411603683697)
                ·
                  refine ⟨17079555105095558702762773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22772740140127411603683697 17079555105095558702762773)
                  ·
                    refine ⟨800604145551354314192005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17079555105095558702762773 800604145551354314192005)
                    ·
                      rfl

theorem cell23_4677513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 6].length) (baseStart_4677513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677513 prefixEnd_4677513 := by exact prefixLift 4677513
  have htrace : WordTrace (prefixWord ++ tailWord_4677513) baseStart_4677513 baseEnd_4677513 := by
    simpa [prefixWord, tailWord_4677513, baseEnd_4677513] using wordTrace_append hprefix tailTrace_4677513
  have hstable : (prefixWord ++ tailWord_4677513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677513).length < 2 ^ (prefixWord ++ tailWord_4677513).sum := by decide
  have hdescent : baseEnd_4677513 < baseStart_4677513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677530 : List Nat := [3, 1, 1, 4, 2, 2, 1, 1, 2, 6]
def baseStart_4677530 : Nat := 118140960795 + 4677530 * 2 ^ 59
def prefixEnd_4677530 : Nat := 4983230072969 + 3 ^ 40 * 4677530 * 2
def baseEnd_4677530 : Nat := 800607055275063125354479

theorem tailTrace_4677530 : CollatzResearch.WordTrace tailWord_4677530 prefixEnd_4677530 800607055275063125354479 := by
  unfold tailWord_4677530
  simp only [CollatzResearch.WordTrace]
  refine ⟨42650883686028785842183511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113735689829410095579156029 42650883686028785842183511)
  ·
    refine ⟨63976325529043178763275267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42650883686028785842183511 63976325529043178763275267)
    ·
      refine ⟨95964488293564768144912901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63976325529043178763275267 95964488293564768144912901)
      ·
        refine ⟨17993341555043394027171169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95964488293564768144912901 17993341555043394027171169)
        ·
          refine ⟨13495006166282545520378377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17993341555043394027171169 13495006166282545520378377)
          ·
            refine ⟨10121254624711909140283783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13495006166282545520378377 10121254624711909140283783)
            ·
              refine ⟨15181881937067863710425675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10121254624711909140283783 15181881937067863710425675)
              ·
                refine ⟨22772822905601795565638513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15181881937067863710425675 22772822905601795565638513)
                ·
                  refine ⟨17079617179201346674228885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22772822905601795565638513 17079617179201346674228885)
                  ·
                    refine ⟨800607055275063125354479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17079617179201346674228885 800607055275063125354479)
                    ·
                      rfl

theorem cell23_4677530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 2, 6].length) (baseStart_4677530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677530 prefixEnd_4677530 := by exact prefixLift 4677530
  have htrace : WordTrace (prefixWord ++ tailWord_4677530) baseStart_4677530 baseEnd_4677530 := by
    simpa [prefixWord, tailWord_4677530, baseEnd_4677530] using wordTrace_append hprefix tailTrace_4677530
  have hstable : (prefixWord ++ tailWord_4677530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677530).length < 2 ^ (prefixWord ++ tailWord_4677530).sum := by decide
  have hdescent : baseEnd_4677530 < baseStart_4677530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677583 : List Nat := [1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 7]
def baseStart_4677583 : Nat := 118140960795 + 4677583 * 2 ^ 59
def prefixEnd_4677583 : Nat := 4983230072969 + 3 ^ 40 * 4677583 * 2
def baseEnd_4677583 : Nat := 2401848380299877668700693

theorem tailTrace_4677583 : CollatzResearch.WordTrace tailWord_4677583 prefixEnd_4677583 2401848380299877668700693 := by
  unfold tailWord_4677583
  simp only [CollatzResearch.WordTrace]
  refine ⟨170605467812923133420413403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113736978541948755613608935 170605467812923133420413403)
  ·
    refine ⟨255908201719384700130620105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170605467812923133420413403 255908201719384700130620105)
    ·
      refine ⟨191931151289538525097965079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255908201719384700130620105 191931151289538525097965079)
      ·
        refine ⟨287896726934307787646947619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191931151289538525097965079 287896726934307787646947619)
        ·
          refine ⟨431845090401461681470421429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287896726934307787646947619 431845090401461681470421429)
          ·
            refine ⟨40485477225137032637852009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 431845090401461681470421429 40485477225137032637852009)
            ·
              refine ⟨30364107918852774478389007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40485477225137032637852009 30364107918852774478389007)
              ·
                refine ⟨45546161878279161717583511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30364107918852774478389007 45546161878279161717583511)
                ·
                  refine ⟨68319242817418742576375267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45546161878279161717583511 68319242817418742576375267)
                  ·
                    refine ⟨102478864226128113864562901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68319242817418742576375267 102478864226128113864562901)
                    ·
                      refine ⟨2401848380299877668700693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 102478864226128113864562901 2401848380299877668700693)
                      ·
                        rfl

theorem cell23_4677583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 7].length) (baseStart_4677583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677583 prefixEnd_4677583 := by exact prefixLift 4677583
  have htrace : WordTrace (prefixWord ++ tailWord_4677583) baseStart_4677583 baseEnd_4677583 := by
    simpa [prefixWord, tailWord_4677583, baseEnd_4677583] using wordTrace_append hprefix tailTrace_4677583
  have hstable : (prefixWord ++ tailWord_4677583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677583).length < 2 ^ (prefixWord ++ tailWord_4677583).sum := by decide
  have hdescent : baseEnd_4677583 < baseStart_4677583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677610 : List Nat := [3, 1, 3, 1, 2, 1, 1, 3, 1, 3, 4]
def baseStart_4677610 : Nat := 118140960795 + 4677610 * 2 ^ 59
def prefixEnd_4677610 : Nat := 4983230072969 + 3 ^ 40 * 4677610 * 2
def baseEnd_4677610 : Nat := 2401862244277549063063069

theorem tailTrace_4677610 : CollatzResearch.WordTrace tailWord_4677610 prefixEnd_4677610 2401862244277549063063069 := by
  unfold tailWord_4677610
  simp only [CollatzResearch.WordTrace]
  refine ⟨42651613145956329257911571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113737635055883544687764189 42651613145956329257911571)
  ·
    refine ⟨63977419718934493886867357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42651613145956329257911571 63977419718934493886867357)
    ·
      refine ⟨23991532394600435207575259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63977419718934493886867357 23991532394600435207575259)
      ·
        refine ⟨35987298591900652811362889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23991532394600435207575259 35987298591900652811362889)
        ·
          refine ⟨26990473943925489608522167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35987298591900652811362889 26990473943925489608522167)
          ·
            refine ⟨40485710915888234412783251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26990473943925489608522167 40485710915888234412783251)
            ·
              refine ⟨60728566373832351619174877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40485710915888234412783251 60728566373832351619174877)
              ·
                refine ⟨22773212390187131857190579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60728566373832351619174877 22773212390187131857190579)
                ·
                  refine ⟨34159818585280697785785869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22773212390187131857190579 34159818585280697785785869)
                  ·
                    refine ⟨12809931969480261669669701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34159818585280697785785869 12809931969480261669669701)
                    ·
                      refine ⟨2401862244277549063063069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12809931969480261669669701 2401862244277549063063069)
                      ·
                        rfl

theorem cell23_4677610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_4677610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677610 prefixEnd_4677610 := by exact prefixLift 4677610
  have htrace : WordTrace (prefixWord ++ tailWord_4677610) baseStart_4677610 baseEnd_4677610 := by
    simpa [prefixWord, tailWord_4677610, baseEnd_4677610] using wordTrace_append hprefix tailTrace_4677610
  have hstable : (prefixWord ++ tailWord_4677610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677610).length < 2 ^ (prefixWord ++ tailWord_4677610).sum := by decide
  have hdescent : baseEnd_4677610 < baseStart_4677610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677637 : List Nat := [1, 3, 1, 1, 2, 4, 3, 1, 3, 4]
def baseStart_4677637 : Nat := 118140960795 + 4677637 * 2 ^ 59
def prefixEnd_4677637 : Nat := 4983230072969 + 3 ^ 40 * 4677637 * 2
def baseEnd_4677637 : Nat := 800625369418406819141815

theorem tailTrace_4677637 : CollatzResearch.WordTrace tailWord_4677637 prefixEnd_4677637 800625369418406819141815 := by
  unfold tailWord_4677637
  simp only [CollatzResearch.WordTrace]
  refine ⟨170607437354727500642879165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113738291569818333761919443 170607437354727500642879165)
  ·
    refine ⟨63977789008022812741079687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170607437354727500642879165 63977789008022812741079687)
    ·
      refine ⟨95966683512034219111619531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63977789008022812741079687 95966683512034219111619531)
      ·
        refine ⟨143950025268051328667429297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95966683512034219111619531 143950025268051328667429297)
        ·
          refine ⟨107962518951038496500571973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143950025268051328667429297 107962518951038496500571973)
          ·
            refine ⟨20242972303319718093857245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107962518951038496500571973 20242972303319718093857245)
            ·
              refine ⟨7591114613744894285196467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20242972303319718093857245 7591114613744894285196467)
              ·
                refine ⟨11386671920617341427794701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7591114613744894285196467 11386671920617341427794701)
                ·
                  refine ⟨4270001970231503035423013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11386671920617341427794701 4270001970231503035423013)
                  ·
                    refine ⟨800625369418406819141815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4270001970231503035423013 800625369418406819141815)
                    ·
                      rfl

theorem cell23_4677637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 3, 4].length) (baseStart_4677637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677637 prefixEnd_4677637 := by exact prefixLift 4677637
  have htrace : WordTrace (prefixWord ++ tailWord_4677637) baseStart_4677637 baseEnd_4677637 := by
    simpa [prefixWord, tailWord_4677637, baseEnd_4677637] using wordTrace_append hprefix tailTrace_4677637
  have hstable : (prefixWord ++ tailWord_4677637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677637).length < 2 ^ (prefixWord ++ tailWord_4677637).sum := by decide
  have hdescent : baseEnd_4677637 < baseStart_4677637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677688 : List Nat := [2, 1, 2, 1, 6, 2, 2, 2, 1, 4]
def baseStart_4677688 : Nat := 118140960795 + 4677688 * 2 ^ 59
def prefixEnd_4677688 : Nat := 4983230072969 + 3 ^ 40 * 4677688 * 2
def baseEnd_4677688 : Nat := 800634098589533252629237

theorem tailTrace_4677688 : CollatzResearch.WordTrace tailWord_4677688 prefixEnd_4677688 800634098589533252629237 := by
  unfold tailWord_4677688
  simp only [CollatzResearch.WordTrace]
  refine ⟨85304648738771368176492859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113739531651695157568657145 85304648738771368176492859)
  ·
    refine ⟨127956973108157052264739289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85304648738771368176492859 127956973108157052264739289)
    ·
      refine ⟨95967729831117789198554467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127956973108157052264739289 95967729831117789198554467)
      ·
        refine ⟨143951594746676683797831701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95967729831117789198554467 143951594746676683797831701)
        ·
          refine ⟨6747731003750469553023361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 143951594746676683797831701 6747731003750469553023361)
          ·
            refine ⟨5060798252812852164767521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6747731003750469553023361 5060798252812852164767521)
            ·
              refine ⟨3795598689609639123575641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5060798252812852164767521 3795598689609639123575641)
              ·
                refine ⟨2846699017207229342681731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3795598689609639123575641 2846699017207229342681731)
                ·
                  refine ⟨4270048525810844014022597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2846699017207229342681731 4270048525810844014022597)
                  ·
                    refine ⟨800634098589533252629237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4270048525810844014022597 800634098589533252629237)
                    ·
                      rfl

theorem cell23_4677688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 2, 1, 4].length) (baseStart_4677688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677688 prefixEnd_4677688 := by exact prefixLift 4677688
  have htrace : WordTrace (prefixWord ++ tailWord_4677688) baseStart_4677688 baseEnd_4677688 := by
    simpa [prefixWord, tailWord_4677688, baseEnd_4677688] using wordTrace_append hprefix tailTrace_4677688
  have hstable : (prefixWord ++ tailWord_4677688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677688).length < 2 ^ (prefixWord ++ tailWord_4677688).sum := by decide
  have hdescent : baseEnd_4677688 < baseStart_4677688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677697 : List Nat := [1, 2, 5, 1, 2, 1, 1, 2, 3, 5]
def baseStart_4677697 : Nat := 118140960795 + 4677697 * 2 ^ 59
def prefixEnd_4677697 : Nat := 4983230072969 + 3 ^ 40 * 4677697 * 2
def baseEnd_4677697 : Nat := 800635639031496740891723

theorem tailTrace_4677697 : CollatzResearch.WordTrace tailWord_4677697 prefixEnd_4677697 800635639031496740891723 := by
  unfold tailWord_4677697
  simp only [CollatzResearch.WordTrace]
  refine ⟨170609625734510130890063345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113739750489673420593375563 170609625734510130890063345)
  ·
    refine ⟨127957219300882598167547509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170609625734510130890063345 127957219300882598167547509)
    ·
      refine ⟨11995989309457743578207579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 127957219300882598167547509 11995989309457743578207579)
      ·
        refine ⟨17993983964186615367311369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11995989309457743578207579 17993983964186615367311369)
        ·
          refine ⟨13495487973139961525483527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17993983964186615367311369 13495487973139961525483527)
          ·
            refine ⟨20243231959709942288225291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13495487973139961525483527 20243231959709942288225291)
            ·
              refine ⟨30364847939564913432337937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20243231959709942288225291 30364847939564913432337937)
              ·
                refine ⟨22773635954673685074253453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30364847939564913432337937 22773635954673685074253453)
                ·
                  refine ⟨8540113483002631902845045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22773635954673685074253453 8540113483002631902845045)
                  ·
                    refine ⟨800635639031496740891723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8540113483002631902845045 800635639031496740891723)
                    ·
                      rfl

theorem cell23_4677697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_4677697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677697 prefixEnd_4677697 := by exact prefixLift 4677697
  have htrace : WordTrace (prefixWord ++ tailWord_4677697) baseStart_4677697 baseEnd_4677697 := by
    simpa [prefixWord, tailWord_4677697, baseEnd_4677697] using wordTrace_append hprefix tailTrace_4677697
  have hstable : (prefixWord ++ tailWord_4677697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677697).length < 2 ^ (prefixWord ++ tailWord_4677697).sum := by decide
  have hdescent : baseEnd_4677697 < baseStart_4677697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677717 : List Nat := [1, 3, 2, 2, 1, 3, 2, 1, 3, 1, 4]
def baseStart_4677717 : Nat := 118140960795 + 4677717 * 2 ^ 59
def prefixEnd_4677717 : Nat := 4983230072969 + 3 ^ 40 * 4677717 * 2
def baseEnd_4677717 : Nat := 2401917186707580144425077

theorem tailTrace_4677717 : CollatzResearch.WordTrace tailWord_4677717 prefixEnd_4677717 2401917186707580144425077 := by
  unfold tailWord_4677717
  simp only [CollatzResearch.WordTrace]
  refine ⟨170610355194437674305791405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113740236796291782870527603 170610355194437674305791405)
  ·
    refine ⟨63978883197914127864671777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170610355194437674305791405 63978883197914127864671777)
    ·
      refine ⟨47984162398435595898503833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63978883197914127864671777 47984162398435595898503833)
      ·
        refine ⟨35988121798826696923877875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47984162398435595898503833 35988121798826696923877875)
        ·
          refine ⟨53982182698240045385816813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35988121798826696923877875 53982182698240045385816813)
          ·
            refine ⟨20243318511840017019681305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53982182698240045385816813 20243318511840017019681305)
            ·
              refine ⟨15182488883880012764760979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20243318511840017019681305 15182488883880012764760979)
              ·
                refine ⟨22773733325820019147141469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15182488883880012764760979 22773733325820019147141469)
                ·
                  refine ⟨8540149997182507180178051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22773733325820019147141469 8540149997182507180178051)
                  ·
                    refine ⟨12810224995773760770267077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8540149997182507180178051 12810224995773760770267077)
                    ·
                      refine ⟨2401917186707580144425077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12810224995773760770267077 2401917186707580144425077)
                      ·
                        rfl

theorem cell23_4677717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_4677717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677717 prefixEnd_4677717 := by exact prefixLift 4677717
  have htrace : WordTrace (prefixWord ++ tailWord_4677717) baseStart_4677717 baseEnd_4677717 := by
    simpa [prefixWord, tailWord_4677717, baseEnd_4677717] using wordTrace_append hprefix tailTrace_4677717
  have hstable : (prefixWord ++ tailWord_4677717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677717).length < 2 ^ (prefixWord ++ tailWord_4677717).sum := by decide
  have hdescent : baseEnd_4677717 < baseStart_4677717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677740 : List Nat := [2, 2, 1, 1, 3, 4, 10]
def baseStart_4677740 : Nat := 118140960795 + 4677740 * 2 ^ 59
def prefixEnd_4677740 : Nat := 4983230072969 + 3 ^ 40 * 4677740 * 2
def baseEnd_4677740 : Nat := 29653444404476957462191

theorem tailTrace_4677740 : CollatzResearch.WordTrace tailWord_4677740 prefixEnd_4677740 29653444404476957462191 := by
  unfold tailWord_4677740
  simp only [CollatzResearch.WordTrace]
  refine ⟨85305597036677174616939337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113740796048902899489252449 85305597036677174616939337)
  ·
    refine ⟨63979197777507880962704503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85305597036677174616939337 63979197777507880962704503)
    ·
      refine ⟨95968796666261821444056755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63979197777507880962704503 95968796666261821444056755)
      ·
        refine ⟨143953194999392732166085133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95968796666261821444056755 143953194999392732166085133)
        ·
          refine ⟨53982448124772274562281925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143953194999392732166085133 53982448124772274562281925)
          ·
            refine ⟨10121709023394801480427861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53982448124772274562281925 10121709023394801480427861)
            ·
              refine ⟨29653444404476957462191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10121709023394801480427861 29653444404476957462191)
              ·
                rfl

theorem cell23_4677740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 10].length) (baseStart_4677740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677740 prefixEnd_4677740 := by exact prefixLift 4677740
  have htrace : WordTrace (prefixWord ++ tailWord_4677740) baseStart_4677740 baseEnd_4677740 := by
    simpa [prefixWord, tailWord_4677740, baseEnd_4677740] using wordTrace_append hprefix tailTrace_4677740
  have hstable : (prefixWord ++ tailWord_4677740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677740).length < 2 ^ (prefixWord ++ tailWord_4677740).sum := by decide
  have hdescent : baseEnd_4677740 < baseStart_4677740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677744 : List Nat := [2, 1, 1, 1, 5, 2, 3, 2, 2, 4]
def baseStart_4677744 : Nat := 118140960795 + 4677744 * 2 ^ 59
def prefixEnd_4677744 : Nat := 4983230072969 + 3 ^ 40 * 4677744 * 2
def baseEnd_4677744 : Nat := 800643683561750512929151

theorem tailTrace_4677744 : CollatzResearch.WordTrace tailWord_4677744 prefixEnd_4677744 800643683561750512929151 := by
  unfold tailWord_4677744
  simp only [CollatzResearch.WordTrace]
  refine ⟨85305669982669928958512143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113740893310226571944682857 85305669982669928958512143)
  ·
    refine ⟨127958504974004893437768215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85305669982669928958512143 127958504974004893437768215)
    ·
      refine ⟨191937757461007340156652323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127958504974004893437768215 191937757461007340156652323)
      ·
        refine ⟨287906636191511010234978485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191937757461007340156652323 287906636191511010234978485)
        ·
          refine ⟨26991247142954157209529233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 287906636191511010234978485 26991247142954157209529233)
          ·
            refine ⟨20243435357215617907146925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26991247142954157209529233 20243435357215617907146925)
            ·
              refine ⟨7591288258955856715180097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20243435357215617907146925 7591288258955856715180097)
              ·
                refine ⟨5693466194216892536385073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7591288258955856715180097 5693466194216892536385073)
                ·
                  refine ⟨4270099645662669402288805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5693466194216892536385073 4270099645662669402288805)
                  ·
                    refine ⟨800643683561750512929151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4270099645662669402288805 800643683561750512929151)
                    ·
                      rfl

theorem cell23_4677744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 2, 4].length) (baseStart_4677744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677744 prefixEnd_4677744 := by exact prefixLift 4677744
  have htrace : WordTrace (prefixWord ++ tailWord_4677744) baseStart_4677744 baseEnd_4677744 := by
    simpa [prefixWord, tailWord_4677744, baseEnd_4677744] using wordTrace_append hprefix tailTrace_4677744
  have hstable : (prefixWord ++ tailWord_4677744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677744).length < 2 ^ (prefixWord ++ tailWord_4677744).sum := by decide
  have hdescent : baseEnd_4677744 < baseStart_4677744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677751 : List Nat := [1, 1, 3, 1, 1, 6, 2, 1, 3, 2, 2]
def baseStart_4677751 : Nat := 118140960795 + 4677751 * 2 ^ 59
def prefixEnd_4677751 : Nat := 4983230072969 + 3 ^ 40 * 4677751 * 2
def baseEnd_4677751 : Nat := 2401934645049833011399921

theorem tailTrace_4677751 : CollatzResearch.WordTrace tailWord_4677751 prefixEnd_4677751 2401934645049833011399921 := by
  unfold tailWord_4677751
  simp only [CollatzResearch.WordTrace]
  refine ⟨170611595276314498112529107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113741063517542998741686071 170611595276314498112529107)
  ·
    refine ⟨255917392914471747168793661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170611595276314498112529107 255917392914471747168793661)
    ·
      refine ⟨95969022342926905188297623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255917392914471747168793661 95969022342926905188297623)
      ·
        refine ⟨143953533514390357782446435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95969022342926905188297623 143953533514390357782446435)
        ·
          refine ⟨215930300271585536673669653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143953533514390357782446435 215930300271585536673669653)
          ·
            refine ⟨10121732825230572031578265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 215930300271585536673669653 10121732825230572031578265)
            ·
              refine ⟨7591299618922929023683699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10121732825230572031578265 7591299618922929023683699)
              ·
                refine ⟨11386949428384393535525549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7591299618922929023683699 11386949428384393535525549)
                ·
                  refine ⟨4270106035644147575822081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11386949428384393535525549 4270106035644147575822081)
                  ·
                    refine ⟨3202579526733110681866561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4270106035644147575822081 3202579526733110681866561)
                    ·
                      refine ⟨2401934645049833011399921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3202579526733110681866561 2401934645049833011399921)
                      ·
                        rfl

theorem cell23_4677751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 3, 2, 2].length) (baseStart_4677751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677751 prefixEnd_4677751 := by exact prefixLift 4677751
  have htrace : WordTrace (prefixWord ++ tailWord_4677751) baseStart_4677751 baseEnd_4677751 := by
    simpa [prefixWord, tailWord_4677751, baseEnd_4677751] using wordTrace_append hprefix tailTrace_4677751
  have hstable : (prefixWord ++ tailWord_4677751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677751).length < 2 ^ (prefixWord ++ tailWord_4677751).sum := by decide
  have hdescent : baseEnd_4677751 < baseStart_4677751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677761 : List Nat := [1, 2, 4, 2, 4, 1, 1, 1, 1, 6]
def baseStart_4677761 : Nat := 118140960795 + 4677761 * 2 ^ 59
def prefixEnd_4677761 : Nat := 4983230072969 + 3 ^ 40 * 4677761 * 2
def baseEnd_4677761 : Nat := 800646593285459324091625

theorem tailTrace_4677761 : CollatzResearch.WordTrace tailWord_4677761 prefixEnd_4677761 800646593285459324091625 := by
  unfold tailWord_4677761
  simp only [CollatzResearch.WordTrace]
  refine ⟨170611960006278269820393137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113741306670852179880262091 170611960006278269820393137)
  ·
    refine ⟨127958970004708702365294853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170611960006278269820393137 127958970004708702365294853)
    ·
      refine ⟨23992306875882881693492785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127958970004708702365294853 23992306875882881693492785)
      ·
        refine ⟨17994230156912161270119589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23992306875882881693492785 17994230156912161270119589)
        ·
          refine ⟨3373918154421030238147423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17994230156912161270119589 3373918154421030238147423)
          ·
            refine ⟨5060877231631545357221135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3373918154421030238147423 5060877231631545357221135)
            ·
              refine ⟨7591315847447318035831703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5060877231631545357221135 7591315847447318035831703)
              ·
                refine ⟨11386973771170977053747555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7591315847447318035831703 11386973771170977053747555)
                ·
                  refine ⟨17080460656756465580621333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11386973771170977053747555 17080460656756465580621333)
                  ·
                    refine ⟨800646593285459324091625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17080460656756465580621333 800646593285459324091625)
                    ·
                      rfl

theorem cell23_4677761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_4677761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677761 prefixEnd_4677761 := by exact prefixLift 4677761
  have htrace : WordTrace (prefixWord ++ tailWord_4677761) baseStart_4677761 baseEnd_4677761 := by
    simpa [prefixWord, tailWord_4677761, baseEnd_4677761] using wordTrace_append hprefix tailTrace_4677761
  have hstable : (prefixWord ++ tailWord_4677761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677761).length < 2 ^ (prefixWord ++ tailWord_4677761).sum := by decide
  have hdescent : baseEnd_4677761 < baseStart_4677761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677777 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 4, 7, 2]
def baseStart_4677777 : Nat := 118140960795 + 4677777 * 2 ^ 59
def prefixEnd_4677777 : Nat := 4983230072969 + 3 ^ 40 * 4677777 * 2
def baseEnd_4677777 : Nat := 2401947995546849909674801

theorem tailTrace_4677777 : CollatzResearch.WordTrace tailWord_4677777 prefixEnd_4677777 2401947995546849909674801 := by
  unfold tailWord_4677777
  simp only [CollatzResearch.WordTrace]
  refine ⟨170612543574220304552975585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113741695716146869701983723 170612543574220304552975585)
  ·
    refine ⟨127959407680665228414731689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170612543574220304552975585 127959407680665228414731689)
    ·
      refine ⟨95969555760498921311048767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127959407680665228414731689 95969555760498921311048767)
      ·
        refine ⟨143954333640748381966573151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95969555760498921311048767 143954333640748381966573151)
        ·
          refine ⟨215931500461122572949859727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143954333640748381966573151 215931500461122572949859727)
          ·
            refine ⟨323897250691683859424789591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215931500461122572949859727 323897250691683859424789591)
            ·
              refine ⟨485845876037525789137184387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323897250691683859424789591 485845876037525789137184387)
              ·
                refine ⟨728768814056288683705776581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 485845876037525789137184387 728768814056288683705776581)
                ·
                  refine ⟨136644152635554128194833109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 728768814056288683705776581 136644152635554128194833109)
                  ·
                    refine ⟨3202597327395799879566401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 136644152635554128194833109 3202597327395799879566401)
                    ·
                      refine ⟨2401947995546849909674801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3202597327395799879566401 2401947995546849909674801)
                      ·
                        rfl

theorem cell23_4677777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 7, 2].length) (baseStart_4677777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677777 prefixEnd_4677777 := by exact prefixLift 4677777
  have htrace : WordTrace (prefixWord ++ tailWord_4677777) baseStart_4677777 baseEnd_4677777 := by
    simpa [prefixWord, tailWord_4677777, baseEnd_4677777] using wordTrace_append hprefix tailTrace_4677777
  have hstable : (prefixWord ++ tailWord_4677777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677777).length < 2 ^ (prefixWord ++ tailWord_4677777).sum := by decide
  have hdescent : baseEnd_4677777 < baseStart_4677777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677802 : List Nat := [3, 1, 5, 1, 3, 1, 1, 1, 3, 2, 2]
def baseStart_4677802 : Nat := 118140960795 + 4677802 * 2 ^ 59
def prefixEnd_4677802 : Nat := 4983230072969 + 3 ^ 40 * 4677802 * 2
def baseEnd_4677802 : Nat := 2401960832563212311862187

theorem tailTrace_4677802 : CollatzResearch.WordTrace tailWord_4677802 prefixEnd_4677802 2401960832563212311862187 := by
  unfold tailWord_4677802
  simp only [CollatzResearch.WordTrace]
  refine ⟨42653363849782433455658915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113742303599419822548423773 42653363849782433455658915)
  ·
    refine ⟨63980045774673650183488373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42653363849782433455658915 63980045774673650183488373)
    ·
      refine ⟨5998129291375654704702035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63980045774673650183488373 5998129291375654704702035)
      ·
        refine ⟨8997193937063482057053053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5998129291375654704702035 8997193937063482057053053)
        ·
          refine ⟨3373947726398805771394895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8997193937063482057053053 3373947726398805771394895)
          ·
            refine ⟨5060921589598208657092343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3373947726398805771394895 5060921589598208657092343)
            ·
              refine ⟨7591382384397312985638515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5060921589598208657092343 7591382384397312985638515)
              ·
                refine ⟨11387073576595969478457773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7591382384397312985638515 11387073576595969478457773)
                ·
                  refine ⟨4270152591223488554421665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11387073576595969478457773 4270152591223488554421665)
                  ·
                    refine ⟨3202614443417616415816249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4270152591223488554421665 3202614443417616415816249)
                    ·
                      refine ⟨2401960832563212311862187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3202614443417616415816249 2401960832563212311862187)
                      ·
                        rfl

theorem cell23_4677802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_4677802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677802 prefixEnd_4677802 := by exact prefixLift 4677802
  have htrace : WordTrace (prefixWord ++ tailWord_4677802) baseStart_4677802 baseEnd_4677802 := by
    simpa [prefixWord, tailWord_4677802, baseEnd_4677802] using wordTrace_append hprefix tailTrace_4677802
  have hstable : (prefixWord ++ tailWord_4677802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677802).length < 2 ^ (prefixWord ++ tailWord_4677802).sum := by decide
  have hdescent : baseEnd_4677802 < baseStart_4677802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677828 : List Nat := [2, 3, 3, 1, 2, 1, 3, 2, 1, 3, 2]
def baseStart_4677828 : Nat := 118140960795 + 4677828 * 2 ^ 59
def prefixEnd_4677828 : Nat := 4983230072969 + 3 ^ 40 * 4677828 * 2
def baseEnd_4677828 : Nat := 2401974183060229210137067

theorem tailTrace_4677828 : CollatzResearch.WordTrace tailWord_4677828 prefixEnd_4677828 2401974183060229210137067 := by
  unfold tailWord_4677828
  simp only [CollatzResearch.WordTrace]
  refine ⟨85307201848517770131541069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 113742935798023693508721425 85307201848517770131541069)
  ·
    refine ⟨31990200693194163799327901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85307201848517770131541069 31990200693194163799327901)
    ·
      refine ⟨11996325259947811424747963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31990200693194163799327901 11996325259947811424747963)
      ·
        refine ⟨17994487889921717137121945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11996325259947811424747963 17994487889921717137121945)
        ·
          refine ⟨13495865917441287852841459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17994487889921717137121945 13495865917441287852841459)
          ·
            refine ⟨20243798876161931779262189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13495865917441287852841459 20243798876161931779262189)
            ·
              refine ⟨7591424578560724417223321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20243798876161931779262189 7591424578560724417223321)
              ·
                refine ⟨5693568433920543312917491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7591424578560724417223321 5693568433920543312917491)
                ·
                  refine ⟨8540352650880814969376237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5693568433920543312917491 8540352650880814969376237)
                  ·
                    refine ⟨3202632244080305613516089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8540352650880814969376237 3202632244080305613516089)
                    ·
                      refine ⟨2401974183060229210137067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3202632244080305613516089 2401974183060229210137067)
                      ·
                        rfl

theorem cell23_4677828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_4677828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677828 prefixEnd_4677828 := by exact prefixLift 4677828
  have htrace : WordTrace (prefixWord ++ tailWord_4677828) baseStart_4677828 baseEnd_4677828 := by
    simpa [prefixWord, tailWord_4677828, baseEnd_4677828] using wordTrace_append hprefix tailTrace_4677828
  have hstable : (prefixWord ++ tailWord_4677828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677828).length < 2 ^ (prefixWord ++ tailWord_4677828).sum := by decide
  have hdescent : baseEnd_4677828 < baseStart_4677828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677845 : List Nat := [1, 3, 2, 4, 2, 1, 3, 1, 1, 3, 2]
def baseStart_4677845 : Nat := 118140960795 + 4677845 * 2 ^ 59
def prefixEnd_4677845 : Nat := 4983230072969 + 3 ^ 40 * 4677845 * 2
def baseEnd_4677845 : Nat := 2401982912231355643624489

theorem tailTrace_4677845 : CollatzResearch.WordTrace tailWord_4677845 prefixEnd_4677845 2401982912231355643624489 := by
  unfold tailWord_4677845
  simp only [CollatzResearch.WordTrace]
  refine ⟨170615023737973952166450989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113743349158649301444300659 170615023737973952166450989)
  ·
    refine ⟨63980633901740232062419121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 170615023737973952166450989 63980633901740232062419121)
    ·
      refine ⟨47985475426305174046814341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63980633901740232062419121 47985475426305174046814341)
      ·
        refine ⟨8997276642432220133777689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47985475426305174046814341 8997276642432220133777689)
        ·
          refine ⟨6747957481824165100333267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8997276642432220133777689 6747957481824165100333267)
          ·
            refine ⟨10121936222736247650499901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6747957481824165100333267 10121936222736247650499901)
            ·
              refine ⟨3795726083526092868937463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10121936222736247650499901 3795726083526092868937463)
              ·
                refine ⟨5693589125289139303406195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3795726083526092868937463 5693589125289139303406195)
                ·
                  refine ⟨8540383687933708955109293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5693589125289139303406195 8540383687933708955109293)
                  ·
                    refine ⟨3202643882975140858165985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8540383687933708955109293 3202643882975140858165985)
                    ·
                      refine ⟨2401982912231355643624489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3202643882975140858165985 2401982912231355643624489)
                      ·
                        rfl

theorem cell23_4677845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_4677845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677845 prefixEnd_4677845 := by exact prefixLift 4677845
  have htrace : WordTrace (prefixWord ++ tailWord_4677845) baseStart_4677845 baseEnd_4677845 := by
    simpa [prefixWord, tailWord_4677845, baseEnd_4677845] using wordTrace_append hprefix tailTrace_4677845
  have hstable : (prefixWord ++ tailWord_4677845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677845).length < 2 ^ (prefixWord ++ tailWord_4677845).sum := by decide
  have hdescent : baseEnd_4677845 < baseStart_4677845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677874 : List Nat := [3, 2, 1, 3, 2, 1, 1, 1, 1, 5, 3]
def baseStart_4677874 : Nat := 118140960795 + 4677874 * 2 ^ 59
def prefixEnd_4677874 : Nat := 4983230072969 + 3 ^ 40 * 4677874 * 2
def baseEnd_4677874 : Nat := 2401997803170336030161855

theorem tailTrace_4677874 : CollatzResearch.WordTrace tailWord_4677874 prefixEnd_4677874 2401997803170336030161855 := by
  unfold tailWord_4677874
  simp only [CollatzResearch.WordTrace]
  refine ⟨42654020363717222529814169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 113744054303245926746171117 42654020363717222529814169)
  ·
    refine ⟨31990515272787916897360627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42654020363717222529814169 31990515272787916897360627)
    ·
      refine ⟨47985772909181875346040941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31990515272787916897360627 47985772909181875346040941)
      ·
        refine ⟨17994664840943203254765353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47985772909181875346040941 17994664840943203254765353)
        ·
          refine ⟨13495998630707402441074015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17994664840943203254765353 13495998630707402441074015)
          ·
            refine ⟨20243997946061103661611023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13495998630707402441074015 20243997946061103661611023)
            ·
              refine ⟨30365996919091655492416535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20243997946061103661611023 30365996919091655492416535)
              ·
                refine ⟨45548995378637483238624803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30365996919091655492416535 45548995378637483238624803)
                ·
                  refine ⟨68323493067956224857937205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45548995378637483238624803 68323493067956224857937205)
                  ·
                    refine ⟨6405327475120896080431613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 68323493067956224857937205 6405327475120896080431613)
                    ·
                      refine ⟨2401997803170336030161855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6405327475120896080431613 2401997803170336030161855)
                      ·
                        rfl

theorem cell23_4677874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_4677874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677874 prefixEnd_4677874 := by exact prefixLift 4677874
  have htrace : WordTrace (prefixWord ++ tailWord_4677874) baseStart_4677874 baseEnd_4677874 := by
    simpa [prefixWord, tailWord_4677874, baseEnd_4677874] using wordTrace_append hprefix tailTrace_4677874
  have hstable : (prefixWord ++ tailWord_4677874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677874).length < 2 ^ (prefixWord ++ tailWord_4677874).sum := by decide
  have hdescent : baseEnd_4677874 < baseStart_4677874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4677977 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 7]
def baseStart_4677977 : Nat := 118140960795 + 4677977 * 2 ^ 59
def prefixEnd_4677977 : Nat := 4983230072969 + 3 ^ 40 * 4677977 * 2
def baseEnd_4677977 : Nat := 2402050691677749127173881

theorem tailTrace_4677977 : CollatzResearch.WordTrace tailWord_4677977 prefixEnd_4677977 2402050691677749127173881 := by
  unfold tailWord_4677977
  simp only [CollatzResearch.WordTrace]
  refine ⟨170619838173495738710256185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113746558782330492473504123 170619838173495738710256185)
  ·
    refine ⟨127964878630121804032692139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170619838173495738710256185 127964878630121804032692139)
    ·
      refine ⟨191947317945182706049038209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127964878630121804032692139 191947317945182706049038209)
      ·
        refine ⟨143960488458887029536778657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191947317945182706049038209 143960488458887029536778657)
        ·
          refine ⟨107970366344165272152583993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143960488458887029536778657 107970366344165272152583993)
          ·
            refine ⟨80977774758123954114437995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107970366344165272152583993 80977774758123954114437995)
            ·
              refine ⟨121466662137185931171656993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80977774758123954114437995 121466662137185931171656993)
              ·
                refine ⟨91099996602889448378742745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121466662137185931171656993 91099996602889448378742745)
                ·
                  refine ⟨68324997452167086284057059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91099996602889448378742745 68324997452167086284057059)
                  ·
                    refine ⟨102487496178250629426085589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68324997452167086284057059 102487496178250629426085589)
                    ·
                      refine ⟨2402050691677749127173881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 102487496178250629426085589 2402050691677749127173881)
                      ·
                        rfl

theorem cell23_4677977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_4677977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4677977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4677977 prefixEnd_4677977 := by exact prefixLift 4677977
  have htrace : WordTrace (prefixWord ++ tailWord_4677977) baseStart_4677977 baseEnd_4677977 := by
    simpa [prefixWord, tailWord_4677977, baseEnd_4677977] using wordTrace_append hprefix tailTrace_4677977
  have hstable : (prefixWord ++ tailWord_4677977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4677977).length < 2 ^ (prefixWord ++ tailWord_4677977).sum := by decide
  have hdescent : baseEnd_4677977 < baseStart_4677977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4677977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678027 : List Nat := [1, 1, 1, 1, 4, 15]
def baseStart_4678027 : Nat := 118140960795 + 4678027 * 2 ^ 59
def prefixEnd_4678027 : Nat := 4983230072969 + 3 ^ 40 * 4678027 * 2
def baseEnd_4678027 : Nat := 9885087924734460623657

theorem tailTrace_4678027 : CollatzResearch.WordTrace tailWord_4678027 prefixEnd_4678027 9885087924734460623657 := by
  unfold tailWord_4678027
  simp only [CollatzResearch.WordTrace]
  refine ⟨170621661823314597249576335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113747774548876398166384223 170621661823314597249576335)
  ·
    refine ⟨255932492734971895874364503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170621661823314597249576335 255932492734971895874364503)
    ·
      refine ⟨383898739102457843811546755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255932492734971895874364503 383898739102457843811546755)
      ·
        refine ⟨575848108653686765717320133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383898739102457843811546755 575848108653686765717320133)
        ·
          refine ⟨107971520372566268571997525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 575848108653686765717320133 107971520372566268571997525)
          ·
            refine ⟨9885087924734460623657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 107971520372566268571997525 9885087924734460623657)
            ·
              rfl

theorem cell23_4678027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 15].length) (baseStart_4678027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678027 prefixEnd_4678027 := by exact prefixLift 4678027
  have htrace : WordTrace (prefixWord ++ tailWord_4678027) baseStart_4678027 baseEnd_4678027 := by
    simpa [prefixWord, tailWord_4678027, baseEnd_4678027] using wordTrace_append hprefix tailTrace_4678027
  have hstable : (prefixWord ++ tailWord_4678027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678027).length < 2 ^ (prefixWord ++ tailWord_4678027).sum := by decide
  have hdescent : baseEnd_4678027 < baseStart_4678027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678051 : List Nat := [1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 4]
def baseStart_4678051 : Nat := 118140960795 + 4678051 * 2 ^ 59
def prefixEnd_4678051 : Nat := 4983230072969 + 3 ^ 40 * 4678051 * 2
def baseEnd_4678051 : Nat := 2402088689246181837648541

theorem tailTrace_4678051 : CollatzResearch.WordTrace tailWord_4678051 prefixEnd_4678051 2402088689246181837648541 := by
  unfold tailWord_4678051
  simp only [CollatzResearch.WordTrace]
  refine ⟨170622537175227649348450007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113748358116818432898966671 170622537175227649348450007)
  ·
    refine ⟨255933805762841474022675011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170622537175227649348450007 255933805762841474022675011)
    ·
      refine ⟨383900708644262211034012517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255933805762841474022675011 383900708644262211034012517)
      ·
        refine ⟨71981382870799164568877347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 383900708644262211034012517 71981382870799164568877347)
        ·
          refine ⟨107972074306198746853316021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71981382870799164568877347 107972074306198746853316021)
          ·
            refine ⟨10122381966206132517498377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 107972074306198746853316021 10122381966206132517498377)
            ·
              refine ⟨7591786474654599388123783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10122381966206132517498377 7591786474654599388123783)
              ·
                refine ⟨11387679711981899082185675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7591786474654599388123783 11387679711981899082185675)
                ·
                  refine ⟨17081519567972848623278513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11387679711981899082185675 17081519567972848623278513)
                  ·
                    refine ⟨12811139675979636467458885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17081519567972848623278513 12811139675979636467458885)
                    ·
                      refine ⟨2402088689246181837648541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12811139675979636467458885 2402088689246181837648541)
                      ·
                        rfl

theorem cell23_4678051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_4678051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678051 prefixEnd_4678051 := by exact prefixLift 4678051
  have htrace : WordTrace (prefixWord ++ tailWord_4678051) baseStart_4678051 baseEnd_4678051 := by
    simpa [prefixWord, tailWord_4678051, baseEnd_4678051] using wordTrace_append hprefix tailTrace_4678051
  have hstable : (prefixWord ++ tailWord_4678051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678051).length < 2 ^ (prefixWord ++ tailWord_4678051).sum := by decide
  have hdescent : baseEnd_4678051 < baseStart_4678051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678055 : List Nat := [1, 1, 6, 1, 1, 3, 1, 2, 3, 2, 2]
def baseStart_4678055 : Nat := 118140960795 + 4678055 * 2 ^ 59
def prefixEnd_4678055 : Nat := 4983230072969 + 3 ^ 40 * 4678055 * 2
def baseEnd_4678055 : Nat := 2402090743168799821998523

theorem tailTrace_4678055 : CollatzResearch.WordTrace tailWord_4678055 prefixEnd_4678055 2402090743168799821998523 := by
  unfold tailWord_4678055
  simp only [CollatzResearch.WordTrace]
  refine ⟨170622683067213158031595619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113748455378142105354397079 170622683067213158031595619)
  ·
    refine ⟨255934024600819737047393429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170622683067213158031595619 255934024600819737047393429)
    ·
      refine ⟨11996907403163425174096567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 255934024600819737047393429 11996907403163425174096567)
      ·
        refine ⟨17995361104745137761144851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11996907403163425174096567 17995361104745137761144851)
        ·
          refine ⟨26993041657117706641717277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17995361104745137761144851 26993041657117706641717277)
          ·
            refine ⟨10122390621419139990643979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26993041657117706641717277 10122390621419139990643979)
            ·
              refine ⟨15183585932128709985965969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10122390621419139990643979 15183585932128709985965969)
              ·
                refine ⟨11387689449096532489474477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15183585932128709985965969 11387689449096532489474477)
                ·
                  refine ⟨4270383543411199683552929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11387689449096532489474477 4270383543411199683552929)
                  ·
                    refine ⟨3202787657558399762664697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4270383543411199683552929 3202787657558399762664697)
                    ·
                      refine ⟨2402090743168799821998523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3202787657558399762664697 2402090743168799821998523)
                      ·
                        rfl

theorem cell23_4678055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_4678055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678055 prefixEnd_4678055 := by exact prefixLift 4678055
  have htrace : WordTrace (prefixWord ++ tailWord_4678055) baseStart_4678055 baseEnd_4678055 := by
    simpa [prefixWord, tailWord_4678055, baseEnd_4678055] using wordTrace_append hprefix tailTrace_4678055
  have hstable : (prefixWord ++ tailWord_4678055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678055).length < 2 ^ (prefixWord ++ tailWord_4678055).sum := by decide
  have hdescent : baseEnd_4678055 < baseStart_4678055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4678071 : List Nat := [1, 1, 3, 1, 3, 3, 2, 2, 1, 3, 3]
def baseStart_4678071 : Nat := 118140960795 + 4678071 * 2 ^ 59
def prefixEnd_4678071 : Nat := 4983230072969 + 3 ^ 40 * 4678071 * 2
def baseEnd_4678071 : Nat := 2402098958859271759398449

theorem tailTrace_4678071 : CollatzResearch.WordTrace tailWord_4678071 prefixEnd_4678071 2402098958859271759398449 := by
  unfold tailWord_4678071
  simp only [CollatzResearch.WordTrace]
  refine ⟨170623266635155192764178067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 113748844423436795176118711 170623266635155192764178067)
  ·
    refine ⟨255934899952732789146267101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170623266635155192764178067 255934899952732789146267101)
    ·
      refine ⟨95975587482274795929850163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 255934899952732789146267101 95975587482274795929850163)
      ·
        refine ⟨143963381223412193894775245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95975587482274795929850163 143963381223412193894775245)
        ·
          refine ⟨53986267958779572710540717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143963381223412193894775245 53986267958779572710540717)
          ·
            refine ⟨20244850484542339766452769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53986267958779572710540717 20244850484542339766452769)
            ·
              refine ⟨15183637863406754824839577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20244850484542339766452769 15183637863406754824839577)
              ·
                refine ⟨11387728397555066118629683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15183637863406754824839577 11387728397555066118629683)
                ·
                  refine ⟨17081592596332599177944525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11387728397555066118629683 17081592596332599177944525)
                  ·
                    refine ⟨6405597223624724691729197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17081592596332599177944525 6405597223624724691729197)
                    ·
                      refine ⟨2402098958859271759398449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6405597223624724691729197 2402098958859271759398449)
                      ·
                        rfl

theorem cell23_4678071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 3, 3].length) (baseStart_4678071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4678071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4678071 prefixEnd_4678071 := by exact prefixLift 4678071
  have htrace : WordTrace (prefixWord ++ tailWord_4678071) baseStart_4678071 baseEnd_4678071 := by
    simpa [prefixWord, tailWord_4678071, baseEnd_4678071] using wordTrace_append hprefix tailTrace_4678071
  have hstable : (prefixWord ++ tailWord_4678071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4678071).length < 2 ^ (prefixWord ++ tailWord_4678071).sum := by decide
  have hdescent : baseEnd_4678071 < baseStart_4678071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4678071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
