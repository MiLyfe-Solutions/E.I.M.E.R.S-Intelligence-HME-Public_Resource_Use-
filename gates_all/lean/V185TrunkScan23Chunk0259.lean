import V185TrunkScan23Chunk0258

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1532209 : List Nat := [1, 2, 2, 3, 4, 1, 1, 1, 1, 1, 6]
def baseStart_1532209 : Nat := 118140960795 + 1532209 * 2 ^ 59
def prefixEnd_1532209 : Nat := 4983230072969 + 3 ^ 40 * 1532209 * 2
def baseEnd_1532209 : Nat := 786759680144900958941005

theorem tailTrace_1532209 : CollatzResearch.WordTrace tailWord_1532209 prefixEnd_1532209 786759680144900958941005 := by
  unfold tailWord_1532209
  simp only [CollatzResearch.WordTrace]
  refine ⟨55884253306075948308863681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37256168870717298872575787 55884253306075948308863681)
  ·
    refine ⟨41913189979556961231647761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55884253306075948308863681 41913189979556961231647761)
    ·
      refine ⟨31434892484667720923735821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41913189979556961231647761 31434892484667720923735821)
      ·
        refine ⟨11788084681750395346400933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31434892484667720923735821 11788084681750395346400933)
        ·
          refine ⟨2210265877828199127450175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11788084681750395346400933 2210265877828199127450175)
          ·
            refine ⟨3315398816742298691175263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2210265877828199127450175 3315398816742298691175263)
            ·
              refine ⟨4973098225113448036762895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3315398816742298691175263 4973098225113448036762895)
              ·
                refine ⟨7459647337670172055144343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4973098225113448036762895 7459647337670172055144343)
                ·
                  refine ⟨11189471006505258082716515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7459647337670172055144343 11189471006505258082716515)
                  ·
                    refine ⟨16784206509757887124074773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11189471006505258082716515 16784206509757887124074773)
                    ·
                      refine ⟨786759680144900958941005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16784206509757887124074773 786759680144900958941005)
                      ·
                        rfl

theorem cell23_1532209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_1532209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532209 prefixEnd_1532209 := by exact prefixLift 1532209
  have htrace : WordTrace (prefixWord ++ tailWord_1532209) baseStart_1532209 baseEnd_1532209 := by
    simpa [prefixWord, tailWord_1532209, baseEnd_1532209] using wordTrace_append hprefix tailTrace_1532209
  have hstable : (prefixWord ++ tailWord_1532209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532209).length < 2 ^ (prefixWord ++ tailWord_1532209).sum := by decide
  have hdescent : baseEnd_1532209 < baseStart_1532209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532263 : List Nat := [1, 1, 5, 1, 3, 2, 1, 3, 2, 1, 3]
def baseStart_1532263 : Nat := 118140960795 + 1532263 * 2 ^ 59
def prefixEnd_1532263 : Nat := 4983230072969 + 3 ^ 40 * 1532263 * 2
def baseEnd_1532263 : Nat := 786787408100243747665757

theorem tailTrace_1532263 : CollatzResearch.WordTrace tailWord_1532263 prefixEnd_1532263 786787408100243747665757 := by
  unfold tailWord_1532263
  simp only [CollatzResearch.WordTrace]
  refine ⟨55886222847880315531329443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37257481898586877020886295 55886222847880315531329443)
  ·
    refine ⟨83829334271820473296994165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55886222847880315531329443 83829334271820473296994165)
    ·
      refine ⟨7859000087983169371593203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83829334271820473296994165 7859000087983169371593203)
      ·
        refine ⟨11788500131974754057389805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7859000087983169371593203 11788500131974754057389805)
        ·
          refine ⟨4420687549490532771521177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11788500131974754057389805 4420687549490532771521177)
          ·
            refine ⟨3315515662117899578640883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4420687549490532771521177 3315515662117899578640883)
            ·
              refine ⟨4973273493176849367961325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3315515662117899578640883 4973273493176849367961325)
              ·
                refine ⟨1864977559941318512985497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4973273493176849367961325 1864977559941318512985497)
                ·
                  refine ⟨1398733169955988884739123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1864977559941318512985497 1398733169955988884739123)
                  ·
                    refine ⟨2098099754933983327108685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1398733169955988884739123 2098099754933983327108685)
                    ·
                      refine ⟨786787408100243747665757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2098099754933983327108685 786787408100243747665757)
                      ·
                        rfl

theorem cell23_1532263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_1532263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532263 prefixEnd_1532263 := by exact prefixLift 1532263
  have htrace : WordTrace (prefixWord ++ tailWord_1532263) baseStart_1532263 baseEnd_1532263 := by
    simpa [prefixWord, tailWord_1532263, baseEnd_1532263] using wordTrace_append hprefix tailTrace_1532263
  have hstable : (prefixWord ++ tailWord_1532263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532263).length < 2 ^ (prefixWord ++ tailWord_1532263).sum := by decide
  have hdescent : baseEnd_1532263 < baseStart_1532263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532396 : List Nat := [2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 3]
def baseStart_1532396 : Nat := 118140960795 + 1532396 * 2 ^ 59
def prefixEnd_1532396 : Nat := 4983230072969 + 3 ^ 40 * 1532396 * 2
def baseEnd_1532396 : Nat := 786855701027291727302645

theorem tailTrace_1532396 : CollatzResearch.WordTrace tailWord_1532396 prefixEnd_1532396 786855701027291727302645 := by
  unfold tailWord_1532396
  simp only [CollatzResearch.WordTrace]
  refine ⟨27945536878199239622960521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37260715837598986163947361 27945536878199239622960521)
  ·
    refine ⟨20959152658649429717220391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27945536878199239622960521 20959152658649429717220391)
    ·
      refine ⟨31438728987974144575830587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20959152658649429717220391 31438728987974144575830587)
      ·
        refine ⟨47158093481961216863745881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31438728987974144575830587 47158093481961216863745881)
        ·
          refine ⟨35368570111470912647809411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47158093481961216863745881 35368570111470912647809411)
          ·
            refine ⟨53052855167206368971714117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35368570111470912647809411 53052855167206368971714117)
            ·
              refine ⟨9947410343851194182196397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53052855167206368971714117 9947410343851194182196397)
              ·
                refine ⟨3730278878944197818323649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9947410343851194182196397 3730278878944197818323649)
                ·
                  refine ⟨2797709159208148363742737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3730278878944197818323649 2797709159208148363742737)
                  ·
                    refine ⟨2098281869406111272807053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2797709159208148363742737 2098281869406111272807053)
                    ·
                      refine ⟨786855701027291727302645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2098281869406111272807053 786855701027291727302645)
                      ·
                        rfl

theorem cell23_1532396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 3].length) (baseStart_1532396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532396 prefixEnd_1532396 := by exact prefixLift 1532396
  have htrace : WordTrace (prefixWord ++ tailWord_1532396) baseStart_1532396 baseEnd_1532396 := by
    simpa [prefixWord, tailWord_1532396, baseEnd_1532396] using wordTrace_append hprefix tailTrace_1532396
  have hstable : (prefixWord ++ tailWord_1532396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532396).length < 2 ^ (prefixWord ++ tailWord_1532396).sum := by decide
  have hdescent : baseEnd_1532396 < baseStart_1532396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532420 : List Nat := [2, 3, 2, 3, 1, 3, 1, 1, 3, 4]
def baseStart_1532420 : Nat := 118140960795 + 1532420 * 2 ^ 59
def prefixEnd_1532420 : Nat := 4983230072969 + 3 ^ 40 * 1532420 * 2
def baseEnd_1532420 : Nat := 262289341520999877800845

theorem tailTrace_1532420 : CollatzResearch.WordTrace tailWord_1532420 prefixEnd_1532420 262289341520999877800845 := by
  unfold tailWord_1532420
  simp only [CollatzResearch.WordTrace]
  refine ⟨27945974554155765672397357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37261299405541020896529809 27945974554155765672397357)
  ·
    refine ⟨10479740457808412127149009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27945974554155765672397357 10479740457808412127149009)
    ·
      refine ⟨7859805343356309095361757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10479740457808412127149009 7859805343356309095361757)
      ·
        refine ⟨2947427003758615910760659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7859805343356309095361757 2947427003758615910760659)
        ·
          refine ⟨4421140505637923866140989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2947427003758615910760659 4421140505637923866140989)
          ·
            refine ⟨1657927689614221449802871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4421140505637923866140989 1657927689614221449802871)
            ·
              refine ⟨2486891534421332174704307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1657927689614221449802871 2486891534421332174704307)
              ·
                refine ⟨3730337301631998262056461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2486891534421332174704307 3730337301631998262056461)
                ·
                  refine ⟨1398876488111999348271173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3730337301631998262056461 1398876488111999348271173)
                  ·
                    refine ⟨262289341520999877800845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1398876488111999348271173 262289341520999877800845)
                    ·
                      rfl

theorem cell23_1532420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_1532420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532420 prefixEnd_1532420 := by exact prefixLift 1532420
  have htrace : WordTrace (prefixWord ++ tailWord_1532420) baseStart_1532420 baseEnd_1532420 := by
    simpa [prefixWord, tailWord_1532420, baseEnd_1532420] using wordTrace_append hprefix tailTrace_1532420
  have hstable : (prefixWord ++ tailWord_1532420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532420).length < 2 ^ (prefixWord ++ tailWord_1532420).sum := by decide
  have hdescent : baseEnd_1532420 < baseStart_1532420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532453 : List Nat := [1, 3, 1, 2, 2, 1, 3, 3, 2, 3, 2]
def baseStart_1532453 : Nat := 118140960795 + 1532453 * 2 ^ 59
def prefixEnd_1532453 : Nat := 4983230072969 + 3 ^ 40 * 1532453 * 2
def baseEnd_1532453 : Nat := 786884969424598004289883

theorem tailTrace_1532453 : CollatzResearch.WordTrace tailWord_1532453 prefixEnd_1532453 786884969424598004289883 := by
  unfold tailWord_1532453
  simp only [CollatzResearch.WordTrace]
  refine ⟨55893152717191977980746013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37262101811461318653830675 55893152717191977980746013)
  ·
    refine ⟨20959932268946991742779755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55893152717191977980746013 20959932268946991742779755)
    ·
      refine ⟨31439898403420487614169633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20959932268946991742779755 31439898403420487614169633)
      ·
        refine ⟨23579923802565365710627225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31439898403420487614169633 23579923802565365710627225)
        ·
          refine ⟨17684942851924024282970419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23579923802565365710627225 17684942851924024282970419)
          ·
            refine ⟨26527414277886036424455629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17684942851924024282970419 26527414277886036424455629)
            ·
              refine ⟨9947780354207263659170861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26527414277886036424455629 9947780354207263659170861)
              ·
                refine ⟨3730417632827723872189073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9947780354207263659170861 3730417632827723872189073)
                ·
                  refine ⟨2797813224620792904141805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3730417632827723872189073 2797813224620792904141805)
                  ·
                    refine ⟨1049179959232797339053177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2797813224620792904141805 1049179959232797339053177)
                    ·
                      refine ⟨786884969424598004289883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1049179959232797339053177 786884969424598004289883)
                      ·
                        rfl

theorem cell23_1532453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 3, 2].length) (baseStart_1532453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532453 prefixEnd_1532453 := by exact prefixLift 1532453
  have htrace : WordTrace (prefixWord ++ tailWord_1532453) baseStart_1532453 baseEnd_1532453 := by
    simpa [prefixWord, tailWord_1532453, baseEnd_1532453] using wordTrace_append hprefix tailTrace_1532453
  have hstable : (prefixWord ++ tailWord_1532453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532453).length < 2 ^ (prefixWord ++ tailWord_1532453).sum := by decide
  have hdescent : baseEnd_1532453 < baseStart_1532453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532477 : List Nat := [1, 4, 1, 3, 2, 2, 1, 4, 1, 1, 3]
def baseStart_1532477 : Nat := 118140960795 + 1532477 * 2 ^ 59
def prefixEnd_1532477 : Nat := 4983230072969 + 3 ^ 40 * 1532477 * 2
def baseEnd_1532477 : Nat := 786897292960305910389773

theorem tailTrace_1532477 : CollatzResearch.WordTrace tailWord_1532477 prefixEnd_1532477 786897292960305910389773 := by
  unfold tailWord_1532477
  simp only [CollatzResearch.WordTrace]
  refine ⟨55894028069105030079619685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37262685379403353386413123 55894028069105030079619685)
  ·
    refine ⟨10480130262957193139928691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55894028069105030079619685 10480130262957193139928691)
    ·
      refine ⟨15720195394435789709893037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10480130262957193139928691 15720195394435789709893037)
      ·
        refine ⟨5895073272913421141209889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15720195394435789709893037 5895073272913421141209889)
        ·
          refine ⟨4421304954685065855907417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5895073272913421141209889 4421304954685065855907417)
          ·
            refine ⟨3315978716013799391930563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4421304954685065855907417 3315978716013799391930563)
            ·
              refine ⟨4973968074020699087895845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3315978716013799391930563 4973968074020699087895845)
              ·
                refine ⟨932619013878881078980471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4973968074020699087895845 932619013878881078980471)
                ·
                  refine ⟨1398928520818321618470707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 932619013878881078980471 1398928520818321618470707)
                  ·
                    refine ⟨2098392781227482427706061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1398928520818321618470707 2098392781227482427706061)
                    ·
                      refine ⟨786897292960305910389773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2098392781227482427706061 786897292960305910389773)
                      ·
                        rfl

theorem cell23_1532477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_1532477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532477 prefixEnd_1532477 := by exact prefixLift 1532477
  have htrace : WordTrace (prefixWord ++ tailWord_1532477) baseStart_1532477 baseEnd_1532477 := by
    simpa [prefixWord, tailWord_1532477, baseEnd_1532477] using wordTrace_append hprefix tailTrace_1532477
  have hstable : (prefixWord ++ tailWord_1532477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532477).length < 2 ^ (prefixWord ++ tailWord_1532477).sum := by decide
  have hdescent : baseEnd_1532477 < baseStart_1532477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532483 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 7, 2, 2]
def baseStart_1532483 : Nat := 118140960795 + 1532483 * 2 ^ 59
def prefixEnd_1532483 : Nat := 4983230072969 + 3 ^ 40 * 1532483 * 2
def baseEnd_1532483 : Nat := 786900373844232886914745

theorem tailTrace_1532483 : CollatzResearch.WordTrace tailWord_1532483 prefixEnd_1532483 786900373844232886914745 := by
  unfold tailWord_1532483
  simp only [CollatzResearch.WordTrace]
  refine ⟨55894246907083293104338103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37262831271388862069558735 55894246907083293104338103)
  ·
    refine ⟨83841370360624939656507155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55894246907083293104338103 83841370360624939656507155)
    ·
      refine ⟨125762055540937409484760733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83841370360624939656507155 125762055540937409484760733)
      ·
        refine ⟨47160770827851528556785275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125762055540937409484760733 47160770827851528556785275)
        ·
          refine ⟨70741156241777292835177913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47160770827851528556785275 70741156241777292835177913)
          ·
            refine ⟨53055867181332969626383435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70741156241777292835177913 53055867181332969626383435)
            ·
              refine ⟨79583800771999454439575153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53055867181332969626383435 79583800771999454439575153)
              ·
                refine ⟨59687850578999590829681365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79583800771999454439575153 59687850578999590829681365)
                ·
                  refine ⟨1398933997945302910070657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 59687850578999590829681365 1398933997945302910070657)
                  ·
                    refine ⟨1049200498458977182552993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1398933997945302910070657 1049200498458977182552993)
                    ·
                      refine ⟨786900373844232886914745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1049200498458977182552993 786900373844232886914745)
                      ·
                        rfl

theorem cell23_1532483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 7, 2, 2].length) (baseStart_1532483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532483 prefixEnd_1532483 := by exact prefixLift 1532483
  have htrace : WordTrace (prefixWord ++ tailWord_1532483) baseStart_1532483 baseEnd_1532483 := by
    simpa [prefixWord, tailWord_1532483, baseEnd_1532483] using wordTrace_append hprefix tailTrace_1532483
  have hstable : (prefixWord ++ tailWord_1532483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532483).length < 2 ^ (prefixWord ++ tailWord_1532483).sum := by decide
  have hdescent : baseEnd_1532483 < baseStart_1532483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532493 : List Nat := [1, 6, 1, 1, 2, 1, 1, 3, 1, 6]
def baseStart_1532493 : Nat := 118140960795 + 1532493 * 2 ^ 59
def prefixEnd_1532493 : Nat := 4983230072969 + 3 ^ 40 * 1532493 * 2
def baseEnd_1532493 : Nat := 262301836216925949263233

theorem tailTrace_1532493 : CollatzResearch.WordTrace tailWord_1532493 prefixEnd_1532493 262301836216925949263233 := by
  unfold tailWord_1532493
  simp only [CollatzResearch.WordTrace]
  refine ⟨55894611637047064812202133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37263074424698043208134755 55894611637047064812202133)
  ·
    refine ⟨2620059920486581163071975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 55894611637047064812202133 2620059920486581163071975)
    ·
      refine ⟨3930089880729871744607963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2620059920486581163071975 3930089880729871744607963)
      ·
        refine ⟨5895134821094807616911945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3930089880729871744607963 5895134821094807616911945)
        ·
          refine ⟨4421351115821105712683959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5895134821094807616911945 4421351115821105712683959)
          ·
            refine ⟨6632026673731658569025939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4421351115821105712683959 6632026673731658569025939)
            ·
              refine ⟨9948040010597487853538909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6632026673731658569025939 9948040010597487853538909)
              ·
                refine ⟨3730515003974057945077091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9948040010597487853538909 3730515003974057945077091)
                ·
                  refine ⟨5595772505961086917615637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3730515003974057945077091 5595772505961086917615637)
                  ·
                    refine ⟨262301836216925949263233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5595772505961086917615637 262301836216925949263233)
                    ·
                      rfl

theorem cell23_1532493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_1532493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532493 prefixEnd_1532493 := by exact prefixLift 1532493
  have htrace : WordTrace (prefixWord ++ tailWord_1532493) baseStart_1532493 baseEnd_1532493 := by
    simpa [prefixWord, tailWord_1532493, baseEnd_1532493] using wordTrace_append hprefix tailTrace_1532493
  have hstable : (prefixWord ++ tailWord_1532493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532493).length < 2 ^ (prefixWord ++ tailWord_1532493).sum := by decide
  have hdescent : baseEnd_1532493 < baseStart_1532493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532500 : List Nat := [2, 4, 1, 1, 1, 3, 1, 1, 5, 2, 2]
def baseStart_1532500 : Nat := 118140960795 + 1532500 * 2 ^ 59
def prefixEnd_1532500 : Nat := 4983230072969 + 3 ^ 40 * 1532500 * 2
def baseEnd_1532500 : Nat := 786909103015359320402167

theorem tailTrace_1532500 : CollatzResearch.WordTrace tailWord_1532500 prefixEnd_1532500 786909103015359320402167 := by
  unfold tailWord_1532500
  simp only [CollatzResearch.WordTrace]
  refine ⟨27947433474010852503853477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37263244632014470005137969 27947433474010852503853477)
  ·
    refine ⟨5240143776377034844472527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27947433474010852503853477 5240143776377034844472527)
    ·
      refine ⟨7860215664565552266708791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5240143776377034844472527 7860215664565552266708791)
      ·
        refine ⟨11790323496848328400063187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7860215664565552266708791 11790323496848328400063187)
        ·
          refine ⟨17685485245272492600094781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11790323496848328400063187 17685485245272492600094781)
          ·
            refine ⟨6632056966977184725035543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17685485245272492600094781 6632056966977184725035543)
            ·
              refine ⟨9948085450465777087553315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6632056966977184725035543 9948085450465777087553315)
              ·
                refine ⟨14922128175698665631329973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9948085450465777087553315 14922128175698665631329973)
                ·
                  refine ⟨1398949516471749902937185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14922128175698665631329973 1398949516471749902937185)
                  ·
                    refine ⟨1049212137353812427202889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1398949516471749902937185 1049212137353812427202889)
                    ·
                      refine ⟨786909103015359320402167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1049212137353812427202889 786909103015359320402167)
                      ·
                        rfl

theorem cell23_1532500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_1532500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532500 prefixEnd_1532500 := by exact prefixLift 1532500
  have htrace : WordTrace (prefixWord ++ tailWord_1532500) baseStart_1532500 baseEnd_1532500 := by
    simpa [prefixWord, tailWord_1532500, baseEnd_1532500] using wordTrace_append hprefix tailTrace_1532500
  have hstable : (prefixWord ++ tailWord_1532500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532500).length < 2 ^ (prefixWord ++ tailWord_1532500).sum := by decide
  have hdescent : baseEnd_1532500 < baseStart_1532500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532503 : List Nat := [1, 1, 3, 2, 2, 2, 2, 4, 1, 2, 3]
def baseStart_1532503 : Nat := 118140960795 + 1532503 * 2 ^ 59
def prefixEnd_1532503 : Nat := 4983230072969 + 3 ^ 40 * 1532503 * 2
def baseEnd_1532503 : Nat := 786910643457322808664653

theorem tailTrace_1532503 : CollatzResearch.WordTrace tailWord_1532503 prefixEnd_1532503 786910643457322808664653 := by
  unfold tailWord_1532503
  simp only [CollatzResearch.WordTrace]
  refine ⟨55894976367010836520066163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37263317578007224346710775 55894976367010836520066163)
  ·
    refine ⟨83842464550516254780099245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55894976367010836520066163 83842464550516254780099245)
    ·
      refine ⟨31440924206443595542537217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83842464550516254780099245 31440924206443595542537217)
      ·
        refine ⟨23580693154832696656902913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31440924206443595542537217 23580693154832696656902913)
        ·
          refine ⟨17685519866124522492677185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23580693154832696656902913 17685519866124522492677185)
          ·
            refine ⟨13264139899593391869507889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17685519866124522492677185 13264139899593391869507889)
            ·
              refine ⟨9948104924695043902130917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13264139899593391869507889 9948104924695043902130917)
              ·
                refine ⟨1865269673380320731649547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9948104924695043902130917 1865269673380320731649547)
                ·
                  refine ⟨2797904510070481097474321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1865269673380320731649547 2797904510070481097474321)
                  ·
                    refine ⟨2098428382552860823105741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2797904510070481097474321 2098428382552860823105741)
                    ·
                      refine ⟨786910643457322808664653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2098428382552860823105741 786910643457322808664653)
                      ·
                        rfl

theorem cell23_1532503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 2, 3].length) (baseStart_1532503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532503 prefixEnd_1532503 := by exact prefixLift 1532503
  have htrace : WordTrace (prefixWord ++ tailWord_1532503) baseStart_1532503 baseEnd_1532503 := by
    simpa [prefixWord, tailWord_1532503, baseEnd_1532503] using wordTrace_append hprefix tailTrace_1532503
  have hstable : (prefixWord ++ tailWord_1532503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532503).length < 2 ^ (prefixWord ++ tailWord_1532503).sum := by decide
  have hdescent : baseEnd_1532503 < baseStart_1532503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532514 : List Nat := [3, 3, 2, 3, 1, 2, 2, 1, 1, 5]
def baseStart_1532514 : Nat := 118140960795 + 1532514 * 2 ^ 59
def prefixEnd_1532514 : Nat := 4983230072969 + 3 ^ 40 * 1532514 * 2
def baseEnd_1532514 : Nat := 262305430581507421875701

theorem tailTrace_1532514 : CollatzResearch.WordTrace tailWord_1532514 prefixEnd_1532514 262305430581507421875701 := by
  unfold tailWord_1532514
  simp only [CollatzResearch.WordTrace]
  refine ⟨13973844392492746349679149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37263585046647323599144397 13973844392492746349679149)
  ·
    refine ⟨5240191647184779881129681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13973844392492746349679149 5240191647184779881129681)
    ·
      refine ⟨3930143735388584910847261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5240191647184779881129681 3930143735388584910847261)
      ·
        refine ⟨1473803900770719341567723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3930143735388584910847261 1473803900770719341567723)
        ·
          refine ⟨2210705851156079012351585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1473803900770719341567723 2210705851156079012351585)
          ·
            refine ⟨1658029388367059259263689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2210705851156079012351585 1658029388367059259263689)
            ·
              refine ⟨1243522041275294444447767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1658029388367059259263689 1243522041275294444447767)
              ·
                refine ⟨1865283061912941666671651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1243522041275294444447767 1865283061912941666671651)
                ·
                  refine ⟨2797924592869412500007477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1865283061912941666671651 2797924592869412500007477)
                  ·
                    refine ⟨262305430581507421875701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2797924592869412500007477 262305430581507421875701)
                    ·
                      rfl

theorem cell23_1532514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_1532514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532514 prefixEnd_1532514 := by exact prefixLift 1532514
  have htrace : WordTrace (prefixWord ++ tailWord_1532514) baseStart_1532514 baseEnd_1532514 := by
    simpa [prefixWord, tailWord_1532514, baseEnd_1532514] using wordTrace_append hprefix tailTrace_1532514
  have hstable : (prefixWord ++ tailWord_1532514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532514).length < 2 ^ (prefixWord ++ tailWord_1532514).sum := by decide
  have hdescent : baseEnd_1532514 < baseStart_1532514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532517 : List Nat := [1, 3, 1, 3, 4, 2, 2, 1, 1, 1, 4]
def baseStart_1532517 : Nat := 118140960795 + 1532517 * 2 ^ 59
def prefixEnd_1532517 : Nat := 4983230072969 + 3 ^ 40 * 1532517 * 2
def baseEnd_1532517 : Nat := 786917832186485753889589

theorem tailTrace_1532517 : CollatzResearch.WordTrace tailWord_1532517 prefixEnd_1532517 786917832186485753889589 := by
  unfold tailWord_1532517
  simp only [CollatzResearch.WordTrace]
  refine ⟨55895486988960116911075805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37263657992640077940717203 55895486988960116911075805)
  ·
    refine ⟨20960807620860043841653427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55895486988960116911075805 20960807620860043841653427)
    ·
      refine ⟨31441211431290065762480141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20960807620860043841653427 31441211431290065762480141)
      ·
        refine ⟨11790454286733774660930053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31441211431290065762480141 11790454286733774660930053)
        ·
          refine ⟨2210710178762582748924385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11790454286733774660930053 2210710178762582748924385)
          ·
            refine ⟨1658032634071937061693289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2210710178762582748924385 1658032634071937061693289)
            ·
              refine ⟨1243524475553952796269967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1658032634071937061693289 1243524475553952796269967)
              ·
                refine ⟨1865286713330929194404951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1243524475553952796269967 1865286713330929194404951)
                ·
                  refine ⟨2797930069996393791607427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1865286713330929194404951 2797930069996393791607427)
                  ·
                    refine ⟨4196895104994590687411141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2797930069996393791607427 4196895104994590687411141)
                    ·
                      refine ⟨786917832186485753889589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4196895104994590687411141 786917832186485753889589)
                      ·
                        rfl

theorem cell23_1532517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_1532517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532517 prefixEnd_1532517 := by exact prefixLift 1532517
  have htrace : WordTrace (prefixWord ++ tailWord_1532517) baseStart_1532517 baseEnd_1532517 := by
    simpa [prefixWord, tailWord_1532517, baseEnd_1532517] using wordTrace_append hprefix tailTrace_1532517
  have hstable : (prefixWord ++ tailWord_1532517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532517).length < 2 ^ (prefixWord ++ tailWord_1532517).sum := by decide
  have hdescent : baseEnd_1532517 < baseStart_1532517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532534 : List Nat := [5, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2]
def baseStart_1532534 : Nat := 118140960795 + 1532534 * 2 ^ 59
def prefixEnd_1532534 : Nat := 4983230072969 + 3 ^ 40 * 1532534 * 2
def baseEnd_1532534 : Nat := 786926561357612187377011

theorem tailTrace_1532534 : CollatzResearch.WordTrace tailWord_1532534 prefixEnd_1532534 786926561357612187377011 := by
  unfold tailWord_1532534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3493506689368658050902791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37264071353265685876296437 3493506689368658050902791)
  ·
    refine ⟨5240260034052987076354187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3493506689368658050902791 5240260034052987076354187)
    ·
      refine ⟨7860390051079480614531281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5240260034052987076354187 7860390051079480614531281)
      ·
        refine ⟨5895292538309610460898461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7860390051079480614531281 5895292538309610460898461)
        ·
          refine ⟨2210734701866103922836923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5895292538309610460898461 2210734701866103922836923)
          ·
            refine ⟨3316102052799155884255385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2210734701866103922836923 3316102052799155884255385)
            ·
              refine ⟨2487076539599366913191539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3316102052799155884255385 2487076539599366913191539)
              ·
                refine ⟨3730614809399050369787309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2487076539599366913191539 3730614809399050369787309)
                ·
                  refine ⟨1398980553524643888670241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3730614809399050369787309 1398980553524643888670241)
                  ·
                    refine ⟨1049235415143482916502681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1398980553524643888670241 1049235415143482916502681)
                    ·
                      refine ⟨786926561357612187377011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1049235415143482916502681 786926561357612187377011)
                      ·
                        rfl

theorem cell23_1532534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_1532534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532534 prefixEnd_1532534 := by exact prefixLift 1532534
  have htrace : WordTrace (prefixWord ++ tailWord_1532534) baseStart_1532534 baseEnd_1532534 := by
    simpa [prefixWord, tailWord_1532534, baseEnd_1532534] using wordTrace_append hprefix tailTrace_1532534
  have hstable : (prefixWord ++ tailWord_1532534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532534).length < 2 ^ (prefixWord ++ tailWord_1532534).sum := by decide
  have hdescent : baseEnd_1532534 < baseStart_1532534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532543 : List Nat := [1, 1, 2, 2, 1, 1, 1, 6, 3, 3, 2]
def baseStart_1532543 : Nat := 118140960795 + 1532543 * 2 ^ 59
def prefixEnd_1532543 : Nat := 4983230072969 + 3 ^ 40 * 1532543 * 2
def baseEnd_1532543 : Nat := 786931182683502652164469

theorem tailTrace_1532543 : CollatzResearch.WordTrace tailWord_1532543 prefixEnd_1532543 786931182683502652164469 := by
  unfold tailWord_1532543
  simp only [CollatzResearch.WordTrace]
  refine ⟨55896435286865923351522283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37264290191243948901014855 55896435286865923351522283)
  ·
    refine ⟨83844652930298885027283425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55896435286865923351522283 83844652930298885027283425)
    ·
      refine ⟨62883489697724163770462569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83844652930298885027283425 62883489697724163770462569)
      ·
        refine ⟨47162617273293122827846927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62883489697724163770462569 47162617273293122827846927)
        ·
          refine ⟨70743925909939684241770391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47162617273293122827846927 70743925909939684241770391)
          ·
            refine ⟨106115888864909526362655587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70743925909939684241770391 106115888864909526362655587)
            ·
              refine ⟨159173833297364289543983381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106115888864909526362655587 159173833297364289543983381)
              ·
                refine ⟨7461273435813951072374221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 159173833297364289543983381 7461273435813951072374221)
                ·
                  refine ⟨2797977538430231652140333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7461273435813951072374221 2797977538430231652140333)
                  ·
                    refine ⟨1049241576911336869552625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2797977538430231652140333 1049241576911336869552625)
                    ·
                      refine ⟨786931182683502652164469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1049241576911336869552625 786931182683502652164469)
                      ·
                        rfl

theorem cell23_1532543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 3, 2].length) (baseStart_1532543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532543 prefixEnd_1532543 := by exact prefixLift 1532543
  have htrace : WordTrace (prefixWord ++ tailWord_1532543) baseStart_1532543 baseEnd_1532543 := by
    simpa [prefixWord, tailWord_1532543, baseEnd_1532543] using wordTrace_append hprefix tailTrace_1532543
  have hstable : (prefixWord ++ tailWord_1532543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532543).length < 2 ^ (prefixWord ++ tailWord_1532543).sum := by decide
  have hdescent : baseEnd_1532543 < baseStart_1532543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532607 : List Nat := [1, 1, 2, 2, 2, 5, 1, 3, 2, 2, 2]
def baseStart_1532607 : Nat := 118140960795 + 1532607 * 2 ^ 59
def prefixEnd_1532607 : Nat := 4983230072969 + 3 ^ 40 * 1532607 * 2
def baseEnd_1532607 : Nat := 786964045445390401764175

theorem tailTrace_1532607 : CollatzResearch.WordTrace tailWord_1532607 prefixEnd_1532607 786964045445390401764175 := by
  unfold tailWord_1532607
  simp only [CollatzResearch.WordTrace]
  refine ⟨55898769558634062281852075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37265846372422708187901383 55898769558634062281852075)
  ·
    refine ⟨83848154337951093422778113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55898769558634062281852075 83848154337951093422778113)
    ·
      refine ⟨62886115753463320067083585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83848154337951093422778113 62886115753463320067083585)
      ·
        refine ⟨47164586815097490050312689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62886115753463320067083585 47164586815097490050312689)
        ·
          refine ⟨35373440111323117537734517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47164586815097490050312689 35373440111323117537734517)
          ·
            refine ⟨3316260010436542269162611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35373440111323117537734517 3316260010436542269162611)
            ·
              refine ⟨4974390015654813403743917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3316260010436542269162611 4974390015654813403743917)
              ·
                refine ⟨1865396255870555026403969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4974390015654813403743917 1865396255870555026403969)
                ·
                  refine ⟨1399047191902916269802977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1865396255870555026403969 1399047191902916269802977)
                  ·
                    refine ⟨1049285393927187202352233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1399047191902916269802977 1049285393927187202352233)
                    ·
                      refine ⟨786964045445390401764175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1049285393927187202352233 786964045445390401764175)
                      ·
                        rfl

theorem cell23_1532607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 2, 2, 2].length) (baseStart_1532607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532607 prefixEnd_1532607 := by exact prefixLift 1532607
  have htrace : WordTrace (prefixWord ++ tailWord_1532607) baseStart_1532607 baseEnd_1532607 := by
    simpa [prefixWord, tailWord_1532607, baseEnd_1532607] using wordTrace_append hprefix tailTrace_1532607
  have hstable : (prefixWord ++ tailWord_1532607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532607).length < 2 ^ (prefixWord ++ tailWord_1532607).sum := by decide
  have hdescent : baseEnd_1532607 < baseStart_1532607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532653 : List Nat := [1, 5, 1, 2, 1, 1, 1, 3, 1, 2, 5]
def baseStart_1532653 : Nat := 118140960795 + 1532653 * 2 ^ 59
def prefixEnd_1532653 : Nat := 4983230072969 + 3 ^ 40 * 1532653 * 2
def baseEnd_1532653 : Nat := 786987665555497221788963

theorem tailTrace_1532653 : CollatzResearch.WordTrace tailWord_1532653 prefixEnd_1532653 786987665555497221788963 := by
  unfold tailWord_1532653
  simp only [CollatzResearch.WordTrace]
  refine ⟨55900447316467412138026613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37266964877644941425351075 55900447316467412138026613)
  ·
    refine ⟨5240666935918819887939995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55900447316467412138026613 5240666935918819887939995)
    ·
      refine ⟨7861000403878229831909993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5240666935918819887939995 7861000403878229831909993)
      ·
        refine ⟨5895750302908672373932495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7861000403878229831909993 5895750302908672373932495)
        ·
          refine ⟨8843625454363008560898743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5895750302908672373932495 8843625454363008560898743)
          ·
            refine ⟨13265438181544512841348115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8843625454363008560898743 13265438181544512841348115)
            ·
              refine ⟨19898157272316769262022173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13265438181544512841348115 19898157272316769262022173)
              ·
                refine ⟨7461808977118788473258315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19898157272316769262022173 7461808977118788473258315)
                ·
                  refine ⟨11192713465678182709887473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7461808977118788473258315 11192713465678182709887473)
                  ·
                    refine ⟨8394535099258637032415605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11192713465678182709887473 8394535099258637032415605)
                    ·
                      refine ⟨786987665555497221788963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8394535099258637032415605 786987665555497221788963)
                      ·
                        rfl

theorem cell23_1532653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_1532653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532653 prefixEnd_1532653 := by exact prefixLift 1532653
  have htrace : WordTrace (prefixWord ++ tailWord_1532653) baseStart_1532653 baseEnd_1532653 := by
    simpa [prefixWord, tailWord_1532653, baseEnd_1532653] using wordTrace_append hprefix tailTrace_1532653
  have hstable : (prefixWord ++ tailWord_1532653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532653).length < 2 ^ (prefixWord ++ tailWord_1532653).sum := by decide
  have hdescent : baseEnd_1532653 < baseStart_1532653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532680 : List Nat := [2, 1, 3, 2, 2, 2, 3, 1, 2, 1, 4]
def baseStart_1532680 : Nat := 118140960795 + 1532680 * 2 ^ 59
def prefixEnd_1532680 : Nat := 4983230072969 + 3 ^ 40 * 1532680 * 2
def baseEnd_1532680 : Nat := 787001529533168616151339

theorem tailTrace_1532680 : CollatzResearch.WordTrace tailWord_1532680 prefixEnd_1532680 787001529533168616151339 := by
  unfold tailWord_1532680
  simp only [CollatzResearch.WordTrace]
  refine ⟨27950716043684797874629747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37267621391579730499506329 27950716043684797874629747)
  ·
    refine ⟨41926074065527196811944621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27950716043684797874629747 41926074065527196811944621)
    ·
      refine ⟨15722277774572698804479233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41926074065527196811944621 15722277774572698804479233)
      ·
        refine ⟨11791708330929524103359425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15722277774572698804479233 11791708330929524103359425)
        ·
          refine ⟨8843781248197143077519569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11791708330929524103359425 8843781248197143077519569)
          ·
            refine ⟨6632835936147857308139677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8843781248197143077519569 6632835936147857308139677)
            ·
              refine ⟨2487313476055446490552379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6632835936147857308139677 2487313476055446490552379)
              ·
                refine ⟨3730970214083169735828569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2487313476055446490552379 3730970214083169735828569)
                ·
                  refine ⟨2798227660562377301871427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3730970214083169735828569 2798227660562377301871427)
                  ·
                    refine ⟨4197341490843565952807141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2798227660562377301871427 4197341490843565952807141)
                    ·
                      refine ⟨787001529533168616151339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4197341490843565952807141 787001529533168616151339)
                      ·
                        rfl

theorem cell23_1532680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_1532680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532680 prefixEnd_1532680 := by exact prefixLift 1532680
  have htrace : WordTrace (prefixWord ++ tailWord_1532680) baseStart_1532680 baseEnd_1532680 := by
    simpa [prefixWord, tailWord_1532680, baseEnd_1532680] using wordTrace_append hprefix tailTrace_1532680
  have hstable : (prefixWord ++ tailWord_1532680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532680).length < 2 ^ (prefixWord ++ tailWord_1532680).sum := by decide
  have hdescent : baseEnd_1532680 < baseStart_1532680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532703 : List Nat := [1, 1, 2, 4, 2, 3, 1, 1, 8]
def baseStart_1532703 : Nat := 118140960795 + 1532703 * 2 ^ 59
def prefixEnd_1532703 : Nat := 4983230072969 + 3 ^ 40 * 1532703 * 2
def baseEnd_1532703 : Nat := 87445926620913558462637

theorem tailTrace_1532703 : CollatzResearch.WordTrace tailWord_1532703 prefixEnd_1532703 87445926620913558462637 := by
  unfold tailWord_1532703
  simp only [CollatzResearch.WordTrace]
  refine ⟨55902270966286270677346763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37268180644190847118231175 55902270966286270677346763)
  ·
    refine ⟨83853406449429406016020145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55902270966286270677346763 83853406449429406016020145)
    ·
      refine ⟨62890054837072054512015109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83853406449429406016020145 62890054837072054512015109)
      ·
        refine ⟨11791885281951010221002833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62890054837072054512015109 11791885281951010221002833)
        ·
          refine ⟨8843913961463257665752125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11791885281951010221002833 8843913961463257665752125)
          ·
            refine ⟨3316467735548721624657047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8843913961463257665752125 3316467735548721624657047)
            ·
              refine ⟨4974701603323082436985571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3316467735548721624657047 4974701603323082436985571)
              ·
                refine ⟨7462052404984623655478357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4974701603323082436985571 7462052404984623655478357)
                ·
                  refine ⟨87445926620913558462637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7462052404984623655478357 87445926620913558462637)
                  ·
                    rfl

theorem cell23_1532703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 8].length) (baseStart_1532703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532703 prefixEnd_1532703 := by exact prefixLift 1532703
  have htrace : WordTrace (prefixWord ++ tailWord_1532703) baseStart_1532703 baseEnd_1532703 := by
    simpa [prefixWord, tailWord_1532703, baseEnd_1532703] using wordTrace_append hprefix tailTrace_1532703
  have hstable : (prefixWord ++ tailWord_1532703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532703).length < 2 ^ (prefixWord ++ tailWord_1532703).sum := by decide
  have hdescent : baseEnd_1532703 < baseStart_1532703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532757 : List Nat := [1, 3, 2, 2, 2, 1, 3, 2, 2, 3, 2]
def baseStart_1532757 : Nat := 118140960795 + 1532757 * 2 ^ 59
def prefixEnd_1532757 : Nat := 4983230072969 + 3 ^ 40 * 1532757 * 2
def baseEnd_1532757 : Nat := 787041067543564814888485

theorem tailTrace_1532757 : CollatzResearch.WordTrace tailWord_1532757 prefixEnd_1532757 787041067543564814888485 := by
  unfold tailWord_1532757
  simp only [CollatzResearch.WordTrace]
  refine ⟨55904240508090637899812525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37269493672060425266541683 55904240508090637899812525)
  ·
    refine ⟨20964090190533989212429697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55904240508090637899812525 20964090190533989212429697)
    ·
      refine ⟨15723067642900491909322273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20964090190533989212429697 15723067642900491909322273)
      ·
        refine ⟨11792300732175368931991705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15723067642900491909322273 11792300732175368931991705)
        ·
          refine ⟨8844225549131526698993779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11792300732175368931991705 8844225549131526698993779)
          ·
            refine ⟨13266338323697290048490669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8844225549131526698993779 13266338323697290048490669)
            ·
              refine ⟨4974876871386483768184001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13266338323697290048490669 4974876871386483768184001)
              ·
                refine ⟨3731157653539862826138001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4974876871386483768184001 3731157653539862826138001)
                ·
                  refine ⟨2798368240154897119603501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3731157653539862826138001 2798368240154897119603501)
                  ·
                    refine ⟨1049388090058086419851313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2798368240154897119603501 1049388090058086419851313)
                    ·
                      refine ⟨787041067543564814888485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1049388090058086419851313 787041067543564814888485)
                      ·
                        rfl

theorem cell23_1532757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_1532757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532757 prefixEnd_1532757 := by exact prefixLift 1532757
  have htrace : WordTrace (prefixWord ++ tailWord_1532757) baseStart_1532757 baseEnd_1532757 := by
    simpa [prefixWord, tailWord_1532757, baseEnd_1532757] using wordTrace_append hprefix tailTrace_1532757
  have hstable : (prefixWord ++ tailWord_1532757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532757).length < 2 ^ (prefixWord ++ tailWord_1532757).sum := by decide
  have hdescent : baseEnd_1532757 < baseStart_1532757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532764 : List Nat := [2, 2, 4, 2, 1, 1, 3, 1, 3, 1, 3]
def baseStart_1532764 : Nat := 118140960795 + 1532764 * 2 ^ 59
def prefixEnd_1532764 : Nat := 4983230072969 + 3 ^ 40 * 1532764 * 2
def baseEnd_1532764 : Nat := 787044661908146287500953

theorem tailTrace_1532764 : CollatzResearch.WordTrace tailWord_1532764 prefixEnd_1532764 787044661908146287500953 := by
  unfold tailWord_1532764
  simp only [CollatzResearch.WordTrace]
  refine ⟨27952247909532639047658673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37269663879376852063544897 27952247909532639047658673)
  ·
    refine ⟨20964185932149479285744005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27952247909532639047658673 20964185932149479285744005)
    ·
      refine ⟨3930784862278027366077001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20964185932149479285744005 3930784862278027366077001)
      ·
        refine ⟨2948088646708520524557751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3930784862278027366077001 2948088646708520524557751)
        ·
          refine ⟨4422132970062780786836627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2948088646708520524557751 4422132970062780786836627)
          ·
            refine ⟨6633199455094171180254941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4422132970062780786836627 6633199455094171180254941)
            ·
              refine ⟨2487449795660314192595603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6633199455094171180254941 2487449795660314192595603)
              ·
                refine ⟨3731174693490471288893405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2487449795660314192595603 3731174693490471288893405)
                ·
                  refine ⟨1399190510058926733335027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3731174693490471288893405 1399190510058926733335027)
                  ·
                    refine ⟨2098785765088390100002541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1399190510058926733335027 2098785765088390100002541)
                    ·
                      refine ⟨787044661908146287500953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2098785765088390100002541 787044661908146287500953)
                      ·
                        rfl

theorem cell23_1532764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_1532764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532764 prefixEnd_1532764 := by exact prefixLift 1532764
  have htrace : WordTrace (prefixWord ++ tailWord_1532764) baseStart_1532764 baseEnd_1532764 := by
    simpa [prefixWord, tailWord_1532764, baseEnd_1532764] using wordTrace_append hprefix tailTrace_1532764
  have hstable : (prefixWord ++ tailWord_1532764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532764).length < 2 ^ (prefixWord ++ tailWord_1532764).sum := by decide
  have hdescent : baseEnd_1532764 < baseStart_1532764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532783 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 4]
def baseStart_1532783 : Nat := 118140960795 + 1532783 * 2 ^ 59
def prefixEnd_1532783 : Nat := 4983230072969 + 3 ^ 40 * 1532783 * 2
def baseEnd_1532783 : Nat := 787054418040581713163365

theorem tailTrace_1532783 : CollatzResearch.WordTrace tailWord_1532783 prefixEnd_1532783 787054418040581713163365 := by
  unfold tailWord_1532783
  simp only [CollatzResearch.WordTrace]
  refine ⟨55905188805996444340259003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37270125870664296226839335 55905188805996444340259003)
  ·
    refine ⟨83857783208994666510388505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55905188805996444340259003 83857783208994666510388505)
    ·
      refine ⟨62893337406745999882791379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83857783208994666510388505 62893337406745999882791379)
      ·
        refine ⟨94340006110118999824187069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62893337406745999882791379 94340006110118999824187069)
        ·
          refine ⟨35377502291294624934070151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94340006110118999824187069 35377502291294624934070151)
          ·
            refine ⟨53066253436941937401105227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35377502291294624934070151 53066253436941937401105227)
            ·
              refine ⟨79599380155412906101657841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53066253436941937401105227 79599380155412906101657841)
              ·
                refine ⟨59699535116559679576243381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79599380155412906101657841 59699535116559679576243381)
                ·
                  refine ⟨5596831417177469960272817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59699535116559679576243381 5596831417177469960272817)
                  ·
                    refine ⟨4197623562883102470204613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5596831417177469960272817 4197623562883102470204613)
                    ·
                      refine ⟨787054418040581713163365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4197623562883102470204613 787054418040581713163365)
                      ·
                        rfl

theorem cell23_1532783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 4].length) (baseStart_1532783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532783 prefixEnd_1532783 := by exact prefixLift 1532783
  have htrace : WordTrace (prefixWord ++ tailWord_1532783) baseStart_1532783 baseEnd_1532783 := by
    simpa [prefixWord, tailWord_1532783, baseEnd_1532783] using wordTrace_append hprefix tailTrace_1532783
  have hstable : (prefixWord ++ tailWord_1532783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532783).length < 2 ^ (prefixWord ++ tailWord_1532783).sum := by decide
  have hdescent : baseEnd_1532783 < baseStart_1532783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532787 : List Nat := [1, 1, 1, 2, 2, 1, 4, 4, 3, 2, 2]
def baseStart_1532787 : Nat := 118140960795 + 1532787 * 2 ^ 59
def prefixEnd_1532787 : Nat := 4983230072969 + 3 ^ 40 * 1532787 * 2
def baseEnd_1532787 : Nat := 787056471963199697513347

theorem tailTrace_1532787 : CollatzResearch.WordTrace tailWord_1532787 prefixEnd_1532787 787056471963199697513347 := by
  unfold tailWord_1532787
  simp only [CollatzResearch.WordTrace]
  refine ⟨55905334697981953023404615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37270223131987968682269743 55905334697981953023404615)
  ·
    refine ⟨83858002046972929535106923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55905334697981953023404615 83858002046972929535106923)
    ·
      refine ⟨125787003070459394302660385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83858002046972929535106923 125787003070459394302660385)
      ·
        refine ⟨94340252302844545726995289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125787003070459394302660385 94340252302844545726995289)
        ·
          refine ⟨70755189227133409295246467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94340252302844545726995289 70755189227133409295246467)
          ·
            refine ⟨106132783840700113942869701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70755189227133409295246467 106132783840700113942869701)
            ·
              refine ⟨19899896970131271364288069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106132783840700113942869701 19899896970131271364288069)
              ·
                refine ⟨3731230681899613380804013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19899896970131271364288069 3731230681899613380804013)
                ·
                  refine ⟨1399211505712355017801505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3731230681899613380804013 1399211505712355017801505)
                  ·
                    refine ⟨1049408629284266263351129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1399211505712355017801505 1049408629284266263351129)
                    ·
                      refine ⟨787056471963199697513347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1049408629284266263351129 787056471963199697513347)
                      ·
                        rfl

theorem cell23_1532787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 3, 2, 2].length) (baseStart_1532787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532787 prefixEnd_1532787 := by exact prefixLift 1532787
  have htrace : WordTrace (prefixWord ++ tailWord_1532787) baseStart_1532787 baseEnd_1532787 := by
    simpa [prefixWord, tailWord_1532787, baseEnd_1532787] using wordTrace_append hprefix tailTrace_1532787
  have hstable : (prefixWord ++ tailWord_1532787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532787).length < 2 ^ (prefixWord ++ tailWord_1532787).sum := by decide
  have hdescent : baseEnd_1532787 < baseStart_1532787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532793 : List Nat := [1, 2, 1, 3, 2, 3, 2, 9]
def baseStart_1532793 : Nat := 118140960795 + 1532793 * 2 ^ 59
def prefixEnd_1532793 : Nat := 4983230072969 + 3 ^ 40 * 1532793 * 2
def baseEnd_1532793 : Nat := 29150353809152839779197

theorem tailTrace_1532793 : CollatzResearch.WordTrace tailWord_1532793 prefixEnd_1532793 29150353809152839779197 := by
  unfold tailWord_1532793
  simp only [CollatzResearch.WordTrace]
  refine ⟨55905553535960216048123033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37270369023973477365415355 55905553535960216048123033)
  ·
    refine ⟨41929165151970162036092275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55905553535960216048123033 41929165151970162036092275)
    ·
      refine ⟨62893747727955243054138413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41929165151970162036092275 62893747727955243054138413)
      ·
        refine ⟨23585155397983216145301905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62893747727955243054138413 23585155397983216145301905)
        ·
          refine ⟨17688866548487412108976429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23585155397983216145301905 17688866548487412108976429)
          ·
            refine ⟨6633324955682779540866161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17688866548487412108976429 6633324955682779540866161)
            ·
              refine ⟨4974993716762084655649621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6633324955682779540866161 4974993716762084655649621)
              ·
                refine ⟨29150353809152839779197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4974993716762084655649621 29150353809152839779197)
                ·
                  rfl

theorem cell23_1532793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 9].length) (baseStart_1532793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532793 prefixEnd_1532793 := by exact prefixLift 1532793
  have htrace : WordTrace (prefixWord ++ tailWord_1532793) baseStart_1532793 baseEnd_1532793 := by
    simpa [prefixWord, tailWord_1532793, baseEnd_1532793] using wordTrace_append hprefix tailTrace_1532793
  have hstable : (prefixWord ++ tailWord_1532793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532793).length < 2 ^ (prefixWord ++ tailWord_1532793).sum := by decide
  have hdescent : baseEnd_1532793 < baseStart_1532793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532807 : List Nat := [1, 1, 4, 2, 3, 3, 1, 1, 1, 1, 5]
def baseStart_1532807 : Nat := 118140960795 + 1532807 * 2 ^ 59
def prefixEnd_1532807 : Nat := 4983230072969 + 3 ^ 40 * 1532807 * 2
def baseEnd_1532807 : Nat := 787066741576289619263255

theorem tailTrace_1532807 : CollatzResearch.WordTrace tailWord_1532807 prefixEnd_1532807 787066741576289619263255 := by
  unfold tailWord_1532807
  simp only [CollatzResearch.WordTrace]
  refine ⟨55906064157909496439132675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37270709438606330959421783 55906064157909496439132675)
  ·
    refine ⟨83859096236864244658699013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55906064157909496439132675 83859096236864244658699013)
    ·
      refine ⟨15723580544412045873506065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83859096236864244658699013 15723580544412045873506065)
      ·
        refine ⟨11792685408309034405129549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15723580544412045873506065 11792685408309034405129549)
        ·
          refine ⟨4422257028115887901923581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11792685408309034405129549 4422257028115887901923581)
          ·
            refine ⟨1658346385543457963221343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4422257028115887901923581 1658346385543457963221343)
            ·
              refine ⟨2487519578315186944832015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1658346385543457963221343 2487519578315186944832015)
              ·
                refine ⟨3731279367472780417248023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2487519578315186944832015 3731279367472780417248023)
                ·
                  refine ⟨5596919051209170625872035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3731279367472780417248023 5596919051209170625872035)
                  ·
                    refine ⟨8395378576813755938808053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5596919051209170625872035 8395378576813755938808053)
                    ·
                      refine ⟨787066741576289619263255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8395378576813755938808053 787066741576289619263255)
                      ·
                        rfl

theorem cell23_1532807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_1532807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532807 prefixEnd_1532807 := by exact prefixLift 1532807
  have htrace : WordTrace (prefixWord ++ tailWord_1532807) baseStart_1532807 baseEnd_1532807 := by
    simpa [prefixWord, tailWord_1532807, baseEnd_1532807] using wordTrace_append hprefix tailTrace_1532807
  have hstable : (prefixWord ++ tailWord_1532807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532807).length < 2 ^ (prefixWord ++ tailWord_1532807).sum := by decide
  have hdescent : baseEnd_1532807 < baseStart_1532807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532821 : List Nat := [1, 3, 2, 1, 1, 5, 1, 4, 1, 2, 2]
def baseStart_1532821 : Nat := 118140960795 + 1532821 * 2 ^ 59
def prefixEnd_1532821 : Nat := 4983230072969 + 3 ^ 40 * 1532821 * 2
def baseEnd_1532821 : Nat := 787073930305452564488191

theorem tailTrace_1532821 : CollatzResearch.WordTrace tailWord_1532821 prefixEnd_1532821 787073930305452564488191 := by
  unfold tailWord_1532821
  simp only [CollatzResearch.WordTrace]
  refine ⟨55906574779858776830142317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37271049853239184553428211 55906574779858776830142317)
  ·
    refine ⟨20964965542447041311303369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55906574779858776830142317 20964965542447041311303369)
    ·
      refine ⟨15723724156835280983477527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20964965542447041311303369 15723724156835280983477527)
      ·
        refine ⟨23585586235252921475216291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15723724156835280983477527 23585586235252921475216291)
        ·
          refine ⟨35378379352879382212824437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23585586235252921475216291 35378379352879382212824437)
          ·
            refine ⟨3316723064332442082452291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35378379352879382212824437 3316723064332442082452291)
            ·
              refine ⟨4975084596498663123678437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3316723064332442082452291 4975084596498663123678437)
              ·
                refine ⟨932828361843499335689707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4975084596498663123678437 932828361843499335689707)
                ·
                  refine ⟨1399242542765249003534561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 932828361843499335689707 1399242542765249003534561)
                  ·
                    refine ⟨1049431907073936752650921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1399242542765249003534561 1049431907073936752650921)
                    ·
                      refine ⟨787073930305452564488191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1049431907073936752650921 787073930305452564488191)
                      ·
                        rfl

theorem cell23_1532821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 4, 1, 2, 2].length) (baseStart_1532821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532821 prefixEnd_1532821 := by exact prefixLift 1532821
  have htrace : WordTrace (prefixWord ++ tailWord_1532821) baseStart_1532821 baseEnd_1532821 := by
    simpa [prefixWord, tailWord_1532821, baseEnd_1532821] using wordTrace_append hprefix tailTrace_1532821
  have hstable : (prefixWord ++ tailWord_1532821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532821).length < 2 ^ (prefixWord ++ tailWord_1532821).sum := by decide
  have hdescent : baseEnd_1532821 < baseStart_1532821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532823 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 1, 9]
def baseStart_1532823 : Nat := 118140960795 + 1532823 * 2 ^ 59
def prefixEnd_1532823 : Nat := 4983230072969 + 3 ^ 40 * 1532823 * 2
def baseEnd_1532823 : Nat := 262358319088920518887727

theorem tailTrace_1532823 : CollatzResearch.WordTrace tailWord_1532823 prefixEnd_1532823 262358319088920518887727 := by
  unfold tailWord_1532823
  simp only [CollatzResearch.WordTrace]
  refine ⟨55906647725851531171715123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37271098483901020781143415 55906647725851531171715123)
  ·
    refine ⟨83859971588777296757572685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55906647725851531171715123 83859971588777296757572685)
    ·
      refine ⟨31447489345791486284089757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83859971588777296757572685 31447489345791486284089757)
      ·
        refine ⟨11792808504671807356533659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31447489345791486284089757 11792808504671807356533659)
        ·
          refine ⟨17689212757007711034800489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11792808504671807356533659 17689212757007711034800489)
          ·
            refine ⟨13266909567755783276100367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17689212757007711034800489 13266909567755783276100367)
            ·
              refine ⟨19900364351633674914150551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13266909567755783276100367 19900364351633674914150551)
              ·
                refine ⟨29850546527450512371225827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19900364351633674914150551 29850546527450512371225827)
                ·
                  refine ⟨44775819791175768556838741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29850546527450512371225827 44775819791175768556838741)
                  ·
                    refine ⟨262358319088920518887727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 44775819791175768556838741 262358319088920518887727)
                    ·
                      rfl

theorem cell23_1532823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 9].length) (baseStart_1532823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532823 prefixEnd_1532823 := by exact prefixLift 1532823
  have htrace : WordTrace (prefixWord ++ tailWord_1532823) baseStart_1532823 baseEnd_1532823 := by
    simpa [prefixWord, tailWord_1532823, baseEnd_1532823] using wordTrace_append hprefix tailTrace_1532823
  have hstable : (prefixWord ++ tailWord_1532823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532823).length < 2 ^ (prefixWord ++ tailWord_1532823).sum := by decide
  have hdescent : baseEnd_1532823 < baseStart_1532823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532864 : List Nat := [2, 1, 1, 2, 3, 4, 1, 3, 1, 3, 2]
def baseStart_1532864 : Nat := 118140960795 + 1532864 * 2 ^ 59
def prefixEnd_1532864 : Nat := 4983230072969 + 3 ^ 40 * 1532864 * 2
def baseEnd_1532864 : Nat := 787096009973595896250493

theorem tailTrace_1532864 : CollatzResearch.WordTrace tailWord_1532864 prefixEnd_1532864 787096009973595896250493 := by
  unfold tailWord_1532864
  simp only [CollatzResearch.WordTrace]
  refine ⟨27954071559351497586978823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37272095412468663449305097 27954071559351497586978823)
  ·
    refine ⟨41931107339027246380468235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27954071559351497586978823 41931107339027246380468235)
    ·
      refine ⟨62896661008540869570702353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41931107339027246380468235 62896661008540869570702353)
      ·
        refine ⟨47172495756405652178026765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62896661008540869570702353 47172495756405652178026765)
        ·
          refine ⟨17689685908652119566760037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47172495756405652178026765 17689685908652119566760037)
          ·
            refine ⟨3316816107872272418767507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17689685908652119566760037 3316816107872272418767507)
            ·
              refine ⟨4975224161808408628151261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3316816107872272418767507 4975224161808408628151261)
              ·
                refine ⟨1865709060678153235556723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4975224161808408628151261 1865709060678153235556723)
                ·
                  refine ⟨2798563591017229853335085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1865709060678153235556723 2798563591017229853335085)
                  ·
                    refine ⟨1049461346631461195000657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2798563591017229853335085 1049461346631461195000657)
                    ·
                      refine ⟨787096009973595896250493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1049461346631461195000657 787096009973595896250493)
                      ·
                        rfl

theorem cell23_1532864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 1, 3, 2].length) (baseStart_1532864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532864 prefixEnd_1532864 := by exact prefixLift 1532864
  have htrace : WordTrace (prefixWord ++ tailWord_1532864) baseStart_1532864 baseEnd_1532864 := by
    simpa [prefixWord, tailWord_1532864, baseEnd_1532864] using wordTrace_append hprefix tailTrace_1532864
  have hstable : (prefixWord ++ tailWord_1532864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532864).length < 2 ^ (prefixWord ++ tailWord_1532864).sum := by decide
  have hdescent : baseEnd_1532864 < baseStart_1532864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532873 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 1, 5, 6]
def baseStart_1532873 : Nat := 118140960795 + 1532873 * 2 ^ 59
def prefixEnd_1532873 : Nat := 4983230072969 + 3 ^ 40 * 1532873 * 2
def baseEnd_1532873 : Nat := 787100631299486361037951

theorem tailTrace_1532873 : CollatzResearch.WordTrace tailWord_1532873 prefixEnd_1532873 787100631299486361037951 := by
  unfold tailWord_1532873
  simp only [CollatzResearch.WordTrace]
  refine ⟨55908471375670389711035273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37272314250446926474023515 55908471375670389711035273)
  ·
    refine ⟨41931353531752792283276455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55908471375670389711035273 41931353531752792283276455)
    ·
      refine ⟨62897030297629188424914683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41931353531752792283276455 62897030297629188424914683)
      ·
        refine ⟨94345545446443782637372025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62897030297629188424914683 94345545446443782637372025)
        ·
          refine ⟨70759159084832836978029019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94345545446443782637372025 70759159084832836978029019)
          ·
            refine ⟨106138738627249255467043529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70759159084832836978029019 106138738627249255467043529)
            ·
              refine ⟨79604053970436941600282647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106138738627249255467043529 79604053970436941600282647)
              ·
                refine ⟨119406080955655412400423971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79604053970436941600282647 119406080955655412400423971)
                ·
                  refine ⟨179109121433483118600635957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119406080955655412400423971 179109121433483118600635957)
                  ·
                    refine ⟨16791480134389042368809621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 179109121433483118600635957 16791480134389042368809621)
                    ·
                      refine ⟨787100631299486361037951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16791480134389042368809621 787100631299486361037951)
                      ·
                        rfl

theorem cell23_1532873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 5, 6].length) (baseStart_1532873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532873 prefixEnd_1532873 := by exact prefixLift 1532873
  have htrace : WordTrace (prefixWord ++ tailWord_1532873) baseStart_1532873 baseEnd_1532873 := by
    simpa [prefixWord, tailWord_1532873, baseEnd_1532873] using wordTrace_append hprefix tailTrace_1532873
  have hstable : (prefixWord ++ tailWord_1532873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532873).length < 2 ^ (prefixWord ++ tailWord_1532873).sum := by decide
  have hdescent : baseEnd_1532873 < baseStart_1532873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532898 : List Nat := [3, 3, 3, 1, 1, 2, 2, 2, 1, 3, 2]
def baseStart_1532898 : Nat := 118140960795 + 1532898 * 2 ^ 59
def prefixEnd_1532898 : Nat := 4983230072969 + 3 ^ 40 * 1532898 * 2
def baseEnd_1532898 : Nat := 787113468315848763225337

theorem tailTrace_1532898 : CollatzResearch.WordTrace tailWord_1532898 prefixEnd_1532898 787113468315848763225337 := by
  unfold tailWord_1532898
  simp only [CollatzResearch.WordTrace]
  refine ⟨13977345800144954745173837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37272922133719879320463565 13977345800144954745173837)
  ·
    refine ⟨5241504675054358029440189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13977345800144954745173837 5241504675054358029440189)
    ·
      refine ⟨1965564253145384261040071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5241504675054358029440189 1965564253145384261040071)
      ·
        refine ⟨2948346379718076391560107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1965564253145384261040071 2948346379718076391560107)
        ·
          refine ⟨4422519569577114587340161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2948346379718076391560107 4422519569577114587340161)
          ·
            refine ⟨3316889677182835940505121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4422519569577114587340161 3316889677182835940505121)
            ·
              refine ⟨2487667257887126955378841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3316889677182835940505121 2487667257887126955378841)
              ·
                refine ⟨1865750443415345216534131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2487667257887126955378841 1865750443415345216534131)
                ·
                  refine ⟨2798625665123017824801197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1865750443415345216534131 2798625665123017824801197)
                  ·
                    refine ⟨1049484624421131684300449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2798625665123017824801197 1049484624421131684300449)
                    ·
                      refine ⟨787113468315848763225337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1049484624421131684300449 787113468315848763225337)
                      ·
                        rfl

theorem cell23_1532898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_1532898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532898 prefixEnd_1532898 := by exact prefixLift 1532898
  have htrace : WordTrace (prefixWord ++ tailWord_1532898) baseStart_1532898 baseEnd_1532898 := by
    simpa [prefixWord, tailWord_1532898, baseEnd_1532898] using wordTrace_append hprefix tailTrace_1532898
  have hstable : (prefixWord ++ tailWord_1532898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532898).length < 2 ^ (prefixWord ++ tailWord_1532898).sum := by decide
  have hdescent : baseEnd_1532898 < baseStart_1532898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532914 : List Nat := [3, 2, 1, 5, 1, 1, 1, 1, 2, 1, 5]
def baseStart_1532914 : Nat := 118140960795 + 1532914 * 2 ^ 59
def prefixEnd_1532914 : Nat := 4983230072969 + 3 ^ 40 * 1532914 * 2
def baseEnd_1532914 : Nat := 787121684006320700625263

theorem tailTrace_1532914 : CollatzResearch.WordTrace tailWord_1532914 prefixEnd_1532914 787121684006320700625263 := by
  unfold tailWord_1532914
  simp only [CollatzResearch.WordTrace]
  refine ⟨13977491692130463428319449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37273311179014569142185197 13977491692130463428319449)
  ·
    refine ⟨10483118769097847571239587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13977491692130463428319449 10483118769097847571239587)
    ·
      refine ⟨15724678153646771356859381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10483118769097847571239587 15724678153646771356859381)
      ·
        refine ⟨1474188576904384814705567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15724678153646771356859381 1474188576904384814705567)
        ·
          refine ⟨2211282865356577222058351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1474188576904384814705567 2211282865356577222058351)
          ·
            refine ⟨3316924298034865833087527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2211282865356577222058351 3316924298034865833087527)
            ·
              refine ⟨4975386447052298749631291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3316924298034865833087527 4975386447052298749631291)
              ·
                refine ⟨7463079670578448124446937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4975386447052298749631291 7463079670578448124446937)
                ·
                  refine ⟨5597309752933836093335203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7463079670578448124446937 5597309752933836093335203)
                  ·
                    refine ⟨8395964629400754140002805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5597309752933836093335203 8395964629400754140002805)
                    ·
                      refine ⟨787121684006320700625263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8395964629400754140002805 787121684006320700625263)
                      ·
                        rfl

theorem cell23_1532914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_1532914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532914 prefixEnd_1532914 := by exact prefixLift 1532914
  have htrace : WordTrace (prefixWord ++ tailWord_1532914) baseStart_1532914 baseEnd_1532914 := by
    simpa [prefixWord, tailWord_1532914, baseEnd_1532914] using wordTrace_append hprefix tailTrace_1532914
  have hstable : (prefixWord ++ tailWord_1532914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532914).length < 2 ^ (prefixWord ++ tailWord_1532914).sum := by decide
  have hdescent : baseEnd_1532914 < baseStart_1532914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532940 : List Nat := [2, 2, 1, 2, 3, 2, 1, 1, 1, 1, 7]
def baseStart_1532940 : Nat := 118140960795 + 1532940 * 2 ^ 59
def prefixEnd_1532940 : Nat := 4983230072969 + 3 ^ 40 * 1532940 * 2
def baseEnd_1532940 : Nat := 787135034503337598900143

theorem tailTrace_1532940 : CollatzResearch.WordTrace tailWord_1532940 prefixEnd_1532940 787135034503337598900143 := by
  unfold tailWord_1532940
  simp only [CollatzResearch.WordTrace]
  refine ⟨27955457533213830076862137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37273943377618440102482849 27955457533213830076862137)
  ·
    refine ⟨20966593149910372557646603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27955457533213830076862137 20966593149910372557646603)
    ·
      refine ⟨31449889724865558836469905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20966593149910372557646603 31449889724865558836469905)
      ·
        refine ⟨23587417293649169127352429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31449889724865558836469905 23587417293649169127352429)
        ·
          refine ⟨8845281485118438422757161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23587417293649169127352429 8845281485118438422757161)
          ·
            refine ⟨6633961113838828817067871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8845281485118438422757161 6633961113838828817067871)
            ·
              refine ⟨9950941670758243225601807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6633961113838828817067871 9950941670758243225601807)
              ·
                refine ⟨14926412506137364838402711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9950941670758243225601807 14926412506137364838402711)
                ·
                  refine ⟨22389618759206047257604067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14926412506137364838402711 22389618759206047257604067)
                  ·
                    refine ⟨33584428138809070886406101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22389618759206047257604067 33584428138809070886406101)
                    ·
                      refine ⟨787135034503337598900143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 33584428138809070886406101 787135034503337598900143)
                      ·
                        rfl

theorem cell23_1532940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_1532940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532940 prefixEnd_1532940 := by exact prefixLift 1532940
  have htrace : WordTrace (prefixWord ++ tailWord_1532940) baseStart_1532940 baseEnd_1532940 := by
    simpa [prefixWord, tailWord_1532940, baseEnd_1532940] using wordTrace_append hprefix tailTrace_1532940
  have hstable : (prefixWord ++ tailWord_1532940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532940).length < 2 ^ (prefixWord ++ tailWord_1532940).sum := by decide
  have hdescent : baseEnd_1532940 < baseStart_1532940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532964 : List Nat := [2, 3, 1, 4, 1, 2, 2, 1, 2, 5]
def baseStart_1532964 : Nat := 118140960795 + 1532964 * 2 ^ 59
def prefixEnd_1532964 : Nat := 4983230072969 + 3 ^ 40 * 1532964 * 2
def baseEnd_1532964 : Nat := 262382452679681835000011

theorem tailTrace_1532964 : CollatzResearch.WordTrace tailWord_1532964 prefixEnd_1532964 262382452679681835000011 := by
  unfold tailWord_1532964
  simp only [CollatzResearch.WordTrace]
  refine ⟨27955895209170356126298973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37274526945560474835065297 27955895209170356126298973)
  ·
    refine ⟨10483460703438883547362115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27955895209170356126298973 10483460703438883547362115)
    ·
      refine ⟨15725191055158325321043173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10483460703438883547362115 15725191055158325321043173)
      ·
        refine ⟨2948473322842185997695595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15725191055158325321043173 2948473322842185997695595)
        ·
          refine ⟨4422709984263278996543393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2948473322842185997695595 4422709984263278996543393)
          ·
            refine ⟨3317032488197459247407545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4422709984263278996543393 3317032488197459247407545)
            ·
              refine ⟨2487774366148094435555659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3317032488197459247407545 2487774366148094435555659)
              ·
                refine ⟨3731661549222141653333489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2487774366148094435555659 3731661549222141653333489)
                ·
                  refine ⟨2798746161916606240000117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3731661549222141653333489 2798746161916606240000117)
                  ·
                    refine ⟨262382452679681835000011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2798746161916606240000117 262382452679681835000011)
                    ·
                      rfl

theorem cell23_1532964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_1532964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1532964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1532964 prefixEnd_1532964 := by exact prefixLift 1532964
  have htrace : WordTrace (prefixWord ++ tailWord_1532964) baseStart_1532964 baseEnd_1532964 := by
    simpa [prefixWord, tailWord_1532964, baseEnd_1532964] using wordTrace_append hprefix tailTrace_1532964
  have hstable : (prefixWord ++ tailWord_1532964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532964).length < 2 ^ (prefixWord ++ tailWord_1532964).sum := by decide
  have hdescent : baseEnd_1532964 < baseStart_1532964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533021 : List Nat := [1, 4, 4, 1, 2, 1, 1, 1, 1, 4, 3]
def baseStart_1533021 : Nat := 118140960795 + 1533021 * 2 ^ 59
def prefixEnd_1533021 : Nat := 4983230072969 + 3 ^ 40 * 1533021 * 2
def baseEnd_1533021 : Nat := 787176626436351781987271

theorem tailTrace_1533021 : CollatzResearch.WordTrace tailWord_1533021 prefixEnd_1533021 787176626436351781987271 := by
  unfold tailWord_1533021
  simp only [CollatzResearch.WordTrace]
  refine ⟨55913869379134210987422917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37275912919422807324948611 55913869379134210987422917)
  ·
    refine ⟨10483850508587664560141797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55913869379134210987422917 10483850508587664560141797)
    ·
      refine ⟨1965721970360187105026587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10483850508587664560141797 1965721970360187105026587)
      ·
        refine ⟨2948582955540280657539881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1965721970360187105026587 2948582955540280657539881)
        ·
          refine ⟨2211437216655210493154911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2948582955540280657539881 2211437216655210493154911)
          ·
            refine ⟨3317155824982815739732367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2211437216655210493154911 3317155824982815739732367)
            ·
              refine ⟨4975733737474223609598551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3317155824982815739732367 4975733737474223609598551)
              ·
                refine ⟨7463600606211335414397827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4975733737474223609598551 7463600606211335414397827)
                ·
                  refine ⟨11195400909317003121596741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7463600606211335414397827 11195400909317003121596741)
                  ·
                    refine ⟨2099137670496938085299389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11195400909317003121596741 2099137670496938085299389)
                    ·
                      refine ⟨787176626436351781987271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2099137670496938085299389 787176626436351781987271)
                      ·
                        rfl

theorem cell23_1533021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_1533021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533021 prefixEnd_1533021 := by exact prefixLift 1533021
  have htrace : WordTrace (prefixWord ++ tailWord_1533021) baseStart_1533021 baseEnd_1533021 := by
    simpa [prefixWord, tailWord_1533021, baseEnd_1533021] using wordTrace_append hprefix tailTrace_1533021
  have hstable : (prefixWord ++ tailWord_1533021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533021).length < 2 ^ (prefixWord ++ tailWord_1533021).sum := by decide
  have hdescent : baseEnd_1533021 < baseStart_1533021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533050 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 1, 12]
def baseStart_1533050 : Nat := 118140960795 + 1533050 * 2 ^ 59
def prefixEnd_1533050 : Nat := 4983230072969 + 3 ^ 40 * 1533050 * 2
def baseEnd_1533050 : Nat := 262397172458444056174879

theorem tailTrace_1533050 : CollatzResearch.WordTrace tailWord_1533050 prefixEnd_1533050 262397172458444056174879 := by
  unfold tailWord_1533050
  simp only [CollatzResearch.WordTrace]
  refine ⟨13978731774007287235057151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37276618064019432626819069 13978731774007287235057151)
  ·
    refine ⟨20968097661010930852585727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13978731774007287235057151 20968097661010930852585727)
    ·
      refine ⟨31452146491516396278878591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20968097661010930852585727 31452146491516396278878591)
      ·
        refine ⟨47178219737274594418317887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31452146491516396278878591 47178219737274594418317887)
        ·
          refine ⟨70767329605911891627476831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47178219737274594418317887 70767329605911891627476831)
          ·
            refine ⟨106150994408867837441215247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70767329605911891627476831 106150994408867837441215247)
            ·
              refine ⟨159226491613301756161822871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106150994408867837441215247 159226491613301756161822871)
              ·
                refine ⟨238839737419952634242734307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159226491613301756161822871 238839737419952634242734307)
                ·
                  refine ⟨358259606129928951364101461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 238839737419952634242734307 358259606129928951364101461)
                  ·
                    refine ⟨262397172458444056174879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 358259606129928951364101461 262397172458444056174879)
                    ·
                      rfl

theorem cell23_1533050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 12].length) (baseStart_1533050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533050 prefixEnd_1533050 := by exact prefixLift 1533050
  have htrace : WordTrace (prefixWord ++ tailWord_1533050) baseStart_1533050 baseEnd_1533050 := by
    simpa [prefixWord, tailWord_1533050, baseEnd_1533050] using wordTrace_append hprefix tailTrace_1533050
  have hstable : (prefixWord ++ tailWord_1533050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533050).length < 2 ^ (prefixWord ++ tailWord_1533050).sum := by decide
  have hdescent : baseEnd_1533050 < baseStart_1533050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533084 : List Nat := [2, 2, 3, 2, 1, 2, 1, 2, 4, 4]
def baseStart_1533084 : Nat := 118140960795 + 1533084 * 2 ^ 59
def prefixEnd_1533084 : Nat := 4983230072969 + 3 ^ 40 * 1533084 * 2
def baseEnd_1533084 : Nat := 262402991905861678499827

theorem tailTrace_1533084 : CollatzResearch.WordTrace tailWord_1533084 prefixEnd_1533084 262402991905861678499827 := by
  unfold tailWord_1533084
  simp only [CollatzResearch.WordTrace]
  refine ⟨27958083588952986373483153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37277444785270648497977537 27958083588952986373483153)
  ·
    refine ⟨20968562691714739780112365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27958083588952986373483153 20968562691714739780112365)
    ·
      refine ⟨7863211009393027417542137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20968562691714739780112365 7863211009393027417542137)
      ·
        refine ⟨5897408257044770563156603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7863211009393027417542137 5897408257044770563156603)
        ·
          refine ⟨8846112385567155844734905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5897408257044770563156603 8846112385567155844734905)
          ·
            refine ⟨6634584289175366883551179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8846112385567155844734905 6634584289175366883551179)
            ·
              refine ⟨9951876433763050325326769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6634584289175366883551179 9951876433763050325326769)
              ·
                refine ⟨7463907325322287743995077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9951876433763050325326769 7463907325322287743995077)
                ·
                  refine ⟨1399482623497928951999077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7463907325322287743995077 1399482623497928951999077)
                  ·
                    refine ⟨262402991905861678499827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1399482623497928951999077 262402991905861678499827)
                    ·
                      rfl

theorem cell23_1533084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_1533084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533084 prefixEnd_1533084 := by exact prefixLift 1533084
  have htrace : WordTrace (prefixWord ++ tailWord_1533084) baseStart_1533084 baseEnd_1533084 := by
    simpa [prefixWord, tailWord_1533084, baseEnd_1533084] using wordTrace_append hprefix tailTrace_1533084
  have hstable : (prefixWord ++ tailWord_1533084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533084).length < 2 ^ (prefixWord ++ tailWord_1533084).sum := by decide
  have hdescent : baseEnd_1533084 < baseStart_1533084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533118 : List Nat := [4, 2, 1, 1, 3, 1, 4, 1, 2, 4]
def baseStart_1533118 : Nat := 118140960795 + 1533118 * 2 ^ 59
def prefixEnd_1533118 : Nat := 4983230072969 + 3 ^ 40 * 1533118 * 2
def baseEnd_1533118 : Nat := 262408811353279300824775

theorem tailTrace_1533118 : CollatzResearch.WordTrace tailWord_1533118 prefixEnd_1533118 262408811353279300824775 := by
  unfold tailWord_1533118
  simp only [CollatzResearch.WordTrace]
  refine ⟨6989675907472849569213001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37278271506521864369136005 6989675907472849569213001)
  ·
    refine ⟨5242256930604637176909751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6989675907472849569213001 5242256930604637176909751)
    ·
      refine ⟨7863385395906955765364627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5242256930604637176909751 7863385395906955765364627)
      ·
        refine ⟨11795078093860433648046941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7863385395906955765364627 11795078093860433648046941)
        ·
          refine ⟨4423154285197662618017603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11795078093860433648046941 4423154285197662618017603)
          ·
            refine ⟨6634731427796493927026405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4423154285197662618017603 6634731427796493927026405)
            ·
              refine ⟨1244012142711842611317451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6634731427796493927026405 1244012142711842611317451)
              ·
                refine ⟨1866018214067763916976177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1244012142711842611317451 1866018214067763916976177)
                ·
                  refine ⟨1399513660550822937732133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1866018214067763916976177 1399513660550822937732133)
                  ·
                    refine ⟨262408811353279300824775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1399513660550822937732133 262408811353279300824775)
                    ·
                      rfl

theorem cell23_1533118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_1533118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533118 prefixEnd_1533118 := by exact prefixLift 1533118
  have htrace : WordTrace (prefixWord ++ tailWord_1533118) baseStart_1533118 baseEnd_1533118 := by
    simpa [prefixWord, tailWord_1533118, baseEnd_1533118] using wordTrace_append hprefix tailTrace_1533118
  have hstable : (prefixWord ++ tailWord_1533118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533118).length < 2 ^ (prefixWord ++ tailWord_1533118).sum := by decide
  have hdescent : baseEnd_1533118 < baseStart_1533118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533122 : List Nat := [3, 5, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_1533122 : Nat := 118140960795 + 1533122 * 2 ^ 59
def prefixEnd_1533122 : Nat := 4983230072969 + 3 ^ 40 * 1533122 * 2
def baseEnd_1533122 : Nat := 262409495994151962274769

theorem tailTrace_1533122 : CollatzResearch.WordTrace tailWord_1533122 prefixEnd_1533122 262409495994151962274769 := by
  unfold tailWord_1533122
  simp only [CollatzResearch.WordTrace]
  refine ⟨13979388287942076309212405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37278368767845536824566413 13979388287942076309212405)
  ·
    refine ⟨1310567651994569653988663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13979388287942076309212405 1310567651994569653988663)
    ·
      refine ⟨1965851477991854480982995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1310567651994569653988663 1965851477991854480982995)
      ·
        refine ⟨2948777216987781721474493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1965851477991854480982995 2948777216987781721474493)
        ·
          refine ⟨1105791456370418145552935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2948777216987781721474493 1105791456370418145552935)
          ·
            refine ⟨1658687184555627218329403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1105791456370418145552935 1658687184555627218329403)
            ·
              refine ⟨2488030776833440827494105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1658687184555627218329403 2488030776833440827494105)
              ·
                refine ⟨1866023082625080620620579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2488030776833440827494105 1866023082625080620620579)
                ·
                  refine ⟨2799034623937620930930869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1866023082625080620620579 2799034623937620930930869)
                  ·
                    refine ⟨262409495994151962274769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2799034623937620930930869 262409495994151962274769)
                    ·
                      rfl

theorem cell23_1533122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_1533122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533122 prefixEnd_1533122 := by exact prefixLift 1533122
  have htrace : WordTrace (prefixWord ++ tailWord_1533122) baseStart_1533122 baseEnd_1533122 := by
    simpa [prefixWord, tailWord_1533122, baseEnd_1533122] using wordTrace_append hprefix tailTrace_1533122
  have hstable : (prefixWord ++ tailWord_1533122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533122).length < 2 ^ (prefixWord ++ tailWord_1533122).sum := by decide
  have hdescent : baseEnd_1533122 < baseStart_1533122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533141 : List Nat := [1, 3, 2, 4, 1, 2, 1, 2, 1, 3, 3]
def baseStart_1533141 : Nat := 118140960795 + 1533141 * 2 ^ 59
def prefixEnd_1533141 : Nat := 4983230072969 + 3 ^ 40 * 1533141 * 2
def baseEnd_1533141 : Nat := 787238244114891312486719

theorem tailTrace_1533141 : CollatzResearch.WordTrace tailWord_1533141 prefixEnd_1533141 787238244114891312486719 := by
  unfold tailWord_1533141
  simp only [CollatzResearch.WordTrace]
  refine ⟨55918246138699471481791277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37278830759132980987860851 55918246138699471481791277)
  ·
    refine ⟨20969342302012301805671729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55918246138699471481791277 20969342302012301805671729)
    ·
      refine ⟨15727006726509226354253797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20969342302012301805671729 15727006726509226354253797)
      ·
        refine ⟨2948813761220479941422587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15727006726509226354253797 2948813761220479941422587)
        ·
          refine ⟨4423220641830719912133881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2948813761220479941422587 4423220641830719912133881)
          ·
            refine ⟨3317415481373039934100411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4423220641830719912133881 3317415481373039934100411)
            ·
              refine ⟨4976123222059559901150617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3317415481373039934100411 4976123222059559901150617)
              ·
                refine ⟨3732092416544669925862963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4976123222059559901150617 3732092416544669925862963)
                ·
                  refine ⟨5598138624817004888794445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3732092416544669925862963 5598138624817004888794445)
                  ·
                    refine ⟨2099301984306376833297917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5598138624817004888794445 2099301984306376833297917)
                    ·
                      refine ⟨787238244114891312486719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2099301984306376833297917 787238244114891312486719)
                      ·
                        rfl

theorem cell23_1533141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_1533141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533141 prefixEnd_1533141 := by exact prefixLift 1533141
  have htrace : WordTrace (prefixWord ++ tailWord_1533141) baseStart_1533141 baseEnd_1533141 := by
    simpa [prefixWord, tailWord_1533141, baseEnd_1533141] using wordTrace_append hprefix tailTrace_1533141
  have hstable : (prefixWord ++ tailWord_1533141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533141).length < 2 ^ (prefixWord ++ tailWord_1533141).sum := by decide
  have hdescent : baseEnd_1533141 < baseStart_1533141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533151 : List Nat := [1, 1, 2, 3, 2, 1, 2, 5, 1, 3, 2]
def baseStart_1533151 : Nat := 118140960795 + 1533151 * 2 ^ 59
def prefixEnd_1533151 : Nat := 4983230072969 + 3 ^ 40 * 1533151 * 2
def baseEnd_1533151 : Nat := 787243378921436273361673

theorem tailTrace_1533151 : CollatzResearch.WordTrace tailWord_1533151 prefixEnd_1533151 787243378921436273361673 := by
  unfold tailWord_1533151
  simp only [CollatzResearch.WordTrace]
  refine ⟨55918610868663243189655307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37279073912442162126436871 55918610868663243189655307)
  ·
    refine ⟨83877916302994864784482961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55918610868663243189655307 83877916302994864784482961)
    ·
      refine ⟨62908437227246148588362221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83877916302994864784482961 62908437227246148588362221)
      ·
        refine ⟨23590663960217305720635833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62908437227246148588362221 23590663960217305720635833)
        ·
          refine ⟨17692997970162979290476875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23590663960217305720635833 17692997970162979290476875)
          ·
            refine ⟨26539496955244468935715313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17692997970162979290476875 26539496955244468935715313)
            ·
              refine ⟨19904622716433351701786485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26539496955244468935715313 19904622716433351701786485)
              ·
                refine ⟨1866058379665626722042483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19904622716433351701786485 1866058379665626722042483)
                ·
                  refine ⟨2799087569498440083063725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1866058379665626722042483 2799087569498440083063725)
                  ·
                    refine ⟨1049657838561915031148897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2799087569498440083063725 1049657838561915031148897)
                    ·
                      refine ⟨787243378921436273361673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1049657838561915031148897 787243378921436273361673)
                      ·
                        rfl

theorem cell23_1533151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 3, 2].length) (baseStart_1533151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533151 prefixEnd_1533151 := by exact prefixLift 1533151
  have htrace : WordTrace (prefixWord ++ tailWord_1533151) baseStart_1533151 baseEnd_1533151 := by
    simpa [prefixWord, tailWord_1533151, baseEnd_1533151] using wordTrace_append hprefix tailTrace_1533151
  have hstable : (prefixWord ++ tailWord_1533151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533151).length < 2 ^ (prefixWord ++ tailWord_1533151).sum := by decide
  have hdescent : baseEnd_1533151 < baseStart_1533151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533159 : List Nat := [1, 1, 5, 3, 2, 2, 2, 2, 1, 2, 2]
def baseStart_1533159 : Nat := 118140960795 + 1533159 * 2 ^ 59
def prefixEnd_1533159 : Nat := 4983230072969 + 3 ^ 40 * 1533159 * 2
def baseEnd_1533159 : Nat := 787247486766672242061637

theorem tailTrace_1533159 : CollatzResearch.WordTrace tailWord_1533159 prefixEnd_1533159 787247486766672242061637 := by
  unfold tailWord_1533159
  simp only [CollatzResearch.WordTrace]
  refine ⟨55918902652634260555946531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37279268435089507037297687 55918902652634260555946531)
  ·
    refine ⟨83878353978951390833919797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55918902652634260555946531 83878353978951390833919797)
    ·
      refine ⟨7863595685526692890679981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83878353978951390833919797 7863595685526692890679981)
      ·
        refine ⟨2948848382072509834004993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7863595685526692890679981 2948848382072509834004993)
        ·
          refine ⟨2211636286554382375503745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2948848382072509834004993 2211636286554382375503745)
          ·
            refine ⟨1658727214915786781627809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2211636286554382375503745 1658727214915786781627809)
            ·
              refine ⟨1244045411186840086220857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1658727214915786781627809 1244045411186840086220857)
              ·
                refine ⟨933034058390130064665643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1244045411186840086220857 933034058390130064665643)
                ·
                  refine ⟨1399551087585195096998465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 933034058390130064665643 1399551087585195096998465)
                  ·
                    refine ⟨1049663315688896322748849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1399551087585195096998465 1049663315688896322748849)
                    ·
                      refine ⟨787247486766672242061637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1049663315688896322748849 787247486766672242061637)
                      ·
                        rfl

theorem cell23_1533159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_1533159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533159 prefixEnd_1533159 := by exact prefixLift 1533159
  have htrace : WordTrace (prefixWord ++ tailWord_1533159) baseStart_1533159 baseEnd_1533159 := by
    simpa [prefixWord, tailWord_1533159, baseEnd_1533159] using wordTrace_append hprefix tailTrace_1533159
  have hstable : (prefixWord ++ tailWord_1533159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533159).length < 2 ^ (prefixWord ++ tailWord_1533159).sum := by decide
  have hdescent : baseEnd_1533159 < baseStart_1533159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533181 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 8, 2, 2]
def baseStart_1533181 : Nat := 118140960795 + 1533181 * 2 ^ 59
def prefixEnd_1533181 : Nat := 4983230072969 + 3 ^ 40 * 1533181 * 2
def baseEnd_1533181 : Nat := 787258783341071155986535

theorem tailTrace_1533181 : CollatzResearch.WordTrace tailWord_1533181 prefixEnd_1533181 787258783341071155986535 := by
  unfold tailWord_1533181
  simp only [CollatzResearch.WordTrace]
  refine ⟨55919705058554558313247397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37279803372369705542164931 55919705058554558313247397)
  ·
    refine ⟨10484944698478979683733887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55919705058554558313247397 10484944698478979683733887)
    ·
      refine ⟨15727417047718469525600831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10484944698478979683733887 15727417047718469525600831)
      ·
        refine ⟨23591125571577704288401247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15727417047718469525600831 23591125571577704288401247)
        ·
          refine ⟨35386688357366556432601871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23591125571577704288401247 35386688357366556432601871)
          ·
            refine ⟨53080032536049834648902807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35386688357366556432601871 53080032536049834648902807)
            ·
              refine ⟨79620048804074751973354211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53080032536049834648902807 79620048804074751973354211)
              ·
                refine ⟨119430073206112127960031317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79620048804074751973354211 119430073206112127960031317)
                ·
                  refine ⟨1399571170384126499531617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 119430073206112127960031317 1399571170384126499531617)
                  ·
                    refine ⟨1049678377788094874648713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1399571170384126499531617 1049678377788094874648713)
                    ·
                      refine ⟨787258783341071155986535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1049678377788094874648713 787258783341071155986535)
                      ·
                        rfl

theorem cell23_1533181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 8, 2, 2].length) (baseStart_1533181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533181 prefixEnd_1533181 := by exact prefixLift 1533181
  have htrace : WordTrace (prefixWord ++ tailWord_1533181) baseStart_1533181 baseEnd_1533181 := by
    simpa [prefixWord, tailWord_1533181, baseEnd_1533181] using wordTrace_append hprefix tailTrace_1533181
  have hstable : (prefixWord ++ tailWord_1533181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533181).length < 2 ^ (prefixWord ++ tailWord_1533181).sum := by decide
  have hdescent : baseEnd_1533181 < baseStart_1533181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533187 : List Nat := [1, 1, 1, 3, 2, 4, 1, 1, 9]
def baseStart_1533187 : Nat := 118140960795 + 1533187 * 2 ^ 59
def prefixEnd_1533187 : Nat := 4983230072969 + 3 ^ 40 * 1533187 * 2
def baseEnd_1533187 : Nat := 87473540469444236945723

theorem tailTrace_1533187 : CollatzResearch.WordTrace tailWord_1533187 prefixEnd_1533187 87473540469444236945723 := by
  unfold tailWord_1533187
  simp only [CollatzResearch.WordTrace]
  refine ⟨55919923896532821337965815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37279949264355214225310543 55919923896532821337965815)
  ·
    refine ⟨83879885844799232006948723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55919923896532821337965815 83879885844799232006948723)
    ·
      refine ⟨125819828767198848010423085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83879885844799232006948723 125819828767198848010423085)
      ·
        refine ⟨47182435787699568003908657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125819828767198848010423085 47182435787699568003908657)
        ·
          refine ⟨35386826840774676002931493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47182435787699568003908657 35386826840774676002931493)
          ·
            refine ⟨6635030032645251750549655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35386826840774676002931493 6635030032645251750549655)
            ·
              refine ⟨9952545048967877625824483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6635030032645251750549655 9952545048967877625824483)
              ·
                refine ⟨14928817573451816438736725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9952545048967877625824483 14928817573451816438736725)
                ·
                  refine ⟨87473540469444236945723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 14928817573451816438736725 87473540469444236945723)
                  ·
                    rfl

theorem cell23_1533187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 9].length) (baseStart_1533187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533187 prefixEnd_1533187 := by exact prefixLift 1533187
  have htrace : WordTrace (prefixWord ++ tailWord_1533187) baseStart_1533187 baseEnd_1533187 := by
    simpa [prefixWord, tailWord_1533187, baseEnd_1533187] using wordTrace_append hprefix tailTrace_1533187
  have hstable : (prefixWord ++ tailWord_1533187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533187).length < 2 ^ (prefixWord ++ tailWord_1533187).sum := by decide
  have hdescent : baseEnd_1533187 < baseStart_1533187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533202 : List Nat := [3, 2, 4, 2, 1, 1, 1, 3, 1, 3, 2]
def baseStart_1533202 : Nat := 118140960795 + 1533202 * 2 ^ 59
def prefixEnd_1533202 : Nat := 4983230072969 + 3 ^ 40 * 1533202 * 2
def baseEnd_1533202 : Nat := 787269566434815573823939

theorem tailTrace_1533202 : CollatzResearch.WordTrace tailWord_1533202 prefixEnd_1533202 787269566434815573823939 := by
  unfold tailWord_1533202
  simp only [CollatzResearch.WordTrace]
  refine ⟨13980117747869619724940465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37280313994318985933174573 13980117747869619724940465)
  ·
    refine ⟨10485088310902214793705349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13980117747869619724940465 10485088310902214793705349)
    ·
      refine ⟨1965954058294165273819753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10485088310902214793705349 1965954058294165273819753)
      ·
        refine ⟨1474465543720623955364815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1965954058294165273819753 1474465543720623955364815)
        ·
          refine ⟨2211698315580935933047223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1474465543720623955364815 2211698315580935933047223)
          ·
            refine ⟨3317547473371403899570835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2211698315580935933047223 3317547473371403899570835)
            ·
              refine ⟨4976321210057105849356253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3317547473371403899570835 4976321210057105849356253)
              ·
                refine ⟨1866120453771414693508595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4976321210057105849356253 1866120453771414693508595)
                ·
                  refine ⟨2799180680657122040262893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1866120453771414693508595 2799180680657122040262893)
                  ·
                    refine ⟨1049692755246420765098585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2799180680657122040262893 1049692755246420765098585)
                    ·
                      refine ⟨787269566434815573823939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1049692755246420765098585 787269566434815573823939)
                      ·
                        rfl

theorem cell23_1533202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_1533202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533202 prefixEnd_1533202 := by exact prefixLift 1533202
  have htrace : WordTrace (prefixWord ++ tailWord_1533202) baseStart_1533202 baseEnd_1533202 := by
    simpa [prefixWord, tailWord_1533202, baseEnd_1533202] using wordTrace_append hprefix tailTrace_1533202
  have hstable : (prefixWord ++ tailWord_1533202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533202).length < 2 ^ (prefixWord ++ tailWord_1533202).sum := by decide
  have hdescent : baseEnd_1533202 < baseStart_1533202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533221 : List Nat := [1, 3, 1, 2, 4, 1, 2, 4, 5]
def baseStart_1533221 : Nat := 118140960795 + 1533221 * 2 ^ 59
def prefixEnd_1533221 : Nat := 4983230072969 + 3 ^ 40 * 1533221 * 2
def baseEnd_1533221 : Nat := 87475480285250111054039

theorem tailTrace_1533221 : CollatzResearch.WordTrace tailWord_1533221 prefixEnd_1533221 87475480285250111054039 := by
  unfold tailWord_1533221
  simp only [CollatzResearch.WordTrace]
  refine ⟨55921163978409645144703517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37280775985606430096469011 55921163978409645144703517)
  ·
    refine ⟨20970436491903616929263819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55921163978409645144703517 20970436491903616929263819)
    ·
      refine ⟨31455654737855425393895729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20970436491903616929263819 31455654737855425393895729)
      ·
        refine ⟨23591741053391569045421797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31455654737855425393895729 23591741053391569045421797)
        ·
          refine ⟨4423451447510919196016587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23591741053391569045421797 4423451447510919196016587)
          ·
            refine ⟨6635177171266378794024881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4423451447510919196016587 6635177171266378794024881)
            ·
              refine ⟨4976382878449784095518661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6635177171266378794024881 4976382878449784095518661)
              ·
                refine ⟨933071789709334517909749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4976382878449784095518661 933071789709334517909749)
                ·
                  refine ⟨87475480285250111054039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 933071789709334517909749 87475480285250111054039)
                  ·
                    rfl

theorem cell23_1533221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 4, 5].length) (baseStart_1533221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533221 prefixEnd_1533221 := by exact prefixLift 1533221
  have htrace : WordTrace (prefixWord ++ tailWord_1533221) baseStart_1533221 baseEnd_1533221 := by
    simpa [prefixWord, tailWord_1533221, baseEnd_1533221] using wordTrace_append hprefix tailTrace_1533221
  have hstable : (prefixWord ++ tailWord_1533221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533221).length < 2 ^ (prefixWord ++ tailWord_1533221).sum := by decide
  have hdescent : baseEnd_1533221 < baseStart_1533221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533234 : List Nat := [3, 2, 1, 1, 4, 1, 1, 2, 1, 7]
def baseStart_1533234 : Nat := 118140960795 + 1533234 * 2 ^ 59
def prefixEnd_1533234 : Nat := 4983230072969 + 3 ^ 40 * 1533234 * 2
def baseEnd_1533234 : Nat := 262428665938586482874597

theorem tailTrace_1533234 : CollatzResearch.WordTrace tailWord_1533234 prefixEnd_1533234 262428665938586482874597 := by
  unfold tailWord_1533234
  simp only [CollatzResearch.WordTrace]
  refine ⟨13980409531840637091231689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37281092084908365576617837 13980409531840637091231689)
  ·
    refine ⟨10485307148880477818423767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13980409531840637091231689 10485307148880477818423767)
    ·
      refine ⟨15727960723320716727635651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10485307148880477818423767 15727960723320716727635651)
      ·
        refine ⟨23591941084981075091453477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15727960723320716727635651 23591941084981075091453477)
        ·
          refine ⟨4423488953433951579647527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23591941084981075091453477 4423488953433951579647527)
          ·
            refine ⟨6635233430150927369471291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4423488953433951579647527 6635233430150927369471291)
            ·
              refine ⟨9952850145226391054206937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6635233430150927369471291 9952850145226391054206937)
              ·
                refine ⟨7464637608919793290655203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9952850145226391054206937 7464637608919793290655203)
                ·
                  refine ⟨11196956413379689935982805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7464637608919793290655203 11196956413379689935982805)
                  ·
                    refine ⟨262428665938586482874597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11196956413379689935982805 262428665938586482874597)
                    ·
                      rfl

theorem cell23_1533234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_1533234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533234 prefixEnd_1533234 := by exact prefixLift 1533234
  have htrace : WordTrace (prefixWord ++ tailWord_1533234) baseStart_1533234 baseEnd_1533234 := by
    simpa [prefixWord, tailWord_1533234, baseEnd_1533234] using wordTrace_append hprefix tailTrace_1533234
  have hstable : (prefixWord ++ tailWord_1533234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533234).length < 2 ^ (prefixWord ++ tailWord_1533234).sum := by decide
  have hdescent : baseEnd_1533234 < baseStart_1533234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533271 : List Nat := [1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 4]
def baseStart_1533271 : Nat := 118140960795 + 1533271 * 2 ^ 59
def prefixEnd_1533271 : Nat := 4983230072969 + 3 ^ 40 * 1533271 * 2
def baseEnd_1533271 : Nat := 787304996599975803861121

theorem tailTrace_1533271 : CollatzResearch.WordTrace tailWord_1533271 prefixEnd_1533271 787304996599975803861121 := by
  unfold tailWord_1533271
  simp only [CollatzResearch.WordTrace]
  refine ⟨55922987628228503684023667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37281991752152335789349111 55922987628228503684023667)
  ·
    refine ⟨83884481442342755526035501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55922987628228503684023667 83884481442342755526035501)
    ·
      refine ⟨31456680540878533322263313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83884481442342755526035501 31456680540878533322263313)
      ·
        refine ⟨23592510405658899991697485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31456680540878533322263313 23592510405658899991697485)
        ·
          refine ⟨8847191402122087496886557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23592510405658899991697485 8847191402122087496886557)
          ·
            refine ⟨3317696775795782811332459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8847191402122087496886557 3317696775795782811332459)
            ·
              refine ⟨4976545163693674216998689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3317696775795782811332459 4976545163693674216998689)
              ·
                refine ⟨3732408872770255662749017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4976545163693674216998689 3732408872770255662749017)
                ·
                  refine ⟨2799306654577691747061763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3732408872770255662749017 2799306654577691747061763)
                  ·
                    refine ⟨4198959981866537620592645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2799306654577691747061763 4198959981866537620592645)
                    ·
                      refine ⟨787304996599975803861121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4198959981866537620592645 787304996599975803861121)
                      ·
                        rfl

theorem cell23_1533271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_1533271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533271 prefixEnd_1533271 := by exact prefixLift 1533271
  have htrace : WordTrace (prefixWord ++ tailWord_1533271) baseStart_1533271 baseEnd_1533271 := by
    simpa [prefixWord, tailWord_1533271, baseEnd_1533271] using wordTrace_append hprefix tailTrace_1533271
  have hstable : (prefixWord ++ tailWord_1533271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533271).length < 2 ^ (prefixWord ++ tailWord_1533271).sum := by decide
  have hdescent : baseEnd_1533271 < baseStart_1533271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533332 : List Nat := [2, 4, 2, 1, 2, 1, 4, 2, 1, 4]
def baseStart_1533332 : Nat := 118140960795 + 1533332 * 2 ^ 59
def prefixEnd_1533332 : Nat := 4983230072969 + 3 ^ 40 * 1533332 * 2
def baseEnd_1533332 : Nat := 262445439639966688399447

theorem tailTrace_1533332 : CollatzResearch.WordTrace tailWord_1533332 prefixEnd_1533332 262445439639966688399447 := by
  unfold tailWord_1533332
  simp only [CollatzResearch.WordTrace]
  refine ⟨27962606240503755550997125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37283474987338340734662833 27962606240503755550997125)
  ·
    refine ⟨5242988670094454165811961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27962606240503755550997125 5242988670094454165811961)
    ·
      refine ⟨3932241502570840624358971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5242988670094454165811961 3932241502570840624358971)
      ·
        refine ⟨5898362253856260936538457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3932241502570840624358971 5898362253856260936538457)
        ·
          refine ⟨4423771690392195702403843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5898362253856260936538457 4423771690392195702403843)
          ·
            refine ⟨6635657535588293553605765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4423771690392195702403843 6635657535588293553605765)
            ·
              refine ⟨1244185787922805041301081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6635657535588293553605765 1244185787922805041301081)
              ·
                refine ⟨933139340942103780975811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1244185787922805041301081 933139340942103780975811)
                ·
                  refine ⟨1399709011413155671463717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 933139340942103780975811 1399709011413155671463717)
                  ·
                    refine ⟨262445439639966688399447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1399709011413155671463717 262445439639966688399447)
                    ·
                      rfl

theorem cell23_1533332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_1533332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533332 prefixEnd_1533332 := by exact prefixLift 1533332
  have htrace : WordTrace (prefixWord ++ tailWord_1533332) baseStart_1533332 baseEnd_1533332 := by
    simpa [prefixWord, tailWord_1533332, baseEnd_1533332] using wordTrace_append hprefix tailTrace_1533332
  have hstable : (prefixWord ++ tailWord_1533332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533332).length < 2 ^ (prefixWord ++ tailWord_1533332).sum := by decide
  have hdescent : baseEnd_1533332 < baseStart_1533332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533338 : List Nat := [3, 1, 1, 4, 1, 1, 2, 3, 3, 1, 3]
def baseStart_1533338 : Nat := 118140960795 + 1533338 * 2 ^ 59
def prefixEnd_1533338 : Nat := 4983230072969 + 3 ^ 40 * 1533338 * 2
def baseEnd_1533338 : Nat := 787339399803827041723313

theorem tailTrace_1533338 : CollatzResearch.WordTrace tailWord_1533338 prefixEnd_1533338 787339399803827041723313 := by
  unfold tailWord_1533338
  simp only [CollatzResearch.WordTrace]
  refine ⟨13981357829746443531678167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37283620879323849417808445 13981357829746443531678167)
  ·
    refine ⟨20972036744619665297517251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13981357829746443531678167 20972036744619665297517251)
    ·
      refine ⟨31458055116929497946275877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20972036744619665297517251 31458055116929497946275877)
      ·
        refine ⟨5898385334424280864926727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31458055116929497946275877 5898385334424280864926727)
        ·
          refine ⟨8847578001636421297390091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5898385334424280864926727 8847578001636421297390091)
          ·
            refine ⟨13271367002454631946085137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8847578001636421297390091 13271367002454631946085137)
            ·
              refine ⟨9953525251840973959563853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13271367002454631946085137 9953525251840973959563853)
              ·
                refine ⟨3732571969440365234836445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9953525251840973959563853 3732571969440365234836445)
                ·
                  refine ⟨1399714488540136963063667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3732571969440365234836445 1399714488540136963063667)
                  ·
                    refine ⟨2099571732810205444595501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1399714488540136963063667 2099571732810205444595501)
                    ·
                      refine ⟨787339399803827041723313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2099571732810205444595501 787339399803827041723313)
                      ·
                        rfl

theorem cell23_1533338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_1533338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533338 prefixEnd_1533338 := by exact prefixLift 1533338
  have htrace : WordTrace (prefixWord ++ tailWord_1533338) baseStart_1533338 baseEnd_1533338 := by
    simpa [prefixWord, tailWord_1533338, baseEnd_1533338] using wordTrace_append hprefix tailTrace_1533338
  have hstable : (prefixWord ++ tailWord_1533338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533338).length < 2 ^ (prefixWord ++ tailWord_1533338).sum := by decide
  have hdescent : baseEnd_1533338 < baseStart_1533338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533341 : List Nat := [1, 4, 2, 1, 3, 1, 1, 2, 3, 5]
def baseStart_1533341 : Nat := 118140960795 + 1533341 * 2 ^ 59
def prefixEnd_1533341 : Nat := 4983230072969 + 3 ^ 40 * 1533341 * 2
def baseEnd_1533341 : Nat := 262446980081930176661933

theorem tailTrace_1533341 : CollatzResearch.WordTrace tailWord_1533341 prefixEnd_1533341 262446980081930176661933 := by
  unfold tailWord_1533341
  simp only [CollatzResearch.WordTrace]
  refine ⟨55925540737974905639071877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37283693825316603759381251 55925540737974905639071877)
  ·
    refine ⟨10486038888370294807325977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55925540737974905639071877 10486038888370294807325977)
    ·
      refine ⟨7864529166277721105494483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10486038888370294807325977 7864529166277721105494483)
      ·
        refine ⟨11796793749416581658241725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7864529166277721105494483 11796793749416581658241725)
        ·
          refine ⟨4423797656031218121840647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11796793749416581658241725 4423797656031218121840647)
          ·
            refine ⟨6635696484046827182760971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4423797656031218121840647 6635696484046827182760971)
            ·
              refine ⟨9953544726070240774141457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6635696484046827182760971 9953544726070240774141457)
              ·
                refine ⟨7465158544552680580606093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9953544726070240774141457 7465158544552680580606093)
                ·
                  refine ⟨2799434454207255217727285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7465158544552680580606093 2799434454207255217727285)
                  ·
                    refine ⟨262446980081930176661933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2799434454207255217727285 262446980081930176661933)
                    ·
                      rfl

theorem cell23_1533341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_1533341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533341 prefixEnd_1533341 := by exact prefixLift 1533341
  have htrace : WordTrace (prefixWord ++ tailWord_1533341) baseStart_1533341 baseEnd_1533341 := by
    simpa [prefixWord, tailWord_1533341, baseEnd_1533341] using wordTrace_append hprefix tailTrace_1533341
  have hstable : (prefixWord ++ tailWord_1533341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533341).length < 2 ^ (prefixWord ++ tailWord_1533341).sum := by decide
  have hdescent : baseEnd_1533341 < baseStart_1533341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533361 : List Nat := [1, 2, 2, 4, 1, 1, 1, 3, 3, 1, 4]
def baseStart_1533361 : Nat := 118140960795 + 1533361 * 2 ^ 59
def prefixEnd_1533361 : Nat := 4983230072969 + 3 ^ 40 * 1533361 * 2
def baseEnd_1533361 : Nat := 787351209858880451735707

theorem tailTrace_1533361 : CollatzResearch.WordTrace tailWord_1533361 prefixEnd_1533361 787351209858880451735707 := by
  unfold tailWord_1533361
  simp only [CollatzResearch.WordTrace]
  refine ⟨55926270197902449054799937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37284180131934966036533291 55926270197902449054799937)
  ·
    refine ⟨41944702648426836791099953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55926270197902449054799937 41944702648426836791099953)
    ·
      refine ⟨31458526986320127593324965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41944702648426836791099953 31458526986320127593324965)
      ·
        refine ⟨5898473809935023923748431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31458526986320127593324965 5898473809935023923748431)
        ·
          refine ⟨8847710714902535885622647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5898473809935023923748431 8847710714902535885622647)
          ·
            refine ⟨13271566072353803828433971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8847710714902535885622647 13271566072353803828433971)
            ·
              refine ⟨19907349108530705742650957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13271566072353803828433971 19907349108530705742650957)
              ·
                refine ⟨7465255915699014653494109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19907349108530705742650957 7465255915699014653494109)
                ·
                  refine ⟨2799470968387130495060291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7465255915699014653494109 2799470968387130495060291)
                  ·
                    refine ⟨4199206452580695742590437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2799470968387130495060291 4199206452580695742590437)
                    ·
                      refine ⟨787351209858880451735707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4199206452580695742590437 787351209858880451735707)
                      ·
                        rfl

theorem cell23_1533361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_1533361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533361 prefixEnd_1533361 := by exact prefixLift 1533361
  have htrace : WordTrace (prefixWord ++ tailWord_1533361) baseStart_1533361 baseEnd_1533361 := by
    simpa [prefixWord, tailWord_1533361, baseEnd_1533361] using wordTrace_append hprefix tailTrace_1533361
  have hstable : (prefixWord ++ tailWord_1533361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533361).length < 2 ^ (prefixWord ++ tailWord_1533361).sum := by decide
  have hdescent : baseEnd_1533361 < baseStart_1533361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533365 : List Nat := [1, 3, 3, 2, 2, 1, 3, 1, 2, 3, 2]
def baseStart_1533365 : Nat := 118140960795 + 1533365 * 2 ^ 59
def prefixEnd_1533365 : Nat := 4983230072969 + 3 ^ 40 * 1533365 * 2
def baseEnd_1533365 : Nat := 787353263781498436085689

theorem tailTrace_1533365 : CollatzResearch.WordTrace tailWord_1533365 prefixEnd_1533365 787353263781498436085689 := by
  unfold tailWord_1533365
  simp only [CollatzResearch.WordTrace]
  refine ⟨55926416089887957737945549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37284277393258638491963699 55926416089887957737945549)
  ·
    refine ⟨20972406033707984151729581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55926416089887957737945549 20972406033707984151729581)
    ·
      refine ⟨7864652262640494056898593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20972406033707984151729581 7864652262640494056898593)
      ·
        refine ⟨5898489196980370542673945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7864652262640494056898593 5898489196980370542673945)
        ·
          refine ⟨4423866897735277907005459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5898489196980370542673945 4423866897735277907005459)
          ·
            refine ⟨6635800346602916860508189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4423866897735277907005459 6635800346602916860508189)
            ·
              refine ⟨2488425129976093822690571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6635800346602916860508189 2488425129976093822690571)
              ·
                refine ⟨3732637694964140734035857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2488425129976093822690571 3732637694964140734035857)
                ·
                  refine ⟨2799478271223105550526893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3732637694964140734035857 2799478271223105550526893)
                  ·
                    refine ⟨1049804351708664581447585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2799478271223105550526893 1049804351708664581447585)
                    ·
                      refine ⟨787353263781498436085689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1049804351708664581447585 787353263781498436085689)
                      ·
                        rfl

theorem cell23_1533365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_1533365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533365 prefixEnd_1533365 := by exact prefixLift 1533365
  have htrace : WordTrace (prefixWord ++ tailWord_1533365) baseStart_1533365 baseEnd_1533365 := by
    simpa [prefixWord, tailWord_1533365, baseEnd_1533365] using wordTrace_append hprefix tailTrace_1533365
  have hstable : (prefixWord ++ tailWord_1533365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533365).length < 2 ^ (prefixWord ++ tailWord_1533365).sum := by decide
  have hdescent : baseEnd_1533365 < baseStart_1533365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533384 : List Nat := [2, 1, 3, 1, 3, 1, 12]
def baseStart_1533384 : Nat := 118140960795 + 1533384 * 2 ^ 59
def prefixEnd_1533384 : Nat := 4983230072969 + 3 ^ 40 * 1533384 * 2
def baseEnd_1533384 : Nat := 9720531110048566194421

theorem tailTrace_1533384 : CollatzResearch.WordTrace tailWord_1533384 prefixEnd_1533384 9720531110048566194421 := by
  unfold tailWord_1533384
  simp only [CollatzResearch.WordTrace]
  refine ⟨27963554538409561991443603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37284739384546082655258137 27963554538409561991443603)
  ·
    refine ⟨41945331807614342987165405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27963554538409561991443603 41945331807614342987165405)
    ·
      refine ⟨15729499427855378620187027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41945331807614342987165405 15729499427855378620187027)
      ·
        refine ⟨23594249141783067930280541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15729499427855378620187027 23594249141783067930280541)
        ·
          refine ⟨8847843428168650473855203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23594249141783067930280541 8847843428168650473855203)
          ·
            refine ⟨13271765142252975710782805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8847843428168650473855203 13271765142252975710782805)
            ·
              refine ⟨9720531110048566194421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 13271765142252975710782805 9720531110048566194421)
              ·
                rfl

theorem cell23_1533384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 12].length) (baseStart_1533384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533384 prefixEnd_1533384 := by exact prefixLift 1533384
  have htrace : WordTrace (prefixWord ++ tailWord_1533384) baseStart_1533384 baseEnd_1533384 := by
    simpa [prefixWord, tailWord_1533384, baseEnd_1533384] using wordTrace_append hprefix tailTrace_1533384
  have hstable : (prefixWord ++ tailWord_1533384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533384).length < 2 ^ (prefixWord ++ tailWord_1533384).sum := by decide
  have hdescent : baseEnd_1533384 < baseStart_1533384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533388 : List Nat := [2, 2, 1, 4, 2, 2, 1, 1, 4, 4]
def baseStart_1533388 : Nat := 118140960795 + 1533388 * 2 ^ 59
def prefixEnd_1533388 : Nat := 4983230072969 + 3 ^ 40 * 1533388 * 2
def baseEnd_1533388 : Nat := 262455024612183948699361

theorem tailTrace_1533388 : CollatzResearch.WordTrace tailWord_1533388 prefixEnd_1533388 262455024612183948699361 := by
  unfold tailWord_1533388
  simp only [CollatzResearch.WordTrace]
  refine ⟨27963627484402316333016409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37284836645869755110688545 27963627484402316333016409)
  ·
    refine ⟨20972720613301737249762307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27963627484402316333016409 20972720613301737249762307)
    ·
      refine ⟨31459080919952605874643461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20972720613301737249762307 31459080919952605874643461)
      ·
        refine ⟨5898577672491113601495649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31459080919952605874643461 5898577672491113601495649)
        ·
          refine ⟨4423933254368335201121737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5898577672491113601495649 4423933254368335201121737)
          ·
            refine ⟨3317949940776251400841303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4423933254368335201121737 3317949940776251400841303)
            ·
              refine ⟨4976924911164377101261955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3317949940776251400841303 4976924911164377101261955)
              ·
                refine ⟨7465387366746565651892933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4976924911164377101261955 7465387366746565651892933)
                ·
                  refine ⟨1399760131264981059729925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7465387366746565651892933 1399760131264981059729925)
                  ·
                    refine ⟨262455024612183948699361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1399760131264981059729925 262455024612183948699361)
                    ·
                      rfl

theorem cell23_1533388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 4, 4].length) (baseStart_1533388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533388 prefixEnd_1533388 := by exact prefixLift 1533388
  have htrace : WordTrace (prefixWord ++ tailWord_1533388) baseStart_1533388 baseEnd_1533388 := by
    simpa [prefixWord, tailWord_1533388, baseEnd_1533388] using wordTrace_append hprefix tailTrace_1533388
  have hstable : (prefixWord ++ tailWord_1533388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533388).length < 2 ^ (prefixWord ++ tailWord_1533388).sum := by decide
  have hdescent : baseEnd_1533388 < baseStart_1533388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533398 : List Nat := [5, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_1533398 : Nat := 118140960795 + 1533398 * 2 ^ 59
def prefixEnd_1533398 : Nat := 4983230072969 + 3 ^ 40 * 1533398 * 2
def baseEnd_1533398 : Nat := 787370208643096806973037

theorem tailTrace_1533398 : CollatzResearch.WordTrace tailWord_1533398 prefixEnd_1533398 787370208643096806973037 := by
  unfold tailWord_1533398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3495476231173025273368553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37285079799178936249264565 3495476231173025273368553)
  ·
    refine ⟨2621607173379768955026415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3495476231173025273368553 2621607173379768955026415)
    ·
      refine ⟨3932410760069653432539623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2621607173379768955026415 3932410760069653432539623)
      ·
        refine ⟨5898616140104480148809435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3932410760069653432539623 5898616140104480148809435)
        ·
          refine ⟨8847924210156720223214153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5898616140104480148809435 8847924210156720223214153)
          ·
            refine ⟨6635943157617540167410615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8847924210156720223214153 6635943157617540167410615)
            ·
              refine ⟨9953914736426310251115923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6635943157617540167410615 9953914736426310251115923)
              ·
                refine ⟨14930872104639465376673885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9953914736426310251115923 14930872104639465376673885)
                ·
                  refine ⟨5599077039239799516252707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14930872104639465376673885 5599077039239799516252707)
                  ·
                    refine ⟨8398615558859699274379061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5599077039239799516252707 8398615558859699274379061)
                    ·
                      refine ⟨787370208643096806973037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8398615558859699274379061 787370208643096806973037)
                      ·
                        rfl

theorem cell23_1533398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_1533398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533398 prefixEnd_1533398 := by exact prefixLift 1533398
  have htrace : WordTrace (prefixWord ++ tailWord_1533398) baseStart_1533398 baseEnd_1533398 := by
    simpa [prefixWord, tailWord_1533398, baseEnd_1533398] using wordTrace_append hprefix tailTrace_1533398
  have hstable : (prefixWord ++ tailWord_1533398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533398).length < 2 ^ (prefixWord ++ tailWord_1533398).sum := by decide
  have hdescent : baseEnd_1533398 < baseStart_1533398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533415 : List Nat := [1, 1, 5, 2, 1, 3, 2, 2, 1, 2, 3]
def baseStart_1533415 : Nat := 118140960795 + 1533415 * 2 ^ 59
def prefixEnd_1533415 : Nat := 4983230072969 + 3 ^ 40 * 1533415 * 2
def baseEnd_1533415 : Nat := 787378937814223240460459

theorem tailTrace_1533415 : CollatzResearch.WordTrace tailWord_1533415 prefixEnd_1533415 787378937814223240460459 := by
  unfold tailWord_1533415
  simp only [CollatzResearch.WordTrace]
  refine ⟨55928239739706816277265699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37285493159804544184843799 55928239739706816277265699)
  ·
    refine ⟨83892359609560224415898549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55928239739706816277265699 83892359609560224415898549)
    ·
      refine ⟨7864908713396271038990489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83892359609560224415898549 7864908713396271038990489)
      ·
        refine ⟨5898681535047203279242867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7864908713396271038990489 5898681535047203279242867)
        ·
          refine ⟨8848022302570804918864301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5898681535047203279242867 8848022302570804918864301)
          ·
            refine ⟨3318008363464051844574113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8848022302570804918864301 3318008363464051844574113)
            ·
              refine ⟨2488506272598038883430585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3318008363464051844574113 2488506272598038883430585)
              ·
                refine ⟨1866379704448529162572939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2488506272598038883430585 1866379704448529162572939)
                ·
                  refine ⟨2799569556672793743859409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1866379704448529162572939 2799569556672793743859409)
                  ·
                    refine ⟨2099677167504595307894557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2799569556672793743859409 2099677167504595307894557)
                    ·
                      refine ⟨787378937814223240460459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2099677167504595307894557 787378937814223240460459)
                      ·
                        rfl

theorem cell23_1533415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_1533415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533415 prefixEnd_1533415 := by exact prefixLift 1533415
  have htrace : WordTrace (prefixWord ++ tailWord_1533415) baseStart_1533415 baseEnd_1533415 := by
    simpa [prefixWord, tailWord_1533415, baseEnd_1533415] using wordTrace_append hprefix tailTrace_1533415
  have hstable : (prefixWord ++ tailWord_1533415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533415).length < 2 ^ (prefixWord ++ tailWord_1533415).sum := by decide
  have hdescent : baseEnd_1533415 < baseStart_1533415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533471 : List Nat := [1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 5]
def baseStart_1533471 : Nat := 118140960795 + 1533471 * 2 ^ 59
def prefixEnd_1533471 : Nat := 4983230072969 + 3 ^ 40 * 1533471 * 2
def baseEnd_1533471 : Nat := 787407692730875021360201

theorem tailTrace_1533471 : CollatzResearch.WordTrace tailWord_1533471 prefixEnd_1533471 787407692730875021360201 := by
  unfold tailWord_1533471
  simp only [CollatzResearch.WordTrace]
  refine ⟨55930282227503937841304267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37286854818335958560869511 55930282227503937841304267)
  ·
    refine ⟨83895423341255906761956401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55930282227503937841304267 83895423341255906761956401)
    ·
      refine ⟨62921567505941930071467301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83895423341255906761956401 62921567505941930071467301)
      ·
        refine ⟨11797793907364111888400119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62921567505941930071467301 11797793907364111888400119)
        ·
          refine ⟨17696690861046167832600179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11797793907364111888400119 17696690861046167832600179)
          ·
            refine ⟨26545036291569251748900269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17696690861046167832600179 26545036291569251748900269)
            ·
              refine ⟨9954388609338469405837601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26545036291569251748900269 9954388609338469405837601)
              ·
                refine ⟨7465791457003852054378201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9954388609338469405837601 7465791457003852054378201)
                ·
                  refine ⟨5599343592752889040783651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7465791457003852054378201 5599343592752889040783651)
                  ·
                    refine ⟨8399015389129333561175477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5599343592752889040783651 8399015389129333561175477)
                    ·
                      refine ⟨787407692730875021360201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8399015389129333561175477 787407692730875021360201)
                      ·
                        rfl

theorem cell23_1533471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_1533471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533471 prefixEnd_1533471 := by exact prefixLift 1533471
  have htrace : WordTrace (prefixWord ++ tailWord_1533471) baseStart_1533471 baseEnd_1533471 := by
    simpa [prefixWord, tailWord_1533471, baseEnd_1533471] using wordTrace_append hprefix tailTrace_1533471
  have hstable : (prefixWord ++ tailWord_1533471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533471).length < 2 ^ (prefixWord ++ tailWord_1533471).sum := by decide
  have hdescent : baseEnd_1533471 < baseStart_1533471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533472 : List Nat := [2, 1, 1, 6, 1, 1, 3, 2, 1, 3, 2]
def baseStart_1533472 : Nat := 118140960795 + 1533472 * 2 ^ 59
def prefixEnd_1533472 : Nat := 4983230072969 + 3 ^ 40 * 1533472 * 2
def baseEnd_1533472 : Nat := 787408206211529517447697

theorem tailTrace_1533472 : CollatzResearch.WordTrace tailWord_1533472 prefixEnd_1533472 787408206211529517447697 := by
  unfold tailWord_1533472
  simp only [CollatzResearch.WordTrace]
  refine ⟨27965159350250157506045335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37286879133666876674727113 27965159350250157506045335)
  ·
    refine ⟨41947739025375236259068003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27965159350250157506045335 41947739025375236259068003)
    ·
      refine ⟨62921608538062854388602005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41947739025375236259068003 62921608538062854388602005)
      ·
        refine ⟨2949450400221696299465719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 62921608538062854388602005 2949450400221696299465719)
        ·
          refine ⟨4424175600332544449198579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2949450400221696299465719 4424175600332544449198579)
          ·
            refine ⟨6636263400498816673797869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4424175600332544449198579 6636263400498816673797869)
            ·
              refine ⟨2488598775187056252674201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6636263400498816673797869 2488598775187056252674201)
              ·
                refine ⟨1866449081390292189505651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2488598775187056252674201 1866449081390292189505651)
                ·
                  refine ⟨2799673622085438284258477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1866449081390292189505651 2799673622085438284258477)
                  ·
                    refine ⟨1049877608282039356596929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2799673622085438284258477 1049877608282039356596929)
                    ·
                      refine ⟨787408206211529517447697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1049877608282039356596929 787408206211529517447697)
                      ·
                        rfl

theorem cell23_1533472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_1533472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533472 prefixEnd_1533472 := by exact prefixLift 1533472
  have htrace : WordTrace (prefixWord ++ tailWord_1533472) baseStart_1533472 baseEnd_1533472 := by
    simpa [prefixWord, tailWord_1533472, baseEnd_1533472] using wordTrace_append hprefix tailTrace_1533472
  have hstable : (prefixWord ++ tailWord_1533472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533472).length < 2 ^ (prefixWord ++ tailWord_1533472).sum := by decide
  have hdescent : baseEnd_1533472 < baseStart_1533472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533521 : List Nat := [1, 2, 2, 1, 3, 2, 2, 2, 1, 7]
def baseStart_1533521 : Nat := 118140960795 + 1533521 * 2 ^ 59
def prefixEnd_1533521 : Nat := 4983230072969 + 3 ^ 40 * 1533521 * 2
def baseEnd_1533521 : Nat := 262477788921199941911657

theorem tailTrace_1533521 : CollatzResearch.WordTrace tailWord_1533521 prefixEnd_1533521 262477788921199941911657 := by
  unfold tailWord_1533521
  simp only [CollatzResearch.WordTrace]
  refine ⟨55932105877322796380624417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37288070584881864253749611 55932105877322796380624417)
  ·
    refine ⟨41949079407992097285468313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55932105877322796380624417 41949079407992097285468313)
    ·
      refine ⟨31461809555994072964101235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41949079407992097285468313 31461809555994072964101235)
      ·
        refine ⟨47192714333991109446151853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31461809555994072964101235 47192714333991109446151853)
        ·
          refine ⟨17697267875246666042306945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47192714333991109446151853 17697267875246666042306945)
          ·
            refine ⟨13272950906434999531730209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17697267875246666042306945 13272950906434999531730209)
            ·
              refine ⟨9954713179826249648797657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13272950906434999531730209 9954713179826249648797657)
              ·
                refine ⟨7466034884869687236598243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9954713179826249648797657 7466034884869687236598243)
                ·
                  refine ⟨11199052327304530854897365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7466034884869687236598243 11199052327304530854897365)
                  ·
                    refine ⟨262477788921199941911657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11199052327304530854897365 262477788921199941911657)
                    ·
                      rfl

theorem cell23_1533521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 7].length) (baseStart_1533521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533521 prefixEnd_1533521 := by exact prefixLift 1533521
  have htrace : WordTrace (prefixWord ++ tailWord_1533521) baseStart_1533521 baseEnd_1533521 := by
    simpa [prefixWord, tailWord_1533521, baseEnd_1533521] using wordTrace_append hprefix tailTrace_1533521
  have hstable : (prefixWord ++ tailWord_1533521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533521).length < 2 ^ (prefixWord ++ tailWord_1533521).sum := by decide
  have hdescent : baseEnd_1533521 < baseStart_1533521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533528 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 4, 5, 2]
def baseStart_1533528 : Nat := 118140960795 + 1533528 * 2 ^ 59
def prefixEnd_1533528 : Nat := 4983230072969 + 3 ^ 40 * 1533528 * 2
def baseEnd_1533528 : Nat := 787436961128181298347439

theorem tailTrace_1533528 : CollatzResearch.WordTrace tailWord_1533528 prefixEnd_1533528 787436961128181298347439 := by
  unfold tailWord_1533528
  simp only [CollatzResearch.WordTrace]
  refine ⟨27966180594148718288064619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37288240792198291050752825 27966180594148718288064619)
  ·
    refine ⟨41949270891223077432096929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27966180594148718288064619 41949270891223077432096929)
    ·
      refine ⟨31461953168417308074072697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41949270891223077432096929 31461953168417308074072697)
      ·
        refine ⟨23596464876312981055554523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31461953168417308074072697 23596464876312981055554523)
        ·
          refine ⟨35394697314469471583331785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23596464876312981055554523 35394697314469471583331785)
          ·
            refine ⟨26546022985852103687498839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35394697314469471583331785 26546022985852103687498839)
            ·
              refine ⟨39819034478778155531248259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26546022985852103687498839 39819034478778155531248259)
              ·
                refine ⟨59728551718167233296872389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39819034478778155531248259 59728551718167233296872389)
                ·
                  refine ⟨11199103447156356243163573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59728551718167233296872389 11199103447156356243163573)
                  ·
                    refine ⟨1049915948170908397796585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11199103447156356243163573 1049915948170908397796585)
                    ·
                      refine ⟨787436961128181298347439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1049915948170908397796585 787436961128181298347439)
                      ·
                        rfl

theorem cell23_1533528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 4, 5, 2].length) (baseStart_1533528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533528 prefixEnd_1533528 := by exact prefixLift 1533528
  have htrace : WordTrace (prefixWord ++ tailWord_1533528) baseStart_1533528 baseEnd_1533528 := by
    simpa [prefixWord, tailWord_1533528, baseEnd_1533528] using wordTrace_append hprefix tailTrace_1533528
  have hstable : (prefixWord ++ tailWord_1533528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533528).length < 2 ^ (prefixWord ++ tailWord_1533528).sum := by decide
  have hdescent : baseEnd_1533528 < baseStart_1533528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533571 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 6]
def baseStart_1533571 : Nat := 118140960795 + 1533571 * 2 ^ 59
def prefixEnd_1533571 : Nat := 4983230072969 + 3 ^ 40 * 1533571 * 2
def baseEnd_1533571 : Nat := 787459040796324630109741

theorem tailTrace_1533571 : CollatzResearch.WordTrace tailWord_1533571 prefixEnd_1533571 787459040796324630109741 := by
  unfold tailWord_1533571
  simp only [CollatzResearch.WordTrace]
  refine ⟨55933929527141654919944567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37289286351427769946629711 55933929527141654919944567)
  ·
    refine ⟨83900894290712482379916851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55933929527141654919944567 83900894290712482379916851)
    ·
      refine ⟨125851341436068723569875277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83900894290712482379916851 125851341436068723569875277)
      ·
        refine ⟨47194253038525771338703229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125851341436068723569875277 47194253038525771338703229)
        ·
          refine ⟨17697844889447164252013711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47194253038525771338703229 17697844889447164252013711)
          ·
            refine ⟨26546767334170746378020567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17697844889447164252013711 26546767334170746378020567)
            ·
              refine ⟨39820151001256119567030851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26546767334170746378020567 39820151001256119567030851)
              ·
                refine ⟨59730226501884179350546277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39820151001256119567030851 59730226501884179350546277)
                ·
                  refine ⟨11199417469103283628227427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59730226501884179350546277 11199417469103283628227427)
                  ·
                    refine ⟨16799126203654925442341141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11199417469103283628227427 16799126203654925442341141)
                    ·
                      refine ⟨787459040796324630109741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16799126203654925442341141 787459040796324630109741)
                      ·
                        rfl

theorem cell23_1533571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_1533571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533571 prefixEnd_1533571 := by exact prefixLift 1533571
  have htrace : WordTrace (prefixWord ++ tailWord_1533571) baseStart_1533571 baseEnd_1533571 := by
    simpa [prefixWord, tailWord_1533571, baseEnd_1533571] using wordTrace_append hprefix tailTrace_1533571
  have hstable : (prefixWord ++ tailWord_1533571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533571).length < 2 ^ (prefixWord ++ tailWord_1533571).sum := by decide
  have hdescent : baseEnd_1533571 < baseStart_1533571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533575 : List Nat := [1, 1, 4, 2, 1, 3, 2, 1, 2, 4, 2]
def baseStart_1533575 : Nat := 118140960795 + 1533575 * 2 ^ 59
def prefixEnd_1533575 : Nat := 4983230072969 + 3 ^ 40 * 1533575 * 2
def baseEnd_1533575 : Nat := 787461094718942614459723

theorem tailTrace_1533575 : CollatzResearch.WordTrace tailWord_1533575 prefixEnd_1533575 787461094718942614459723 := by
  unfold tailWord_1533575
  simp only [CollatzResearch.WordTrace]
  refine ⟨55934075419127163603090179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37289383612751442402060119 55934075419127163603090179)
  ·
    refine ⟨83901113128690745404635269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55934075419127163603090179 83901113128690745404635269)
    ·
      refine ⟨15731458711629514763369113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83901113128690745404635269 15731458711629514763369113)
      ·
        refine ⟨11798594033722136072526835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15731458711629514763369113 11798594033722136072526835)
        ·
          refine ⟨17697891050583204108790253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11798594033722136072526835 17697891050583204108790253)
          ·
            refine ⟨6636709143968701540796345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17697891050583204108790253 6636709143968701540796345)
            ·
              refine ⟨4977531857976526155597259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6636709143968701540796345 4977531857976526155597259)
              ·
                refine ⟨7466297786964789233395889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4977531857976526155597259 7466297786964789233395889)
                ·
                  refine ⟨5599723340223591925046917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7466297786964789233395889 5599723340223591925046917)
                  ·
                    refine ⟨1049948126291923485946297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5599723340223591925046917 1049948126291923485946297)
                    ·
                      refine ⟨787461094718942614459723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1049948126291923485946297 787461094718942614459723)
                      ·
                        rfl

theorem cell23_1533575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_1533575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533575 prefixEnd_1533575 := by exact prefixLift 1533575
  have htrace : WordTrace (prefixWord ++ tailWord_1533575) baseStart_1533575 baseEnd_1533575 := by
    simpa [prefixWord, tailWord_1533575, baseEnd_1533575] using wordTrace_append hprefix tailTrace_1533575
  have hstable : (prefixWord ++ tailWord_1533575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533575).length < 2 ^ (prefixWord ++ tailWord_1533575).sum := by decide
  have hdescent : baseEnd_1533575 < baseStart_1533575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533658 : List Nat := [3, 1, 1, 2, 2, 3, 1, 1, 3, 6]
def baseStart_1533658 : Nat := 118140960795 + 1533658 * 2 ^ 59
def prefixEnd_1533658 : Nat := 4983230072969 + 3 ^ 40 * 1533658 * 2
def baseEnd_1533658 : Nat := 262501237871088596573947

theorem tailTrace_1533658 : CollatzResearch.WordTrace tailWord_1533658 prefixEnd_1533658 262501237871088596573947 := by
  unfold tailWord_1533658
  simp only [CollatzResearch.WordTrace]
  refine ⟨13984275669456617194590407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37291401785217645852241085 13984275669456617194590407)
  ·
    refine ⟨20976413504184925791885611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13984275669456617194590407 20976413504184925791885611)
    ·
      refine ⟨31464620256277388687828417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20976413504184925791885611 31464620256277388687828417)
      ·
        refine ⟨23598465192208041515871313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31464620256277388687828417 23598465192208041515871313)
        ·
          refine ⟨17698848894156031136903485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23598465192208041515871313 17698848894156031136903485)
          ·
            refine ⟨6637068335308511676338807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17698848894156031136903485 6637068335308511676338807)
            ·
              refine ⟨9955602502962767514508211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6637068335308511676338807 9955602502962767514508211)
              ·
                refine ⟨14933403754444151271762317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9955602502962767514508211 14933403754444151271762317)
                ·
                  refine ⟨5600026407916556726910869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14933403754444151271762317 5600026407916556726910869)
                  ·
                    refine ⟨262501237871088596573947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5600026407916556726910869 262501237871088596573947)
                    ·
                      rfl

theorem cell23_1533658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 3, 6].length) (baseStart_1533658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533658 prefixEnd_1533658 := by exact prefixLift 1533658
  have htrace : WordTrace (prefixWord ++ tailWord_1533658) baseStart_1533658 baseEnd_1533658 := by
    simpa [prefixWord, tailWord_1533658, baseEnd_1533658] using wordTrace_append hprefix tailTrace_1533658
  have hstable : (prefixWord ++ tailWord_1533658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533658).length < 2 ^ (prefixWord ++ tailWord_1533658).sum := by decide
  have hdescent : baseEnd_1533658 < baseStart_1533658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533675 : List Nat := [1, 1, 1, 1, 2, 4, 3, 4, 2, 4]
def baseStart_1533675 : Nat := 118140960795 + 1533675 * 2 ^ 59
def prefixEnd_1533675 : Nat := 4983230072969 + 3 ^ 40 * 1533675 * 2
def baseEnd_1533675 : Nat := 262504147594797407736421

theorem tailTrace_1533675 : CollatzResearch.WordTrace tailWord_1533675 prefixEnd_1533675 262504147594797407736421 := by
  unfold tailWord_1533675
  simp only [CollatzResearch.WordTrace]
  refine ⟨55937722718764880681730479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37291815145843253787820319 55937722718764880681730479)
  ·
    refine ⟨83906584078147321022595719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55937722718764880681730479 83906584078147321022595719)
    ·
      refine ⟨125859876117220981533893579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83906584078147321022595719 125859876117220981533893579)
      ·
        refine ⟨188789814175831472300840369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125859876117220981533893579 188789814175831472300840369)
        ·
          refine ⟨141592360631873604225630277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188789814175831472300840369 141592360631873604225630277)
          ·
            refine ⟨26548567618476300792305677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141592360631873604225630277 26548567618476300792305677)
            ·
              refine ⟨9955712856928612797114629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26548567618476300792305677 9955712856928612797114629)
              ·
                refine ⟨1866696160674114899458993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9955712856928612797114629 1866696160674114899458993)
                ·
                  refine ⟨1400022120505586174594245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1866696160674114899458993 1400022120505586174594245)
                  ·
                    refine ⟨262504147594797407736421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1400022120505586174594245 262504147594797407736421)
                    ·
                      rfl

theorem cell23_1533675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 2, 4].length) (baseStart_1533675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533675 prefixEnd_1533675 := by exact prefixLift 1533675
  have htrace : WordTrace (prefixWord ++ tailWord_1533675) baseStart_1533675 baseEnd_1533675 := by
    simpa [prefixWord, tailWord_1533675, baseEnd_1533675] using wordTrace_append hprefix tailTrace_1533675
  have hstable : (prefixWord ++ tailWord_1533675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533675).length < 2 ^ (prefixWord ++ tailWord_1533675).sum := by decide
  have hdescent : baseEnd_1533675 < baseStart_1533675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533719 : List Nat := [1, 1, 3, 4, 2, 1, 4, 1, 1, 2, 3]
def baseStart_1533719 : Nat := 118140960795 + 1533719 * 2 ^ 59
def prefixEnd_1533719 : Nat := 4983230072969 + 3 ^ 40 * 1533719 * 2
def baseEnd_1533719 : Nat := 787535035933190051059061

theorem tailTrace_1533719 : CollatzResearch.WordTrace tailWord_1533719 prefixEnd_1533719 787535035933190051059061 := by
  unfold tailWord_1533719
  simp only [CollatzResearch.WordTrace]
  refine ⟨55939327530605476196332211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37292885020403650797554807 55939327530605476196332211)
  ·
    refine ⟨83908991295908214294498317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55939327530605476196332211 83908991295908214294498317)
    ·
      refine ⟨31465871735965580360436869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83908991295908214294498317 31465871735965580360436869)
      ·
        refine ⟨5899850950493546317581913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31465871735965580360436869 5899850950493546317581913)
        ·
          refine ⟨4424888212870159738186435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5899850950493546317581913 4424888212870159738186435)
          ·
            refine ⟨6637332319305239607279653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4424888212870159738186435 6637332319305239607279653)
            ·
              refine ⟨1244499809869732426364935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6637332319305239607279653 1244499809869732426364935)
              ·
                refine ⟨1866749714804598639547403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1244499809869732426364935 1866749714804598639547403)
                ·
                  refine ⟨2800124572206897959321105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1866749714804598639547403 2800124572206897959321105)
                  ·
                    refine ⟨2100093429155173469490829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2800124572206897959321105 2100093429155173469490829)
                    ·
                      refine ⟨787535035933190051059061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2100093429155173469490829 787535035933190051059061)
                      ·
                        rfl

theorem cell23_1533719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_1533719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533719 prefixEnd_1533719 := by exact prefixLift 1533719
  have htrace : WordTrace (prefixWord ++ tailWord_1533719) baseStart_1533719 baseEnd_1533719 := by
    simpa [prefixWord, tailWord_1533719, baseEnd_1533719] using wordTrace_append hprefix tailTrace_1533719
  have hstable : (prefixWord ++ tailWord_1533719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533719).length < 2 ^ (prefixWord ++ tailWord_1533719).sum := by decide
  have hdescent : baseEnd_1533719 < baseStart_1533719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533726 : List Nat := [4, 3, 2, 2, 1, 1, 1, 1, 4, 4]
def baseStart_1533726 : Nat := 118140960795 + 1533726 * 2 ^ 59
def prefixEnd_1533726 : Nat := 4983230072969 + 3 ^ 40 * 1533726 * 2
def baseEnd_1533726 : Nat := 262512876765923841223843

theorem tailTrace_1533726 : CollatzResearch.WordTrace tailWord_1533726 prefixEnd_1533726 262512876765923841223843 := by
  unfold tailWord_1533726
  simp only [CollatzResearch.WordTrace]
  refine ⟨6992447855197514548979629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37293055227720077594558021 6992447855197514548979629)
  ·
    refine ⟨2622167945699067955867361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6992447855197514548979629 2622167945699067955867361)
    ·
      refine ⟨1966625959274300966900521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2622167945699067955867361 1966625959274300966900521)
      ·
        refine ⟨1474969469455725725175391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1966625959274300966900521 1474969469455725725175391)
        ·
          refine ⟨2212454204183588587763087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1474969469455725725175391 2212454204183588587763087)
          ·
            refine ⟨3318681306275382881644631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2212454204183588587763087 3318681306275382881644631)
            ·
              refine ⟨4978021959413074322466947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3318681306275382881644631 4978021959413074322466947)
              ·
                refine ⟨7467032939119611483700421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4978021959413074322466947 7467032939119611483700421)
                ·
                  refine ⟨1400068676084927153193829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7467032939119611483700421 1400068676084927153193829)
                  ·
                    refine ⟨262512876765923841223843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1400068676084927153193829 262512876765923841223843)
                    ·
                      rfl

theorem cell23_1533726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_1533726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533726 prefixEnd_1533726 := by exact prefixLift 1533726
  have htrace : WordTrace (prefixWord ++ tailWord_1533726) baseStart_1533726 baseEnd_1533726 := by
    simpa [prefixWord, tailWord_1533726, baseEnd_1533726] using wordTrace_append hprefix tailTrace_1533726
  have hstable : (prefixWord ++ tailWord_1533726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533726).length < 2 ^ (prefixWord ++ tailWord_1533726).sum := by decide
  have hdescent : baseEnd_1533726 < baseStart_1533726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533749 : List Nat := [1, 3, 3, 1, 4, 2, 1, 1, 1, 3, 3]
def baseStart_1533749 : Nat := 118140960795 + 1533749 * 2 ^ 59
def prefixEnd_1533749 : Nat := 4983230072969 + 3 ^ 40 * 1533749 * 2
def baseEnd_1533749 : Nat := 787550440352824933683923

theorem tailTrace_1533749 : CollatzResearch.WordTrace tailWord_1533749 prefixEnd_1533749 787550440352824933683923 := by
  unfold tailWord_1533749
  simp only [CollatzResearch.WordTrace]
  refine ⟨55940421720496791319924301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37293614480331194213282867 55940421720496791319924301)
  ·
    refine ⟨20977658145186296744971613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55940421720496791319924301 20977658145186296744971613)
    ·
      refine ⟨7866621804444861279364355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20977658145186296744971613 7866621804444861279364355)
      ·
        refine ⟨11799932706667291919046533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7866621804444861279364355 11799932706667291919046533)
        ·
          refine ⟨2212487382500117234821225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11799932706667291919046533 2212487382500117234821225)
          ·
            refine ⟨1659365536875087926115919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2212487382500117234821225 1659365536875087926115919)
            ·
              refine ⟨2489048305312631889173879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1659365536875087926115919 2489048305312631889173879)
              ·
                refine ⟨3733572457968947833760819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2489048305312631889173879 3733572457968947833760819)
                ·
                  refine ⟨5600358686953421750641229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3733572457968947833760819 5600358686953421750641229)
                  ·
                    refine ⟨2100134507607533156490461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5600358686953421750641229 2100134507607533156490461)
                    ·
                      refine ⟨787550440352824933683923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2100134507607533156490461 787550440352824933683923)
                      ·
                        rfl

theorem cell23_1533749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_1533749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533749 prefixEnd_1533749 := by exact prefixLift 1533749
  have htrace : WordTrace (prefixWord ++ tailWord_1533749) baseStart_1533749 baseEnd_1533749 := by
    simpa [prefixWord, tailWord_1533749, baseEnd_1533749] using wordTrace_append hprefix tailTrace_1533749
  have hstable : (prefixWord ++ tailWord_1533749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533749).length < 2 ^ (prefixWord ++ tailWord_1533749).sum := by decide
  have hdescent : baseEnd_1533749 < baseStart_1533749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533766 : List Nat := [6, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3]
def baseStart_1533766 : Nat := 118140960795 + 1533766 * 2 ^ 59
def prefixEnd_1533766 : Nat := 4983230072969 + 3 ^ 40 * 1533766 * 2
def baseEnd_1533766 : Nat := 787559169523951367171345

theorem tailTrace_1533766 : CollatzResearch.WordTrace tailWord_1533766 prefixEnd_1533766 787559169523951367171345 := by
  unfold tailWord_1533766
  simp only [CollatzResearch.WordTrace]
  refine ⟨1748157555044850100727911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37294027840956802148862101 1748157555044850100727911)
  ·
    refine ⟨2622236332567275151091867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1748157555044850100727911 2622236332567275151091867)
    ·
      refine ⟨3933354498850912726637801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2622236332567275151091867 3933354498850912726637801)
      ·
        refine ⟨2950015874138184544978351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3933354498850912726637801 2950015874138184544978351)
        ·
          refine ⟨4425023811207276817467527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2950015874138184544978351 4425023811207276817467527)
          ·
            refine ⟨6637535716810915226201291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4425023811207276817467527 6637535716810915226201291)
            ·
              refine ⟨9956303575216372839301937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6637535716810915226201291 9956303575216372839301937)
              ·
                refine ⟨7467227681412279629476453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9956303575216372839301937 7467227681412279629476453)
                ·
                  refine ⟨1400105190264802430526835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7467227681412279629476453 1400105190264802430526835)
                  ·
                    refine ⟨2100157785397203645790253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1400105190264802430526835 2100157785397203645790253)
                    ·
                      refine ⟨787559169523951367171345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2100157785397203645790253 787559169523951367171345)
                      ·
                        rfl

theorem cell23_1533766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_1533766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533766 prefixEnd_1533766 := by exact prefixLift 1533766
  have htrace : WordTrace (prefixWord ++ tailWord_1533766) baseStart_1533766 baseEnd_1533766 := by
    simpa [prefixWord, tailWord_1533766, baseEnd_1533766] using wordTrace_append hprefix tailTrace_1533766
  have hstable : (prefixWord ++ tailWord_1533766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533766).length < 2 ^ (prefixWord ++ tailWord_1533766).sum := by decide
  have hdescent : baseEnd_1533766 < baseStart_1533766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533852 : List Nat := [2, 2, 3, 3, 1, 1, 2, 1, 1, 2, 5]
def baseStart_1533852 : Nat := 118140960795 + 1533852 * 2 ^ 59
def prefixEnd_1533852 : Nat := 4983230072969 + 3 ^ 40 * 1533852 * 2
def baseEnd_1533852 : Nat := 787603328860238030695949

theorem tailTrace_1533852 : CollatzResearch.WordTrace tailWord_1533852 prefixEnd_1533852 787603328860238030695949 := by
  unfold tailWord_1533852
  simp only [CollatzResearch.WordTrace]
  refine ⟨27972089219561819955461905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37296118959415759940615873 27972089219561819955461905)
  ·
    refine ⟨20979066914671364966596429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27972089219561819955461905 20979066914671364966596429)
    ·
      refine ⟨7867150093001761862473661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20979066914671364966596429 7867150093001761862473661)
      ·
        refine ⟨2950181284875660698427623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7867150093001761862473661 2950181284875660698427623)
        ·
          refine ⟨4425271927313491047641435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2950181284875660698427623 4425271927313491047641435)
          ·
            refine ⟨6637907890970236571462153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4425271927313491047641435 6637907890970236571462153)
            ·
              refine ⟨4978430918227677428596615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6637907890970236571462153 4978430918227677428596615)
              ·
                refine ⟨7467646377341516142894923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4978430918227677428596615 7467646377341516142894923)
                ·
                  refine ⟨11201469566012274214342385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7467646377341516142894923 11201469566012274214342385)
                  ·
                    refine ⟨8401102174509205660756789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11201469566012274214342385 8401102174509205660756789)
                    ·
                      refine ⟨787603328860238030695949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8401102174509205660756789 787603328860238030695949)
                      ·
                        rfl

theorem cell23_1533852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_1533852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533852 prefixEnd_1533852 := by exact prefixLift 1533852
  have htrace : WordTrace (prefixWord ++ tailWord_1533852) baseStart_1533852 baseEnd_1533852 := by
    simpa [prefixWord, tailWord_1533852, baseEnd_1533852] using wordTrace_append hprefix tailTrace_1533852
  have hstable : (prefixWord ++ tailWord_1533852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533852).length < 2 ^ (prefixWord ++ tailWord_1533852).sum := by decide
  have hdescent : baseEnd_1533852 < baseStart_1533852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533882 : List Nat := [3, 1, 1, 1, 2, 1, 2, 5, 2, 2, 3]
def baseStart_1533882 : Nat := 118140960795 + 1533882 * 2 ^ 59
def prefixEnd_1533882 : Nat := 4983230072969 + 3 ^ 40 * 1533882 * 2
def baseEnd_1533882 : Nat := 787618733279872913320811

theorem tailTrace_1533882 : CollatzResearch.WordTrace tailWord_1533882 prefixEnd_1533882 787618733279872913320811 := by
  unfold tailWord_1533882
  simp only [CollatzResearch.WordTrace]
  refine ⟨13986318157253738758628975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37296848419343303356343933 13986318157253738758628975)
  ·
    refine ⟨20979477235880608137943463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13986318157253738758628975 20979477235880608137943463)
    ·
      refine ⟨31469215853820912206915195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20979477235880608137943463 31469215853820912206915195)
      ·
        refine ⟨47203823780731368310372793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31469215853820912206915195 47203823780731368310372793)
        ·
          refine ⟨35402867835548526232779595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47203823780731368310372793 35402867835548526232779595)
          ·
            refine ⟨53104301753322789349169393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35402867835548526232779595 53104301753322789349169393)
            ·
              refine ⟨39828226314992092011877045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53104301753322789349169393 39828226314992092011877045)
              ·
                refine ⟨3733896217030508626113473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39828226314992092011877045 3733896217030508626113473)
                ·
                  refine ⟨2800422162772881469585105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3733896217030508626113473 2800422162772881469585105)
                  ·
                    refine ⟨2100316622079661102188829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2800422162772881469585105 2100316622079661102188829)
                    ·
                      refine ⟨787618733279872913320811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2100316622079661102188829 787618733279872913320811)
                      ·
                        rfl

theorem cell23_1533882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 2, 2, 3].length) (baseStart_1533882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533882 prefixEnd_1533882 := by exact prefixLift 1533882
  have htrace : WordTrace (prefixWord ++ tailWord_1533882) baseStart_1533882 baseEnd_1533882 := by
    simpa [prefixWord, tailWord_1533882, baseEnd_1533882] using wordTrace_append hprefix tailTrace_1533882
  have hstable : (prefixWord ++ tailWord_1533882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533882).length < 2 ^ (prefixWord ++ tailWord_1533882).sum := by decide
  have hdescent : baseEnd_1533882 < baseStart_1533882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533906 : List Nat := [3, 2, 2, 3, 2, 1, 2, 1, 3, 4]
def baseStart_1533906 : Nat := 118140960795 + 1533906 * 2 ^ 59
def prefixEnd_1533906 : Nat := 4983230072969 + 3 ^ 40 * 1533906 * 2
def baseEnd_1533906 : Nat := 262543685605193606473567

theorem tailTrace_1533906 : CollatzResearch.WordTrace tailWord_1533906 prefixEnd_1533906 262543685605193606473567 := by
  unfold tailWord_1533906
  simp only [CollatzResearch.WordTrace]
  refine ⟨13986536995232001783347393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37297431987285338088926381 13986536995232001783347393)
  ·
    refine ⟨10489902746424001337510545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13986536995232001783347393 10489902746424001337510545)
    ·
      refine ⟨7867427059818001003132909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10489902746424001337510545 7867427059818001003132909)
      ·
        refine ⟨2950285147431750376174841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7867427059818001003132909 2950285147431750376174841)
        ·
          refine ⟨2212713860573812782131131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2950285147431750376174841 2212713860573812782131131)
          ·
            refine ⟨3319070790860719173196697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2212713860573812782131131 3319070790860719173196697)
            ·
              refine ⟨2489303093145539379897523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3319070790860719173196697 2489303093145539379897523)
              ·
                refine ⟨3733954639718309069846285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2489303093145539379897523 3733954639718309069846285)
                ·
                  refine ⟨1400232989894365901192357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3733954639718309069846285 1400232989894365901192357)
                  ·
                    refine ⟨262543685605193606473567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1400232989894365901192357 262543685605193606473567)
                    ·
                      rfl

theorem cell23_1533906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_1533906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533906 prefixEnd_1533906 := by exact prefixLift 1533906
  have htrace : WordTrace (prefixWord ++ tailWord_1533906) baseStart_1533906 baseEnd_1533906 := by
    simpa [prefixWord, tailWord_1533906, baseEnd_1533906] using wordTrace_append hprefix tailTrace_1533906
  have hstable : (prefixWord ++ tailWord_1533906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533906).length < 2 ^ (prefixWord ++ tailWord_1533906).sum := by decide
  have hdescent : baseEnd_1533906 < baseStart_1533906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533919 : List Nat := [1, 1, 2, 3, 4, 2, 3, 1, 6]
def baseStart_1533919 : Nat := 118140960795 + 1533919 * 2 ^ 59
def prefixEnd_1533919 : Nat := 4983230072969 + 3 ^ 40 * 1533919 * 2
def baseEnd_1533919 : Nat := 87515303562676585395349

theorem tailTrace_1533919 : CollatzResearch.WordTrace tailWord_1533919 prefixEnd_1533919 87515303562676585395349 := by
  unfold tailWord_1533919
  simp only [CollatzResearch.WordTrace]
  refine ⟨55946622129880910353612811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37297748086587273569075207 55946622129880910353612811)
  ·
    refine ⟨83919933194821365530419217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55946622129880910353612811 83919933194821365530419217)
    ·
      refine ⟨62939949896116024147814413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83919933194821365530419217 62939949896116024147814413)
      ·
        refine ⟨23602481211043509055430405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62939949896116024147814413 23602481211043509055430405)
        ·
          refine ⟨4425465227070657947893201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23602481211043509055430405 4425465227070657947893201)
          ·
            refine ⟨3319098920302993460919901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4425465227070657947893201 3319098920302993460919901)
            ·
              refine ⟨1244662095113622547844963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3319098920302993460919901 1244662095113622547844963)
              ·
                refine ⟨1866993142670433821767445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1244662095113622547844963 1866993142670433821767445)
                ·
                  refine ⟨87515303562676585395349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1866993142670433821767445 87515303562676585395349)
                  ·
                    rfl

theorem cell23_1533919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 6].length) (baseStart_1533919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533919 prefixEnd_1533919 := by exact prefixLift 1533919
  have htrace : WordTrace (prefixWord ++ tailWord_1533919) baseStart_1533919 baseEnd_1533919 := by
    simpa [prefixWord, tailWord_1533919, baseEnd_1533919] using wordTrace_append hprefix tailTrace_1533919
  have hstable : (prefixWord ++ tailWord_1533919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533919).length < 2 ^ (prefixWord ++ tailWord_1533919).sum := by decide
  have hdescent : baseEnd_1533919 < baseStart_1533919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533963 : List Nat := [1, 1, 1, 1, 6, 1, 5, 2, 1, 1, 3]
def baseStart_1533963 : Nat := 118140960795 + 1533963 * 2 ^ 59
def prefixEnd_1533963 : Nat := 4983230072969 + 3 ^ 40 * 1533963 * 2
def baseEnd_1533963 : Nat := 787660325212887096407939

theorem tailTrace_1533963 : CollatzResearch.WordTrace tailWord_1533963 prefixEnd_1533963 787660325212887096407939 := by
  unfold tailWord_1533963
  simp only [CollatzResearch.WordTrace]
  refine ⟨55948226941721505868214543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37298817961147670578809695 55948226941721505868214543)
  ·
    refine ⟨83922340412582258802321815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55948226941721505868214543 83922340412582258802321815)
    ·
      refine ⟨125883510618873388203482723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83922340412582258802321815 125883510618873388203482723)
      ·
        refine ⟨188825265928310082305224085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125883510618873388203482723 188825265928310082305224085)
        ·
          refine ⟨8851184340389535108057379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 188825265928310082305224085 8851184340389535108057379)
          ·
            refine ⟨13276776510584302662086069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8851184340389535108057379 13276776510584302662086069)
            ·
              refine ⟨1244697797867278374570569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13276776510584302662086069 1244697797867278374570569)
              ·
                refine ⟨933523348400458780927927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1244697797867278374570569 933523348400458780927927)
                ·
                  refine ⟨1400285022600688171391891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 933523348400458780927927 1400285022600688171391891)
                  ·
                    refine ⟨2100427533901032257087837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1400285022600688171391891 2100427533901032257087837)
                    ·
                      refine ⟨787660325212887096407939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2100427533901032257087837 787660325212887096407939)
                      ·
                        rfl

theorem cell23_1533963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 2, 1, 1, 3].length) (baseStart_1533963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533963 prefixEnd_1533963 := by exact prefixLift 1533963
  have htrace : WordTrace (prefixWord ++ tailWord_1533963) baseStart_1533963 baseEnd_1533963 := by
    simpa [prefixWord, tailWord_1533963, baseEnd_1533963] using wordTrace_append hprefix tailTrace_1533963
  have hstable : (prefixWord ++ tailWord_1533963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533963).length < 2 ^ (prefixWord ++ tailWord_1533963).sum := by decide
  have hdescent : baseEnd_1533963 < baseStart_1533963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533986 : List Nat := [3, 3, 1, 1, 1, 2, 2, 1, 5, 2, 2]
def baseStart_1533986 : Nat := 118140960795 + 1533986 * 2 ^ 59
def prefixEnd_1533986 : Nat := 4983230072969 + 3 ^ 40 * 1533986 * 2
def baseEnd_1533986 : Nat := 787672135267940506420333

theorem tailTrace_1533986 : CollatzResearch.WordTrace tailWord_1533986 prefixEnd_1533986 787672135267940506420333 := by
  unfold tailWord_1533986
  simp only [CollatzResearch.WordTrace]
  refine ⟨13987266455159545199075453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37299377213758787197534541 13987266455159545199075453)
  ·
    refine ⟨5245224920684829449653295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13987266455159545199075453 5245224920684829449653295)
    ·
      refine ⟨7867837381027244174479943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5245224920684829449653295 7867837381027244174479943)
      ·
        refine ⟨11801756071540866261719915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7867837381027244174479943 11801756071540866261719915)
        ·
          refine ⟨17702634107311299392579873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11801756071540866261719915 17702634107311299392579873)
          ·
            refine ⟨13276975580483474544434905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17702634107311299392579873 13276975580483474544434905)
            ·
              refine ⟨9957731685362605908326179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13276975580483474544434905 9957731685362605908326179)
              ·
                refine ⟨14936597528043908862489269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9957731685362605908326179 14936597528043908862489269)
                ·
                  refine ⟨1400306018254116455858369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14936597528043908862489269 1400306018254116455858369)
                  ·
                    refine ⟨1050229513690587341893777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1400306018254116455858369 1050229513690587341893777)
                    ·
                      refine ⟨787672135267940506420333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1050229513690587341893777 787672135267940506420333)
                      ·
                        rfl

theorem cell23_1533986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_1533986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533986 prefixEnd_1533986 := by exact prefixLift 1533986
  have htrace : WordTrace (prefixWord ++ tailWord_1533986) baseStart_1533986 baseEnd_1533986 := by
    simpa [prefixWord, tailWord_1533986, baseEnd_1533986] using wordTrace_append hprefix tailTrace_1533986
  have hstable : (prefixWord ++ tailWord_1533986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533986).length < 2 ^ (prefixWord ++ tailWord_1533986).sum := by decide
  have hdescent : baseEnd_1533986 < baseStart_1533986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533989 : List Nat := [1, 3, 1, 2, 2, 4, 1, 1, 3, 2, 3]
def baseStart_1533989 : Nat := 118140960795 + 1533989 * 2 ^ 59
def prefixEnd_1533989 : Nat := 4983230072969 + 3 ^ 40 * 1533989 * 2
def baseEnd_1533989 : Nat := 787673675709903994682819

theorem tailTrace_1533989 : CollatzResearch.WordTrace tailWord_1533989 prefixEnd_1533989 787673675709903994682819 := by
  unfold tailWord_1533989
  simp only [CollatzResearch.WordTrace]
  refine ⟨55949175239627312308661021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37299450159751541539107347 55949175239627312308661021)
  ·
    refine ⟨20980940714860242115747883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55949175239627312308661021 20980940714860242115747883)
    ·
      refine ⟨31471411072290363173621825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20980940714860242115747883 31471411072290363173621825)
      ·
        refine ⟨23603558304217772380216369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31471411072290363173621825 23603558304217772380216369)
        ·
          refine ⟨17702668728163329285162277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23603558304217772380216369 17702668728163329285162277)
          ·
            refine ⟨3319250386530624240967927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17702668728163329285162277 3319250386530624240967927)
            ·
              refine ⟨4978875579795936361451891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3319250386530624240967927 4978875579795936361451891)
              ·
                refine ⟨7468313369693904542177837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4978875579795936361451891 7468313369693904542177837)
                ·
                  refine ⟨2800617513635214203316689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7468313369693904542177837 2800617513635214203316689)
                  ·
                    refine ⟨2100463135226410652487517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2800617513635214203316689 2100463135226410652487517)
                    ·
                      refine ⟨787673675709903994682819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2100463135226410652487517 787673675709903994682819)
                      ·
                        rfl

theorem cell23_1533989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_1533989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1533989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1533989 prefixEnd_1533989 := by exact prefixLift 1533989
  have htrace : WordTrace (prefixWord ++ tailWord_1533989) baseStart_1533989 baseEnd_1533989 := by
    simpa [prefixWord, tailWord_1533989, baseEnd_1533989] using wordTrace_append hprefix tailTrace_1533989
  have hstable : (prefixWord ++ tailWord_1533989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533989).length < 2 ^ (prefixWord ++ tailWord_1533989).sum := by decide
  have hdescent : baseEnd_1533989 < baseStart_1533989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534014 : List Nat := [4, 2, 1, 3, 3, 1, 2, 2, 1, 1, 3]
def baseStart_1534014 : Nat := 118140960795 + 1534014 * 2 ^ 59
def prefixEnd_1534014 : Nat := 4983230072969 + 3 ^ 40 * 1534014 * 2
def baseEnd_1534014 : Nat := 787686512726266396870205

theorem tailTrace_1534014 : CollatzResearch.WordTrace tailWord_1534014 prefixEnd_1534014 787686512726266396870205 := by
  unfold tailWord_1534014
  simp only [CollatzResearch.WordTrace]
  refine ⟨6993760883067092697290137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37300058043024494385547397 6993760883067092697290137)
  ·
    refine ⟨5245320662300319522967603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6993760883067092697290137 5245320662300319522967603)
    ·
      refine ⟨7867980993450479284451405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5245320662300319522967603 7867980993450479284451405)
      ·
        refine ⟨2950492872543929731669277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7867980993450479284451405 2950492872543929731669277)
        ·
          refine ⟨1106434827203973649375979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2950492872543929731669277 1106434827203973649375979)
          ·
            refine ⟨1659652240805960474063969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1106434827203973649375979 1659652240805960474063969)
            ·
              refine ⟨1244739180604470355547977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1659652240805960474063969 1244739180604470355547977)
              ·
                refine ⟨933554385453352766660983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1244739180604470355547977 933554385453352766660983)
                ·
                  refine ⟨1400331578180029149991475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 933554385453352766660983 1400331578180029149991475)
                  ·
                    refine ⟨2100497367270043724987213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1400331578180029149991475 2100497367270043724987213)
                    ·
                      refine ⟨787686512726266396870205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2100497367270043724987213 787686512726266396870205)
                      ·
                        rfl

theorem cell23_1534014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_1534014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534014 prefixEnd_1534014 := by exact prefixLift 1534014
  have htrace : WordTrace (prefixWord ++ tailWord_1534014) baseStart_1534014 baseEnd_1534014 := by
    simpa [prefixWord, tailWord_1534014, baseEnd_1534014] using wordTrace_append hprefix tailTrace_1534014
  have hstable : (prefixWord ++ tailWord_1534014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534014).length < 2 ^ (prefixWord ++ tailWord_1534014).sum := by decide
  have hdescent : baseEnd_1534014 < baseStart_1534014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534042 : List Nat := [3, 1, 1, 2, 1, 1, 3, 2, 2, 3, 4]
def baseStart_1534042 : Nat := 118140960795 + 1534042 * 2 ^ 59
def prefixEnd_1534042 : Nat := 4983230072969 + 3 ^ 40 * 1534042 * 2
def baseEnd_1534042 : Nat := 787700890184592287320075

theorem tailTrace_1534042 : CollatzResearch.WordTrace tailWord_1534042 prefixEnd_1534042 787700890184592287320075 := by
  unfold tailWord_1534042
  simp only [CollatzResearch.WordTrace]
  refine ⟨13987777077108825590085095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37300738872290201573560253 13987777077108825590085095)
  ·
    refine ⟨20981665615663238385127643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13987777077108825590085095 20981665615663238385127643)
    ·
      refine ⟨31472498423494857577691465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20981665615663238385127643 31472498423494857577691465)
      ·
        refine ⟨23604373817621143183268599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31472498423494857577691465 23604373817621143183268599)
        ·
          refine ⟨35406560726431714774902899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23604373817621143183268599 35406560726431714774902899)
          ·
            refine ⟨53109841089647572162354349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35406560726431714774902899 53109841089647572162354349)
            ·
              refine ⟨19916190408617839560882881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53109841089647572162354349 19916190408617839560882881)
              ·
                refine ⟨14937142806463379670662161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19916190408617839560882881 14937142806463379670662161)
                ·
                  refine ⟨11202857104847534752996621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14937142806463379670662161 11202857104847534752996621)
                  ·
                    refine ⟨4201071414317825532373733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11202857104847534752996621 4201071414317825532373733)
                    ·
                      refine ⟨787700890184592287320075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4201071414317825532373733 787700890184592287320075)
                      ·
                        rfl

theorem cell23_1534042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_1534042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534042 prefixEnd_1534042 := by exact prefixLift 1534042
  have htrace : WordTrace (prefixWord ++ tailWord_1534042) baseStart_1534042 baseEnd_1534042 := by
    simpa [prefixWord, tailWord_1534042, baseEnd_1534042] using wordTrace_append hprefix tailTrace_1534042
  have hstable : (prefixWord ++ tailWord_1534042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534042).length < 2 ^ (prefixWord ++ tailWord_1534042).sum := by decide
  have hdescent : baseEnd_1534042 < baseStart_1534042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534063 : List Nat := [1, 1, 2, 1, 3, 4, 4, 1, 1, 3, 2]
def baseStart_1534063 : Nat := 118140960795 + 1534063 * 2 ^ 59
def prefixEnd_1534063 : Nat := 4983230072969 + 3 ^ 40 * 1534063 * 2
def baseEnd_1534063 : Nat := 787711673278336705157479

theorem tailTrace_1534063 : CollatzResearch.WordTrace tailWord_1534063 prefixEnd_1534063 787711673278336705157479 := by
  unfold tailWord_1534063
  simp only [CollatzResearch.WordTrace]
  refine ⟨55951874241359222946854843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37301249494239481964569895 55951874241359222946854843)
  ·
    refine ⟨83927811362038834420282265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55951874241359222946854843 83927811362038834420282265)
    ·
      refine ⟨62945858521529125815211699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83927811362038834420282265 62945858521529125815211699)
      ·
        refine ⟨94418787782293688722817549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62945858521529125815211699 94418787782293688722817549)
        ·
          refine ⟨35407045418360133271056581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94418787782293688722817549 35407045418360133271056581)
          ·
            refine ⟨6638821015942524988323109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35407045418360133271056581 6638821015942524988323109)
            ·
              refine ⟨1244778940489223435310583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6638821015942524988323109 1244778940489223435310583)
              ·
                refine ⟨1867168410733835152965875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1244778940489223435310583 1867168410733835152965875)
                ·
                  refine ⟨2800752616100752729448813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1867168410733835152965875 2800752616100752729448813)
                  ·
                    refine ⟨1050282231037782273543305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2800752616100752729448813 1050282231037782273543305)
                    ·
                      refine ⟨787711673278336705157479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1050282231037782273543305 787711673278336705157479)
                      ·
                        rfl

theorem cell23_1534063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 1, 3, 2].length) (baseStart_1534063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534063 prefixEnd_1534063 := by exact prefixLift 1534063
  have htrace : WordTrace (prefixWord ++ tailWord_1534063) baseStart_1534063 baseEnd_1534063 := by
    simpa [prefixWord, tailWord_1534063, baseEnd_1534063] using wordTrace_append hprefix tailTrace_1534063
  have hstable : (prefixWord ++ tailWord_1534063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534063).length < 2 ^ (prefixWord ++ tailWord_1534063).sum := by decide
  have hdescent : baseEnd_1534063 < baseStart_1534063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534070 : List Nat := [5, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3]
def baseStart_1534070 : Nat := 118140960795 + 1534070 * 2 ^ 59
def prefixEnd_1534070 : Nat := 4983230072969 + 3 ^ 40 * 1534070 * 2
def baseEnd_1534070 : Nat := 787715267642918177769947

theorem tailTrace_1534070 : CollatzResearch.WordTrace tailWord_1534070 prefixEnd_1534070 787715267642918177769947 := by
  unfold tailWord_1534070
  simp only [CollatzResearch.WordTrace]
  refine ⟨3497008097020866446397479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37301419701555908761573109 3497008097020866446397479)
  ·
    refine ⟨5245512145531299669596219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3497008097020866446397479 5245512145531299669596219)
    ·
      refine ⟨7868268218296949504394329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5245512145531299669596219 7868268218296949504394329)
      ·
        refine ⟨5901201163722712128295747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7868268218296949504394329 5901201163722712128295747)
        ·
          refine ⟨8851801745584068192443621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5901201163722712128295747 8851801745584068192443621)
          ·
            refine ⟨1659712827297012786083179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8851801745584068192443621 1659712827297012786083179)
            ·
              refine ⟨2489569240945519179124769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1659712827297012786083179 2489569240945519179124769)
              ·
                refine ⟨1867176930709139384343577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2489569240945519179124769 1867176930709139384343577)
                ·
                  refine ⟨1400382698031854538257683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1867176930709139384343577 1400382698031854538257683)
                  ·
                    refine ⟨2100574047047781807386525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1400382698031854538257683 2100574047047781807386525)
                    ·
                      refine ⟨787715267642918177769947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2100574047047781807386525 787715267642918177769947)
                      ·
                        rfl

theorem cell23_1534070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_1534070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534070 prefixEnd_1534070 := by exact prefixLift 1534070
  have htrace : WordTrace (prefixWord ++ tailWord_1534070) baseStart_1534070 baseEnd_1534070 := by
    simpa [prefixWord, tailWord_1534070, baseEnd_1534070] using wordTrace_append hprefix tailTrace_1534070
  have hstable : (prefixWord ++ tailWord_1534070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534070).length < 2 ^ (prefixWord ++ tailWord_1534070).sum := by decide
  have hdescent : baseEnd_1534070 < baseStart_1534070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534133 : List Nat := [1, 3, 3, 4, 1, 2, 1, 1, 7]
def baseStart_1534133 : Nat := 118140960795 + 1534133 * 2 ^ 59
def prefixEnd_1534133 : Nat := 4983230072969 + 3 ^ 40 * 1534133 * 2
def baseEnd_1534133 : Nat := 87527512991572381253573

theorem tailTrace_1534133 : CollatzResearch.WordTrace tailWord_1534133 prefixEnd_1534133 87527512991572381253573 := by
  unfold tailWord_1534133
  simp only [CollatzResearch.WordTrace]
  refine ⟨55954427351105624901903053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37302951567403749934602035 55954427351105624901903053)
  ·
    refine ⟨20982910256664609338213645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55954427351105624901903053 20982910256664609338213645)
    ·
      refine ⟨7868591346249228501830117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20982910256664609338213645 7868591346249228501830117)
      ·
        refine ⟨1475360877421730344093147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7868591346249228501830117 1475360877421730344093147)
        ·
          refine ⟨2213041316132595516139721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1475360877421730344093147 2213041316132595516139721)
          ·
            refine ⟨1659780987099446637104791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2213041316132595516139721 1659780987099446637104791)
            ·
              refine ⟨2489671480649169955657187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1659780987099446637104791 2489671480649169955657187)
              ·
                refine ⟨3734507220973754933485781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2489671480649169955657187 3734507220973754933485781)
                ·
                  refine ⟨87527512991572381253573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3734507220973754933485781 87527512991572381253573)
                  ·
                    rfl

theorem cell23_1534133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 7].length) (baseStart_1534133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534133 prefixEnd_1534133 := by exact prefixLift 1534133
  have htrace : WordTrace (prefixWord ++ tailWord_1534133) baseStart_1534133 baseEnd_1534133 := by
    simpa [prefixWord, tailWord_1534133, baseEnd_1534133] using wordTrace_append hprefix tailTrace_1534133
  have hstable : (prefixWord ++ tailWord_1534133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534133).length < 2 ^ (prefixWord ++ tailWord_1534133).sum := by decide
  have hdescent : baseEnd_1534133 < baseStart_1534133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534159 : List Nat := [1, 1, 2, 1, 1, 3, 4, 1, 5, 4]
def baseStart_1534159 : Nat := 118140960795 + 1534159 * 2 ^ 59
def prefixEnd_1534159 : Nat := 4983230072969 + 3 ^ 40 * 1534159 * 2
def baseEnd_1534159 : Nat := 262586989140389443185679

theorem tailTrace_1534159 : CollatzResearch.WordTrace tailWord_1534159 prefixEnd_1534159 262586989140389443185679 := by
  unfold tailWord_1534159
  simp only [CollatzResearch.WordTrace]
  refine ⟨55955375649011431342349531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37303583766007620894899687 55955375649011431342349531)
  ·
    refine ⟨83933063473517147013524297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55955375649011431342349531 83933063473517147013524297)
    ·
      refine ⟨62949797605137860260143223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83933063473517147013524297 62949797605137860260143223)
      ·
        refine ⟨94424696407706790390214835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62949797605137860260143223 94424696407706790390214835)
        ·
          refine ⟨141637044611560185585322253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94424696407706790390214835 141637044611560185585322253)
          ·
            refine ⟨53113891729335069594495845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141637044611560185585322253 53113891729335069594495845)
            ·
              refine ⟨9958854699250325548967971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53113891729335069594495845 9958854699250325548967971)
              ·
                refine ⟨14938282048875488323451957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9958854699250325548967971 14938282048875488323451957)
                ·
                  refine ⟨1400463942082077030323621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14938282048875488323451957 1400463942082077030323621)
                  ·
                    refine ⟨262586989140389443185679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1400463942082077030323621 262586989140389443185679)
                    ·
                      rfl

theorem cell23_1534159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 5, 4].length) (baseStart_1534159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534159 prefixEnd_1534159 := by exact prefixLift 1534159
  have htrace : WordTrace (prefixWord ++ tailWord_1534159) baseStart_1534159 baseEnd_1534159 := by
    simpa [prefixWord, tailWord_1534159, baseEnd_1534159] using wordTrace_append hprefix tailTrace_1534159
  have hstable : (prefixWord ++ tailWord_1534159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534159).length < 2 ^ (prefixWord ++ tailWord_1534159).sum := by decide
  have hdescent : baseEnd_1534159 < baseStart_1534159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534169 : List Nat := [1, 2, 1, 2, 3, 1, 2, 3, 1, 4, 3]
def baseStart_1534169 : Nat := 118140960795 + 1534169 * 2 ^ 59
def prefixEnd_1534169 : Nat := 4983230072969 + 3 ^ 40 * 1534169 * 2
def baseEnd_1534169 : Nat := 787766102227713290431991

theorem tailTrace_1534169 : CollatzResearch.WordTrace tailWord_1534169 prefixEnd_1534169 787766102227713290431991 := by
  unfold tailWord_1534169
  simp only [CollatzResearch.WordTrace]
  refine ⟨55955740378975203050213561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37303826919316802033475707 55955740378975203050213561)
  ·
    refine ⟨41966805284231402287660171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55955740378975203050213561 41966805284231402287660171)
    ·
      refine ⟨62950207926347103431490257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41966805284231402287660171 62950207926347103431490257)
      ·
        refine ⟨47212655944760327573617693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62950207926347103431490257 47212655944760327573617693)
        ·
          refine ⟨17704745979285122840106635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47212655944760327573617693 17704745979285122840106635)
          ·
            refine ⟨26557118968927684260159953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17704745979285122840106635 26557118968927684260159953)
            ·
              refine ⟨19917839226695763195119965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26557118968927684260159953 19917839226695763195119965)
              ·
                refine ⟨7469189710010911198169987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19917839226695763195119965 7469189710010911198169987)
                ·
                  refine ⟨11203784565016366797254981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7469189710010911198169987 11203784565016366797254981)
                  ·
                    refine ⟨2100709605940568774485309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11203784565016366797254981 2100709605940568774485309)
                    ·
                      refine ⟨787766102227713290431991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2100709605940568774485309 787766102227713290431991)
                      ·
                        rfl

theorem cell23_1534169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 4, 3].length) (baseStart_1534169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534169 prefixEnd_1534169 := by exact prefixLift 1534169
  have htrace : WordTrace (prefixWord ++ tailWord_1534169) baseStart_1534169 baseEnd_1534169 := by
    simpa [prefixWord, tailWord_1534169, baseEnd_1534169] using wordTrace_append hprefix tailTrace_1534169
  have hstable : (prefixWord ++ tailWord_1534169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534169).length < 2 ^ (prefixWord ++ tailWord_1534169).sum := by decide
  have hdescent : baseEnd_1534169 < baseStart_1534169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534186 : List Nat := [3, 1, 3, 1, 1, 2, 1, 4, 2, 2, 3]
def baseStart_1534186 : Nat := 118140960795 + 1534186 * 2 ^ 59
def prefixEnd_1534186 : Nat := 4983230072969 + 3 ^ 40 * 1534186 * 2
def baseEnd_1534186 : Nat := 787774831398839723919413

theorem tailTrace_1534186 : CollatzResearch.WordTrace tailWord_1534186 prefixEnd_1534186 787774831398839723919413 := by
  unfold tailWord_1534186
  simp only [CollatzResearch.WordTrace]
  refine ⟨13989090104978403738395603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37304240279942409969054941 13989090104978403738395603)
  ·
    refine ⟨20983635157467605607593405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13989090104978403738395603 20983635157467605607593405)
    ·
      refine ⟨7868863184050352102847527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20983635157467605607593405 7868863184050352102847527)
      ·
        refine ⟨11803294776075528154271291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7868863184050352102847527 11803294776075528154271291)
        ·
          refine ⟨17704942164113292231406937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11803294776075528154271291 17704942164113292231406937)
          ·
            refine ⟨13278706623084969173555203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17704942164113292231406937 13278706623084969173555203)
            ·
              refine ⟨19918059934627453760332805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13278706623084969173555203 19918059934627453760332805)
              ·
                refine ⟨3734636237742647580062401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19918059934627453760332805 3734636237742647580062401)
                ·
                  refine ⟨2800977178306985685046801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3734636237742647580062401 2800977178306985685046801)
                  ·
                    refine ⟨2100732883730239263785101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2800977178306985685046801 2100732883730239263785101)
                    ·
                      refine ⟨787774831398839723919413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2100732883730239263785101 787774831398839723919413)
                      ·
                        rfl

theorem cell23_1534186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_1534186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534186 prefixEnd_1534186 := by exact prefixLift 1534186
  have htrace : WordTrace (prefixWord ++ tailWord_1534186) baseStart_1534186 baseEnd_1534186 := by
    simpa [prefixWord, tailWord_1534186, baseEnd_1534186] using wordTrace_append hprefix tailTrace_1534186
  have hstable : (prefixWord ++ tailWord_1534186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534186).length < 2 ^ (prefixWord ++ tailWord_1534186).sum := by decide
  have hdescent : baseEnd_1534186 < baseStart_1534186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534206 : List Nat := [4, 2, 2, 1, 1, 1, 1, 5, 6]
def baseStart_1534206 : Nat := 118140960795 + 1534206 * 2 ^ 59
def prefixEnd_1534206 : Nat := 4983230072969 + 3 ^ 40 * 1534206 * 2
def baseEnd_1534206 : Nat := 87531677890214405074369

theorem tailTrace_1534206 : CollatzResearch.WordTrace tailWord_1534206 prefixEnd_1534206 87531677890214405074369 := by
  unfold tailWord_1534206
  simp only [CollatzResearch.WordTrace]
  refine ⟨6994636234980144796163809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37304726586560772246206981 6994636234980144796163809)
  ·
    refine ⟨5245977176235108597122857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6994636234980144796163809 5245977176235108597122857)
    ·
      refine ⟨3934482882176331447842143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5245977176235108597122857 3934482882176331447842143)
      ·
        refine ⟨5901724323264497171763215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3934482882176331447842143 5901724323264497171763215)
        ·
          refine ⟨8852586484896745757644823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5901724323264497171763215 8852586484896745757644823)
          ·
            refine ⟨13278879727345118636467235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8852586484896745757644823 13278879727345118636467235)
            ·
              refine ⟨19918319591017677954700853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13278879727345118636467235 19918319591017677954700853)
              ·
                refine ⟨1867342461657907308253205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19918319591017677954700853 1867342461657907308253205)
                ·
                  refine ⟨87531677890214405074369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1867342461657907308253205 87531677890214405074369)
                  ·
                    rfl

theorem cell23_1534206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_1534206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534206 prefixEnd_1534206 := by exact prefixLift 1534206
  have htrace : WordTrace (prefixWord ++ tailWord_1534206) baseStart_1534206 baseEnd_1534206 := by
    simpa [prefixWord, tailWord_1534206, baseEnd_1534206] using wordTrace_append hprefix tailTrace_1534206
  have hstable : (prefixWord ++ tailWord_1534206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534206).length < 2 ^ (prefixWord ++ tailWord_1534206).sum := by decide
  have hdescent : baseEnd_1534206 < baseStart_1534206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534219 : List Nat := [1, 1, 1, 1, 5, 2, 1, 3, 3, 5]
def baseStart_1534219 : Nat := 118140960795 + 1534219 * 2 ^ 59
def prefixEnd_1534219 : Nat := 4983230072969 + 3 ^ 40 * 1534219 * 2
def baseEnd_1534219 : Nat := 262597258753479364935587

theorem tailTrace_1534219 : CollatzResearch.WordTrace tailWord_1534219 prefixEnd_1534219 262597258753479364935587 := by
  unfold tailWord_1534219
  simp only [CollatzResearch.WordTrace]
  refine ⟨55957564028794061589533711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37305042685862707726355807 55957564028794061589533711)
  ·
    refine ⟨83936346043191092384300567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55957564028794061589533711 83936346043191092384300567)
    ·
      refine ⟨125904519064786638576450851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83936346043191092384300567 125904519064786638576450851)
      ·
        refine ⟨188856778597179957864676277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125904519064786638576450851 188856778597179957864676277)
        ·
          refine ⟨17705322993485621049813401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 188856778597179957864676277 17705322993485621049813401)
          ·
            refine ⟨13278992245114215787360051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17705322993485621049813401 13278992245114215787360051)
            ·
              refine ⟨19918488367671323681040077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13278992245114215787360051 19918488367671323681040077)
              ·
                refine ⟨7469433137876746380390029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19918488367671323681040077 7469433137876746380390029)
                ·
                  refine ⟨2801037426703779892646261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7469433137876746380390029 2801037426703779892646261)
                  ·
                    refine ⟨262597258753479364935587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2801037426703779892646261 262597258753479364935587)
                    ·
                      rfl

theorem cell23_1534219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 5].length) (baseStart_1534219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534219 prefixEnd_1534219 := by exact prefixLift 1534219
  have htrace : WordTrace (prefixWord ++ tailWord_1534219) baseStart_1534219 baseEnd_1534219 := by
    simpa [prefixWord, tailWord_1534219, baseEnd_1534219] using wordTrace_append hprefix tailTrace_1534219
  have hstable : (prefixWord ++ tailWord_1534219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534219).length < 2 ^ (prefixWord ++ tailWord_1534219).sum := by decide
  have hdescent : baseEnd_1534219 < baseStart_1534219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534266 : List Nat := [3, 1, 1, 1, 4, 2, 3, 1, 1, 6]
def baseStart_1534266 : Nat := 118140960795 + 1534266 * 2 ^ 59
def prefixEnd_1534266 : Nat := 4983230072969 + 3 ^ 40 * 1534266 * 2
def baseEnd_1534266 : Nat := 262605303283733136973015

theorem tailTrace_1534266 : CollatzResearch.WordTrace tailWord_1534266 prefixEnd_1534266 262605303283733136973015 := by
  unfold tailWord_1534266
  simp only [CollatzResearch.WordTrace]
  refine ⟨13989819564905947154123663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37306185506415859077663101 13989819564905947154123663)
  ·
    refine ⟨20984729347358920731185495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13989819564905947154123663 20984729347358920731185495)
    ·
      refine ⟨31477094021038381096778243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20984729347358920731185495 31477094021038381096778243)
      ·
        refine ⟨47215641031557571645167365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31477094021038381096778243 47215641031557571645167365)
        ·
          refine ⟨8852932693417044683468881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47215641031557571645167365 8852932693417044683468881)
          ·
            refine ⟨6639699520062783512601661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8852932693417044683468881 6639699520062783512601661)
            ·
              refine ⟨2489887320023543817225623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6639699520062783512601661 2489887320023543817225623)
              ·
                refine ⟨3734830980035315725838435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2489887320023543817225623 3734830980035315725838435)
                ·
                  refine ⟨5602246470052973588757653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3734830980035315725838435 5602246470052973588757653)
                  ·
                    refine ⟨262605303283733136973015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5602246470052973588757653 262605303283733136973015)
                    ·
                      rfl

theorem cell23_1534266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 1, 6].length) (baseStart_1534266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534266 prefixEnd_1534266 := by exact prefixLift 1534266
  have htrace : WordTrace (prefixWord ++ tailWord_1534266) baseStart_1534266 baseEnd_1534266 := by
    simpa [prefixWord, tailWord_1534266, baseEnd_1534266] using wordTrace_append hprefix tailTrace_1534266
  have hstable : (prefixWord ++ tailWord_1534266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534266).length < 2 ^ (prefixWord ++ tailWord_1534266).sum := by decide
  have hdescent : baseEnd_1534266 < baseStart_1534266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534279 : List Nat := [1, 1, 4, 1, 2, 2, 3, 9]
def baseStart_1534279 : Nat := 118140960795 + 1534279 * 2 ^ 59
def prefixEnd_1534279 : Nat := 4983230072969 + 3 ^ 40 * 1534279 * 2
def baseEnd_1534279 : Nat := 29178614262952142965055

theorem tailTrace_1534279 : CollatzResearch.WordTrace tailWord_1534279 prefixEnd_1534279 29178614262952142965055 := by
  unfold tailWord_1534279
  simp only [CollatzResearch.WordTrace]
  refine ⟨55959752408576691836717891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37306501605717794557811927 55959752408576691836717891)
  ·
    refine ⟨83939628612865037755076837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55959752408576691836717891 83939628612865037755076837)
    ·
      refine ⟨15738680364912194579076907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83939628612865037755076837 15738680364912194579076907)
      ·
        refine ⟨23608020547368291868615361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15738680364912194579076907 23608020547368291868615361)
        ·
          refine ⟨17706015410526218901461521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23608020547368291868615361 17706015410526218901461521)
          ·
            refine ⟨13279511557894664176096141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17706015410526218901461521 13279511557894664176096141)
            ·
              refine ⟨4979816834210499066036053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13279511557894664176096141 4979816834210499066036053)
              ·
                refine ⟨29178614262952142965055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4979816834210499066036053 29178614262952142965055)
                ·
                  rfl

theorem cell23_1534279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 9].length) (baseStart_1534279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534279 prefixEnd_1534279 := by exact prefixLift 1534279
  have htrace : WordTrace (prefixWord ++ tailWord_1534279) baseStart_1534279 baseEnd_1534279 := by
    simpa [prefixWord, tailWord_1534279, baseEnd_1534279] using wordTrace_append hprefix tailTrace_1534279
  have hstable : (prefixWord ++ tailWord_1534279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534279).length < 2 ^ (prefixWord ++ tailWord_1534279).sum := by decide
  have hdescent : baseEnd_1534279 < baseStart_1534279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534293 : List Nat := [1, 3, 2, 2, 4, 1, 2, 1, 1, 1, 5]
def baseStart_1534293 : Nat := 118140960795 + 1534293 * 2 ^ 59
def prefixEnd_1534293 : Nat := 4983230072969 + 3 ^ 40 * 1534293 * 2
def baseEnd_1534293 : Nat := 787829773828870805281421

theorem tailTrace_1534293 : CollatzResearch.WordTrace tailWord_1534293 prefixEnd_1534293 787829773828870805281421 := by
  unfold tailWord_1534293
  simp only [CollatzResearch.WordTrace]
  refine ⟨55960263030525972227727533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37306842020350648151818355 55960263030525972227727533)
  ·
    refine ⟨20985098636447239585397825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55960263030525972227727533 20985098636447239585397825)
    ·
      refine ⟨15738823977335429689048369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20985098636447239585397825 15738823977335429689048369)
      ·
        refine ⟨11804117983001572266786277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15738823977335429689048369 11804117983001572266786277)
        ·
          refine ⟨2213272121812794800022427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11804117983001572266786277 2213272121812794800022427)
          ·
            refine ⟨3319908182719192200033641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2213272121812794800022427 3319908182719192200033641)
            ·
              refine ⟨2489931137039394150025231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3319908182719192200033641 2489931137039394150025231)
              ·
                refine ⟨3734896705559091225037847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2489931137039394150025231 3734896705559091225037847)
                ·
                  refine ⟨5602345058338636837556771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3734896705559091225037847 5602345058338636837556771)
                  ·
                    refine ⟨8403517587507955256335157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5602345058338636837556771 8403517587507955256335157)
                    ·
                      refine ⟨787829773828870805281421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8403517587507955256335157 787829773828870805281421)
                      ·
                        rfl

theorem cell23_1534293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_1534293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534293 prefixEnd_1534293 := by exact prefixLift 1534293
  have htrace : WordTrace (prefixWord ++ tailWord_1534293) baseStart_1534293 baseEnd_1534293 := by
    simpa [prefixWord, tailWord_1534293, baseEnd_1534293] using wordTrace_append hprefix tailTrace_1534293
  have hstable : (prefixWord ++ tailWord_1534293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534293).length < 2 ^ (prefixWord ++ tailWord_1534293).sum := by decide
  have hdescent : baseEnd_1534293 < baseStart_1534293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534319 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 5]
def baseStart_1534319 : Nat := 118140960795 + 1534319 * 2 ^ 59
def prefixEnd_1534319 : Nat := 4983230072969 + 3 ^ 40 * 1534319 * 2
def baseEnd_1534319 : Nat := 787843124325887703556301

theorem tailTrace_1534319 : CollatzResearch.WordTrace tailWord_1534319 prefixEnd_1534319 787843124325887703556301 := by
  unfold tailWord_1534319
  simp only [CollatzResearch.WordTrace]
  refine ⟨55961211328431778668174011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37307474218954519112116007 55961211328431778668174011)
  ·
    refine ⟨83941816992647668002261017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55961211328431778668174011 83941816992647668002261017)
    ·
      refine ⟨62956362744485751001695763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83941816992647668002261017 62956362744485751001695763)
      ·
        refine ⟨94434544116728626502543645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62956362744485751001695763 94434544116728626502543645)
        ·
          refine ⟨35412954043773234938453867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94434544116728626502543645 35412954043773234938453867)
          ·
            refine ⟨53119431065659852407680801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35412954043773234938453867 53119431065659852407680801)
            ·
              refine ⟨39839573299244889305760601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53119431065659852407680801 39839573299244889305760601)
              ·
                refine ⟨29879679974433666979320451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39839573299244889305760601 29879679974433666979320451)
                ·
                  refine ⟨44819519961650500468980677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29879679974433666979320451 44819519961650500468980677)
                  ·
                    refine ⟨8403659992809468837933877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44819519961650500468980677 8403659992809468837933877)
                    ·
                      refine ⟨787843124325887703556301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8403659992809468837933877 787843124325887703556301)
                      ·
                        rfl

theorem cell23_1534319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 5].length) (baseStart_1534319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534319 prefixEnd_1534319 := by exact prefixLift 1534319
  have htrace : WordTrace (prefixWord ++ tailWord_1534319) baseStart_1534319 baseEnd_1534319 := by
    simpa [prefixWord, tailWord_1534319, baseEnd_1534319] using wordTrace_append hprefix tailTrace_1534319
  have hstable : (prefixWord ++ tailWord_1534319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534319).length < 2 ^ (prefixWord ++ tailWord_1534319).sum := by decide
  have hdescent : baseEnd_1534319 < baseStart_1534319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534323 : List Nat := [1, 1, 1, 2, 2, 1, 2, 7, 2, 1, 3]
def baseStart_1534323 : Nat := 118140960795 + 1534323 * 2 ^ 59
def prefixEnd_1534323 : Nat := 4983230072969 + 3 ^ 40 * 1534323 * 2
def baseEnd_1534323 : Nat := 787845178248505687906283

theorem tailTrace_1534323 : CollatzResearch.WordTrace tailWord_1534323 prefixEnd_1534323 787845178248505687906283 := by
  unfold tailWord_1534323
  simp only [CollatzResearch.WordTrace]
  refine ⟨55961357220417287351319623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37307571480278191567546415 55961357220417287351319623)
  ·
    refine ⟨83942035830625931026979435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55961357220417287351319623 83942035830625931026979435)
    ·
      refine ⟨125913053745938896540469153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83942035830625931026979435 125913053745938896540469153)
      ·
        refine ⟨94434790309454172405351865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125913053745938896540469153 94434790309454172405351865)
        ·
          refine ⟨70826092732090629304013899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94434790309454172405351865 70826092732090629304013899)
          ·
            refine ⟨106239139098135943956020849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70826092732090629304013899 106239139098135943956020849)
            ·
              refine ⟨79679354323601957967015637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106239139098135943956020849 79679354323601957967015637)
              ·
                refine ⟨1867484866959420889851929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 79679354323601957967015637 1867484866959420889851929)
                ·
                  refine ⟨1400613650219565667388947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1867484866959420889851929 1400613650219565667388947)
                  ·
                    refine ⟨2100920475329348501083421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1400613650219565667388947 2100920475329348501083421)
                    ·
                      refine ⟨787845178248505687906283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2100920475329348501083421 787845178248505687906283)
                      ·
                        rfl

theorem cell23_1534323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 2, 1, 3].length) (baseStart_1534323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534323 prefixEnd_1534323 := by exact prefixLift 1534323
  have htrace : WordTrace (prefixWord ++ tailWord_1534323) baseStart_1534323 baseEnd_1534323 := by
    simpa [prefixWord, tailWord_1534323, baseEnd_1534323] using wordTrace_append hprefix tailTrace_1534323
  have hstable : (prefixWord ++ tailWord_1534323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534323).length < 2 ^ (prefixWord ++ tailWord_1534323).sum := by decide
  have hdescent : baseEnd_1534323 < baseStart_1534323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534329 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 1, 2, 8]
def baseStart_1534329 : Nat := 118140960795 + 1534329 * 2 ^ 59
def prefixEnd_1534329 : Nat := 4983230072969 + 3 ^ 40 * 1534329 * 2
def baseEnd_1534329 : Nat := 787848259132432664431255

theorem tailTrace_1534329 : CollatzResearch.WordTrace tailWord_1534329 prefixEnd_1534329 787848259132432664431255 := by
  unfold tailWord_1534329
  simp only [CollatzResearch.WordTrace]
  refine ⟨55961576058395550376038041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37307717372263700250692027 55961576058395550376038041)
  ·
    refine ⟨41971182043796662782028531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55961576058395550376038041 41971182043796662782028531)
    ·
      refine ⟨62956773065694994173042797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41971182043796662782028531 62956773065694994173042797)
      ·
        refine ⟨23608789899635622814891049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62956773065694994173042797 23608789899635622814891049)
        ·
          refine ⟨17706592424726717111168287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23608789899635622814891049 17706592424726717111168287)
          ·
            refine ⟨26559888637090075666752431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17706592424726717111168287 26559888637090075666752431)
            ·
              refine ⟨39839832955635113500128647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26559888637090075666752431 39839832955635113500128647)
              ·
                refine ⟨59759749433452670250192971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39839832955635113500128647 59759749433452670250192971)
                ·
                  refine ⟨89639624150179005375289457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59759749433452670250192971 89639624150179005375289457)
                  ·
                    refine ⟨67229718112634254031467093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89639624150179005375289457 67229718112634254031467093)
                    ·
                      refine ⟨787848259132432664431255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 67229718112634254031467093 787848259132432664431255)
                      ·
                        rfl

theorem cell23_1534329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_1534329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534329 prefixEnd_1534329 := by exact prefixLift 1534329
  have htrace : WordTrace (prefixWord ++ tailWord_1534329) baseStart_1534329 baseEnd_1534329 := by
    simpa [prefixWord, tailWord_1534329, baseEnd_1534329] using wordTrace_append hprefix tailTrace_1534329
  have hstable : (prefixWord ++ tailWord_1534329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534329).length < 2 ^ (prefixWord ++ tailWord_1534329).sum := by decide
  have hdescent : baseEnd_1534329 < baseStart_1534329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534386 : List Nat := [3, 2, 1, 1, 1, 1, 5, 2, 7]
def baseStart_1534386 : Nat := 118140960795 + 1534386 * 2 ^ 59
def prefixEnd_1534386 : Nat := 4983230072969 + 3 ^ 40 * 1534386 * 2
def baseEnd_1534386 : Nat := 87541947503304326824277

theorem tailTrace_1534386 : CollatzResearch.WordTrace tailWord_1534386 prefixEnd_1534386 87541947503304326824277 := by
  unfold tailWord_1534386
  simp only [CollatzResearch.WordTrace]
  refine ⟨13990913754797262277715753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37309103346126032740575341 13990913754797262277715753)
  ·
    refine ⟨10493185316097946708286815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13990913754797262277715753 10493185316097946708286815)
    ·
      refine ⟨15739777974146920062430223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10493185316097946708286815 15739777974146920062430223)
      ·
        refine ⟨23609666961220380093645335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15739777974146920062430223 23609666961220380093645335)
        ·
          refine ⟨35414500441830570140468003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23609666961220380093645335 35414500441830570140468003)
          ·
            refine ⟨53121750662745855210702005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35414500441830570140468003 53121750662745855210702005)
            ·
              refine ⟨4980164124632423926003313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53121750662745855210702005 4980164124632423926003313)
              ·
                refine ⟨3735123093474317944502485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4980164124632423926003313 3735123093474317944502485)
                ·
                  refine ⟨87541947503304326824277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3735123093474317944502485 87541947503304326824277)
                  ·
                    rfl

theorem cell23_1534386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 7].length) (baseStart_1534386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534386 prefixEnd_1534386 := by exact prefixLift 1534386
  have htrace : WordTrace (prefixWord ++ tailWord_1534386) baseStart_1534386 baseEnd_1534386 := by
    simpa [prefixWord, tailWord_1534386, baseEnd_1534386] using wordTrace_append hprefix tailTrace_1534386
  have hstable : (prefixWord ++ tailWord_1534386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534386).length < 2 ^ (prefixWord ++ tailWord_1534386).sum := by decide
  have hdescent : baseEnd_1534386 < baseStart_1534386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534401 : List Nat := [1, 2, 7, 1, 1, 1, 1, 3, 1, 3, 2]
def baseStart_1534401 : Nat := 118140960795 + 1534401 * 2 ^ 59
def prefixEnd_1534401 : Nat := 4983230072969 + 3 ^ 40 * 1534401 * 2
def baseEnd_1534401 : Nat := 787885229739556382730925

theorem tailTrace_1534401 : CollatzResearch.WordTrace tailWord_1534401 prefixEnd_1534401 787885229739556382730925 := by
  unfold tailWord_1534401
  simp only [CollatzResearch.WordTrace]
  refine ⟨55964202114134706672659057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37309468076089804448439371 55964202114134706672659057)
  ·
    refine ⟨41973151585601030004494293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55964202114134706672659057 41973151585601030004494293)
    ·
      refine ⟨983745740287524140730335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 41973151585601030004494293 983745740287524140730335)
      ·
        refine ⟨1475618610431286211095503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 983745740287524140730335 1475618610431286211095503)
        ·
          refine ⟨2213427915646929316643255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1475618610431286211095503 2213427915646929316643255)
          ·
            refine ⟨3320141873470393974964883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2213427915646929316643255 3320141873470393974964883)
            ·
              refine ⟨4980212810205590962447325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3320141873470393974964883 4980212810205590962447325)
              ·
                refine ⟨1867579803827096610917747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4980212810205590962447325 1867579803827096610917747)
                ·
                  refine ⟨2801369705740644916376621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1867579803827096610917747 2801369705740644916376621)
                  ·
                    refine ⟨1050513639652741843641233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2801369705740644916376621 1050513639652741843641233)
                    ·
                      refine ⟨787885229739556382730925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1050513639652741843641233 787885229739556382730925)
                      ·
                        rfl

theorem cell23_1534401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_1534401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534401 prefixEnd_1534401 := by exact prefixLift 1534401
  have htrace : WordTrace (prefixWord ++ tailWord_1534401) baseStart_1534401 baseEnd_1534401 := by
    simpa [prefixWord, tailWord_1534401, baseEnd_1534401] using wordTrace_append hprefix tailTrace_1534401
  have hstable : (prefixWord ++ tailWord_1534401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534401).length < 2 ^ (prefixWord ++ tailWord_1534401).sum := by decide
  have hdescent : baseEnd_1534401 < baseStart_1534401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534420 : List Nat := [2, 4, 1, 2, 2, 1, 2, 4, 5]
def baseStart_1534420 : Nat := 118140960795 + 1534420 * 2 ^ 59
def prefixEnd_1534420 : Nat := 4983230072969 + 3 ^ 40 * 1534420 * 2
def baseEnd_1534420 : Nat := 87543887319110200932593

theorem tailTrace_1534420 : CollatzResearch.WordTrace tailWord_1534420 prefixEnd_1534420 87543887319110200932593 := by
  unfold tailWord_1534420
  simp only [CollatzResearch.WordTrace]
  refine ⟨27982447550532936458800357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37309930067377248611733809 27982447550532936458800357)
  ·
    refine ⟨5246708915724925586025067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27982447550532936458800357 5246708915724925586025067)
    ·
      refine ⟨7870063373587388379037601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5246708915724925586025067 7870063373587388379037601)
      ·
        refine ⟨5902547530190541284278201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7870063373587388379037601 5902547530190541284278201)
        ·
          refine ⟨4426910647642905963208651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5902547530190541284278201 4426910647642905963208651)
          ·
            refine ⟨6640365971464358944812977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4426910647642905963208651 6640365971464358944812977)
            ·
              refine ⟨4980274478598269208609733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6640365971464358944812977 4980274478598269208609733)
              ·
                refine ⟨933801464737175476614325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4980274478598269208609733 933801464737175476614325)
                ·
                  refine ⟨87543887319110200932593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 933801464737175476614325 87543887319110200932593)
                  ·
                    rfl

theorem cell23_1534420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_1534420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534420 prefixEnd_1534420 := by exact prefixLift 1534420
  have htrace : WordTrace (prefixWord ++ tailWord_1534420) baseStart_1534420 baseEnd_1534420 := by
    simpa [prefixWord, tailWord_1534420, baseEnd_1534420] using wordTrace_append hprefix tailTrace_1534420
  have hstable : (prefixWord ++ tailWord_1534420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534420).length < 2 ^ (prefixWord ++ tailWord_1534420).sum := by decide
  have hdescent : baseEnd_1534420 < baseStart_1534420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534426 : List Nat := [3, 1, 1, 2, 3, 1, 2, 1, 1, 1, 7]
def baseStart_1534426 : Nat := 118140960795 + 1534426 * 2 ^ 59
def prefixEnd_1534426 : Nat := 4983230072969 + 3 ^ 40 * 1534426 * 2
def baseEnd_1534426 : Nat := 787898066755918784918309

theorem tailTrace_1534426 : CollatzResearch.WordTrace tailWord_1534426 prefixEnd_1534426 787898066755918784918309 := by
  unfold tailWord_1534426
  simp only [CollatzResearch.WordTrace]
  refine ⟨13991278484761033985579783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37310075959362757294879421 13991278484761033985579783)
  ·
    refine ⟨20986917727141550978369675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13991278484761033985579783 20986917727141550978369675)
    ·
      refine ⟨31480376590712326467554513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20986917727141550978369675 31480376590712326467554513)
      ·
        refine ⟨23610282443034244850665885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31480376590712326467554513 23610282443034244850665885)
        ·
          refine ⟨8853855916137841818999707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23610282443034244850665885 8853855916137841818999707)
          ·
            refine ⟨13280783874206762728499561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8853855916137841818999707 13280783874206762728499561)
            ·
              refine ⟨9960587905655072046374671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13280783874206762728499561 9960587905655072046374671)
              ·
                refine ⟨14940881858482608069562007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9960587905655072046374671 14940881858482608069562007)
                ·
                  refine ⟨22411322787723912104343011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14940881858482608069562007 22411322787723912104343011)
                  ·
                    refine ⟨33616984181585868156514517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22411322787723912104343011 33616984181585868156514517)
                    ·
                      refine ⟨787898066755918784918309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 33616984181585868156514517 787898066755918784918309)
                      ·
                        rfl

theorem cell23_1534426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_1534426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534426 prefixEnd_1534426 := by exact prefixLift 1534426
  have htrace : WordTrace (prefixWord ++ tailWord_1534426) baseStart_1534426 baseEnd_1534426 := by
    simpa [prefixWord, tailWord_1534426, baseEnd_1534426] using wordTrace_append hprefix tailTrace_1534426
  have hstable : (prefixWord ++ tailWord_1534426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534426).length < 2 ^ (prefixWord ++ tailWord_1534426).sum := by decide
  have hdescent : baseEnd_1534426 < baseStart_1534426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534477 : List Nat := [1, 7, 1, 1, 1, 2, 1, 1, 1, 2, 5]
def baseStart_1534477 : Nat := 118140960795 + 1534477 * 2 ^ 59
def prefixEnd_1534477 : Nat := 4983230072969 + 3 ^ 40 * 1534477 * 2
def baseEnd_1534477 : Nat := 787924254269298085380575

theorem tailTrace_1534477 : CollatzResearch.WordTrace tailWord_1534477 prefixEnd_1534477 787924254269298085380575 := by
  unfold tailWord_1534477
  simp only [CollatzResearch.WordTrace]
  refine ⟨55966974061859371652425685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37311316041239581101617123 55966974061859371652425685)
  ·
    refine ⟨1311725954574829023103727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 55966974061859371652425685 1311725954574829023103727)
    ·
      refine ⟨1967588931862243534655591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1311725954574829023103727 1967588931862243534655591)
      ·
        refine ⟨2951383397793365301983387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1967588931862243534655591 2951383397793365301983387)
        ·
          refine ⟨4427075096690047952975081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2951383397793365301983387 4427075096690047952975081)
          ·
            refine ⟨3320306322517535964731311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4427075096690047952975081 3320306322517535964731311)
            ·
              refine ⟨4980459483776303947096967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3320306322517535964731311 4980459483776303947096967)
              ·
                refine ⟨7470689225664455920645451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4980459483776303947096967 7470689225664455920645451)
                ·
                  refine ⟨11206033838496683880968177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7470689225664455920645451 11206033838496683880968177)
                  ·
                    refine ⟨8404525378872512910726133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11206033838496683880968177 8404525378872512910726133)
                    ·
                      refine ⟨787924254269298085380575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8404525378872512910726133 787924254269298085380575)
                      ·
                        rfl

theorem cell23_1534477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_1534477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534477 prefixEnd_1534477 := by exact prefixLift 1534477
  have htrace : WordTrace (prefixWord ++ tailWord_1534477) baseStart_1534477 baseEnd_1534477 := by
    simpa [prefixWord, tailWord_1534477, baseEnd_1534477] using wordTrace_append hprefix tailTrace_1534477
  have hstable : (prefixWord ++ tailWord_1534477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534477).length < 2 ^ (prefixWord ++ tailWord_1534477).sum := by decide
  have hdescent : baseEnd_1534477 < baseStart_1534477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534543 : List Nat := [1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 4]
def baseStart_1534543 : Nat := 118140960795 + 1534543 * 2 ^ 59
def prefixEnd_1534543 : Nat := 4983230072969 + 3 ^ 40 * 1534543 * 2
def baseEnd_1534543 : Nat := 787958143992494827155271

theorem tailTrace_1534543 : CollatzResearch.WordTrace tailWord_1534543 prefixEnd_1534543 787958143992494827155271 := by
  unfold tailWord_1534543
  simp only [CollatzResearch.WordTrace]
  refine ⟨55969381279620264924328283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37312920853080176616218855 55969381279620264924328283)
  ·
    refine ⟨83954071919430397386492425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55969381279620264924328283 83954071919430397386492425)
    ·
      refine ⟨62965553939572798039869319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83954071919430397386492425 62965553939572798039869319)
      ·
        refine ⟨94448330909359197059803979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62965553939572798039869319 94448330909359197059803979)
        ·
          refine ⟨141672496364038795589705969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94448330909359197059803979 141672496364038795589705969)
          ·
            refine ⟨106254372273029096692279477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141672496364038795589705969 106254372273029096692279477)
            ·
              refine ⟨9961347400596477814901201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106254372273029096692279477 9961347400596477814901201)
              ·
                refine ⟨7471010550447358361175901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9961347400596477814901201 7471010550447358361175901)
                ·
                  refine ⟨2801628956417759385440963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7471010550447358361175901 2801628956417759385440963)
                  ·
                    refine ⟨4202443434626639078161445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2801628956417759385440963 4202443434626639078161445)
                    ·
                      refine ⟨787958143992494827155271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4202443434626639078161445 787958143992494827155271)
                      ·
                        rfl

theorem cell23_1534543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 4].length) (baseStart_1534543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534543 prefixEnd_1534543 := by exact prefixLift 1534543
  have htrace : WordTrace (prefixWord ++ tailWord_1534543) baseStart_1534543 baseEnd_1534543 := by
    simpa [prefixWord, tailWord_1534543, baseEnd_1534543] using wordTrace_append hprefix tailTrace_1534543
  have hstable : (prefixWord ++ tailWord_1534543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534543).length < 2 ^ (prefixWord ++ tailWord_1534543).sum := by decide
  have hdescent : baseEnd_1534543 < baseStart_1534543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534553 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 8, 4]
def baseStart_1534553 : Nat := 118140960795 + 1534553 * 2 ^ 59
def prefixEnd_1534553 : Nat := 4983230072969 + 3 ^ 40 * 1534553 * 2
def baseEnd_1534553 : Nat := 262654426266346596010075

theorem tailTrace_1534553 : CollatzResearch.WordTrace tailWord_1534553 prefixEnd_1534553 262654426266346596010075 := by
  unfold tailWord_1534553
  simp only [CollatzResearch.WordTrace]
  refine ⟨55969746009584036632192313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37313164006389357754794875 55969746009584036632192313)
  ·
    refine ⟨41977309507188027474144235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55969746009584036632192313 41977309507188027474144235)
    ·
      refine ⟨62965964260782041211216353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41977309507188027474144235 62965964260782041211216353)
      ·
        refine ⟨47224473195586530908412265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62965964260782041211216353 47224473195586530908412265)
        ·
          refine ⟨35418354896689898181309199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47224473195586530908412265 35418354896689898181309199)
          ·
            refine ⟨53127532345034847271963799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35418354896689898181309199 53127532345034847271963799)
            ·
              refine ⟨79691298517552270907945699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53127532345034847271963799 79691298517552270907945699)
              ·
                refine ⟨119536947776328406361918549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79691298517552270907945699 119536947776328406361918549)
                ·
                  refine ⟨1400823606753848512053733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 119536947776328406361918549 1400823606753848512053733)
                  ·
                    refine ⟨262654426266346596010075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1400823606753848512053733 262654426266346596010075)
                    ·
                      rfl

theorem cell23_1534553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 8, 4].length) (baseStart_1534553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534553 prefixEnd_1534553 := by exact prefixLift 1534553
  have htrace : WordTrace (prefixWord ++ tailWord_1534553) baseStart_1534553 baseEnd_1534553 := by
    simpa [prefixWord, tailWord_1534553, baseEnd_1534553] using wordTrace_append hprefix tailTrace_1534553
  have hstable : (prefixWord ++ tailWord_1534553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534553).length < 2 ^ (prefixWord ++ tailWord_1534553).sum := by decide
  have hdescent : baseEnd_1534553 < baseStart_1534553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534558 : List Nat := [4, 4, 1, 2, 1, 2, 1, 1, 2, 2, 3]
def baseStart_1534558 : Nat := 118140960795 + 1534558 * 2 ^ 59
def prefixEnd_1534558 : Nat := 4983230072969 + 3 ^ 40 * 1534558 * 2
def baseEnd_1534558 : Nat := 787965846202312268467703

theorem tailTrace_1534558 : CollatzResearch.WordTrace tailWord_1534558 prefixEnd_1534558 787965846202312268467703 := by
  unfold tailWord_1534558
  simp only [CollatzResearch.WordTrace]
  refine ⟨6996241046820740310765541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37313285583043948324082885 6996241046820740310765541)
  ·
    refine ⟨1311795196278888808268539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6996241046820740310765541 1311795196278888808268539)
    ·
      refine ⟨1967692794418333212402809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1311795196278888808268539 1967692794418333212402809)
      ·
        refine ⟨1475769595813749909302107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1967692794418333212402809 1475769595813749909302107)
        ·
          refine ⟨2213654393720624863953161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1475769595813749909302107 2213654393720624863953161)
          ·
            refine ⟨1660240795290468647964871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2213654393720624863953161 1660240795290468647964871)
            ·
              refine ⟨2490361192935702971947307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1660240795290468647964871 2490361192935702971947307)
              ·
                refine ⟨3735541789403554457920961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2490361192935702971947307 3735541789403554457920961)
                ·
                  refine ⟨2801656342052665843440721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3735541789403554457920961 2801656342052665843440721)
                  ·
                    refine ⟨2101242256539499382580541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2801656342052665843440721 2101242256539499382580541)
                    ·
                      refine ⟨787965846202312268467703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2101242256539499382580541 787965846202312268467703)
                      ·
                        rfl

theorem cell23_1534558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_1534558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534558 prefixEnd_1534558 := by exact prefixLift 1534558
  have htrace : WordTrace (prefixWord ++ tailWord_1534558) baseStart_1534558 baseEnd_1534558 := by
    simpa [prefixWord, tailWord_1534558, baseEnd_1534558] using wordTrace_append hprefix tailTrace_1534558
  have hstable : (prefixWord ++ tailWord_1534558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534558).length < 2 ^ (prefixWord ++ tailWord_1534558).sum := by decide
  have hdescent : baseEnd_1534558 < baseStart_1534558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534570 : List Nat := [3, 1, 3, 2, 1, 1, 2, 2, 4, 4]
def baseStart_1534570 : Nat := 118140960795 + 1534570 * 2 ^ 59
def prefixEnd_1534570 : Nat := 4983230072969 + 3 ^ 40 * 1534570 * 2
def baseEnd_1534570 : Nat := 262657335990055407172549

theorem tailTrace_1534570 : CollatzResearch.WordTrace tailWord_1534570 prefixEnd_1534570 262657335990055407172549 := by
  unfold tailWord_1534570
  simp only [CollatzResearch.WordTrace]
  refine ⟨13992591512630612133890291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37313577367014965690374109 13992591512630612133890291)
  ·
    refine ⟨20988887268945918200835437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13992591512630612133890291 20988887268945918200835437)
    ·
      refine ⟨7870832725854719325313289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20988887268945918200835437 7870832725854719325313289)
      ·
        refine ⟨5903124544391039493984967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7870832725854719325313289 5903124544391039493984967)
        ·
          refine ⟨8854686816586559240977451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5903124544391039493984967 8854686816586559240977451)
          ·
            refine ⟨13282030224879838861466177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8854686816586559240977451 13282030224879838861466177)
            ·
              refine ⟨9961522668659879146099633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13282030224879838861466177 9961522668659879146099633)
              ·
                refine ⟨7471142001494909359574725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9961522668659879146099633 7471142001494909359574725)
                ·
                  refine ⟨1400839125280295504920261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7471142001494909359574725 1400839125280295504920261)
                  ·
                    refine ⟨262657335990055407172549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1400839125280295504920261 262657335990055407172549)
                    ·
                      rfl

theorem cell23_1534570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_1534570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534570 prefixEnd_1534570 := by exact prefixLift 1534570
  have htrace : WordTrace (prefixWord ++ tailWord_1534570) baseStart_1534570 baseEnd_1534570 := by
    simpa [prefixWord, tailWord_1534570, baseEnd_1534570] using wordTrace_append hprefix tailTrace_1534570
  have hstable : (prefixWord ++ tailWord_1534570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534570).length < 2 ^ (prefixWord ++ tailWord_1534570).sum := by decide
  have hdescent : baseEnd_1534570 < baseStart_1534570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534574 : List Nat := [4, 1, 2, 2, 2, 3, 2, 1, 1, 5]
def baseStart_1534574 : Nat := 118140960795 + 1534574 * 2 ^ 59
def prefixEnd_1534574 : Nat := 4983230072969 + 3 ^ 40 * 1534574 * 2
def baseEnd_1534574 : Nat := 262658020630928068622543

theorem tailTrace_1534574 : CollatzResearch.WordTrace tailWord_1534574 prefixEnd_1534574 262658020630928068622543 := by
  unfold tailWord_1534574
  simp only [CollatzResearch.WordTrace]
  refine ⟨6996313992813494652338347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37313674628338638145804517 6996313992813494652338347)
  ·
    refine ⟨10494470989220241978507521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6996313992813494652338347 10494470989220241978507521)
    ·
      refine ⟨7870853241915181483880641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10494470989220241978507521 7870853241915181483880641)
      ·
        refine ⟨5903139931436386112910481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7870853241915181483880641 5903139931436386112910481)
        ·
          refine ⟨4427354948577289584682861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5903139931436386112910481 4427354948577289584682861)
          ·
            refine ⟨1660258105716483594256073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4427354948577289584682861 1660258105716483594256073)
            ·
              refine ⟨1245193579287362695692055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1660258105716483594256073 1245193579287362695692055)
              ·
                refine ⟨1867790368931044043538083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1245193579287362695692055 1867790368931044043538083)
                ·
                  refine ⟨2801685553396566065307125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1867790368931044043538083 2801685553396566065307125)
                  ·
                    refine ⟨262658020630928068622543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2801685553396566065307125 262658020630928068622543)
                    ·
                      rfl

theorem cell23_1534574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_1534574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534574 prefixEnd_1534574 := by exact prefixLift 1534574
  have htrace : WordTrace (prefixWord ++ tailWord_1534574) baseStart_1534574 baseEnd_1534574 := by
    simpa [prefixWord, tailWord_1534574, baseEnd_1534574] using wordTrace_append hprefix tailTrace_1534574
  have hstable : (prefixWord ++ tailWord_1534574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534574).length < 2 ^ (prefixWord ++ tailWord_1534574).sum := by decide
  have hdescent : baseEnd_1534574 < baseStart_1534574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534634 : List Nat := [3, 1, 5, 2, 2, 1, 9]
def baseStart_1534634 : Nat := 118140960795 + 1534634 * 2 ^ 59
def prefixEnd_1534634 : Nat := 4983230072969 + 3 ^ 40 * 1534634 * 2
def baseEnd_1534634 : Nat := 9728455194222888532313

theorem tailTrace_1534634 : CollatzResearch.WordTrace tailWord_1534634 prefixEnd_1534634 9728455194222888532313 := by
  unfold tailWord_1534634
  simp only [CollatzResearch.WordTrace]
  refine ⟨13993175080572646866472739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37315133548193724977260637 13993175080572646866472739)
  ·
    refine ⟨20989762620858970299709109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13993175080572646866472739 20989762620858970299709109)
    ·
      refine ⟨1967790245705528465597729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20989762620858970299709109 1967790245705528465597729)
      ·
        refine ⟨1475842684279146349198297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1967790245705528465597729 1475842684279146349198297)
        ·
          refine ⟨1106882013209359761898723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1475842684279146349198297 1106882013209359761898723)
          ·
            refine ⟨1660323019814039642848085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1106882013209359761898723 1660323019814039642848085)
            ·
              refine ⟨9728455194222888532313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1660323019814039642848085 9728455194222888532313)
              ·
                rfl

theorem cell23_1534634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 9].length) (baseStart_1534634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534634 prefixEnd_1534634 := by exact prefixLift 1534634
  have htrace : WordTrace (prefixWord ++ tailWord_1534634) baseStart_1534634 baseEnd_1534634 := by
    simpa [prefixWord, tailWord_1534634, baseEnd_1534634] using wordTrace_append hprefix tailTrace_1534634
  have hstable : (prefixWord ++ tailWord_1534634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534634).length < 2 ^ (prefixWord ++ tailWord_1534634).sum := by decide
  have hdescent : baseEnd_1534634 < baseStart_1534634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534670 : List Nat := [4, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5]
def baseStart_1534670 : Nat := 118140960795 + 1534670 * 2 ^ 59
def prefixEnd_1534670 : Nat := 4983230072969 + 3 ^ 40 * 1534670 * 2
def baseEnd_1534670 : Nat := 788023356035615830267187

theorem tailTrace_1534670 : CollatzResearch.WordTrace tailWord_1534670 prefixEnd_1534670 788023356035615830267187 := by
  unfold tailWord_1534670
  simp only [CollatzResearch.WordTrace]
  refine ⟨6996751668770020701775183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37316008900106777076134309 6996751668770020701775183)
  ·
    refine ⟨10495127503155031052662775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6996751668770020701775183 10495127503155031052662775)
    ·
      refine ⟨15742691254732546578994163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10495127503155031052662775 15742691254732546578994163)
      ·
        refine ⟨23614036882098819868491245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15742691254732546578994163 23614036882098819868491245)
        ·
          refine ⟨8855263830787057450684217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23614036882098819868491245 8855263830787057450684217)
          ·
            refine ⟨6641447873090293088013163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8855263830787057450684217 6641447873090293088013163)
            ·
              refine ⟨9962171809635439632019745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6641447873090293088013163 9962171809635439632019745)
              ·
                refine ⟨7471628857226579724014809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9962171809635439632019745 7471628857226579724014809)
                ·
                  refine ⟨5603721642919934793011107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7471628857226579724014809 5603721642919934793011107)
                  ·
                    refine ⟨8405582464379902189516661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5603721642919934793011107 8405582464379902189516661)
                    ·
                      refine ⟨788023356035615830267187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8405582464379902189516661 788023356035615830267187)
                      ·
                        rfl

theorem cell23_1534670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_1534670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534670 prefixEnd_1534670 := by exact prefixLift 1534670
  have htrace : WordTrace (prefixWord ++ tailWord_1534670) baseStart_1534670 baseEnd_1534670 := by
    simpa [prefixWord, tailWord_1534670, baseEnd_1534670] using wordTrace_append hprefix tailTrace_1534670
  have hstable : (prefixWord ++ tailWord_1534670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534670).length < 2 ^ (prefixWord ++ tailWord_1534670).sum := by decide
  have hdescent : baseEnd_1534670 < baseStart_1534670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534673 : List Nat := [1, 2, 2, 1, 2, 3, 2, 1, 9]
def baseStart_1534673 : Nat := 118140960795 + 1534673 * 2 ^ 59
def prefixEnd_1534673 : Nat := 4983230072969 + 3 ^ 40 * 1534673 * 2
def baseEnd_1534673 : Nat := 87558321830842146503297

theorem tailTrace_1534673 : CollatzResearch.WordTrace tailWord_1534673 prefixEnd_1534673 87558321830842146503297 := by
  unfold tailWord_1534673
  simp only [CollatzResearch.WordTrace]
  refine ⟨55974122769149297126560673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37316081846099531417707115 55974122769149297126560673)
  ·
    refine ⟨41980592076861972844920505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55974122769149297126560673 41980592076861972844920505)
    ·
      refine ⟨31485444057646479633690379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41980592076861972844920505 31485444057646479633690379)
      ·
        refine ⟨47228166086469719450535569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31485444057646479633690379 47228166086469719450535569)
        ·
          refine ⟨35421124564852289587901677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47228166086469719450535569 35421124564852289587901677)
          ·
            refine ⟨13282921711819608595463129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35421124564852289587901677 13282921711819608595463129)
            ·
              refine ⟨9962191283864706446597347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13282921711819608595463129 9962191283864706446597347)
              ·
                refine ⟨14943286925797059669896021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9962191283864706446597347 14943286925797059669896021)
                ·
                  refine ⟨87558321830842146503297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 14943286925797059669896021 87558321830842146503297)
                  ·
                    rfl

theorem cell23_1534673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 9].length) (baseStart_1534673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534673 prefixEnd_1534673 := by exact prefixLift 1534673
  have htrace : WordTrace (prefixWord ++ tailWord_1534673) baseStart_1534673 baseEnd_1534673 := by
    simpa [prefixWord, tailWord_1534673, baseEnd_1534673] using wordTrace_append hprefix tailTrace_1534673
  have hstable : (prefixWord ++ tailWord_1534673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534673).length < 2 ^ (prefixWord ++ tailWord_1534673).sum := by decide
  have hdescent : baseEnd_1534673 < baseStart_1534673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534684 : List Nat := [2, 2, 5, 1, 1, 1, 1, 1, 3, 4, 2]
def baseStart_1534684 : Nat := 118140960795 + 1534684 * 2 ^ 59
def prefixEnd_1534684 : Nat := 4983230072969 + 3 ^ 40 * 1534684 * 2
def baseEnd_1534684 : Nat := 788030544764778775492123

theorem tailTrace_1534684 : CollatzResearch.WordTrace tailWord_1534684 prefixEnd_1534684 788030544764778775492123 := by
  unfold tailWord_1534684
  simp only [CollatzResearch.WordTrace]
  refine ⟨27987261986054723002605553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37316349314739630670140737 27987261986054723002605553)
  ·
    refine ⟨20990446489541042251954165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27987261986054723002605553 20990446489541042251954165)
    ·
      refine ⟨1967854358394472711120703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20990446489541042251954165 1967854358394472711120703)
      ·
        refine ⟨2951781537591709066681055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1967854358394472711120703 2951781537591709066681055)
        ·
          refine ⟨4427672306387563600021583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2951781537591709066681055 4427672306387563600021583)
          ·
            refine ⟨6641508459581345400032375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4427672306387563600021583 6641508459581345400032375)
            ·
              refine ⟨9962262689372018100048563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6641508459581345400032375 9962262689372018100048563)
              ·
                refine ⟨14943394034058027150072845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9962262689372018100048563 14943394034058027150072845)
                ·
                  refine ⟨5603772762771760181277317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14943394034058027150072845 5603772762771760181277317)
                  ·
                    refine ⟨1050707393019705033989497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5603772762771760181277317 1050707393019705033989497)
                    ·
                      refine ⟨788030544764778775492123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1050707393019705033989497 788030544764778775492123)
                      ·
                        rfl

theorem cell23_1534684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_1534684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534684 prefixEnd_1534684 := by exact prefixLift 1534684
  have htrace : WordTrace (prefixWord ++ tailWord_1534684) baseStart_1534684 baseEnd_1534684 := by
    simpa [prefixWord, tailWord_1534684, baseEnd_1534684] using wordTrace_append hprefix tailTrace_1534684
  have hstable : (prefixWord ++ tailWord_1534684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534684).length < 2 ^ (prefixWord ++ tailWord_1534684).sum := by decide
  have hdescent : baseEnd_1534684 < baseStart_1534684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534700 : List Nat := [2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 3]
def baseStart_1534700 : Nat := 118140960795 + 1534700 * 2 ^ 59
def prefixEnd_1534700 : Nat := 4983230072969 + 3 ^ 40 * 1534700 * 2
def baseEnd_1534700 : Nat := 788038760455250712892049

theorem tailTrace_1534700 : CollatzResearch.WordTrace tailWord_1534700 prefixEnd_1534700 788038760455250712892049 := by
  unfold tailWord_1534700
  simp only [CollatzResearch.WordTrace]
  refine ⟨27987553770025740368896777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37316738360034320491862369 27987553770025740368896777)
  ·
    refine ⟨20990665327519305276672583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27987553770025740368896777 20990665327519305276672583)
    ·
      refine ⟨31485997991278957915008875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20990665327519305276672583 31485997991278957915008875)
      ·
        refine ⟨47228996986918436872513313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31485997991278957915008875 47228996986918436872513313)
        ·
          refine ⟨35421747740188827654384985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47228996986918436872513313 35421747740188827654384985)
          ·
            refine ⟨26566310805141620740788739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35421747740188827654384985 26566310805141620740788739)
            ·
              refine ⟨39849466207712431111183109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26566310805141620740788739 39849466207712431111183109)
              ·
                refine ⟨7471774913946080833346833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39849466207712431111183109 7471774913946080833346833)
                ·
                  refine ⟨5603831185459560625010125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7471774913946080833346833 5603831185459560625010125)
                  ·
                    refine ⟨2101436694547335234378797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5603831185459560625010125 2101436694547335234378797)
                    ·
                      refine ⟨788038760455250712892049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2101436694547335234378797 788038760455250712892049)
                      ·
                        rfl

theorem cell23_1534700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 3].length) (baseStart_1534700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534700 prefixEnd_1534700 := by exact prefixLift 1534700
  have htrace : WordTrace (prefixWord ++ tailWord_1534700) baseStart_1534700 baseEnd_1534700 := by
    simpa [prefixWord, tailWord_1534700, baseEnd_1534700] using wordTrace_append hprefix tailTrace_1534700
  have hstable : (prefixWord ++ tailWord_1534700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534700).length < 2 ^ (prefixWord ++ tailWord_1534700).sum := by decide
  have hdescent : baseEnd_1534700 < baseStart_1534700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534701 : List Nat := [1, 5, 1, 2, 1, 1, 4, 2, 2, 2, 2]
def baseStart_1534701 : Nat := 118140960795 + 1534701 * 2 ^ 59
def prefixEnd_1534701 : Nat := 4983230072969 + 3 ^ 40 * 1534701 * 2
def baseEnd_1534701 : Nat := 788039273935905208979545

theorem tailTrace_1534701 : CollatzResearch.WordTrace tailWord_1534701 prefixEnd_1534701 788039273935905208979545 := by
  unfold tailWord_1534701
  simp only [CollatzResearch.WordTrace]
  refine ⟨55975144013047857908579957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37316762675365238605719971 55975144013047857908579957)
  ·
    refine ⟨5247669751223236678929371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55975144013047857908579957 5247669751223236678929371)
    ·
      refine ⟨7871504626834855018394057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5247669751223236678929371 7871504626834855018394057)
      ·
        refine ⟨5903628470126141263795543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7871504626834855018394057 5903628470126141263795543)
        ·
          refine ⟨8855442705189211895693315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5903628470126141263795543 8855442705189211895693315)
          ·
            refine ⟨13283164057783817843539973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8855442705189211895693315 13283164057783817843539973)
            ·
              refine ⟨2490593260834465845663745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13283164057783817843539973 2490593260834465845663745)
              ·
                refine ⟨1867944945625849384247809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2490593260834465845663745 1867944945625849384247809)
                ·
                  refine ⟨1400958709219387038185857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1867944945625849384247809 1400958709219387038185857)
                  ·
                    refine ⟨1050719031914540278639393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1400958709219387038185857 1050719031914540278639393)
                    ·
                      refine ⟨788039273935905208979545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1050719031914540278639393 788039273935905208979545)
                      ·
                        rfl

theorem cell23_1534701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_1534701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534701 prefixEnd_1534701 := by exact prefixLift 1534701
  have htrace : WordTrace (prefixWord ++ tailWord_1534701) baseStart_1534701 baseEnd_1534701 := by
    simpa [prefixWord, tailWord_1534701, baseEnd_1534701] using wordTrace_append hprefix tailTrace_1534701
  have hstable : (prefixWord ++ tailWord_1534701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534701).length < 2 ^ (prefixWord ++ tailWord_1534701).sum := by decide
  have hdescent : baseEnd_1534701 < baseStart_1534701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534757 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 4, 4, 2]
def baseStart_1534757 : Nat := 118140960795 + 1534757 * 2 ^ 59
def prefixEnd_1534757 : Nat := 4983230072969 + 3 ^ 40 * 1534757 * 2
def baseEnd_1534757 : Nat := 788068028852556989879287

theorem tailTrace_1534757 : CollatzResearch.WordTrace tailWord_1534757 prefixEnd_1534757 788068028852556989879287 := by
  unfold tailWord_1534757
  simp only [CollatzResearch.WordTrace]
  refine ⟨55977186500844979472618525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37318124333896652981745683 55977186500844979472618525)
  ·
    refine ⟨20991444937816867302231947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55977186500844979472618525 20991444937816867302231947)
    ·
      refine ⟨31487167406725300953347921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20991444937816867302231947 31487167406725300953347921)
      ·
        refine ⟨23615375555043975715010941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31487167406725300953347921 23615375555043975715010941)
        ·
          refine ⟨8855765833141490893129103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23615375555043975715010941 8855765833141490893129103)
          ·
            refine ⟨13283648749712236339693655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8855765833141490893129103 13283648749712236339693655)
            ·
              refine ⟨19925473124568354509540483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13283648749712236339693655 19925473124568354509540483)
              ·
                refine ⟨29888209686852531764310725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19925473124568354509540483 29888209686852531764310725)
                ·
                  refine ⟨5604039316284849705808261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29888209686852531764310725 5604039316284849705808261)
                  ·
                    refine ⟨1050757371803409319839049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5604039316284849705808261 1050757371803409319839049)
                    ·
                      refine ⟨788068028852556989879287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1050757371803409319839049 788068028852556989879287)
                      ·
                        rfl

theorem cell23_1534757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 4, 2].length) (baseStart_1534757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534757 prefixEnd_1534757 := by exact prefixLift 1534757
  have htrace : WordTrace (prefixWord ++ tailWord_1534757) baseStart_1534757 baseEnd_1534757 := by
    simpa [prefixWord, tailWord_1534757, baseEnd_1534757] using wordTrace_append hprefix tailTrace_1534757
  have hstable : (prefixWord ++ tailWord_1534757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534757).length < 2 ^ (prefixWord ++ tailWord_1534757).sum := by decide
  have hdescent : baseEnd_1534757 < baseStart_1534757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534770 : List Nat := [3, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6]
def baseStart_1534770 : Nat := 118140960795 + 1534770 * 2 ^ 59
def prefixEnd_1534770 : Nat := 4983230072969 + 3 ^ 40 * 1534770 * 2
def baseEnd_1534770 : Nat := 788074704101065439016727

theorem tailTrace_1534770 : CollatzResearch.WordTrace tailWord_1534770 prefixEnd_1534770 788074704101065439016727 := by
  unfold tailWord_1534770
  simp only [CollatzResearch.WordTrace]
  refine ⟨13994415162449470673210441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37318440433198588461894509 13994415162449470673210441)
  ·
    refine ⟨10495811371837103004907831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13994415162449470673210441 10495811371837103004907831)
    ·
      refine ⟨15743717057755654507361747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10495811371837103004907831 15743717057755654507361747)
      ·
        refine ⟨23615575586633481761042621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15743717057755654507361747 23615575586633481761042621)
        ·
          refine ⟨8855840844987555660390983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23615575586633481761042621 8855840844987555660390983)
          ·
            refine ⟨13283761267481333490586475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8855840844987555660390983 13283761267481333490586475)
            ·
              refine ⟨19925641901222000235879713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13283761267481333490586475 19925641901222000235879713)
              ·
                refine ⟨14944231425916500176909785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19925641901222000235879713 14944231425916500176909785)
                ·
                  refine ⟨11208173569437375132682339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14944231425916500176909785 11208173569437375132682339)
                  ·
                    refine ⟨16812260354156062699023509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11208173569437375132682339 16812260354156062699023509)
                    ·
                      refine ⟨788074704101065439016727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16812260354156062699023509 788074704101065439016727)
                      ·
                        rfl

theorem cell23_1534770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_1534770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534770 prefixEnd_1534770 := by exact prefixLift 1534770
  have htrace : WordTrace (prefixWord ++ tailWord_1534770) baseStart_1534770 baseEnd_1534770 := by
    simpa [prefixWord, tailWord_1534770, baseEnd_1534770] using wordTrace_append hprefix tailTrace_1534770
  have hstable : (prefixWord ++ tailWord_1534770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534770).length < 2 ^ (prefixWord ++ tailWord_1534770).sum := by decide
  have hdescent : baseEnd_1534770 < baseStart_1534770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534817 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 3, 5, 2]
def baseStart_1534817 : Nat := 118140960795 + 1534817 * 2 ^ 59
def prefixEnd_1534817 : Nat := 4983230072969 + 3 ^ 40 * 1534817 * 2
def baseEnd_1534817 : Nat := 788098837691826755129011

theorem tailTrace_1534817 : CollatzResearch.WordTrace tailWord_1534817 prefixEnd_1534817 788098837691826755129011 := by
  unfold tailWord_1534817
  simp only [CollatzResearch.WordTrace]
  refine ⟨55979374880627609719802705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37319583253751739813201803 55979374880627609719802705)
  ·
    refine ⟨41984531160470707289852029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55979374880627609719802705 41984531160470707289852029)
    ·
      refine ⟨15744199185176515233694511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41984531160470707289852029 15744199185176515233694511)
      ·
        refine ⟨23616298777764772850541767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15744199185176515233694511 23616298777764772850541767)
        ·
          refine ⟨35424448166647159275812651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23616298777764772850541767 35424448166647159275812651)
          ·
            refine ⟨53136672249970738913718977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35424448166647159275812651 53136672249970738913718977)
            ·
              refine ⟨39852504187478054185289233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53136672249970738913718977 39852504187478054185289233)
              ·
                refine ⟨29889378140608540638966925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39852504187478054185289233 29889378140608540638966925)
                ·
                  refine ⟨11208516802728202739612597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29889378140608540638966925 11208516802728202739612597)
                  ·
                    refine ⟨1050798450255769006838681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11208516802728202739612597 1050798450255769006838681)
                    ·
                      refine ⟨788098837691826755129011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1050798450255769006838681 788098837691826755129011)
                      ·
                        rfl

theorem cell23_1534817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 5, 2].length) (baseStart_1534817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534817 prefixEnd_1534817 := by exact prefixLift 1534817
  have htrace : WordTrace (prefixWord ++ tailWord_1534817) baseStart_1534817 baseEnd_1534817 := by
    simpa [prefixWord, tailWord_1534817, baseEnd_1534817] using wordTrace_append hprefix tailTrace_1534817
  have hstable : (prefixWord ++ tailWord_1534817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534817).length < 2 ^ (prefixWord ++ tailWord_1534817).sum := by decide
  have hdescent : baseEnd_1534817 < baseStart_1534817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534818 : List Nat := [3, 3, 2, 1, 4, 1, 1, 1, 3, 4]
def baseStart_1534818 : Nat := 118140960795 + 1534818 * 2 ^ 59
def prefixEnd_1534818 : Nat := 4983230072969 + 3 ^ 40 * 1534818 * 2
def baseEnd_1534818 : Nat := 262699783724160417072169

theorem tailTrace_1534818 : CollatzResearch.WordTrace tailWord_1534818 prefixEnd_1534818 262699783724160417072169 := by
  unfold tailWord_1534818
  simp only [CollatzResearch.WordTrace]
  refine ⟨13994852838405996722647277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37319607569082657927059405 13994852838405996722647277)
  ·
    refine ⟨5248069814402248770992729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13994852838405996722647277 5248069814402248770992729)
    ·
      refine ⟨3936052360801686578244547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5248069814402248770992729 3936052360801686578244547)
      ·
        refine ⟨5904078541202529867366821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3936052360801686578244547 5904078541202529867366821)
        ·
          refine ⟨1107014726475474350131279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5904078541202529867366821 1107014726475474350131279)
          ·
            refine ⟨1660522089713211525196919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1107014726475474350131279 1660522089713211525196919)
            ·
              refine ⟨2490783134569817287795379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1660522089713211525196919 2490783134569817287795379)
              ·
                refine ⟨3736174701854725931693069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2490783134569817287795379 3736174701854725931693069)
                ·
                  refine ⟨1401065513195522224384901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3736174701854725931693069 1401065513195522224384901)
                  ·
                    refine ⟨262699783724160417072169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1401065513195522224384901 262699783724160417072169)
                    ·
                      rfl

theorem cell23_1534818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_1534818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534818 prefixEnd_1534818 := by exact prefixLift 1534818
  have htrace : WordTrace (prefixWord ++ tailWord_1534818) baseStart_1534818 baseEnd_1534818 := by
    simpa [prefixWord, tailWord_1534818, baseEnd_1534818] using wordTrace_append hprefix tailTrace_1534818
  have hstable : (prefixWord ++ tailWord_1534818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534818).length < 2 ^ (prefixWord ++ tailWord_1534818).sum := by decide
  have hdescent : baseEnd_1534818 < baseStart_1534818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534847 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 2, 6, 2]
def baseStart_1534847 : Nat := 118140960795 + 1534847 * 2 ^ 59
def prefixEnd_1534847 : Nat := 4983230072969 + 3 ^ 40 * 1534847 * 2
def baseEnd_1534847 : Nat := 788114242111461637753873

theorem tailTrace_1534847 : CollatzResearch.WordTrace tailWord_1534847 prefixEnd_1534847 788114242111461637753873 := by
  unfold tailWord_1534847
  simp only [CollatzResearch.WordTrace]
  refine ⟨55980469070518924843394795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37320312713679283228929863 55980469070518924843394795)
  ·
    refine ⟨83970703605778387265092193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55980469070518924843394795 83970703605778387265092193)
    ·
      refine ⟨62978027704333790448819145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83970703605778387265092193 62978027704333790448819145)
      ·
        refine ⟨47233520778250342836614359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62978027704333790448819145 47233520778250342836614359)
        ·
          refine ⟨70850281167375514254921539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47233520778250342836614359 70850281167375514254921539)
          ·
            refine ⟨106275421751063271382382309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70850281167375514254921539 106275421751063271382382309)
            ·
              refine ⟨19926641578324363384196683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106275421751063271382382309 19926641578324363384196683)
              ·
                refine ⟨29889962367486545076295025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19926641578324363384196683 29889962367486545076295025)
                ·
                  refine ⟨22417471775614908807221269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29889962367486545076295025 22417471775614908807221269)
                  ·
                    refine ⟨1050818989481948850338497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22417471775614908807221269 1050818989481948850338497)
                    ·
                      refine ⟨788114242111461637753873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1050818989481948850338497 788114242111461637753873)
                      ·
                        rfl

theorem cell23_1534847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 6, 2].length) (baseStart_1534847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534847 prefixEnd_1534847 := by exact prefixLift 1534847
  have htrace : WordTrace (prefixWord ++ tailWord_1534847) baseStart_1534847 baseEnd_1534847 := by
    simpa [prefixWord, tailWord_1534847, baseEnd_1534847] using wordTrace_append hprefix tailTrace_1534847
  have hstable : (prefixWord ++ tailWord_1534847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534847).length < 2 ^ (prefixWord ++ tailWord_1534847).sum := by decide
  have hdescent : baseEnd_1534847 < baseStart_1534847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534857 : List Nat := [1, 2, 1, 1, 5, 3, 1, 2, 1, 6]
def baseStart_1534857 : Nat := 118140960795 + 1534857 * 2 ^ 59
def prefixEnd_1534857 : Nat := 4983230072969 + 3 ^ 40 * 1534857 * 2
def baseEnd_1534857 : Nat := 262706458972668866209609

theorem tailTrace_1534857 : CollatzResearch.WordTrace tailWord_1534857 prefixEnd_1534857 262706458972668866209609 := by
  unfold tailWord_1534857
  simp only [CollatzResearch.WordTrace]
  refine ⟨55980833800482696551258825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37320555866988464367505883 55980833800482696551258825)
  ·
    refine ⟨41985625350362022413444119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55980833800482696551258825 41985625350362022413444119)
    ·
      refine ⟨62978438025543033620166179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41985625350362022413444119 62978438025543033620166179)
      ·
        refine ⟨94467657038314550430249269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62978438025543033620166179 94467657038314550430249269)
        ·
          refine ⟨8856342847341989102835869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94467657038314550430249269 8856342847341989102835869)
          ·
            refine ⟨3321128567753245913563451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8856342847341989102835869 3321128567753245913563451)
            ·
              refine ⟨4981692851629868870345177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3321128567753245913563451 4981692851629868870345177)
              ·
                refine ⟨3736269638722401652758883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4981692851629868870345177 3736269638722401652758883)
                ·
                  refine ⟨5604404458083602479138325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3736269638722401652758883 5604404458083602479138325)
                  ·
                    refine ⟨262706458972668866209609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5604404458083602479138325 262706458972668866209609)
                    ·
                      rfl

theorem cell23_1534857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 6].length) (baseStart_1534857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534857 prefixEnd_1534857 := by exact prefixLift 1534857
  have htrace : WordTrace (prefixWord ++ tailWord_1534857) baseStart_1534857 baseEnd_1534857 := by
    simpa [prefixWord, tailWord_1534857, baseEnd_1534857] using wordTrace_append hprefix tailTrace_1534857
  have hstable : (prefixWord ++ tailWord_1534857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534857).length < 2 ^ (prefixWord ++ tailWord_1534857).sum := by decide
  have hdescent : baseEnd_1534857 < baseStart_1534857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534877 : List Nat := [1, 4, 2, 1, 2, 1, 1, 2, 3, 2, 4]
def baseStart_1534877 : Nat := 118140960795 + 1534877 * 2 ^ 59
def prefixEnd_1534877 : Nat := 4983230072969 + 3 ^ 40 * 1534877 * 2
def baseEnd_1534877 : Nat := 788129646531096520378735

theorem tailTrace_1534877 : CollatzResearch.WordTrace tailWord_1534877 prefixEnd_1534877 788129646531096520378735 := by
  unfold tailWord_1534877
  simp only [CollatzResearch.WordTrace]
  refine ⟨55981563260410239966986885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37321042173606826644657923 55981563260410239966986885)
  ·
    refine ⟨10496543111326919993810041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55981563260410239966986885 10496543111326919993810041)
    ·
      refine ⟨7872407333495189995357531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10496543111326919993810041 7872407333495189995357531)
      ·
        refine ⟨11808611000242784993036297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7872407333495189995357531 11808611000242784993036297)
        ·
          refine ⟨8856458250182088744777223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11808611000242784993036297 8856458250182088744777223)
          ·
            refine ⟨13284687375273133117165835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8856458250182088744777223 13284687375273133117165835)
            ·
              refine ⟨19927031062909699675748753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13284687375273133117165835 19927031062909699675748753)
              ·
                refine ⟨14945273297182274756811565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19927031062909699675748753 14945273297182274756811565)
                ·
                  refine ⟨5604477486443353033804337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14945273297182274756811565 5604477486443353033804337)
                  ·
                    refine ⟨4203358114832514775353253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5604477486443353033804337 4203358114832514775353253)
                    ·
                      refine ⟨788129646531096520378735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4203358114832514775353253 788129646531096520378735)
                      ·
                        rfl

theorem cell23_1534877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_1534877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534877 prefixEnd_1534877 := by exact prefixLift 1534877
  have htrace : WordTrace (prefixWord ++ tailWord_1534877) baseStart_1534877 baseEnd_1534877 := by
    simpa [prefixWord, tailWord_1534877, baseEnd_1534877] using wordTrace_append hprefix tailTrace_1534877
  have hstable : (prefixWord ++ tailWord_1534877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534877).length < 2 ^ (prefixWord ++ tailWord_1534877).sum := by decide
  have hdescent : baseEnd_1534877 < baseStart_1534877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534925 : List Nat := [1, 6, 3, 1, 1, 1, 1, 1, 4, 4]
def baseStart_1534925 : Nat := 118140960795 + 1534925 * 2 ^ 59
def prefixEnd_1534925 : Nat := 4983230072969 + 3 ^ 40 * 1534925 * 2
def baseEnd_1534925 : Nat := 262718097867504110859505

theorem tailTrace_1534925 : CollatzResearch.WordTrace tailWord_1534925 prefixEnd_1534925 262718097867504110859505 := by
  unfold tailWord_1534925
  simp only [CollatzResearch.WordTrace]
  refine ⟨55983313964236344164734229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37322209309490896109822819 55983313964236344164734229)
  ·
    refine ⟨2624217842073578632721917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 55983313964236344164734229 2624217842073578632721917)
    ·
      refine ⟨984081690777591987270719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2624217842073578632721917 984081690777591987270719)
      ·
        refine ⟨1476122536166387980906079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 984081690777591987270719 1476122536166387980906079)
        ·
          refine ⟨2214183804249581971359119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1476122536166387980906079 2214183804249581971359119)
          ·
            refine ⟨3321275706374372957038679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2214183804249581971359119 3321275706374372957038679)
            ·
              refine ⟨4981913559561559435558019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3321275706374372957038679 4981913559561559435558019)
              ·
                refine ⟨7472870339342339153337029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4981913559561559435558019 7472870339342339153337029)
                ·
                  refine ⟨1401163188626688591250693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7472870339342339153337029 1401163188626688591250693)
                  ·
                    refine ⟨262718097867504110859505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1401163188626688591250693 262718097867504110859505)
                    ·
                      rfl

theorem cell23_1534925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_1534925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534925 prefixEnd_1534925 := by exact prefixLift 1534925
  have htrace : WordTrace (prefixWord ++ tailWord_1534925) baseStart_1534925 baseEnd_1534925 := by
    simpa [prefixWord, tailWord_1534925, baseEnd_1534925] using wordTrace_append hprefix tailTrace_1534925
  have hstable : (prefixWord ++ tailWord_1534925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534925).length < 2 ^ (prefixWord ++ tailWord_1534925).sum := by decide
  have hdescent : baseEnd_1534925 < baseStart_1534925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534947 : List Nat := [1, 1, 1, 6, 1, 1, 1, 3, 2, 6]
def baseStart_1534947 : Nat := 118140960795 + 1534947 * 2 ^ 59
def prefixEnd_1534947 : Nat := 4983230072969 + 3 ^ 40 * 1534947 * 2
def baseEnd_1534947 : Nat := 262721863392303748834471

theorem tailTrace_1534947 : CollatzResearch.WordTrace tailWord_1534947 prefixEnd_1534947 262721863392303748834471 := by
  unfold tailWord_1534947
  simp only [CollatzResearch.WordTrace]
  refine ⟨55984116370156641922035095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37322744246771094614690063 55984116370156641922035095)
  ·
    refine ⟨83976174555234962883052643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55984116370156641922035095 83976174555234962883052643)
    ·
      refine ⟨125964261832852444324578965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83976174555234962883052643 125964261832852444324578965)
      ·
        refine ⟨5904574773414958327714639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 125964261832852444324578965 5904574773414958327714639)
        ·
          refine ⟨8856862160122437491571959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5904574773414958327714639 8856862160122437491571959)
          ·
            refine ⟨13285293240183656237357939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8856862160122437491571959 13285293240183656237357939)
            ·
              refine ⟨19927939860275484356036909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13285293240183656237357939 19927939860275484356036909)
              ·
                refine ⟨7472977447603306633513841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19927939860275484356036909 7472977447603306633513841)
                ·
                  refine ⟨5604733085702479975135381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7472977447603306633513841 5604733085702479975135381)
                  ·
                    refine ⟨262721863392303748834471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5604733085702479975135381 262721863392303748834471)
                    ·
                      rfl

theorem cell23_1534947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 6].length) (baseStart_1534947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1534947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1534947 prefixEnd_1534947 := by exact prefixLift 1534947
  have htrace : WordTrace (prefixWord ++ tailWord_1534947) baseStart_1534947 baseEnd_1534947 := by
    simpa [prefixWord, tailWord_1534947, baseEnd_1534947] using wordTrace_append hprefix tailTrace_1534947
  have hstable : (prefixWord ++ tailWord_1534947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534947).length < 2 ^ (prefixWord ++ tailWord_1534947).sum := by decide
  have hdescent : baseEnd_1534947 < baseStart_1534947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535005 : List Nat := [1, 4, 2, 2, 3, 1, 1, 3, 2, 2, 2]
def baseStart_1535005 : Nat := 118140960795 + 1535005 * 2 ^ 59
def prefixEnd_1535005 : Nat := 4983230072969 + 3 ^ 40 * 1535005 * 2
def baseEnd_1535005 : Nat := 788195372054872019578147

theorem tailTrace_1535005 : CollatzResearch.WordTrace tailWord_1535005 prefixEnd_1535005 788195372054872019578147 := by
  unfold tailWord_1535005
  simp only [CollatzResearch.WordTrace]
  refine ⟨55986231803946517827646469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37324154535964345218430979 55986231803946517827646469)
  ·
    refine ⟨10497418463239972092683713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55986231803946517827646469 10497418463239972092683713)
    ·
      refine ⟨7873063847429979069512785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10497418463239972092683713 7873063847429979069512785)
      ·
        refine ⟨5904797885572484302134589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7873063847429979069512785 5904797885572484302134589)
        ·
          refine ⟨2214299207089681613300471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5904797885572484302134589 2214299207089681613300471)
          ·
            refine ⟨3321448810634522419950707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2214299207089681613300471 3321448810634522419950707)
            ·
              refine ⟨4982173215951783629926061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3321448810634522419950707 4982173215951783629926061)
              ·
                refine ⟨1868314955981918861222273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4982173215951783629926061 1868314955981918861222273)
                ·
                  refine ⟨1401236216986439145916705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1868314955981918861222273 1401236216986439145916705)
                  ·
                    refine ⟨1050927162739829359437529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1401236216986439145916705 1050927162739829359437529)
                    ·
                      refine ⟨788195372054872019578147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1050927162739829359437529 788195372054872019578147)
                      ·
                        rfl

theorem cell23_1535005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_1535005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535005 prefixEnd_1535005 := by exact prefixLift 1535005
  have htrace : WordTrace (prefixWord ++ tailWord_1535005) baseStart_1535005 baseEnd_1535005 := by
    simpa [prefixWord, tailWord_1535005, baseEnd_1535005] using wordTrace_append hprefix tailTrace_1535005
  have hstable : (prefixWord ++ tailWord_1535005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535005).length < 2 ^ (prefixWord ++ tailWord_1535005).sum := by decide
  have hdescent : baseEnd_1535005 < baseStart_1535005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535024 : List Nat := [2, 1, 1, 1, 2, 4, 4, 1, 2, 5]
def baseStart_1535024 : Nat := 118140960795 + 1535024 * 2 ^ 59
def prefixEnd_1535024 : Nat := 4983230072969 + 3 ^ 40 * 1535024 * 2
def baseEnd_1535024 : Nat := 262735042729102481746853

theorem tailTrace_1535024 : CollatzResearch.WordTrace tailWord_1535024 prefixEnd_1535024 262735042729102481746853 := by
  unfold tailWord_1535024
  simp only [CollatzResearch.WordTrace]
  refine ⟨27993462395438842036294063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37324616527251789381725417 27993462395438842036294063)
  ·
    refine ⟨41990193593158263054441095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27993462395438842036294063 41990193593158263054441095)
    ·
      refine ⟨62985290389737394581661643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41990193593158263054441095 62985290389737394581661643)
      ·
        refine ⟨94477935584606091872492465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62985290389737394581661643 94477935584606091872492465)
        ·
          refine ⟨70858451688454568904369349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94477935584606091872492465 70858451688454568904369349)
          ·
            refine ⟨13285959691585231669569253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70858451688454568904369349 13285959691585231669569253)
            ·
              refine ⟨2491117442172230938044235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13285959691585231669569253 2491117442172230938044235)
              ·
                refine ⟨3736676163258346407066353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2491117442172230938044235 3736676163258346407066353)
                ·
                  refine ⟨2802507122443759805299765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3736676163258346407066353 2802507122443759805299765)
                  ·
                    refine ⟨262735042729102481746853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2802507122443759805299765 262735042729102481746853)
                    ·
                      rfl

theorem cell23_1535024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 2, 5].length) (baseStart_1535024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535024 prefixEnd_1535024 := by exact prefixLift 1535024
  have htrace : WordTrace (prefixWord ++ tailWord_1535024) baseStart_1535024 baseEnd_1535024 := by
    simpa [prefixWord, tailWord_1535024, baseEnd_1535024] using wordTrace_append hprefix tailTrace_1535024
  have hstable : (prefixWord ++ tailWord_1535024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535024).length < 2 ^ (prefixWord ++ tailWord_1535024).sum := by decide
  have hdescent : baseEnd_1535024 < baseStart_1535024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535061 : List Nat := [1, 3, 2, 2, 1, 2, 3, 1, 2, 4, 2]
def baseStart_1535061 : Nat := 118140960795 + 1535061 * 2 ^ 59
def prefixEnd_1535061 : Nat := 4983230072969 + 3 ^ 40 * 1535061 * 2
def baseEnd_1535061 : Nat := 788224126971523800477889

theorem tailTrace_1535061 : CollatzResearch.WordTrace tailWord_1535061 prefixEnd_1535061 788224126971523800477889 := by
  unfold tailWord_1535061
  simp only [CollatzResearch.WordTrace]
  refine ⟨55988274291743639391685037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37325516194495759594456691 55988274291743639391685037)
  ·
    refine ⟨20995602859403864771881889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55988274291743639391685037 20995602859403864771881889)
    ·
      refine ⟨15746702144552898578911417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20995602859403864771881889 15746702144552898578911417)
      ·
        refine ⟨11810026608414673934183563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15746702144552898578911417 11810026608414673934183563)
        ·
          refine ⟨17715039912622010901275345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11810026608414673934183563 17715039912622010901275345)
          ·
            refine ⟨13286279934466508175956509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17715039912622010901275345 13286279934466508175956509)
            ·
              refine ⟨4982354975424940565983691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13286279934466508175956509 4982354975424940565983691)
              ·
                refine ⟨7473532463137410848975537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4982354975424940565983691 7473532463137410848975537)
                ·
                  refine ⟨5605149347353058136731653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7473532463137410848975537 5605149347353058136731653)
                  ·
                    refine ⟨1050965502628698400637185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5605149347353058136731653 1050965502628698400637185)
                    ·
                      refine ⟨788224126971523800477889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1050965502628698400637185 788224126971523800477889)
                      ·
                        rfl

theorem cell23_1535061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_1535061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535061 prefixEnd_1535061 := by exact prefixLift 1535061
  have htrace : WordTrace (prefixWord ++ tailWord_1535061) baseStart_1535061 baseEnd_1535061 := by
    simpa [prefixWord, tailWord_1535061, baseEnd_1535061] using wordTrace_append hprefix tailTrace_1535061
  have hstable : (prefixWord ++ tailWord_1535061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535061).length < 2 ^ (prefixWord ++ tailWord_1535061).sum := by decide
  have hdescent : baseEnd_1535061 < baseStart_1535061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535064 : List Nat := [2, 1, 2, 2, 1, 3, 2, 2, 1, 4, 3]
def baseStart_1535064 : Nat := 118140960795 + 1535064 * 2 ^ 59
def prefixEnd_1535064 : Nat := 4983230072969 + 3 ^ 40 * 1535064 * 2
def baseEnd_1535064 : Nat := 788225667413487288740375

theorem tailTrace_1535064 : CollatzResearch.WordTrace tailWord_1535064 prefixEnd_1535064 788225667413487288740375 := by
  unfold tailWord_1535064
  simp only [CollatzResearch.WordTrace]
  refine ⟨27994191855366385452022123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37325589140488513936029497 27994191855366385452022123)
  ·
    refine ⟨41991287783049578178033185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27994191855366385452022123 41991287783049578178033185)
    ·
      refine ⟨31493465837287183633524889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41991287783049578178033185 31493465837287183633524889)
      ·
        refine ⟨23620099377965387725143667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31493465837287183633524889 23620099377965387725143667)
        ·
          refine ⟨35430149066948081587715501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23620099377965387725143667 35430149066948081587715501)
          ·
            refine ⟨13286305900105530595393313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35430149066948081587715501 13286305900105530595393313)
            ·
              refine ⟨9964729425079147946544985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13286305900105530595393313 9964729425079147946544985)
              ·
                refine ⟨7473547068809360959908739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9964729425079147946544985 7473547068809360959908739)
                ·
                  refine ⟨11210320603214041439863109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7473547068809360959908739 11210320603214041439863109)
                  ·
                    refine ⟨2101935113102632769974333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11210320603214041439863109 2101935113102632769974333)
                    ·
                      refine ⟨788225667413487288740375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2101935113102632769974333 788225667413487288740375)
                      ·
                        rfl

theorem cell23_1535064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_1535064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535064 prefixEnd_1535064 := by exact prefixLift 1535064
  have htrace : WordTrace (prefixWord ++ tailWord_1535064) baseStart_1535064 baseEnd_1535064 := by
    simpa [prefixWord, tailWord_1535064, baseEnd_1535064] using wordTrace_append hprefix tailTrace_1535064
  have hstable : (prefixWord ++ tailWord_1535064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535064).length < 2 ^ (prefixWord ++ tailWord_1535064).sum := by decide
  have hdescent : baseEnd_1535064 < baseStart_1535064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535081 : List Nat := [1, 2, 1, 1, 1, 6, 3, 1, 2, 2, 3]
def baseStart_1535081 : Nat := 118140960795 + 1535081 * 2 ^ 59
def prefixEnd_1535081 : Nat := 4983230072969 + 3 ^ 40 * 1535081 * 2
def baseEnd_1535081 : Nat := 788234396584613722227797

theorem tailTrace_1535081 : CollatzResearch.WordTrace tailWord_1535081 prefixEnd_1535081 788234396584613722227797 := by
  unfold tailWord_1535081
  simp only [CollatzResearch.WordTrace]
  refine ⟨55989003751671182807413097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37326002501114121871608731 55989003751671182807413097)
  ·
    refine ⟨41991752813753387105559823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55989003751671182807413097 41991752813753387105559823)
    ·
      refine ⟨62987629220630080658339735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41991752813753387105559823 62987629220630080658339735)
      ·
        refine ⟨94481443830945120987509603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62987629220630080658339735 94481443830945120987509603)
        ·
          refine ⟨141722165746417681481264405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94481443830945120987509603 141722165746417681481264405)
          ·
            refine ⟨6643226519363328819434269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 141722165746417681481264405 6643226519363328819434269)
            ·
              refine ⟨2491209944761248307287851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6643226519363328819434269 2491209944761248307287851)
              ·
                refine ⟨3736814917141872460931777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2491209944761248307287851 3736814917141872460931777)
                ·
                  refine ⟨2802611187856404345698833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3736814917141872460931777 2802611187856404345698833)
                  ·
                    refine ⟨2101958390892303259274125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2802611187856404345698833 2101958390892303259274125)
                    ·
                      refine ⟨788234396584613722227797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2101958390892303259274125 788234396584613722227797)
                      ·
                        rfl

theorem cell23_1535081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 2, 3].length) (baseStart_1535081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535081 prefixEnd_1535081 := by exact prefixLift 1535081
  have htrace : WordTrace (prefixWord ++ tailWord_1535081) baseStart_1535081 baseEnd_1535081 := by
    simpa [prefixWord, tailWord_1535081, baseEnd_1535081] using wordTrace_append hprefix tailTrace_1535081
  have hstable : (prefixWord ++ tailWord_1535081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535081).length < 2 ^ (prefixWord ++ tailWord_1535081).sum := by decide
  have hdescent : baseEnd_1535081 < baseStart_1535081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535088 : List Nat := [2, 1, 1, 1, 5, 1, 4, 3, 1, 4]
def baseStart_1535088 : Nat := 118140960795 + 1535088 * 2 ^ 59
def prefixEnd_1535088 : Nat := 4983230072969 + 3 ^ 40 * 1535088 * 2
def baseEnd_1535088 : Nat := 262745996983065064946755

theorem tailTrace_1535088 : CollatzResearch.WordTrace tailWord_1535088 prefixEnd_1535088 262745996983065064946755 := by
  unfold tailWord_1535088
  simp only [CollatzResearch.WordTrace]
  refine ⟨27994629531322911501458959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37326172708430548668611945 27994629531322911501458959)
  ·
    refine ⟨41991944296984367252188439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27994629531322911501458959 41991944296984367252188439)
    ·
      refine ⟨62987916445476550878282659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41991944296984367252188439 62987916445476550878282659)
      ·
        refine ⟨94481874668214826317423989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62987916445476550878282659 94481874668214826317423989)
        ·
          refine ⟨8857675750145139967258499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94481874668214826317423989 8857675750145139967258499)
          ·
            refine ⟨13286513625217709950887749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8857675750145139967258499 13286513625217709950887749)
            ·
              refine ⟨2491221304728320615791453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13286513625217709950887749 2491221304728320615791453)
              ·
                refine ⟨934207989273120230921795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2491221304728320615791453 934207989273120230921795)
                ·
                  refine ⟨1401311983909680346382693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 934207989273120230921795 1401311983909680346382693)
                  ·
                    refine ⟨262745996983065064946755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1401311983909680346382693 262745996983065064946755)
                    ·
                      rfl

theorem cell23_1535088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 3, 1, 4].length) (baseStart_1535088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535088 prefixEnd_1535088 := by exact prefixLift 1535088
  have htrace : WordTrace (prefixWord ++ tailWord_1535088) baseStart_1535088 baseEnd_1535088 := by
    simpa [prefixWord, tailWord_1535088, baseEnd_1535088] using wordTrace_append hprefix tailTrace_1535088
  have hstable : (prefixWord ++ tailWord_1535088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535088).length < 2 ^ (prefixWord ++ tailWord_1535088).sum := by decide
  have hdescent : baseEnd_1535088 < baseStart_1535088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535118 : List Nat := [4, 1, 1, 3, 2, 2, 3, 1, 6]
def baseStart_1535118 : Nat := 118140960795 + 1535118 * 2 ^ 59
def prefixEnd_1535118 : Nat := 4983230072969 + 3 ^ 40 * 1535118 * 2
def baseEnd_1535118 : Nat := 87583710596536675273903

theorem tailTrace_1535118 : CollatzResearch.WordTrace tailWord_1535118 prefixEnd_1535118 87583710596536675273903 := by
  unfold tailWord_1535118
  simp only [CollatzResearch.WordTrace]
  refine ⟨6998794156567142265813751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37326902168358092084340005 6998794156567142265813751)
  ·
    refine ⟨10498191234850713398720627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6998794156567142265813751 10498191234850713398720627)
    ·
      refine ⟨15747286852276070098080941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10498191234850713398720627 15747286852276070098080941)
      ·
        refine ⟨5905232569603526286780353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15747286852276070098080941 5905232569603526286780353)
        ·
          refine ⟨4428924427202644715085265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5905232569603526286780353 4428924427202644715085265)
          ·
            refine ⟨3321693320401983536313949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4428924427202644715085265 3321693320401983536313949)
            ·
              refine ⟨1245634995150743826117731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3321693320401983536313949 1245634995150743826117731)
              ·
                refine ⟨1868452492726115739176597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1245634995150743826117731 1868452492726115739176597)
                ·
                  refine ⟨87583710596536675273903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1868452492726115739176597 87583710596536675273903)
                  ·
                    rfl

theorem cell23_1535118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 6].length) (baseStart_1535118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535118 prefixEnd_1535118 := by exact prefixLift 1535118
  have htrace : WordTrace (prefixWord ++ tailWord_1535118) baseStart_1535118 baseEnd_1535118 := by
    simpa [prefixWord, tailWord_1535118, baseEnd_1535118] using wordTrace_append hprefix tailTrace_1535118
  have hstable : (prefixWord ++ tailWord_1535118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535118).length < 2 ^ (prefixWord ++ tailWord_1535118).sum := by decide
  have hdescent : baseEnd_1535118 < baseStart_1535118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535128 : List Nat := [2, 1, 2, 4, 2, 1, 2, 2, 3, 1, 3]
def baseStart_1535128 : Nat := 118140960795 + 1535128 * 2 ^ 59
def prefixEnd_1535128 : Nat := 4983230072969 + 3 ^ 40 * 1535128 * 2
def baseEnd_1535128 : Nat := 788258530175375038340081

theorem tailTrace_1535128 : CollatzResearch.WordTrace tailWord_1535128 prefixEnd_1535128 788258530175375038340081 := by
  unfold tailWord_1535128
  simp only [CollatzResearch.WordTrace]
  refine ⟨27995358991250454917187019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37327145321667273222916025 27995358991250454917187019)
  ·
    refine ⟨41993038486875682375780529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27995358991250454917187019 41993038486875682375780529)
    ·
      refine ⟨31494778865156761781835397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41993038486875682375780529 31494778865156761781835397)
      ·
        refine ⟨5905271037216892834094137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31494778865156761781835397 5905271037216892834094137)
        ·
          refine ⟨4428953277912669625570603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5905271037216892834094137 4428953277912669625570603)
          ·
            refine ⟨6643429916869004438355905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4428953277912669625570603 6643429916869004438355905)
            ·
              refine ⟨4982572437651753328766929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6643429916869004438355905 4982572437651753328766929)
              ·
                refine ⟨3736929328238814996575197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4982572437651753328766929 3736929328238814996575197)
                ·
                  refine ⟨1401348498089555623715699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3736929328238814996575197 1401348498089555623715699)
                  ·
                    refine ⟨2102022747134333435573549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1401348498089555623715699 2102022747134333435573549)
                    ·
                      refine ⟨788258530175375038340081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2102022747134333435573549 788258530175375038340081)
                      ·
                        rfl

theorem cell23_1535128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_1535128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535128 prefixEnd_1535128 := by exact prefixLift 1535128
  have htrace : WordTrace (prefixWord ++ tailWord_1535128) baseStart_1535128 baseEnd_1535128 := by
    simpa [prefixWord, tailWord_1535128, baseEnd_1535128] using wordTrace_append hprefix tailTrace_1535128
  have hstable : (prefixWord ++ tailWord_1535128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535128).length < 2 ^ (prefixWord ++ tailWord_1535128).sum := by decide
  have hdescent : baseEnd_1535128 < baseStart_1535128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535151 : List Nat := [1, 1, 2, 1, 2, 3, 4, 3, 1, 1, 4]
def baseStart_1535151 : Nat := 118140960795 + 1535151 * 2 ^ 59
def prefixEnd_1535151 : Nat := 4983230072969 + 3 ^ 40 * 1535151 * 2
def baseEnd_1535151 : Nat := 788270340230428448352475

theorem tailTrace_1535151 : CollatzResearch.WordTrace tailWord_1535151 prefixEnd_1535151 788270340230428448352475 := by
  unfold tailWord_1535151
  simp only [CollatzResearch.WordTrace]
  refine ⟨55991556861417584762461307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37327704574278389841640871 55991556861417584762461307)
  ·
    refine ⟨83987335292126377143691961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55991556861417584762461307 83987335292126377143691961)
    ·
      refine ⟨62990501469094782857768971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83987335292126377143691961 62990501469094782857768971)
      ·
        refine ⟨94485752203642174286653457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62990501469094782857768971 94485752203642174286653457)
        ·
          refine ⟨70864314152731630714990093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94485752203642174286653457 70864314152731630714990093)
          ·
            refine ⟨26574117807274361518121285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70864314152731630714990093 26574117807274361518121285)
            ·
              refine ⟨4982647088863942784647741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26574117807274361518121285 4982647088863942784647741)
              ·
                refine ⟨1868492658323978544242903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4982647088863942784647741 1868492658323978544242903)
                ·
                  refine ⟨2802738987485967816364355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1868492658323978544242903 2802738987485967816364355)
                  ·
                    refine ⟨4204108481228951724546533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2802738987485967816364355 4204108481228951724546533)
                    ·
                      refine ⟨788270340230428448352475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4204108481228951724546533 788270340230428448352475)
                      ·
                        rfl

theorem cell23_1535151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 1, 4].length) (baseStart_1535151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535151 prefixEnd_1535151 := by exact prefixLift 1535151
  have htrace : WordTrace (prefixWord ++ tailWord_1535151) baseStart_1535151 baseEnd_1535151 := by
    simpa [prefixWord, tailWord_1535151, baseEnd_1535151] using wordTrace_append hprefix tailTrace_1535151
  have hstable : (prefixWord ++ tailWord_1535151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535151).length < 2 ^ (prefixWord ++ tailWord_1535151).sum := by decide
  have hdescent : baseEnd_1535151 < baseStart_1535151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535161 : List Nat := [1, 2, 1, 4, 1, 3, 2, 1, 4, 4]
def baseStart_1535161 : Nat := 118140960795 + 1535161 * 2 ^ 59
def prefixEnd_1535161 : Nat := 4983230072969 + 3 ^ 40 * 1535161 * 2
def baseEnd_1535161 : Nat := 262758491678991136409143

theorem tailTrace_1535161 : CollatzResearch.WordTrace tailWord_1535161 prefixEnd_1535161 262758491678991136409143 := by
  unfold tailWord_1535161
  simp only [CollatzResearch.WordTrace]
  refine ⟨55991921591381356470325337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37327947727587570980216891 55991921591381356470325337)
  ·
    refine ⟨41993941193536017352744003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55991921591381356470325337 41993941193536017352744003)
    ·
      refine ⟨62990911790304026029116005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41993941193536017352744003 62990911790304026029116005)
      ·
        refine ⟨11810795960682004880459251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62990911790304026029116005 11810795960682004880459251)
        ·
          refine ⟨17716193941023007320688877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11810795960682004880459251 17716193941023007320688877)
          ·
            refine ⟨6643572727883627745258329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17716193941023007320688877 6643572727883627745258329)
            ·
              refine ⟨4982679545912720808943747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6643572727883627745258329 4982679545912720808943747)
              ·
                refine ⟨7474019318869081213415621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4982679545912720808943747 7474019318869081213415621)
                ·
                  refine ⟨1401378622287952727515429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7474019318869081213415621 1401378622287952727515429)
                  ·
                    refine ⟨262758491678991136409143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1401378622287952727515429 262758491678991136409143)
                    ·
                      rfl

theorem cell23_1535161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 4, 4].length) (baseStart_1535161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535161 prefixEnd_1535161 := by exact prefixLift 1535161
  have htrace : WordTrace (prefixWord ++ tailWord_1535161) baseStart_1535161 baseEnd_1535161 := by
    simpa [prefixWord, tailWord_1535161, baseEnd_1535161] using wordTrace_append hprefix tailTrace_1535161
  have hstable : (prefixWord ++ tailWord_1535161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535161).length < 2 ^ (prefixWord ++ tailWord_1535161).sum := by decide
  have hdescent : baseEnd_1535161 < baseStart_1535161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535178 : List Nat := [3, 1, 2, 1, 3, 3, 1, 3, 2, 4]
def baseStart_1535178 : Nat := 118140960795 + 1535178 * 2 ^ 59
def prefixEnd_1535178 : Nat := 4983230072969 + 3 ^ 40 * 1535178 * 2
def baseEnd_1535178 : Nat := 262761401402699947571617

theorem tailTrace_1535178 : CollatzResearch.WordTrace tailWord_1535178 prefixEnd_1535178 262761401402699947571617 := by
  unfold tailWord_1535178
  simp only [CollatzResearch.WordTrace]
  refine ⟨13998135408079942093423547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37328361088213178915796125 13998135408079942093423547)
  ·
    refine ⟨20997203112119913140135321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13998135408079942093423547 20997203112119913140135321)
    ·
      refine ⟨15747902334089934855101491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20997203112119913140135321 15747902334089934855101491)
      ·
        refine ⟨23621853501134902282652237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15747902334089934855101491 23621853501134902282652237)
        ·
          refine ⟨8858195062925588355994589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23621853501134902282652237 8858195062925588355994589)
          ·
            refine ⟨3321823148597095633497971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8858195062925588355994589 3321823148597095633497971)
            ·
              refine ⟨4982734722895643450246957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3321823148597095633497971 4982734722895643450246957)
              ·
                refine ⟨1868525521085866293842609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4982734722895643450246957 1868525521085866293842609)
                ·
                  refine ⟨1401394140814399720381957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1868525521085866293842609 1401394140814399720381957)
                  ·
                    refine ⟨262761401402699947571617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1401394140814399720381957 262761401402699947571617)
                    ·
                      rfl

theorem cell23_1535178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_1535178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535178 prefixEnd_1535178 := by exact prefixLift 1535178
  have htrace : WordTrace (prefixWord ++ tailWord_1535178) baseStart_1535178 baseEnd_1535178 := by
    simpa [prefixWord, tailWord_1535178, baseEnd_1535178] using wordTrace_append hprefix tailTrace_1535178
  have hstable : (prefixWord ++ tailWord_1535178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535178).length < 2 ^ (prefixWord ++ tailWord_1535178).sum := by decide
  have hdescent : baseEnd_1535178 < baseStart_1535178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535201 : List Nat := [1, 2, 3, 1, 3, 2, 1, 1, 3, 3, 3]
def baseStart_1535201 : Nat := 118140960795 + 1535201 * 2 ^ 59
def prefixEnd_1535201 : Nat := 4983230072969 + 3 ^ 40 * 1535201 * 2
def baseEnd_1535201 : Nat := 788296014263153252727245

theorem tailTrace_1535201 : CollatzResearch.WordTrace tailWord_1535201 prefixEnd_1535201 788296014263153252727245 := by
  unfold tailWord_1535201
  simp only [CollatzResearch.WordTrace]
  refine ⟨55993380511236443301781457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37328920340824295534520971 55993380511236443301781457)
  ·
    refine ⟨41995035383427332476336093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55993380511236443301781457 41995035383427332476336093)
    ·
      refine ⟨15748138268785249678626035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41995035383427332476336093 15748138268785249678626035)
      ·
        refine ⟨23622207403177874517939053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15748138268785249678626035 23622207403177874517939053)
        ·
          refine ⟨8858327776191702944227145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23622207403177874517939053 8858327776191702944227145)
          ·
            refine ⟨6643745832143777208170359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8858327776191702944227145 6643745832143777208170359)
            ·
              refine ⟨9965618748215665812255539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6643745832143777208170359 9965618748215665812255539)
              ·
                refine ⟨14948428122323498718383309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9965618748215665812255539 14948428122323498718383309)
                ·
                  refine ⟨5605660545871312019393741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14948428122323498718383309 5605660545871312019393741)
                  ·
                    refine ⟨2102122704701742007272653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5605660545871312019393741 2102122704701742007272653)
                    ·
                      refine ⟨788296014263153252727245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2102122704701742007272653 788296014263153252727245)
                      ·
                        rfl

theorem cell23_1535201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_1535201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535201 prefixEnd_1535201 := by exact prefixLift 1535201
  have htrace : WordTrace (prefixWord ++ tailWord_1535201) baseStart_1535201 baseEnd_1535201 := by
    simpa [prefixWord, tailWord_1535201, baseEnd_1535201] using wordTrace_append hprefix tailTrace_1535201
  have hstable : (prefixWord ++ tailWord_1535201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535201).length < 2 ^ (prefixWord ++ tailWord_1535201).sum := by decide
  have hdescent : baseEnd_1535201 < baseStart_1535201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535205 : List Nat := [1, 3, 1, 4, 4, 1, 1, 1, 1, 1, 5]
def baseStart_1535205 : Nat := 118140960795 + 1535205 * 2 ^ 59
def prefixEnd_1535205 : Nat := 4983230072969 + 3 ^ 40 * 1535205 * 2
def baseEnd_1535205 : Nat := 788298068185771237077227

theorem tailTrace_1535205 : CollatzResearch.WordTrace tailWord_1535205 prefixEnd_1535205 788298068185771237077227 := by
  unfold tailWord_1535205
  simp only [CollatzResearch.WordTrace]
  refine ⟨55993526403221951984927069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37329017602147967989951379 55993526403221951984927069)
  ·
    refine ⟨20997572401208231994347651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55993526403221951984927069 20997572401208231994347651)
    ·
      refine ⟨31496358601812347991521477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20997572401208231994347651 31496358601812347991521477)
      ·
        refine ⟨5905567237839815248410277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31496358601812347991521477 5905567237839815248410277)
        ·
          refine ⟨1107293857094965359076927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5905567237839815248410277 1107293857094965359076927)
          ·
            refine ⟨1660940785642448038615391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1107293857094965359076927 1660940785642448038615391)
            ·
              refine ⟨2491411178463672057923087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1660940785642448038615391 2491411178463672057923087)
              ·
                refine ⟨3737116767695508086884631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2491411178463672057923087 3737116767695508086884631)
                ·
                  refine ⟨5605675151543262130326947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3737116767695508086884631 5605675151543262130326947)
                  ·
                    refine ⟨8408512727314893195490421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5605675151543262130326947 8408512727314893195490421)
                    ·
                      refine ⟨788298068185771237077227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8408512727314893195490421 788298068185771237077227)
                      ·
                        rfl

theorem cell23_1535205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_1535205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535205 prefixEnd_1535205 := by exact prefixLift 1535205
  have htrace : WordTrace (prefixWord ++ tailWord_1535205) baseStart_1535205 baseEnd_1535205 := by
    simpa [prefixWord, tailWord_1535205, baseEnd_1535205] using wordTrace_append hprefix tailTrace_1535205
  have hstable : (prefixWord ++ tailWord_1535205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535205).length < 2 ^ (prefixWord ++ tailWord_1535205).sum := by decide
  have hdescent : baseEnd_1535205 < baseStart_1535205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535219 : List Nat := [1, 1, 1, 2, 2, 7, 2, 2, 1, 2, 2]
def baseStart_1535219 : Nat := 118140960795 + 1535219 * 2 ^ 59
def prefixEnd_1535219 : Nat := 4983230072969 + 3 ^ 40 * 1535219 * 2
def baseEnd_1535219 : Nat := 788305256914934182302163

theorem tailTrace_1535219 : CollatzResearch.WordTrace tailWord_1535219 prefixEnd_1535219 788305256914934182302163 := by
  unfold tailWord_1535219
  simp only [CollatzResearch.WordTrace]
  refine ⟨55994037025171232375936711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37329358016780821583957807 55994037025171232375936711)
  ·
    refine ⟨83991055537756848563905067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55994037025171232375936711 83991055537756848563905067)
    ·
      refine ⟨125986583306635272845857601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83991055537756848563905067 125986583306635272845857601)
      ·
        refine ⟨94489937479976454634393201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125986583306635272845857601 94489937479976454634393201)
        ·
          refine ⟨70867453109982340975794901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94489937479976454634393201 70867453109982340975794901)
          ·
            refine ⟨1660955932265211116620193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 70867453109982340975794901 1660955932265211116620193)
            ·
              refine ⟨1245716949198908337465145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1660955932265211116620193 1245716949198908337465145)
              ·
                refine ⟨934287711899181253098859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1245716949198908337465145 934287711899181253098859)
                ·
                  refine ⟨1401431567848771879648289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 934287711899181253098859 1401431567848771879648289)
                  ·
                    refine ⟨1051073675886578909736217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1401431567848771879648289 1051073675886578909736217)
                    ·
                      refine ⟨788305256914934182302163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1051073675886578909736217 788305256914934182302163)
                      ·
                        rfl

theorem cell23_1535219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 2, 1, 2, 2].length) (baseStart_1535219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535219 prefixEnd_1535219 := by exact prefixLift 1535219
  have htrace : WordTrace (prefixWord ++ tailWord_1535219) baseStart_1535219 baseEnd_1535219 := by
    simpa [prefixWord, tailWord_1535219, baseEnd_1535219] using wordTrace_append hprefix tailTrace_1535219
  have hstable : (prefixWord ++ tailWord_1535219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535219).length < 2 ^ (prefixWord ++ tailWord_1535219).sum := by decide
  have hdescent : baseEnd_1535219 < baseStart_1535219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535281 : List Nat := [1, 2, 2, 3, 3, 1, 1, 3, 7]
def baseStart_1535281 : Nat := 118140960795 + 1535281 * 2 ^ 59
def prefixEnd_1535281 : Nat := 4983230072969 + 3 ^ 40 * 1535281 * 2
def baseEnd_1535281 : Nat := 87593010301723659969653

theorem tailTrace_1535281 : CollatzResearch.WordTrace tailWord_1535281 prefixEnd_1535281 87593010301723659969653 := by
  unfold tailWord_1535281
  simp only [CollatzResearch.WordTrace]
  refine ⟨55996298350946616964693697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37330865567297744643129131 55996298350946616964693697)
  ·
    refine ⟨41997223763209962723520273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55996298350946616964693697 41997223763209962723520273)
    ·
      refine ⟨31497917822407472042640205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41997223763209962723520273 31497917822407472042640205)
      ·
        refine ⟨11811719183402802015990077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31497917822407472042640205 11811719183402802015990077)
        ·
          refine ⟨4429394693776050755996279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11811719183402802015990077 4429394693776050755996279)
          ·
            refine ⟨6644092040664076133994419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4429394693776050755996279 6644092040664076133994419)
            ·
              refine ⟨9966138060996114200991629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6644092040664076133994419 9966138060996114200991629)
              ·
                refine ⟨3737301772873542825371861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9966138060996114200991629 3737301772873542825371861)
                ·
                  refine ⟨87593010301723659969653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3737301772873542825371861 87593010301723659969653)
                  ·
                    rfl

theorem cell23_1535281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 7].length) (baseStart_1535281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535281 prefixEnd_1535281 := by exact prefixLift 1535281
  have htrace : WordTrace (prefixWord ++ tailWord_1535281) baseStart_1535281 baseEnd_1535281 := by
    simpa [prefixWord, tailWord_1535281, baseEnd_1535281] using wordTrace_append hprefix tailTrace_1535281
  have hstable : (prefixWord ++ tailWord_1535281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535281).length < 2 ^ (prefixWord ++ tailWord_1535281).sum := by decide
  have hdescent : baseEnd_1535281 < baseStart_1535281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535286 : List Nat := [5, 1, 2, 3, 1, 1, 3, 1, 2, 1, 3]
def baseStart_1535286 : Nat := 118140960795 + 1535286 * 2 ^ 59
def prefixEnd_1535286 : Nat := 4983230072969 + 3 ^ 40 * 1535286 * 2
def baseEnd_1535286 : Nat := 788339660118785420164355

theorem tailTrace_1535286 : CollatzResearch.WordTrace tailWord_1535286 prefixEnd_1535286 788339660118785420164355 := by
  unfold tailWord_1535286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3499780044745531426164107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37330987143952335212417141 3499780044745531426164107)
  ·
    refine ⟨5249670067118297139246161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3499780044745531426164107 5249670067118297139246161)
    ·
      refine ⟨3937252550338722854434621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5249670067118297139246161 3937252550338722854434621)
      ·
        refine ⟨1476469706377021070412983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3937252550338722854434621 1476469706377021070412983)
        ·
          refine ⟨2214704559565531605619475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1476469706377021070412983 2214704559565531605619475)
          ·
            refine ⟨3322056839348297408429213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2214704559565531605619475 3322056839348297408429213)
            ·
              refine ⟨1245771314755611528160955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3322056839348297408429213 1245771314755611528160955)
              ·
                refine ⟨1868656972133417292241433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1245771314755611528160955 1868656972133417292241433)
                ·
                  refine ⟨1401492729100062969181075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1868656972133417292241433 1401492729100062969181075)
                  ·
                    refine ⟨2102239093650094453771613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1401492729100062969181075 2102239093650094453771613)
                    ·
                      refine ⟨788339660118785420164355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2102239093650094453771613 788339660118785420164355)
                      ·
                        rfl

theorem cell23_1535286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_1535286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535286 prefixEnd_1535286 := by exact prefixLift 1535286
  have htrace : WordTrace (prefixWord ++ tailWord_1535286) baseStart_1535286 baseEnd_1535286 := by
    simpa [prefixWord, tailWord_1535286, baseEnd_1535286] using wordTrace_append hprefix tailTrace_1535286
  have hstable : (prefixWord ++ tailWord_1535286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535286).length < 2 ^ (prefixWord ++ tailWord_1535286).sum := by decide
  have hdescent : baseEnd_1535286 < baseStart_1535286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535328 : List Nat := [2, 1, 1, 3, 4, 2, 1, 2, 2, 5]
def baseStart_1535328 : Nat := 118140960795 + 1535328 * 2 ^ 59
def prefixEnd_1535328 : Nat := 4983230072969 + 3 ^ 40 * 1535328 * 2
def baseEnd_1535328 : Nat := 262787075435424751946387

theorem tailTrace_1535328 : CollatzResearch.WordTrace tailWord_1535328 prefixEnd_1535328 262787075435424751946387 := by
  unfold tailWord_1535328
  simp only [CollatzResearch.WordTrace]
  refine ⟨27999006290888171995827319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37332008387850895994436425 27999006290888171995827319)
  ·
    refine ⟨41998509436332257993740979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27999006290888171995827319 41998509436332257993740979)
    ·
      refine ⟨62997764154498386990611469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41998509436332257993740979 62997764154498386990611469)
      ·
        refine ⟨23624161557936895121479301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62997764154498386990611469 23624161557936895121479301)
        ·
          refine ⟨4429530292113167835277369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23624161557936895121479301 4429530292113167835277369)
          ·
            refine ⟨3322147719084875876458027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4429530292113167835277369 3322147719084875876458027)
            ·
              refine ⟨4983221578627313814687041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3322147719084875876458027 4983221578627313814687041)
              ·
                refine ⟨3737416183970485361015281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4983221578627313814687041 3737416183970485361015281)
                ·
                  refine ⟨2803062137977864020761461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3737416183970485361015281 2803062137977864020761461)
                  ·
                    refine ⟨262787075435424751946387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2803062137977864020761461 262787075435424751946387)
                    ·
                      rfl

theorem cell23_1535328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 2, 5].length) (baseStart_1535328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535328 prefixEnd_1535328 := by exact prefixLift 1535328
  have htrace : WordTrace (prefixWord ++ tailWord_1535328) baseStart_1535328 baseEnd_1535328 := by
    simpa [prefixWord, tailWord_1535328, baseEnd_1535328] using wordTrace_append hprefix tailTrace_1535328
  have hstable : (prefixWord ++ tailWord_1535328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535328).length < 2 ^ (prefixWord ++ tailWord_1535328).sum := by decide
  have hdescent : baseEnd_1535328 < baseStart_1535328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535362 : List Nat := [3, 4, 2, 1, 1, 2, 2, 1, 2, 5]
def baseStart_1535362 : Nat := 118140960795 + 1535362 * 2 ^ 59
def prefixEnd_1535362 : Nat := 4983230072969 + 3 ^ 40 * 1535362 * 2
def baseEnd_1535362 : Nat := 262792894882842374271335

theorem tailTrace_1535362 : CollatzResearch.WordTrace tailWord_1535362 prefixEnd_1535362 262792894882842374271335 := by
  unfold tailWord_1535362
  simp only [CollatzResearch.WordTrace]
  refine ⟨13999813165913291949598085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37332835109102111865594893 13999813165913291949598085)
  ·
    refine ⟨2624964968608742240549641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13999813165913291949598085 2624964968608742240549641)
    ·
      refine ⟨1968723726456556680412231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2624964968608742240549641 1968723726456556680412231)
      ·
        refine ⟨2953085589684835020618347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1968723726456556680412231 2953085589684835020618347)
        ·
          refine ⟨4429628384527252530927521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2953085589684835020618347 4429628384527252530927521)
          ·
            refine ⟨3322221288395439398195641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4429628384527252530927521 3322221288395439398195641)
            ·
              refine ⟨2491665966296579548646731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3322221288395439398195641 2491665966296579548646731)
              ·
                refine ⟨3737498949444869322970097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2491665966296579548646731 3737498949444869322970097)
                ·
                  refine ⟨2803124212083651992227573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3737498949444869322970097 2803124212083651992227573)
                  ·
                    refine ⟨262792894882842374271335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2803124212083651992227573 262792894882842374271335)
                    ·
                      rfl

theorem cell23_1535362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_1535362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535362 prefixEnd_1535362 := by exact prefixLift 1535362
  have htrace : WordTrace (prefixWord ++ tailWord_1535362) baseStart_1535362 baseEnd_1535362 := by
    simpa [prefixWord, tailWord_1535362, baseEnd_1535362] using wordTrace_append hprefix tailTrace_1535362
  have hstable : (prefixWord ++ tailWord_1535362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535362).length < 2 ^ (prefixWord ++ tailWord_1535362).sum := by decide
  have hdescent : baseEnd_1535362 < baseStart_1535362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535405 : List Nat := [1, 5, 2, 2, 1, 1, 2, 3, 6]
def baseStart_1535405 : Nat := 118140960795 + 1535405 * 2 ^ 59
def prefixEnd_1535405 : Nat := 4983230072969 + 3 ^ 40 * 1535405 * 2
def baseEnd_1535405 : Nat := 87600084924074494952923

theorem tailTrace_1535405 : CollatzResearch.WordTrace tailWord_1535405 prefixEnd_1535405 87600084924074494952923 := by
  unfold tailWord_1535405
  simp only [CollatzResearch.WordTrace]
  refine ⟨56000821002497386142207669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37333880668331590761471779 56000821002497386142207669)
  ·
    refine ⟨5250076968984129950831969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56000821002497386142207669 5250076968984129950831969)
    ·
      refine ⟨3937557726738097463123977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5250076968984129950831969 3937557726738097463123977)
      ·
        refine ⟨2953168295053573097342983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3937557726738097463123977 2953168295053573097342983)
        ·
          refine ⟨4429752442580359646014475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2953168295053573097342983 4429752442580359646014475)
          ·
            refine ⟨6644628663870539469021713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4429752442580359646014475 6644628663870539469021713)
            ·
              refine ⟨4983471497902904601766285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6644628663870539469021713 4983471497902904601766285)
              ·
                refine ⟨1868801811713589225662357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4983471497902904601766285 1868801811713589225662357)
                ·
                  refine ⟨87600084924074494952923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1868801811713589225662357 87600084924074494952923)
                  ·
                    rfl

theorem cell23_1535405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_1535405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535405 prefixEnd_1535405 := by exact prefixLift 1535405
  have htrace : WordTrace (prefixWord ++ tailWord_1535405) baseStart_1535405 baseEnd_1535405 := by
    simpa [prefixWord, tailWord_1535405, baseEnd_1535405] using wordTrace_append hprefix tailTrace_1535405
  have hstable : (prefixWord ++ tailWord_1535405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535405).length < 2 ^ (prefixWord ++ tailWord_1535405).sum := by decide
  have hdescent : baseEnd_1535405 < baseStart_1535405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535415 : List Nat := [1, 1, 3, 1, 3, 2, 3, 2, 3, 1, 3]
def baseStart_1535415 : Nat := 118140960795 + 1535415 * 2 ^ 59
def prefixEnd_1535415 : Nat := 4983230072969 + 3 ^ 40 * 1535415 * 2
def baseEnd_1535415 : Nat := 788405899123215415451261

theorem tailTrace_1535415 : CollatzResearch.WordTrace tailWord_1535415 prefixEnd_1535415 788405899123215415451261 := by
  unfold tailWord_1535415
  simp only [CollatzResearch.WordTrace]
  refine ⟨56001185732461157850071699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37334123821640771900047799 56001185732461157850071699)
  ·
    refine ⟨84001778598691736775107549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56001185732461157850071699 84001778598691736775107549)
    ·
      refine ⟨31500666974509401290665331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84001778598691736775107549 31500666974509401290665331)
      ·
        refine ⟨47251000461764101935997997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31500666974509401290665331 47251000461764101935997997)
        ·
          refine ⟨17719125173161538225999249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47251000461764101935997997 17719125173161538225999249)
          ·
            refine ⟨13289343879871153669499437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17719125173161538225999249 13289343879871153669499437)
            ·
              refine ⟨4983503954951682626062289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13289343879871153669499437 4983503954951682626062289)
              ·
                refine ⟨3737627966213761969546717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4983503954951682626062289 3737627966213761969546717)
                ·
                  refine ⟨1401610487330160738580019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3737627966213761969546717 1401610487330160738580019)
                  ·
                    refine ⟨2102415730995241107870029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1401610487330160738580019 2102415730995241107870029)
                    ·
                      refine ⟨788405899123215415451261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2102415730995241107870029 788405899123215415451261)
                      ·
                        rfl

theorem cell23_1535415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 3, 1, 3].length) (baseStart_1535415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535415 prefixEnd_1535415 := by exact prefixLift 1535415
  have htrace : WordTrace (prefixWord ++ tailWord_1535415) baseStart_1535415 baseEnd_1535415 := by
    simpa [prefixWord, tailWord_1535415, baseEnd_1535415] using wordTrace_append hprefix tailTrace_1535415
  have hstable : (prefixWord ++ tailWord_1535415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535415).length < 2 ^ (prefixWord ++ tailWord_1535415).sum := by decide
  have hdescent : baseEnd_1535415 < baseStart_1535415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535435 : List Nat := [1, 1, 1, 1, 3, 3, 6, 1, 1, 5]
def baseStart_1535435 : Nat := 118140960795 + 1535435 * 2 ^ 59
def prefixEnd_1535435 : Nat := 4983230072969 + 3 ^ 40 * 1535435 * 2
def baseEnd_1535435 : Nat := 262805389578768445733723

theorem tailTrace_1535435 : CollatzResearch.WordTrace tailWord_1535435 prefixEnd_1535435 262805389578768445733723 := by
  unfold tailWord_1535435
  simp only [CollatzResearch.WordTrace]
  refine ⟨56001915192388701265799759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37334610128259134177199839 56001915192388701265799759)
  ·
    refine ⟨84002872788583051898699639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56001915192388701265799759 84002872788583051898699639)
    ·
      refine ⟨126004309182874577848049459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84002872788583051898699639 126004309182874577848049459)
      ·
        refine ⟨189006463774311866772074189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126004309182874577848049459 189006463774311866772074189)
        ·
          refine ⟨70877423915366950039527821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189006463774311866772074189 70877423915366950039527821)
          ·
            refine ⟨26579033968262606264822933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70877423915366950039527821 26579033968262606264822933)
            ·
              refine ⟨1245892217262309668663575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26579033968262606264822933 1245892217262309668663575)
              ·
                refine ⟨1868838325893464502995363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1245892217262309668663575 1868838325893464502995363)
                ·
                  refine ⟨2803257488840196754493045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1868838325893464502995363 2803257488840196754493045)
                  ·
                    refine ⟨262805389578768445733723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2803257488840196754493045 262805389578768445733723)
                    ·
                      rfl

theorem cell23_1535435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 1, 5].length) (baseStart_1535435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535435 prefixEnd_1535435 := by exact prefixLift 1535435
  have htrace : WordTrace (prefixWord ++ tailWord_1535435) baseStart_1535435 baseEnd_1535435 := by
    simpa [prefixWord, tailWord_1535435, baseEnd_1535435] using wordTrace_append hprefix tailTrace_1535435
  have hstable : (prefixWord ++ tailWord_1535435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535435).length < 2 ^ (prefixWord ++ tailWord_1535435).sum := by decide
  have hdescent : baseEnd_1535435 < baseStart_1535435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535451 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 6]
def baseStart_1535451 : Nat := 118140960795 + 1535451 * 2 ^ 59
def prefixEnd_1535451 : Nat := 4983230072969 + 3 ^ 40 * 1535451 * 2
def baseEnd_1535451 : Nat := 788424384426777274601095

theorem tailTrace_1535451 : CollatzResearch.WordTrace tailWord_1535451 prefixEnd_1535451 788424384426777274601095 := by
  unfold tailWord_1535451
  simp only [CollatzResearch.WordTrace]
  refine ⟨56002498760330735998382207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37334999173553823998921471 56002498760330735998382207)
  ·
    refine ⟨84003748140496103997573311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56002498760330735998382207 84003748140496103997573311)
    ·
      refine ⟨126005622210744155996359967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84003748140496103997573311 126005622210744155996359967)
      ·
        refine ⟨189008433316116233994539951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126005622210744155996359967 189008433316116233994539951)
        ·
          refine ⟨283512649974174350991809927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189008433316116233994539951 283512649974174350991809927)
          ·
            refine ⟨425268974961261526487714891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283512649974174350991809927 425268974961261526487714891)
            ·
              refine ⟨637903462441892289731572337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 425268974961261526487714891 637903462441892289731572337)
              ·
                refine ⟨478427596831419217298679253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 637903462441892289731572337 478427596831419217298679253)
                ·
                  refine ⟨11213146800736387905437795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 478427596831419217298679253 11213146800736387905437795)
                  ·
                    refine ⟨16819720201104581858156693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11213146800736387905437795 16819720201104581858156693)
                    ·
                      refine ⟨788424384426777274601095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16819720201104581858156693 788424384426777274601095)
                      ·
                        rfl

theorem cell23_1535451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 6].length) (baseStart_1535451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535451 prefixEnd_1535451 := by exact prefixLift 1535451
  have htrace : WordTrace (prefixWord ++ tailWord_1535451) baseStart_1535451 baseEnd_1535451 := by
    simpa [prefixWord, tailWord_1535451, baseEnd_1535451] using wordTrace_append hprefix tailTrace_1535451
  have hstable : (prefixWord ++ tailWord_1535451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535451).length < 2 ^ (prefixWord ++ tailWord_1535451).sum := by decide
  have hdescent : baseEnd_1535451 < baseStart_1535451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535468 : List Nat := [2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 4]
def baseStart_1535468 : Nat := 118140960795 + 1535468 * 2 ^ 59
def prefixEnd_1535468 : Nat := 4983230072969 + 3 ^ 40 * 1535468 * 2
def baseEnd_1535468 : Nat := 788433113597903708088517

theorem tailTrace_1535468 : CollatzResearch.WordTrace tailWord_1535468 prefixEnd_1535468 788433113597903708088517 := by
  unfold tailWord_1535468
  simp only [CollatzResearch.WordTrace]
  refine ⟨28001559400634573950875529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37335412534179431934500705 28001559400634573950875529)
  ·
    refine ⟨21001169550475930463156647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28001559400634573950875529 21001169550475930463156647)
    ·
      refine ⟨31501754325713895694734971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21001169550475930463156647 31501754325713895694734971)
      ·
        refine ⟨47252631488570843542102457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31501754325713895694734971 47252631488570843542102457)
        ·
          refine ⟨35439473616428132656576843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47252631488570843542102457 35439473616428132656576843)
          ·
            refine ⟨53159210424642198984865265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35439473616428132656576843 53159210424642198984865265)
            ·
              refine ⟨39869407818481649238648949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53159210424642198984865265 39869407818481649238648949)
              ·
                refine ⟨3737756982982654616123339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39869407818481649238648949 3737756982982654616123339)
                ·
                  refine ⟨5606635474473981924185009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3737756982982654616123339 5606635474473981924185009)
                  ·
                    refine ⟨4204976605855486443138757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5606635474473981924185009 4204976605855486443138757)
                    ·
                      refine ⟨788433113597903708088517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4204976605855486443138757 788433113597903708088517)
                      ·
                        rfl

theorem cell23_1535468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 4].length) (baseStart_1535468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535468 prefixEnd_1535468 := by exact prefixLift 1535468
  have htrace : WordTrace (prefixWord ++ tailWord_1535468) baseStart_1535468 baseEnd_1535468 := by
    simpa [prefixWord, tailWord_1535468, baseEnd_1535468] using wordTrace_append hprefix tailTrace_1535468
  have hstable : (prefixWord ++ tailWord_1535468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535468).length < 2 ^ (prefixWord ++ tailWord_1535468).sum := by decide
  have hdescent : baseEnd_1535468 < baseStart_1535468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535472 : List Nat := [2, 1, 1, 1, 3, 4, 2, 2, 3, 2, 2]
def baseStart_1535472 : Nat := 118140960795 + 1535472 * 2 ^ 59
def prefixEnd_1535472 : Nat := 4983230072969 + 3 ^ 40 * 1535472 * 2
def baseEnd_1535472 : Nat := 788435167520521692438499

theorem tailTrace_1535472 : CollatzResearch.WordTrace tailWord_1535472 prefixEnd_1535472 788435167520521692438499 := by
  unfold tailWord_1535472
  simp only [CollatzResearch.WordTrace]
  refine ⟨28001632346627328292448335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37335509795503104389931113 28001632346627328292448335)
  ·
    refine ⟨42002448519940992438672503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28001632346627328292448335 42002448519940992438672503)
    ·
      refine ⟨63003672779911488658008755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42002448519940992438672503 63003672779911488658008755)
      ·
        refine ⟨94505509169867232987013133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63003672779911488658008755 94505509169867232987013133)
        ·
          refine ⟨35439565938700212370129925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94505509169867232987013133 35439565938700212370129925)
          ·
            refine ⟨6644918613506289819399361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35439565938700212370129925 6644918613506289819399361)
            ·
              refine ⟨4983688960129717364549521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6644918613506289819399361 4983688960129717364549521)
              ·
                refine ⟨3737766720097288023412141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4983688960129717364549521 3737766720097288023412141)
                ·
                  refine ⟨1401662520036483008779553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3737766720097288023412141 1401662520036483008779553)
                  ·
                    refine ⟨1051246890027362256584665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1401662520036483008779553 1051246890027362256584665)
                    ·
                      refine ⟨788435167520521692438499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1051246890027362256584665 788435167520521692438499)
                      ·
                        rfl

theorem cell23_1535472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 3, 2, 2].length) (baseStart_1535472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535472 prefixEnd_1535472 := by exact prefixLift 1535472
  have htrace : WordTrace (prefixWord ++ tailWord_1535472) baseStart_1535472 baseEnd_1535472 := by
    simpa [prefixWord, tailWord_1535472, baseEnd_1535472] using wordTrace_append hprefix tailTrace_1535472
  have hstable : (prefixWord ++ tailWord_1535472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535472).length < 2 ^ (prefixWord ++ tailWord_1535472).sum := by decide
  have hdescent : baseEnd_1535472 < baseStart_1535472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535492 : List Nat := [2, 3, 2, 3, 2, 1, 2, 1, 1, 1, 5]
def baseStart_1535492 : Nat := 118140960795 + 1535492 * 2 ^ 59
def prefixEnd_1535492 : Nat := 4983230072969 + 3 ^ 40 * 1535492 * 2
def baseEnd_1535492 : Nat := 788445437133611614188407

theorem tailTrace_1535492 : CollatzResearch.WordTrace tailWord_1535492 prefixEnd_1535492 788445437133611614188407 := by
  unfold tailWord_1535492
  simp only [CollatzResearch.WordTrace]
  refine ⟨28001997076591100000312365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37335996102121466667083153 28001997076591100000312365)
  ·
    refine ⟨10500748903721662500117137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28001997076591100000312365 10500748903721662500117137)
    ·
      refine ⟨7875561677791246875087853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10500748903721662500117137 7875561677791246875087853)
      ·
        refine ⟨2953335629171717578157945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7875561677791246875087853 2953335629171717578157945)
        ·
          refine ⟨2215001721878788183618459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2953335629171717578157945 2215001721878788183618459)
          ·
            refine ⟨3322502582818182275427689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2215001721878788183618459 3322502582818182275427689)
            ·
              refine ⟨2491876937113636706570767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3322502582818182275427689 2491876937113636706570767)
              ·
                refine ⟨3737815405670455059856151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2491876937113636706570767 3737815405670455059856151)
                ·
                  refine ⟨5606723108505682589784227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3737815405670455059856151 5606723108505682589784227)
                  ·
                    refine ⟨8410084662758523884676341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5606723108505682589784227 8410084662758523884676341)
                    ·
                      refine ⟨788445437133611614188407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8410084662758523884676341 788445437133611614188407)
                      ·
                        rfl

theorem cell23_1535492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_1535492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535492 prefixEnd_1535492 := by exact prefixLift 1535492
  have htrace : WordTrace (prefixWord ++ tailWord_1535492) baseStart_1535492 baseEnd_1535492 := by
    simpa [prefixWord, tailWord_1535492, baseEnd_1535492] using wordTrace_append hprefix tailTrace_1535492
  have hstable : (prefixWord ++ tailWord_1535492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535492).length < 2 ^ (prefixWord ++ tailWord_1535492).sum := by decide
  have hdescent : baseEnd_1535492 < baseStart_1535492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535505 : List Nat := [1, 2, 2, 1, 1, 2, 3, 3, 4, 1, 3]
def baseStart_1535505 : Nat := 118140960795 + 1535505 * 2 ^ 59
def prefixEnd_1535505 : Nat := 4983230072969 + 3 ^ 40 * 1535505 * 2
def baseEnd_1535505 : Nat := 788452112382120063325847

theorem tailTrace_1535505 : CollatzResearch.WordTrace tailWord_1535505 prefixEnd_1535505 788452112382120063325847 := by
  unfold tailWord_1535505
  simp only [CollatzResearch.WordTrace]
  refine ⟨56004468302135103220847969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37336312201423402147231979 56004468302135103220847969)
  ·
    refine ⟨42003351226601327415635977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56004468302135103220847969 42003351226601327415635977)
    ·
      refine ⟨31502513419950995561726983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42003351226601327415635977 31502513419950995561726983)
      ·
        refine ⟨47253770129926493342590475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31502513419950995561726983 47253770129926493342590475)
        ·
          refine ⟨70880655194889740013885713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47253770129926493342590475 70880655194889740013885713)
          ·
            refine ⟨53160491396167305010414285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70880655194889740013885713 53160491396167305010414285)
            ·
              refine ⟨19935184273562739378905357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53160491396167305010414285 19935184273562739378905357)
              ·
                refine ⟨7475694102586027267089509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19935184273562739378905357 7475694102586027267089509)
                ·
                  refine ⟨1401692644234880112579283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7475694102586027267089509 1401692644234880112579283)
                  ·
                    refine ⟨2102538966352320168868925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1401692644234880112579283 2102538966352320168868925)
                    ·
                      refine ⟨788452112382120063325847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2102538966352320168868925 788452112382120063325847)
                      ·
                        rfl

theorem cell23_1535505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 4, 1, 3].length) (baseStart_1535505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535505 prefixEnd_1535505 := by exact prefixLift 1535505
  have htrace : WordTrace (prefixWord ++ tailWord_1535505) baseStart_1535505 baseEnd_1535505 := by
    simpa [prefixWord, tailWord_1535505, baseEnd_1535505] using wordTrace_append hprefix tailTrace_1535505
  have hstable : (prefixWord ++ tailWord_1535505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535505).length < 2 ^ (prefixWord ++ tailWord_1535505).sum := by decide
  have hdescent : baseEnd_1535505 < baseStart_1535505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535538 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 4, 6]
def baseStart_1535538 : Nat := 118140960795 + 1535538 * 2 ^ 59
def prefixEnd_1535538 : Nat := 4983230072969 + 3 ^ 40 * 1535538 * 2
def baseEnd_1535538 : Nat := 262823019081239478071065

theorem tailTrace_1535538 : CollatzResearch.WordTrace tailWord_1535538 prefixEnd_1535538 262823019081239478071065 := by
  unfold tailWord_1535538
  simp only [CollatzResearch.WordTrace]
  refine ⟨14001417977753887464199817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37337114607343699904532845 14001417977753887464199817)
  ·
    refine ⟨10501063483315415598149863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14001417977753887464199817 10501063483315415598149863)
    ·
      refine ⟨15751595224973123397224795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10501063483315415598149863 15751595224973123397224795)
      ·
        refine ⟨23627392837459685095837193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15751595224973123397224795 23627392837459685095837193)
        ·
          refine ⟨17720544628094763821877895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23627392837459685095837193 17720544628094763821877895)
          ·
            refine ⟨26580816942142145732816843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17720544628094763821877895 26580816942142145732816843)
            ·
              refine ⟨39871225413213218599225265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26580816942142145732816843 39871225413213218599225265)
              ·
                refine ⟨29903419059909913949418949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39871225413213218599225265 29903419059909913949418949)
                ·
                  refine ⟨5606891073733108865516053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29903419059909913949418949 5606891073733108865516053)
                  ·
                    refine ⟨262823019081239478071065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5606891073733108865516053 262823019081239478071065)
                    ·
                      rfl

theorem cell23_1535538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_1535538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535538 prefixEnd_1535538 := by exact prefixLift 1535538
  have htrace : WordTrace (prefixWord ++ tailWord_1535538) baseStart_1535538 baseEnd_1535538 := by
    simpa [prefixWord, tailWord_1535538, baseEnd_1535538] using wordTrace_append hprefix tailTrace_1535538
  have hstable : (prefixWord ++ tailWord_1535538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535538).length < 2 ^ (prefixWord ++ tailWord_1535538).sum := by decide
  have hdescent : baseEnd_1535538 < baseStart_1535538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535568 : List Nat := [2, 1, 1, 1, 1, 3, 4, 3, 7]
def baseStart_1535568 : Nat := 118140960795 + 1535568 * 2 ^ 59
def prefixEnd_1535568 : Nat := 4983230072969 + 3 ^ 40 * 1535568 * 2
def baseEnd_1535568 : Nat := 87609384629261479648673

theorem tailTrace_1535568 : CollatzResearch.WordTrace tailWord_1535568 prefixEnd_1535568 87609384629261479648673 := by
  unfold tailWord_1535568
  simp only [CollatzResearch.WordTrace]
  refine ⟨28003383050453432490195679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37337844067271243320260905 28003383050453432490195679)
  ·
    refine ⟨42005074575680148735293519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28003383050453432490195679 42005074575680148735293519)
    ·
      refine ⟨63007611863520223102940279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42005074575680148735293519 63007611863520223102940279)
      ·
        refine ⟨94511417795280334654410419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63007611863520223102940279 94511417795280334654410419)
        ·
          refine ⟨141767126692920501981615629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94511417795280334654410419 141767126692920501981615629)
          ·
            refine ⟨53162672509845188243105861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141767126692920501981615629 53162672509845188243105861)
            ·
              refine ⟨9968001095595972795582349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53162672509845188243105861 9968001095595972795582349)
              ·
                refine ⟨3738000410848489798343381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9968001095595972795582349 3738000410848489798343381)
                ·
                  refine ⟨87609384629261479648673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3738000410848489798343381 87609384629261479648673)
                  ·
                    rfl

theorem cell23_1535568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 7].length) (baseStart_1535568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535568 prefixEnd_1535568 := by exact prefixLift 1535568
  have htrace : WordTrace (prefixWord ++ tailWord_1535568) baseStart_1535568 baseEnd_1535568 := by
    simpa [prefixWord, tailWord_1535568, baseEnd_1535568] using wordTrace_append hprefix tailTrace_1535568
  have hstable : (prefixWord ++ tailWord_1535568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535568).length < 2 ^ (prefixWord ++ tailWord_1535568).sum := by decide
  have hdescent : baseEnd_1535568 < baseStart_1535568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535575 : List Nat := [1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 4]
def baseStart_1535575 : Nat := 118140960795 + 1535575 * 2 ^ 59
def prefixEnd_1535575 : Nat := 4983230072969 + 3 ^ 40 * 1535575 * 2
def baseEnd_1535575 : Nat := 788488056027934789450525

theorem tailTrace_1535575 : CollatzResearch.WordTrace tailWord_1535575 prefixEnd_1535575 788488056027934789450525 := by
  unfold tailWord_1535575
  simp only [CollatzResearch.WordTrace]
  refine ⟨56007021411881505175896179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37338014274587670117264119 56007021411881505175896179)
  ·
    refine ⟨84010532117822257763844269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56007021411881505175896179 84010532117822257763844269)
    ·
      refine ⟨31503949544183346661441601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84010532117822257763844269 31503949544183346661441601)
      ·
        refine ⟨23627962158137509996081201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31503949544183346661441601 23627962158137509996081201)
        ·
          refine ⟨17720971618603132497060901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23627962158137509996081201 17720971618603132497060901)
          ·
            refine ⟨3322682178488087343198919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17720971618603132497060901 3322682178488087343198919)
            ·
              refine ⟨4984023267732131014798379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3322682178488087343198919 4984023267732131014798379)
              ·
                refine ⟨7476034901598196522197569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4984023267732131014798379 7476034901598196522197569)
                ·
                  refine ⟨5607026176198647391648177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7476034901598196522197569 5607026176198647391648177)
                  ·
                    refine ⟨4205269632148985543736133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5607026176198647391648177 4205269632148985543736133)
                    ·
                      refine ⟨788488056027934789450525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4205269632148985543736133 788488056027934789450525)
                      ·
                        rfl

theorem cell23_1535575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_1535575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535575 prefixEnd_1535575 := by exact prefixLift 1535575
  have htrace : WordTrace (prefixWord ++ tailWord_1535575) baseStart_1535575 baseEnd_1535575 := by
    simpa [prefixWord, tailWord_1535575, baseEnd_1535575] using wordTrace_append hprefix tailTrace_1535575
  have hstable : (prefixWord ++ tailWord_1535575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535575).length < 2 ^ (prefixWord ++ tailWord_1535575).sum := by decide
  have hdescent : baseEnd_1535575 < baseStart_1535575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535602 : List Nat := [3, 2, 1, 2, 3, 1, 1, 5, 5]
def baseStart_1535602 : Nat := 118140960795 + 1535602 * 2 ^ 59
def prefixEnd_1535602 : Nat := 4983230072969 + 3 ^ 40 * 1535602 * 2
def baseEnd_1535602 : Nat := 87611324445067353756989

theorem tailTrace_1535602 : CollatzResearch.WordTrace tailWord_1535602 prefixEnd_1535602 87611324445067353756989 := by
  unfold tailWord_1535602
  simp only [CollatzResearch.WordTrace]
  refine ⟨14002001545695922196782265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37338670788522459191419373 14002001545695922196782265)
  ·
    refine ⟨10501501159271941647586699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14002001545695922196782265 10501501159271941647586699)
    ·
      refine ⟨15752251738907912471380049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10501501159271941647586699 15752251738907912471380049)
      ·
        refine ⟨11814188804180934353535037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15752251738907912471380049 11814188804180934353535037)
        ·
          refine ⟨4430320801567850382575639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11814188804180934353535037 4430320801567850382575639)
          ·
            refine ⟨6645481202351775573863459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4430320801567850382575639 6645481202351775573863459)
            ·
              refine ⟨9968221803527663360795189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6645481202351775573863459 9968221803527663360795189)
              ·
                refine ⟨934520794080718440074549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9968221803527663360795189 934520794080718440074549)
                ·
                  refine ⟨87611324445067353756989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 934520794080718440074549 87611324445067353756989)
                  ·
                    rfl

theorem cell23_1535602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 5, 5].length) (baseStart_1535602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535602 prefixEnd_1535602 := by exact prefixLift 1535602
  have htrace : WordTrace (prefixWord ++ tailWord_1535602) baseStart_1535602 baseEnd_1535602 := by
    simpa [prefixWord, tailWord_1535602, baseEnd_1535602] using wordTrace_append hprefix tailTrace_1535602
  have hstable : (prefixWord ++ tailWord_1535602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535602).length < 2 ^ (prefixWord ++ tailWord_1535602).sum := by decide
  have hdescent : baseEnd_1535602 < baseStart_1535602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535669 : List Nat := [1, 3, 3, 3, 2, 1, 1, 2, 2, 1, 4]
def baseStart_1535669 : Nat := 118140960795 + 1535669 * 2 ^ 59
def prefixEnd_1535669 : Nat := 4983230072969 + 3 ^ 40 * 1535669 * 2
def baseEnd_1535669 : Nat := 788536323209457421675093

theorem tailTrace_1535669 : CollatzResearch.WordTrace tailWord_1535669 prefixEnd_1535669 788536323209457421675093 := by
  unfold tailWord_1535669
  simp only [CollatzResearch.WordTrace]
  refine ⟨56010449873540959229818061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37340299915693972819878707 56010449873540959229818061)
  ·
    refine ⟨21003918702577859711181773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56010449873540959229818061 21003918702577859711181773)
    ·
      refine ⟨7876469513466697391693165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21003918702577859711181773 7876469513466697391693165)
      ·
        refine ⟨2953676067550011521884937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7876469513466697391693165 2953676067550011521884937)
        ·
          refine ⟨2215257050662508641413703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2953676067550011521884937 2215257050662508641413703)
          ·
            refine ⟨3322885575993762962120555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2215257050662508641413703 3322885575993762962120555)
            ·
              refine ⟨4984328363990644443180833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3322885575993762962120555 4984328363990644443180833)
              ·
                refine ⟨3738246272992983332385625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4984328363990644443180833 3738246272992983332385625)
                ·
                  refine ⟨2803684704744737499289219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3738246272992983332385625 2803684704744737499289219)
                  ·
                    refine ⟨4205527057117106248933829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2803684704744737499289219 4205527057117106248933829)
                    ·
                      refine ⟨788536323209457421675093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4205527057117106248933829 788536323209457421675093)
                      ·
                        rfl

theorem cell23_1535669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_1535669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535669 prefixEnd_1535669 := by exact prefixLift 1535669
  have htrace : WordTrace (prefixWord ++ tailWord_1535669) baseStart_1535669 baseEnd_1535669 := by
    simpa [prefixWord, tailWord_1535669, baseEnd_1535669] using wordTrace_append hprefix tailTrace_1535669
  have hstable : (prefixWord ++ tailWord_1535669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535669).length < 2 ^ (prefixWord ++ tailWord_1535669).sum := by decide
  have hdescent : baseEnd_1535669 < baseStart_1535669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535712 : List Nat := [2, 1, 1, 3, 1, 2, 2, 3, 1, 5, 2]
def baseStart_1535712 : Nat := 118140960795 + 1535712 * 2 ^ 59
def prefixEnd_1535712 : Nat := 4983230072969 + 3 ^ 40 * 1535712 * 2
def baseEnd_1535712 : Nat := 788558402877600753437395

theorem tailTrace_1535712 : CollatzResearch.WordTrace tailWord_1535712 prefixEnd_1535712 788558402877600753437395 := by
  unfold tailWord_1535712
  simp only [CollatzResearch.WordTrace]
  refine ⟨28006009106192588786816695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37341345474923451715755593 28006009106192588786816695)
  ·
    refine ⟨42009013659288883180225043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28006009106192588786816695 42009013659288883180225043)
    ·
      refine ⟨63013520488933324770337565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42009013659288883180225043 63013520488933324770337565)
      ·
        refine ⟨23630070183349996788876587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63013520488933324770337565 23630070183349996788876587)
        ·
          refine ⟨35445105275024995183314881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23630070183349996788876587 35445105275024995183314881)
          ·
            refine ⟨26583828956268746387486161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35445105275024995183314881 26583828956268746387486161)
            ·
              refine ⟨19937871717201559790614621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26583828956268746387486161 19937871717201559790614621)
              ·
                refine ⟨7476701893950584921480483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19937871717201559790614621 7476701893950584921480483)
                ·
                  refine ⟨11215052840925877382220725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7476701893950584921480483 11215052840925877382220725)
                  ·
                    refine ⟨1051411203836801004583193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11215052840925877382220725 1051411203836801004583193)
                    ·
                      refine ⟨788558402877600753437395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1051411203836801004583193 788558402877600753437395)
                      ·
                        rfl

theorem cell23_1535712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 1, 5, 2].length) (baseStart_1535712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535712 prefixEnd_1535712 := by exact prefixLift 1535712
  have htrace : WordTrace (prefixWord ++ tailWord_1535712) baseStart_1535712 baseEnd_1535712 := by
    simpa [prefixWord, tailWord_1535712, baseEnd_1535712] using wordTrace_append hprefix tailTrace_1535712
  have hstable : (prefixWord ++ tailWord_1535712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535712).length < 2 ^ (prefixWord ++ tailWord_1535712).sum := by decide
  have hdescent : baseEnd_1535712 < baseStart_1535712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535722 : List Nat := [3, 1, 3, 1, 1, 1, 2, 5, 1, 5]
def baseStart_1535722 : Nat := 118140960795 + 1535722 * 2 ^ 59
def prefixEnd_1535722 : Nat := 4983230072969 + 3 ^ 40 * 1535722 * 2
def baseEnd_1535722 : Nat := 262854512561381904770783

theorem tailTrace_1535722 : CollatzResearch.WordTrace tailWord_1535722 prefixEnd_1535722 262854512561381904770783 := by
  unfold tailWord_1535722
  simp only [CollatzResearch.WordTrace]
  refine ⟨14003095735587237320374355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37341588628232632854331613 14003095735587237320374355)
  ·
    refine ⟨21004643603380855980561533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14003095735587237320374355 21004643603380855980561533)
    ·
      refine ⟨7876741351267820992710575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21004643603380855980561533 7876741351267820992710575)
      ·
        refine ⟨11815112026901731489065863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7876741351267820992710575 11815112026901731489065863)
        ·
          refine ⟨17722668040352597233598795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11815112026901731489065863 17722668040352597233598795)
          ·
            refine ⟨26584002060528895850398193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17722668040352597233598795 26584002060528895850398193)
            ·
              refine ⟨19938001545396671887798645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26584002060528895850398193 19938001545396671887798645)
              ·
                refine ⟨1869187644880937989481123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19938001545396671887798645 1869187644880937989481123)
                ·
                  refine ⟨2803781467321406984221685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1869187644880937989481123 2803781467321406984221685)
                  ·
                    refine ⟨262854512561381904770783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2803781467321406984221685 262854512561381904770783)
                    ·
                      rfl

theorem cell23_1535722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_1535722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535722 prefixEnd_1535722 := by exact prefixLift 1535722
  have htrace : WordTrace (prefixWord ++ tailWord_1535722) baseStart_1535722 baseEnd_1535722 := by
    simpa [prefixWord, tailWord_1535722, baseEnd_1535722] using wordTrace_append hprefix tailTrace_1535722
  have hstable : (prefixWord ++ tailWord_1535722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535722).length < 2 ^ (prefixWord ++ tailWord_1535722).sum := by decide
  have hdescent : baseEnd_1535722 < baseStart_1535722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535729 : List Nat := [1, 2, 2, 2, 2, 3, 2, 2, 2, 3, 2]
def baseStart_1535729 : Nat := 118140960795 + 1535729 * 2 ^ 59
def prefixEnd_1535729 : Nat := 4983230072969 + 3 ^ 40 * 1535729 * 2
def baseEnd_1535729 : Nat := 788567132048727186924817

theorem tailTrace_1535729 : CollatzResearch.WordTrace tailWord_1535729 prefixEnd_1535729 788567132048727186924817 := by
  unfold tailWord_1535729
  simp only [CollatzResearch.WordTrace]
  refine ⟨56012638253323589477002241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37341758835549059651334827 56012638253323589477002241)
  ·
    refine ⟨42009478689992692107751681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56012638253323589477002241 42009478689992692107751681)
    ·
      refine ⟨31507109017494519080813761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42009478689992692107751681 31507109017494519080813761)
      ·
        refine ⟨23630331763120889310610321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31507109017494519080813761 23630331763120889310610321)
        ·
          refine ⟨17722748822340666982957741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23630331763120889310610321 17722748822340666982957741)
          ·
            refine ⟨6646030808377750118609153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17722748822340666982957741 6646030808377750118609153)
            ·
              refine ⟨4984523106283312588956865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6646030808377750118609153 4984523106283312588956865)
              ·
                refine ⟨3738392329712484441717649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4984523106283312588956865 3738392329712484441717649)
                ·
                  refine ⟨2803794247284363331288237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3738392329712484441717649 2803794247284363331288237)
                  ·
                    refine ⟨1051422842731636249233089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2803794247284363331288237 1051422842731636249233089)
                    ·
                      refine ⟨788567132048727186924817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1051422842731636249233089 788567132048727186924817)
                      ·
                        rfl

theorem cell23_1535729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 3, 2].length) (baseStart_1535729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535729 prefixEnd_1535729 := by exact prefixLift 1535729
  have htrace : WordTrace (prefixWord ++ tailWord_1535729) baseStart_1535729 baseEnd_1535729 := by
    simpa [prefixWord, tailWord_1535729, baseEnd_1535729] using wordTrace_append hprefix tailTrace_1535729
  have hstable : (prefixWord ++ tailWord_1535729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535729).length < 2 ^ (prefixWord ++ tailWord_1535729).sum := by decide
  have hdescent : baseEnd_1535729 < baseStart_1535729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535752 : List Nat := [2, 1, 3, 2, 2, 1, 4, 1, 1, 6]
def baseStart_1535752 : Nat := 118140960795 + 1535752 * 2 ^ 59
def prefixEnd_1535752 : Nat := 4983230072969 + 3 ^ 40 * 1535752 * 2
def baseEnd_1535752 : Nat := 262859647367926865645737

theorem tailTrace_1535752 : CollatzResearch.WordTrace tailWord_1535752 prefixEnd_1535752 262859647367926865645737 := by
  unfold tailWord_1535752
  simp only [CollatzResearch.WordTrace]
  refine ⟨28006738566120132202544755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37342318088160176270059673 28006738566120132202544755)
  ·
    refine ⟨42010107849180198303817133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28006738566120132202544755 42010107849180198303817133)
    ·
      refine ⟨15753790443442574363931425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42010107849180198303817133 15753790443442574363931425)
      ·
        refine ⟨11815342832581930772948569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15753790443442574363931425 11815342832581930772948569)
        ·
          refine ⟨8861507124436448079711427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11815342832581930772948569 8861507124436448079711427)
          ·
            refine ⟨13292260686654672119567141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8861507124436448079711427 13292260686654672119567141)
            ·
              refine ⟨2492298878747751022418839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13292260686654672119567141 2492298878747751022418839)
              ·
                refine ⟨3738448318121626533628259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2492298878747751022418839 3738448318121626533628259)
                ·
                  refine ⟨5607672477182439800442389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3738448318121626533628259 5607672477182439800442389)
                  ·
                    refine ⟨262859647367926865645737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5607672477182439800442389 262859647367926865645737)
                    ·
                      rfl

theorem cell23_1535752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_1535752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535752 prefixEnd_1535752 := by exact prefixLift 1535752
  have htrace : WordTrace (prefixWord ++ tailWord_1535752) baseStart_1535752 baseEnd_1535752 := by
    simpa [prefixWord, tailWord_1535752, baseEnd_1535752] using wordTrace_append hprefix tailTrace_1535752
  have hstable : (prefixWord ++ tailWord_1535752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535752).length < 2 ^ (prefixWord ++ tailWord_1535752).sum := by decide
  have hdescent : baseEnd_1535752 < baseStart_1535752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535755 : List Nat := [1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 6]
def baseStart_1535755 : Nat := 118140960795 + 1535755 * 2 ^ 59
def prefixEnd_1535755 : Nat := 4983230072969 + 3 ^ 40 * 1535755 * 2
def baseEnd_1535755 : Nat := 788580482545744085199697

theorem tailTrace_1535755 : CollatzResearch.WordTrace tailWord_1535755 prefixEnd_1535755 788580482545744085199697 := by
  unfold tailWord_1535755
  simp only [CollatzResearch.WordTrace]
  refine ⟨56013586551229395917448719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37342391034152930611632479 56013586551229395917448719)
  ·
    refine ⟨84020379826844093876173079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56013586551229395917448719 84020379826844093876173079)
    ·
      refine ⟨126030569740266140814259619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84020379826844093876173079 126030569740266140814259619)
      ·
        refine ⟨189045854610399211221389429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126030569740266140814259619 189045854610399211221389429)
        ·
          refine ⟨17723048869724926052005259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 189045854610399211221389429 17723048869724926052005259)
          ·
            refine ⟨26584573304587389078007889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17723048869724926052005259 26584573304587389078007889)
            ·
              refine ⟨19938429978440541808505917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26584573304587389078007889 19938429978440541808505917)
              ·
                refine ⟨7476911241915203178189719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19938429978440541808505917 7476911241915203178189719)
                ·
                  refine ⟨11215366862872804767284579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7476911241915203178189719 11215366862872804767284579)
                  ·
                    refine ⟨16823050294309207150926869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11215366862872804767284579 16823050294309207150926869)
                    ·
                      refine ⟨788580482545744085199697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16823050294309207150926869 788580482545744085199697)
                      ·
                        rfl

theorem cell23_1535755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 6].length) (baseStart_1535755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535755 prefixEnd_1535755 := by exact prefixLift 1535755
  have htrace : WordTrace (prefixWord ++ tailWord_1535755) baseStart_1535755 baseEnd_1535755 := by
    simpa [prefixWord, tailWord_1535755, baseEnd_1535755] using wordTrace_append hprefix tailTrace_1535755
  have hstable : (prefixWord ++ tailWord_1535755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535755).length < 2 ^ (prefixWord ++ tailWord_1535755).sum := by decide
  have hdescent : baseEnd_1535755 < baseStart_1535755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535757 : List Nat := [1, 7, 2, 1, 1, 2, 1, 1, 2, 2, 3]
def baseStart_1535757 : Nat := 118140960795 + 1535757 * 2 ^ 59
def prefixEnd_1535757 : Nat := 4983230072969 + 3 ^ 40 * 1535757 * 2
def baseEnd_1535757 : Nat := 788581509507053077374689

theorem tailTrace_1535757 : CollatzResearch.WordTrace tailWord_1535757 prefixEnd_1535757 788581509507053077374689 := by
  unfold tailWord_1535757
  simp only [CollatzResearch.WordTrace]
  refine ⟨56013659497222150259021525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37342439664814766839347683 56013659497222150259021525)
  ·
    refine ⟨1312820144466144146695817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 56013659497222150259021525 1312820144466144146695817)
    ·
      refine ⟨984615108349608110021863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1312820144466144146695817 984615108349608110021863)
      ·
        refine ⟨1476922662524412165032795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 984615108349608110021863 1476922662524412165032795)
        ·
          refine ⟨2215383993786618247549193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1476922662524412165032795 2215383993786618247549193)
          ·
            refine ⟨1661537995339963685661895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2215383993786618247549193 1661537995339963685661895)
            ·
              refine ⟨2492306993009945528492843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1661537995339963685661895 2492306993009945528492843)
              ·
                refine ⟨3738460489514918292739265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2492306993009945528492843 3738460489514918292739265)
                ·
                  refine ⟨2803845367136188719554449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3738460489514918292739265 2803845367136188719554449)
                  ·
                    refine ⟨2102884025352141539665837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2803845367136188719554449 2102884025352141539665837)
                    ·
                      refine ⟨788581509507053077374689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2102884025352141539665837 788581509507053077374689)
                      ·
                        rfl

theorem cell23_1535757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_1535757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535757 prefixEnd_1535757 := by exact prefixLift 1535757
  have htrace : WordTrace (prefixWord ++ tailWord_1535757) baseStart_1535757 baseEnd_1535757 := by
    simpa [prefixWord, tailWord_1535757, baseEnd_1535757] using wordTrace_append hprefix tailTrace_1535757
  have hstable : (prefixWord ++ tailWord_1535757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535757).length < 2 ^ (prefixWord ++ tailWord_1535757).sum := by decide
  have hdescent : baseEnd_1535757 < baseStart_1535757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535772 : List Nat := [2, 2, 3, 1, 1, 2, 1, 4, 1, 2, 4]
def baseStart_1535772 : Nat := 118140960795 + 1535772 * 2 ^ 59
def prefixEnd_1535772 : Nat := 4983230072969 + 3 ^ 40 * 1535772 * 2
def baseEnd_1535772 : Nat := 788589211716870518687119

theorem tailTrace_1535772 : CollatzResearch.WordTrace tailWord_1535772 prefixEnd_1535772 788589211716870518687119 := by
  unfold tailWord_1535772
  simp only [CollatzResearch.WordTrace]
  refine ⟨28007103296083903910408785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37342804394778538547211713 28007103296083903910408785)
  ·
    refine ⟨21005327472062927932806589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28007103296083903910408785 21005327472062927932806589)
    ·
      refine ⟨7876997802023597974802471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21005327472062927932806589 7876997802023597974802471)
      ·
        refine ⟨11815496703035396962203707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7876997802023597974802471 11815496703035396962203707)
        ·
          refine ⟨17723245054553095443305561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11815496703035396962203707 17723245054553095443305561)
          ·
            refine ⟨13292433790914821582479171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17723245054553095443305561 13292433790914821582479171)
            ·
              refine ⟨19938650686372232373718757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13292433790914821582479171 19938650686372232373718757)
              ·
                refine ⟨3738497003694793570072267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19938650686372232373718757 3738497003694793570072267)
                ·
                  refine ⟨5607745505542190355108401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3738497003694793570072267 5607745505542190355108401)
                  ·
                    refine ⟨4205809129156642766331301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5607745505542190355108401 4205809129156642766331301)
                    ·
                      refine ⟨788589211716870518687119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4205809129156642766331301 788589211716870518687119)
                      ·
                        rfl

theorem cell23_1535772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_1535772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535772 prefixEnd_1535772 := by exact prefixLift 1535772
  have htrace : WordTrace (prefixWord ++ tailWord_1535772) baseStart_1535772 baseEnd_1535772 := by
    simpa [prefixWord, tailWord_1535772, baseEnd_1535772] using wordTrace_append hprefix tailTrace_1535772
  have hstable : (prefixWord ++ tailWord_1535772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535772).length < 2 ^ (prefixWord ++ tailWord_1535772).sum := by decide
  have hdescent : baseEnd_1535772 < baseStart_1535772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535793 : List Nat := [1, 2, 2, 3, 2, 2, 2, 4, 1, 2, 2]
def baseStart_1535793 : Nat := 118140960795 + 1535793 * 2 ^ 59
def prefixEnd_1535793 : Nat := 4983230072969 + 3 ^ 40 * 1535793 * 2
def baseEnd_1535793 : Nat := 788599994810614936524523

theorem tailTrace_1535793 : CollatzResearch.WordTrace tailWord_1535793 prefixEnd_1535793 788599994810614936524523 := by
  unfold tailWord_1535793
  simp only [CollatzResearch.WordTrace]
  refine ⟨56014972525091728407332033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37343315016727818938221355 56014972525091728407332033)
  ·
    refine ⟨42011229393818796305499025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56014972525091728407332033 42011229393818796305499025)
    ·
      refine ⟨31508422045364097229124269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42011229393818796305499025 31508422045364097229124269)
      ·
        refine ⟨11815658267011536460921601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31508422045364097229124269 11815658267011536460921601)
        ·
          refine ⟨8861743700258652345691201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11815658267011536460921601 8861743700258652345691201)
          ·
            refine ⟨6646307775193989259268401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8861743700258652345691201 6646307775193989259268401)
            ·
              refine ⟨4984730831395491944451301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6646307775193989259268401 4984730831395491944451301)
              ·
                refine ⟨934637030886654739584619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4984730831395491944451301 934637030886654739584619)
                ·
                  refine ⟨1401955546329982109376929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 934637030886654739584619 1401955546329982109376929)
                  ·
                    refine ⟨1051466659747486582032697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1401955546329982109376929 1051466659747486582032697)
                    ·
                      refine ⟨788599994810614936524523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1051466659747486582032697 788599994810614936524523)
                      ·
                        rfl

theorem cell23_1535793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_1535793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535793 prefixEnd_1535793 := by exact prefixLift 1535793
  have htrace : WordTrace (prefixWord ++ tailWord_1535793) baseStart_1535793 baseEnd_1535793 := by
    simpa [prefixWord, tailWord_1535793, baseEnd_1535793] using wordTrace_append hprefix tailTrace_1535793
  have hstable : (prefixWord ++ tailWord_1535793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535793).length < 2 ^ (prefixWord ++ tailWord_1535793).sum := by decide
  have hdescent : baseEnd_1535793 < baseStart_1535793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535806 : List Nat := [4, 2, 1, 2, 2, 3, 1, 1, 1, 2, 4]
def baseStart_1535806 : Nat := 118140960795 + 1535806 * 2 ^ 59
def prefixEnd_1535806 : Nat := 4983230072969 + 3 ^ 40 * 1535806 * 2
def baseEnd_1535806 : Nat := 788606670059123385661963

theorem tailTrace_1535806 : CollatzResearch.WordTrace tailWord_1535806 prefixEnd_1535806 788606670059123385661963 := by
  unfold tailWord_1535806
  simp only [CollatzResearch.WordTrace]
  refine ⟨7001930834255578953444409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37343631116029754418370181 7001930834255578953444409)
  ·
    refine ⟨5251448125691684215083307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7001930834255578953444409 5251448125691684215083307)
    ·
      refine ⟨7877172188537526322624961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5251448125691684215083307 7877172188537526322624961)
      ·
        refine ⟨5907879141403144741968721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7877172188537526322624961 5907879141403144741968721)
        ·
          refine ⟨4430909356052358556476541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5907879141403144741968721 4430909356052358556476541)
          ·
            refine ⟨1661591008519634458678703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4430909356052358556476541 1661591008519634458678703)
            ·
              refine ⟨2492386512779451688018055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1661591008519634458678703 2492386512779451688018055)
              ·
                refine ⟨3738579769169177532027083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2492386512779451688018055 3738579769169177532027083)
                ·
                  refine ⟨5607869653753766298040625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3738579769169177532027083 5607869653753766298040625)
                  ·
                    refine ⟨4205902240315324723530469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5607869653753766298040625 4205902240315324723530469)
                    ·
                      refine ⟨788606670059123385661963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4205902240315324723530469 788606670059123385661963)
                      ·
                        rfl

theorem cell23_1535806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_1535806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535806 prefixEnd_1535806 := by exact prefixLift 1535806
  have htrace : WordTrace (prefixWord ++ tailWord_1535806) baseStart_1535806 baseEnd_1535806 := by
    simpa [prefixWord, tailWord_1535806, baseEnd_1535806] using wordTrace_append hprefix tailTrace_1535806
  have hstable : (prefixWord ++ tailWord_1535806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535806).length < 2 ^ (prefixWord ++ tailWord_1535806).sum := by decide
  have hdescent : baseEnd_1535806 < baseStart_1535806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535870 : List Nat := [4, 2, 3, 1, 1, 1, 3, 2, 1, 3, 2]
def baseStart_1535870 : Nat := 118140960795 + 1535870 * 2 ^ 59
def prefixEnd_1535870 : Nat := 4983230072969 + 3 ^ 40 * 1535870 * 2
def baseEnd_1535870 : Nat := 788639532821011135261669

theorem tailTrace_1535870 : CollatzResearch.WordTrace tailWord_1535870 prefixEnd_1535870 788639532821011135261669 := by
  unfold tailWord_1535870
  simp only [CollatzResearch.WordTrace]
  refine ⟨7002222618226596319735633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37345187297208513705256709 7002222618226596319735633)
  ·
    refine ⟨5251666963669947239801725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7002222618226596319735633 5251666963669947239801725)
    ·
      refine ⟨1969375111376230214925647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5251666963669947239801725 1969375111376230214925647)
      ·
        refine ⟨2954062667064345322388471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1969375111376230214925647 2954062667064345322388471)
        ·
          refine ⟨4431094000596517983582707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2954062667064345322388471 4431094000596517983582707)
          ·
            refine ⟨6646641000894776975374061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4431094000596517983582707 6646641000894776975374061)
            ·
              refine ⟨2492490375335541365765273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6646641000894776975374061 2492490375335541365765273)
              ·
                refine ⟨1869367781501656024323955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2492490375335541365765273 1869367781501656024323955)
                ·
                  refine ⟨2804051672252484036485933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1869367781501656024323955 2804051672252484036485933)
                  ·
                    refine ⟨1051519377094681513682225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2804051672252484036485933 1051519377094681513682225)
                    ·
                      refine ⟨788639532821011135261669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1051519377094681513682225 788639532821011135261669)
                      ·
                        rfl

theorem cell23_1535870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_1535870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535870 prefixEnd_1535870 := by exact prefixLift 1535870
  have htrace : WordTrace (prefixWord ++ tailWord_1535870) baseStart_1535870 baseEnd_1535870 := by
    simpa [prefixWord, tailWord_1535870, baseEnd_1535870] using wordTrace_append hprefix tailTrace_1535870
  have hstable : (prefixWord ++ tailWord_1535870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535870).length < 2 ^ (prefixWord ++ tailWord_1535870).sum := by decide
  have hdescent : baseEnd_1535870 < baseStart_1535870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535900 : List Nat := [2, 2, 3, 3, 1, 2, 2, 2, 2, 2, 2]
def baseStart_1535900 : Nat := 118140960795 + 1535900 * 2 ^ 59
def prefixEnd_1535900 : Nat := 4983230072969 + 3 ^ 40 * 1535900 * 2
def baseEnd_1535900 : Nat := 788654937240646017886531

theorem tailTrace_1535900 : CollatzResearch.WordTrace tailWord_1535900 prefixEnd_1535900 788654937240646017886531 := by
  unfold tailWord_1535900
  simp only [CollatzResearch.WordTrace]
  refine ⟨28009437567852042840738577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37345916757136057120984769 28009437567852042840738577)
  ·
    refine ⟨21007078175889032130553933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28009437567852042840738577 21007078175889032130553933)
    ·
      refine ⟨7877654315958387048957725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21007078175889032130553933 7877654315958387048957725)
      ·
        refine ⟨2954120368484395143359147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7877654315958387048957725 2954120368484395143359147)
        ·
          refine ⟨4431180552726592715038721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2954120368484395143359147 4431180552726592715038721)
          ·
            refine ⟨3323385414544944536279041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4431180552726592715038721 3323385414544944536279041)
            ·
              refine ⟨2492539060908708402209281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3323385414544944536279041 2492539060908708402209281)
              ·
                refine ⟨1869404295681531301656961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2492539060908708402209281 1869404295681531301656961)
                ·
                  refine ⟨1402053221761148476242721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1869404295681531301656961 1402053221761148476242721)
                  ·
                    refine ⟨1051539916320861357182041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1402053221761148476242721 1051539916320861357182041)
                    ·
                      refine ⟨788654937240646017886531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1051539916320861357182041 788654937240646017886531)
                      ·
                        rfl

theorem cell23_1535900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_1535900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535900 prefixEnd_1535900 := by exact prefixLift 1535900
  have htrace : WordTrace (prefixWord ++ tailWord_1535900) baseStart_1535900 baseEnd_1535900 := by
    simpa [prefixWord, tailWord_1535900, baseEnd_1535900] using wordTrace_append hprefix tailTrace_1535900
  have hstable : (prefixWord ++ tailWord_1535900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535900).length < 2 ^ (prefixWord ++ tailWord_1535900).sum := by decide
  have hdescent : baseEnd_1535900 < baseStart_1535900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535939 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 6, 4, 2]
def baseStart_1535939 : Nat := 118140960795 + 1535939 * 2 ^ 59
def prefixEnd_1535939 : Nat := 4983230072969 + 3 ^ 40 * 1535939 * 2
def baseEnd_1535939 : Nat := 788674962986171365298851

theorem tailTrace_1535939 : CollatzResearch.WordTrace tailWord_1535939 prefixEnd_1535939 788674962986171365298851 := by
  unfold tailWord_1535939
  simp only [CollatzResearch.WordTrace]
  refine ⟨56020297582562795342146871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37346865055041863561431247 56020297582562795342146871)
  ·
    refine ⟨84030446373844193013220307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56020297582562795342146871 84030446373844193013220307)
    ·
      refine ⟨126045669560766289519830461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84030446373844193013220307 126045669560766289519830461)
      ·
        refine ⟨47267126085287358569936423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126045669560766289519830461 47267126085287358569936423)
        ·
          refine ⟨70900689127931037854904635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47267126085287358569936423 70900689127931037854904635)
          ·
            refine ⟨106351033691896556782356953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70900689127931037854904635 106351033691896556782356953)
            ·
              refine ⟨79763275268922417586767715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106351033691896556782356953 79763275268922417586767715)
              ·
                refine ⟨119644912903383626380151573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79763275268922417586767715 119644912903383626380151573)
                ·
                  refine ⟨5608355292346107486569605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 119644912903383626380151573 5608355292346107486569605)
                  ·
                    refine ⟨1051566617314895153731801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5608355292346107486569605 1051566617314895153731801)
                    ·
                      refine ⟨788674962986171365298851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1051566617314895153731801 788674962986171365298851)
                      ·
                        rfl

theorem cell23_1535939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 4, 2].length) (baseStart_1535939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535939 prefixEnd_1535939 := by exact prefixLift 1535939
  have htrace : WordTrace (prefixWord ++ tailWord_1535939) baseStart_1535939 baseEnd_1535939 := by
    simpa [prefixWord, tailWord_1535939, baseEnd_1535939] using wordTrace_append hprefix tailTrace_1535939
  have hstable : (prefixWord ++ tailWord_1535939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535939).length < 2 ^ (prefixWord ++ tailWord_1535939).sum := by decide
  have hdescent : baseEnd_1535939 < baseStart_1535939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535952 : List Nat := [2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 6]
def baseStart_1535952 : Nat := 118140960795 + 1535952 * 2 ^ 59
def prefixEnd_1535952 : Nat := 4983230072969 + 3 ^ 40 * 1535952 * 2
def baseEnd_1535952 : Nat := 788681638234679814436291

theorem tailTrace_1535952 : CollatzResearch.WordTrace tailWord_1535952 prefixEnd_1535952 788681638234679814436291 := by
  unfold tailWord_1535952
  simp only [CollatzResearch.WordTrace]
  refine ⟨28010385865757849281185055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37347181154343799041580073 28010385865757849281185055)
  ·
    refine ⟨42015578798636773921777583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28010385865757849281185055 42015578798636773921777583)
    ·
      refine ⟨63023368197955160882666375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42015578798636773921777583 63023368197955160882666375)
      ·
        refine ⟨94535052296932741323999563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63023368197955160882666375 94535052296932741323999563)
        ·
          refine ⟨141802578445399111985999345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94535052296932741323999563 141802578445399111985999345)
          ·
            refine ⟨106351933834049333989499509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141802578445399111985999345 106351933834049333989499509)
            ·
              refine ⟨9970493796942125061515579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106351933834049333989499509 9970493796942125061515579)
              ·
                refine ⟨14955740695413187592273369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9970493796942125061515579 14955740695413187592273369)
                ·
                  refine ⟨11216805521559890694205027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14955740695413187592273369 11216805521559890694205027)
                  ·
                    refine ⟨16825208282339836041307541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11216805521559890694205027 16825208282339836041307541)
                    ·
                      refine ⟨788681638234679814436291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16825208282339836041307541 788681638234679814436291)
                      ·
                        rfl

theorem cell23_1535952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 6].length) (baseStart_1535952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535952 prefixEnd_1535952 := by exact prefixLift 1535952
  have htrace : WordTrace (prefixWord ++ tailWord_1535952) baseStart_1535952 baseEnd_1535952 := by
    simpa [prefixWord, tailWord_1535952, baseEnd_1535952] using wordTrace_append hprefix tailTrace_1535952
  have hstable : (prefixWord ++ tailWord_1535952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535952).length < 2 ^ (prefixWord ++ tailWord_1535952).sum := by decide
  have hdescent : baseEnd_1535952 < baseStart_1535952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535956 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 4, 4, 2]
def baseStart_1535956 : Nat := 118140960795 + 1535956 * 2 ^ 59
def prefixEnd_1535956 : Nat := 4983230072969 + 3 ^ 40 * 1535956 * 2
def baseEnd_1535956 : Nat := 788683692157297798786273

theorem tailTrace_1535956 : CollatzResearch.WordTrace tailWord_1535956 prefixEnd_1535956 788683692157297798786273 := by
  unfold tailWord_1535956
  simp only [CollatzResearch.WordTrace]
  refine ⟨28010458811750603622757861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37347278415667471497010481 28010458811750603622757861)
  ·
    refine ⟨5251961027203238179267099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28010458811750603622757861 5251961027203238179267099)
    ·
      refine ⟨7877941540804857268900649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5251961027203238179267099 7877941540804857268900649)
      ·
        refine ⟨5908456155603642951675487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7877941540804857268900649 5908456155603642951675487)
        ·
          refine ⟨8862684233405464427513231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5908456155603642951675487 8862684233405464427513231)
          ·
            refine ⟨13294026350108196641269847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8862684233405464427513231 13294026350108196641269847)
            ·
              refine ⟨19941039525162294961904771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13294026350108196641269847 19941039525162294961904771)
              ·
                refine ⟨29911559287743442442857157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19941039525162294961904771 29911559287743442442857157)
                ·
                  refine ⟨5608417366451895458035717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29911559287743442442857157 5608417366451895458035717)
                  ·
                    refine ⟨1051578256209730398381697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5608417366451895458035717 1051578256209730398381697)
                    ·
                      refine ⟨788683692157297798786273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1051578256209730398381697 788683692157297798786273)
                      ·
                        rfl

theorem cell23_1535956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_1535956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535956 prefixEnd_1535956 := by exact prefixLift 1535956
  have htrace : WordTrace (prefixWord ++ tailWord_1535956) baseStart_1535956 baseEnd_1535956 := by
    simpa [prefixWord, tailWord_1535956, baseEnd_1535956] using wordTrace_append hprefix tailTrace_1535956
  have hstable : (prefixWord ++ tailWord_1535956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535956).length < 2 ^ (prefixWord ++ tailWord_1535956).sum := by decide
  have hdescent : baseEnd_1535956 < baseStart_1535956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535959 : List Nat := [1, 1, 3, 2, 1, 1, 4, 1, 4, 2, 3]
def baseStart_1535959 : Nat := 118140960795 + 1535959 * 2 ^ 59
def prefixEnd_1535959 : Nat := 4983230072969 + 3 ^ 40 * 1535959 * 2
def baseEnd_1535959 : Nat := 788685232599261287048759

theorem tailTrace_1535959 : CollatzResearch.WordTrace tailWord_1535959 prefixEnd_1535959 788685232599261287048759 := by
  unfold tailWord_1535959
  simp only [CollatzResearch.WordTrace]
  refine ⟨56021027042490338757874931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37347351361660225838583287 56021027042490338757874931)
  ·
    refine ⟨84031540563735508136812397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56021027042490338757874931 84031540563735508136812397)
    ·
      refine ⟨31511827711400815551304649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84031540563735508136812397 31511827711400815551304649)
      ·
        refine ⟨23633870783550611663478487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31511827711400815551304649 23633870783550611663478487)
        ·
          refine ⟨35450806175325917495217731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23633870783550611663478487 35450806175325917495217731)
          ·
            refine ⟨53176209262988876242826597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35450806175325917495217731 53176209262988876242826597)
            ·
              refine ⟨9970539236810414295529987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53176209262988876242826597 9970539236810414295529987)
              ·
                refine ⟨14955808855215621443294981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9970539236810414295529987 14955808855215621443294981)
                ·
                  refine ⟨2804214160352929020617809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14955808855215621443294981 2804214160352929020617809)
                  ·
                    refine ⟨2103160620264696765463357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2804214160352929020617809 2103160620264696765463357)
                    ·
                      refine ⟨788685232599261287048759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2103160620264696765463357 788685232599261287048759)
                      ·
                        rfl

theorem cell23_1535959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_1535959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1535959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1535959 prefixEnd_1535959 := by exact prefixLift 1535959
  have htrace : WordTrace (prefixWord ++ tailWord_1535959) baseStart_1535959 baseEnd_1535959 := by
    simpa [prefixWord, tailWord_1535959, baseEnd_1535959] using wordTrace_append hprefix tailTrace_1535959
  have hstable : (prefixWord ++ tailWord_1535959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535959).length < 2 ^ (prefixWord ++ tailWord_1535959).sum := by decide
  have hdescent : baseEnd_1535959 < baseStart_1535959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536016 : List Nat := [2, 1, 1, 1, 1, 1, 1, 8, 2, 3, 2]
def baseStart_1536016 : Nat := 118140960795 + 1536016 * 2 ^ 59
def prefixEnd_1536016 : Nat := 4983230072969 + 3 ^ 40 * 1536016 * 2
def baseEnd_1536016 : Nat := 788714500996567564035997

theorem tailTrace_1536016 : CollatzResearch.WordTrace tailWord_1536016 prefixEnd_1536016 788714500996567564035997 := by
  unfold tailWord_1536016
  simp only [CollatzResearch.WordTrace]
  refine ⟨28011553001641918746349951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37348737335522558328466601 28011553001641918746349951)
  ·
    refine ⟨42017329502462878119524927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28011553001641918746349951 42017329502462878119524927)
    ·
      refine ⟨63025994253694317179287391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42017329502462878119524927 63025994253694317179287391)
      ·
        refine ⟨94538991380541475768931087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63025994253694317179287391 94538991380541475768931087)
        ·
          refine ⟨141808487070812213653396631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94538991380541475768931087 141808487070812213653396631)
          ·
            refine ⟨212712730606218320480094947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141808487070812213653396631 212712730606218320480094947)
            ·
              refine ⟨319069095909327480720142421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212712730606218320480094947 319069095909327480720142421)
              ·
                refine ⟨3739090967687431414689169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 319069095909327480720142421 3739090967687431414689169)
                ·
                  refine ⟨2804318225765573561016877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3739090967687431414689169 2804318225765573561016877)
                  ·
                    refine ⟨1051619334662090085381329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2804318225765573561016877 1051619334662090085381329)
                    ·
                      refine ⟨788714500996567564035997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1051619334662090085381329 788714500996567564035997)
                      ·
                        rfl

theorem cell23_1536016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 2, 3, 2].length) (baseStart_1536016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536016 prefixEnd_1536016 := by exact prefixLift 1536016
  have htrace : WordTrace (prefixWord ++ tailWord_1536016) baseStart_1536016 baseEnd_1536016 := by
    simpa [prefixWord, tailWord_1536016, baseEnd_1536016] using wordTrace_append hprefix tailTrace_1536016
  have hstable : (prefixWord ++ tailWord_1536016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536016).length < 2 ^ (prefixWord ++ tailWord_1536016).sum := by decide
  have hdescent : baseEnd_1536016 < baseStart_1536016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536056 : List Nat := [2, 1, 2, 1, 6, 1, 1, 2, 1, 6]
def baseStart_1536056 : Nat := 118140960795 + 1536056 * 2 ^ 59
def prefixEnd_1536056 : Nat := 4983230072969 + 3 ^ 40 * 1536056 * 2
def baseEnd_1536056 : Nat := 262911680074249135845271

theorem tailTrace_1536056 : CollatzResearch.WordTrace tailWord_1536056 prefixEnd_1536056 262911680074249135845271 := by
  unfold tailWord_1536056
  simp only [CollatzResearch.WordTrace]
  refine ⟨28012282461569462162078011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37349709948759282882770681 28012282461569462162078011)
  ·
    refine ⟨42018423692354193243117017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28012282461569462162078011 42018423692354193243117017)
    ·
      refine ⟨31513817769265644932337763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42018423692354193243117017 31513817769265644932337763)
      ·
        refine ⟨47270726653898467398506645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31513817769265644932337763 47270726653898467398506645)
        ·
          refine ⟨2215815311901490659304999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47270726653898467398506645 2215815311901490659304999)
          ·
            refine ⟨3323722967852235988957499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2215815311901490659304999 3323722967852235988957499)
            ·
              refine ⟨4985584451778353983436249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3323722967852235988957499 4985584451778353983436249)
              ·
                refine ⟨3739188338833765487577187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4985584451778353983436249 3739188338833765487577187)
                ·
                  refine ⟨5608782508250648231365781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3739188338833765487577187 5608782508250648231365781)
                  ·
                    refine ⟨262911680074249135845271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5608782508250648231365781 262911680074249135845271)
                    ·
                      rfl

theorem cell23_1536056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 1, 6].length) (baseStart_1536056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536056 prefixEnd_1536056 := by exact prefixLift 1536056
  have htrace : WordTrace (prefixWord ++ tailWord_1536056) baseStart_1536056 baseEnd_1536056 := by
    simpa [prefixWord, tailWord_1536056, baseEnd_1536056] using wordTrace_append hprefix tailTrace_1536056
  have hstable : (prefixWord ++ tailWord_1536056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536056).length < 2 ^ (prefixWord ++ tailWord_1536056).sum := by decide
  have hdescent : baseEnd_1536056 < baseStart_1536056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536059 : List Nat := [1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 4]
def baseStart_1536059 : Nat := 118140960795 + 1536059 * 2 ^ 59
def prefixEnd_1536059 : Nat := 4983230072969 + 3 ^ 40 * 1536059 * 2
def baseEnd_1536059 : Nat := 788736580664710895798299

theorem tailTrace_1536059 : CollatzResearch.WordTrace tailWord_1536059 prefixEnd_1536059 788736580664710895798299 := by
  unfold tailWord_1536059
  simp only [CollatzResearch.WordTrace]
  refine ⟨56024674342128055836515231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37349782894752037224343487 56024674342128055836515231)
  ·
    refine ⟨84037011513192083754772847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56024674342128055836515231 84037011513192083754772847)
    ·
      refine ⟨126055517269788125632159271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84037011513192083754772847 126055517269788125632159271)
      ·
        refine ⟨189083275904682188448238907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126055517269788125632159271 189083275904682188448238907)
        ·
          refine ⟨283624913857023282672358361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189083275904682188448238907 283624913857023282672358361)
          ·
            refine ⟨212718685392767462004268771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283624913857023282672358361 212718685392767462004268771)
            ·
              refine ⟨319078028089151193006403157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212718685392767462004268771 319078028089151193006403157)
              ·
                refine ⟨3739195641669740543043787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 319078028089151193006403157 3739195641669740543043787)
                ·
                  refine ⟨5608793462504610814565681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3739195641669740543043787 5608793462504610814565681)
                  ·
                    refine ⟨4206595096878458110924261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5608793462504610814565681 4206595096878458110924261)
                    ·
                      refine ⟨788736580664710895798299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4206595096878458110924261 788736580664710895798299)
                      ·
                        rfl

theorem cell23_1536059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 4].length) (baseStart_1536059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536059 prefixEnd_1536059 := by exact prefixLift 1536059
  have htrace : WordTrace (prefixWord ++ tailWord_1536059) baseStart_1536059 baseEnd_1536059 := by
    simpa [prefixWord, tailWord_1536059, baseEnd_1536059] using wordTrace_append hprefix tailTrace_1536059
  have hstable : (prefixWord ++ tailWord_1536059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536059).length < 2 ^ (prefixWord ++ tailWord_1536059).sum := by decide
  have hdescent : baseEnd_1536059 < baseStart_1536059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536093 : List Nat := [1, 4, 4, 1, 1, 1, 1, 3, 1, 2, 4]
def baseStart_1536093 : Nat := 118140960795 + 1536093 * 2 ^ 59
def prefixEnd_1536093 : Nat := 4983230072969 + 3 ^ 40 * 1536093 * 2
def baseEnd_1536093 : Nat := 788754039006963762773143

theorem tailTrace_1536093 : CollatzResearch.WordTrace tailWord_1536093 prefixEnd_1536093 788754039006963762773143 := by
  unfold tailWord_1536093
  simp only [CollatzResearch.WordTrace]
  refine ⟨56025914424004879643252933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37350609616003253095501955 56025914424004879643252933)
  ·
    refine ⟨10504858954500914933109925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56025914424004879643252933 10504858954500914933109925)
    ·
      refine ⟨1969661053968921549958111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10504858954500914933109925 1969661053968921549958111)
      ·
        refine ⟨2954491580953382324937167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1969661053968921549958111 2954491580953382324937167)
        ·
          refine ⟨4431737371430073487405751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2954491580953382324937167 4431737371430073487405751)
          ·
            refine ⟨6647606057145110231108627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4431737371430073487405751 6647606057145110231108627)
            ·
              refine ⟨9971409085717665346662941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6647606057145110231108627 9971409085717665346662941)
              ·
                refine ⟨3739278407144124504998603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9971409085717665346662941 3739278407144124504998603)
                ·
                  refine ⟨5608917610716186757497905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3739278407144124504998603 5608917610716186757497905)
                  ·
                    refine ⟨4206688208037140068123429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5608917610716186757497905 4206688208037140068123429)
                    ·
                      refine ⟨788754039006963762773143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4206688208037140068123429 788754039006963762773143)
                      ·
                        rfl

theorem cell23_1536093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_1536093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536093 prefixEnd_1536093 := by exact prefixLift 1536093
  have htrace : WordTrace (prefixWord ++ tailWord_1536093) baseStart_1536093 baseEnd_1536093 := by
    simpa [prefixWord, tailWord_1536093, baseEnd_1536093] using wordTrace_append hprefix tailTrace_1536093
  have hstable : (prefixWord ++ tailWord_1536093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536093).length < 2 ^ (prefixWord ++ tailWord_1536093).sum := by decide
  have hdescent : baseEnd_1536093 < baseStart_1536093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536096 : List Nat := [2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 3]
def baseStart_1536096 : Nat := 118140960795 + 1536096 * 2 ^ 59
def prefixEnd_1536096 : Nat := 4983230072969 + 3 ^ 40 * 1536096 * 2
def baseEnd_1536096 : Nat := 788755579448927251035629

theorem tailTrace_1536096 : CollatzResearch.WordTrace tailWord_1536096 prefixEnd_1536096 788755579448927251035629 := by
  unfold tailWord_1536096
  simp only [CollatzResearch.WordTrace]
  refine ⟨28013011921497005577806071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37350682561996007437074761 28013011921497005577806071)
  ·
    refine ⟨42019517882245508366709107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28013011921497005577806071 42019517882245508366709107)
    ·
      refine ⟨63029276823368262550063661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42019517882245508366709107 63029276823368262550063661)
      ·
        refine ⟨23635978808763098456273873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63029276823368262550063661 23635978808763098456273873)
        ·
          refine ⟨17726984106572323842205405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23635978808763098456273873 17726984106572323842205405)
          ·
            refine ⟨6647619039964621440827027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17726984106572323842205405 6647619039964621440827027)
            ·
              refine ⟨9971428559946932161240541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6647619039964621440827027 9971428559946932161240541)
              ·
                refine ⟨3739285709980099560465203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9971428559946932161240541 3739285709980099560465203)
                ·
                  refine ⟨5608928564970149340697805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3739285709980099560465203 5608928564970149340697805)
                  ·
                    refine ⟨2103348211863806002761677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5608928564970149340697805 2103348211863806002761677)
                    ·
                      refine ⟨788755579448927251035629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2103348211863806002761677 788755579448927251035629)
                      ·
                        rfl

theorem cell23_1536096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_1536096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536096 prefixEnd_1536096 := by exact prefixLift 1536096
  have htrace : WordTrace (prefixWord ++ tailWord_1536096) baseStart_1536096 baseEnd_1536096 := by
    simpa [prefixWord, tailWord_1536096, baseEnd_1536096] using wordTrace_append hprefix tailTrace_1536096
  have hstable : (prefixWord ++ tailWord_1536096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536096).length < 2 ^ (prefixWord ++ tailWord_1536096).sum := by decide
  have hdescent : baseEnd_1536096 < baseStart_1536096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536139 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 5]
def baseStart_1536139 : Nat := 118140960795 + 1536139 * 2 ^ 59
def prefixEnd_1536139 : Nat := 4983230072969 + 3 ^ 40 * 1536139 * 2
def baseEnd_1536139 : Nat := 788777659117070582797931

theorem tailTrace_1536139 : CollatzResearch.WordTrace tailWord_1536139 prefixEnd_1536139 788777659117070582797931 := by
  unfold tailWord_1536139
  simp only [CollatzResearch.WordTrace]
  refine ⟨56027592181838229499427471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37351728121225486332951647 56027592181838229499427471)
  ·
    refine ⟨84041388272757344249141207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56027592181838229499427471 84041388272757344249141207)
    ·
      refine ⟨126062082409136016373711811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84041388272757344249141207 126062082409136016373711811)
      ·
        refine ⟨189093123613704024560567717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126062082409136016373711811 189093123613704024560567717)
        ·
          refine ⟨35454960677569504605106447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189093123613704024560567717 35454960677569504605106447)
          ·
            refine ⟨53182441016354256907659671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35454960677569504605106447 53182441016354256907659671)
            ·
              refine ⟨79773661524531385361489507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53182441016354256907659671 79773661524531385361489507)
              ·
                refine ⟨119660492286797078042234261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79773661524531385361489507 119660492286797078042234261)
                ·
                  refine ⟨5609085575943613033229731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 119660492286797078042234261 5609085575943613033229731)
                  ·
                    refine ⟨8413628363915419549844597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5609085575943613033229731 8413628363915419549844597)
                    ·
                      refine ⟨788777659117070582797931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8413628363915419549844597 788777659117070582797931)
                      ·
                        rfl

theorem cell23_1536139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 5].length) (baseStart_1536139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536139 prefixEnd_1536139 := by exact prefixLift 1536139
  have htrace : WordTrace (prefixWord ++ tailWord_1536139) baseStart_1536139 baseEnd_1536139 := by
    simpa [prefixWord, tailWord_1536139, baseEnd_1536139] using wordTrace_append hprefix tailTrace_1536139
  have hstable : (prefixWord ++ tailWord_1536139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536139).length < 2 ^ (prefixWord ++ tailWord_1536139).sum := by decide
  have hdescent : baseEnd_1536139 < baseStart_1536139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536146 : List Nat := [3, 2, 3, 1, 1, 1, 1, 3, 2, 6]
def baseStart_1536146 : Nat := 118140960795 + 1536146 * 2 ^ 59
def prefixEnd_1536146 : Nat := 4983230072969 + 3 ^ 40 * 1536146 * 2
def baseEnd_1536146 : Nat := 262927084493884018470133

theorem tailTrace_1536146 : CollatzResearch.WordTrace tailWord_1536146 prefixEnd_1536146 262927084493884018470133 := by
  unfold tailWord_1536146
  simp only [CollatzResearch.WordTrace]
  refine ⟨14006961873203217423733073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37351898328541913129954861 14006961873203217423733073)
  ·
    refine ⟨10505221404902413067799805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14006961873203217423733073 10505221404902413067799805)
    ·
      refine ⟨3939458026838404900424927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10505221404902413067799805 3939458026838404900424927)
      ·
        refine ⟨5909187040257607350637391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3939458026838404900424927 5909187040257607350637391)
        ·
          refine ⟨8863780560386411025956087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5909187040257607350637391 8863780560386411025956087)
          ·
            refine ⟨13295670840579616538934131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8863780560386411025956087 13295670840579616538934131)
            ·
              refine ⟨19943506260869424808401197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13295670840579616538934131 19943506260869424808401197)
              ·
                refine ⟨7478814847826034303150449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19943506260869424808401197 7478814847826034303150449)
                ·
                  refine ⟨5609111135869525727362837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7478814847826034303150449 5609111135869525727362837)
                  ·
                    refine ⟨262927084493884018470133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5609111135869525727362837 262927084493884018470133)
                    ·
                      rfl

theorem cell23_1536146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_1536146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536146 prefixEnd_1536146 := by exact prefixLift 1536146
  have htrace : WordTrace (prefixWord ++ tailWord_1536146) baseStart_1536146 baseEnd_1536146 := by
    simpa [prefixWord, tailWord_1536146, baseEnd_1536146] using wordTrace_append hprefix tailTrace_1536146
  have hstable : (prefixWord ++ tailWord_1536146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536146).length < 2 ^ (prefixWord ++ tailWord_1536146).sum := by decide
  have hdescent : baseEnd_1536146 < baseStart_1536146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536156 : List Nat := [2, 2, 3, 2, 1, 1, 2, 2, 2, 1, 5]
def baseStart_1536156 : Nat := 118140960795 + 1536156 * 2 ^ 59
def prefixEnd_1536156 : Nat := 4983230072969 + 3 ^ 40 * 1536156 * 2
def baseEnd_1536156 : Nat := 788786388288197016285353

theorem tailTrace_1536156 : CollatzResearch.WordTrace tailWord_1536156 prefixEnd_1536156 788786388288197016285353 := by
  unfold tailWord_1536156
  simp only [CollatzResearch.WordTrace]
  refine ⟨28014106111388320701398161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37352141481851094268530881 28014106111388320701398161)
  ·
    refine ⟨21010579583541240526048621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28014106111388320701398161 21010579583541240526048621)
    ·
      refine ⟨7878967343827965197268233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21010579583541240526048621 7878967343827965197268233)
      ·
        refine ⟨5909225507870973897951175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7878967343827965197268233 5909225507870973897951175)
        ·
          refine ⟨8863838261806460846926763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5909225507870973897951175 8863838261806460846926763)
          ·
            refine ⟨13295757392709691270390145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8863838261806460846926763 13295757392709691270390145)
            ·
              refine ⟨9971818044532268452792609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13295757392709691270390145 9971818044532268452792609)
              ·
                refine ⟨7478863533399201339594457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9971818044532268452792609 7478863533399201339594457)
                ·
                  refine ⟨5609147650049401004695843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7478863533399201339594457 5609147650049401004695843)
                  ·
                    refine ⟨8413721475074101507043765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5609147650049401004695843 8413721475074101507043765)
                    ·
                      refine ⟨788786388288197016285353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8413721475074101507043765 788786388288197016285353)
                      ·
                        rfl

theorem cell23_1536156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_1536156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536156 prefixEnd_1536156 := by exact prefixLift 1536156
  have htrace : WordTrace (prefixWord ++ tailWord_1536156) baseStart_1536156 baseEnd_1536156 := by
    simpa [prefixWord, tailWord_1536156, baseEnd_1536156] using wordTrace_append hprefix tailTrace_1536156
  have hstable : (prefixWord ++ tailWord_1536156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536156).length < 2 ^ (prefixWord ++ tailWord_1536156).sum := by decide
  have hdescent : baseEnd_1536156 < baseStart_1536156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536173 : List Nat := [1, 5, 2, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_1536173 : Nat := 118140960795 + 1536173 * 2 ^ 59
def prefixEnd_1536173 : Nat := 4983230072969 + 3 ^ 40 * 1536173 * 2
def baseEnd_1536173 : Nat := 788795117459323449772775

theorem tailTrace_1536173 : CollatzResearch.WordTrace tailWord_1536173 prefixEnd_1536173 788795117459323449772775 := by
  unfold tailWord_1536173
  simp only [CollatzResearch.WordTrace]
  refine ⟨56028832263715053306165173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37352554842476702204110115 56028832263715053306165173)
  ·
    refine ⟨5252703024723286247452985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56028832263715053306165173 5252703024723286247452985)
    ·
      refine ⟨3939527268542464685589739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5252703024723286247452985 3939527268542464685589739)
      ·
        refine ⟨5909290902813697028384609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3939527268542464685589739 5909290902813697028384609)
        ·
          refine ⟨4431968177110272771288457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5909290902813697028384609 4431968177110272771288457)
          ·
            refine ⟨3323976132832704578466343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4431968177110272771288457 3323976132832704578466343)
            ·
              refine ⟨4985964199249056867699515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3323976132832704578466343 4985964199249056867699515)
              ·
                refine ⟨7478946298873585301549273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4985964199249056867699515 7478946298873585301549273)
                ·
                  refine ⟨5609209724155188976161955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7478946298873585301549273 5609209724155188976161955)
                  ·
                    refine ⟨8413814586232783464242933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5609209724155188976161955 8413814586232783464242933)
                    ·
                      refine ⟨788795117459323449772775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8413814586232783464242933 788795117459323449772775)
                      ·
                        rfl

theorem cell23_1536173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_1536173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536173 prefixEnd_1536173 := by exact prefixLift 1536173
  have htrace : WordTrace (prefixWord ++ tailWord_1536173) baseStart_1536173 baseEnd_1536173 := by
    simpa [prefixWord, tailWord_1536173, baseEnd_1536173] using wordTrace_append hprefix tailTrace_1536173
  have hstable : (prefixWord ++ tailWord_1536173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536173).length < 2 ^ (prefixWord ++ tailWord_1536173).sum := by decide
  have hdescent : baseEnd_1536173 < baseStart_1536173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536186 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 4, 3, 3]
def baseStart_1536186 : Nat := 118140960795 + 1536186 * 2 ^ 59
def prefixEnd_1536186 : Nat := 4983230072969 + 3 ^ 40 * 1536186 * 2
def baseEnd_1536186 : Nat := 788801792707831898910215

theorem tailTrace_1536186 : CollatzResearch.WordTrace tailWord_1536186 prefixEnd_1536186 788801792707831898910215 := by
  unfold tailWord_1536186
  simp only [CollatzResearch.WordTrace]
  refine ⟨14007326603166989131597103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37352870941778637684258941 14007326603166989131597103)
  ·
    refine ⟨21010989904750483697395655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14007326603166989131597103 21010989904750483697395655)
    ·
      refine ⟨31516484857125725546093483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21010989904750483697395655 31516484857125725546093483)
      ·
        refine ⟨47274727285688588319140225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31516484857125725546093483 47274727285688588319140225)
        ·
          refine ⟨35456045464266441239355169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47274727285688588319140225 35456045464266441239355169)
          ·
            refine ⟨26592034098199830929516377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35456045464266441239355169 26592034098199830929516377)
            ·
              refine ⟨19944025573649873197137283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26592034098199830929516377 19944025573649873197137283)
              ·
                refine ⟨29916038360474809795705925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19944025573649873197137283 29916038360474809795705925)
                ·
                  refine ⟨5609257192589026836694861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29916038360474809795705925 5609257192589026836694861)
                  ·
                    refine ⟨2103471447220885063760573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5609257192589026836694861 2103471447220885063760573)
                    ·
                      refine ⟨788801792707831898910215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2103471447220885063760573 788801792707831898910215)
                      ·
                        rfl

theorem cell23_1536186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 4, 3, 3].length) (baseStart_1536186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536186 prefixEnd_1536186 := by exact prefixLift 1536186
  have htrace : WordTrace (prefixWord ++ tailWord_1536186) baseStart_1536186 baseEnd_1536186 := by
    simpa [prefixWord, tailWord_1536186, baseEnd_1536186] using wordTrace_append hprefix tailTrace_1536186
  have hstable : (prefixWord ++ tailWord_1536186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536186).length < 2 ^ (prefixWord ++ tailWord_1536186).sum := by decide
  have hdescent : baseEnd_1536186 < baseStart_1536186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536204 : List Nat := [2, 2, 1, 6, 1, 1, 1, 3, 2, 2, 2]
def baseStart_1536204 : Nat := 118140960795 + 1536204 * 2 ^ 59
def prefixEnd_1536204 : Nat := 4983230072969 + 3 ^ 40 * 1536204 * 2
def baseEnd_1536204 : Nat := 788811035359612828485133

theorem tailTrace_1536204 : CollatzResearch.WordTrace tailWord_1536204 prefixEnd_1536204 788811035359612828485133 := by
  unfold tailWord_1536204
  simp only [CollatzResearch.WordTrace]
  refine ⟨28014981463301372800271833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37353308617735163733695777 28014981463301372800271833)
  ·
    refine ⟨21011236097476029600203875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28014981463301372800271833 21011236097476029600203875)
    ·
      refine ⟨31516854146214044400305813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21011236097476029600203875 31516854146214044400305813)
      ·
        refine ⟨1477352538103783331264335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 31516854146214044400305813 1477352538103783331264335)
        ·
          refine ⟨2216028807155674996896503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1477352538103783331264335 2216028807155674996896503)
          ·
            refine ⟨3324043210733512495344755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2216028807155674996896503 3324043210733512495344755)
            ·
              refine ⟨4986064816100268743017133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3324043210733512495344755 4986064816100268743017133)
              ·
                refine ⟨1869774306037600778631425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4986064816100268743017133 1869774306037600778631425)
                ·
                  refine ⟨1402330729528200583973569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1869774306037600778631425 1402330729528200583973569)
                  ·
                    refine ⟨1051748047146150437980177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1402330729528200583973569 1051748047146150437980177)
                    ·
                      refine ⟨788811035359612828485133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1051748047146150437980177 788811035359612828485133)
                      ·
                        rfl

theorem cell23_1536204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_1536204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536204 prefixEnd_1536204 := by exact prefixLift 1536204
  have htrace : WordTrace (prefixWord ++ tailWord_1536204) baseStart_1536204 baseEnd_1536204 := by
    simpa [prefixWord, tailWord_1536204, baseEnd_1536204] using wordTrace_append hprefix tailTrace_1536204
  have hstable : (prefixWord ++ tailWord_1536204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536204).length < 2 ^ (prefixWord ++ tailWord_1536204).sum := by decide
  have hdescent : baseEnd_1536204 < baseStart_1536204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536219 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 1, 10]
def baseStart_1536219 : Nat := 118140960795 + 1536219 * 2 ^ 59
def prefixEnd_1536219 : Nat := 4983230072969 + 3 ^ 40 * 1536219 * 2
def baseEnd_1536219 : Nat := 262939579189810089932521

theorem tailTrace_1536219 : CollatzResearch.WordTrace tailWord_1536219 prefixEnd_1536219 262939579189810089932521 := by
  unfold tailWord_1536219
  simp only [CollatzResearch.WordTrace]
  refine ⟨56030510021548403162339711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37353673347698935441559807 56030510021548403162339711)
  ·
    refine ⟨84045765032322604743509567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56030510021548403162339711 84045765032322604743509567)
    ·
      refine ⟨126068647548483907115264351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84045765032322604743509567 126068647548483907115264351)
      ·
        refine ⟨189102971322725860672896527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126068647548483907115264351 189102971322725860672896527)
        ·
          refine ⟨283654456984088791009344791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189102971322725860672896527 283654456984088791009344791)
          ·
            refine ⟨425481685476133186514017187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283654456984088791009344791 425481685476133186514017187)
            ·
              refine ⟨638222528214199779771025781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 425481685476133186514017187 638222528214199779771025781)
              ·
                refine ⟨59833362020081229353533667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 638222528214199779771025781 59833362020081229353533667)
                ·
                  refine ⟨89750043030121844030300501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59833362020081229353533667 89750043030121844030300501)
                  ·
                    refine ⟨262939579189810089932521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 89750043030121844030300501 262939579189810089932521)
                    ·
                      rfl

theorem cell23_1536219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 10].length) (baseStart_1536219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536219 prefixEnd_1536219 := by exact prefixLift 1536219
  have htrace : WordTrace (prefixWord ++ tailWord_1536219) baseStart_1536219 baseEnd_1536219 := by
    simpa [prefixWord, tailWord_1536219, baseEnd_1536219] using wordTrace_append hprefix tailTrace_1536219
  have hstable : (prefixWord ++ tailWord_1536219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536219).length < 2 ^ (prefixWord ++ tailWord_1536219).sum := by decide
  have hdescent : baseEnd_1536219 < baseStart_1536219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536243 : List Nat := [1, 1, 1, 2, 2, 4, 2, 2, 2, 4, 2]
def baseStart_1536243 : Nat := 118140960795 + 1536243 * 2 ^ 59
def prefixEnd_1536243 : Nat := 4983230072969 + 3 ^ 40 * 1536243 * 2
def baseEnd_1536243 : Nat := 788831061105138175897453

theorem tailTrace_1536243 : CollatzResearch.WordTrace tailWord_1536243 prefixEnd_1536243 788831061105138175897453 := by
  unfold tailWord_1536243
  simp only [CollatzResearch.WordTrace]
  refine ⟨56031385373461455261213383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37354256915640970174142255 56031385373461455261213383)
  ·
    refine ⟨84047078060192182891820075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56031385373461455261213383 84047078060192182891820075)
    ·
      refine ⟨126070617090288274337730113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84047078060192182891820075 126070617090288274337730113)
      ·
        refine ⟨94552962817716205753297585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126070617090288274337730113 94552962817716205753297585)
        ·
          refine ⟨70914722113287154314973189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94552962817716205753297585 70914722113287154314973189)
          ·
            refine ⟨13296510396241341434057473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70914722113287154314973189 13296510396241341434057473)
            ·
              refine ⟨9972382797181006075543105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13296510396241341434057473 9972382797181006075543105)
              ·
                refine ⟨7479287097885754556657329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9972382797181006075543105 7479287097885754556657329)
                ·
                  refine ⟨5609465323414315917492997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7479287097885754556657329 5609465323414315917492997)
                  ·
                    refine ⟨1051774748140184234529937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5609465323414315917492997 1051774748140184234529937)
                    ·
                      refine ⟨788831061105138175897453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1051774748140184234529937 788831061105138175897453)
                      ·
                        rfl

theorem cell23_1536243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 4, 2].length) (baseStart_1536243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536243 prefixEnd_1536243 := by exact prefixLift 1536243
  have htrace : WordTrace (prefixWord ++ tailWord_1536243) baseStart_1536243 baseEnd_1536243 := by
    simpa [prefixWord, tailWord_1536243, baseEnd_1536243] using wordTrace_append hprefix tailTrace_1536243
  have hstable : (prefixWord ++ tailWord_1536243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536243).length < 2 ^ (prefixWord ++ tailWord_1536243).sum := by decide
  have hdescent : baseEnd_1536243 < baseStart_1536243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536287 : List Nat := [1, 1, 2, 4, 3, 2, 2, 3, 1, 4]
def baseStart_1536287 : Nat := 118140960795 + 1536287 * 2 ^ 59
def prefixEnd_1536287 : Nat := 4983230072969 + 3 ^ 40 * 1536287 * 2
def baseEnd_1536287 : Nat := 262951218084645334582417

theorem tailTrace_1536287 : CollatzResearch.WordTrace tailWord_1536287 prefixEnd_1536287 262951218084645334582417 := by
  unfold tailWord_1536287
  simp only [CollatzResearch.WordTrace]
  refine ⟨56032990185302050775815115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37355326790201367183876743 56032990185302050775815115)
  ·
    refine ⟨84049485277953076163722673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56032990185302050775815115 84049485277953076163722673)
    ·
      refine ⟨63037113958464807122792005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84049485277953076163722673 63037113958464807122792005)
      ·
        refine ⟨11819458867212151335523501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63037113958464807122792005 11819458867212151335523501)
        ·
          refine ⟨4432297075204556750821313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11819458867212151335523501 4432297075204556750821313)
          ·
            refine ⟨3324222806403417563115985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4432297075204556750821313 3324222806403417563115985)
            ·
              refine ⟨2493167104802563172336989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3324222806403417563115985 2493167104802563172336989)
              ·
                refine ⟨934937664300961189626371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2493167104802563172336989 934937664300961189626371)
                ·
                  refine ⟨1402406496451441784439557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 934937664300961189626371 1402406496451441784439557)
                  ·
                    refine ⟨262951218084645334582417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1402406496451441784439557 262951218084645334582417)
                    ·
                      rfl

theorem cell23_1536287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 3, 1, 4].length) (baseStart_1536287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536287 prefixEnd_1536287 := by exact prefixLift 1536287
  have htrace : WordTrace (prefixWord ++ tailWord_1536287) baseStart_1536287 baseEnd_1536287 := by
    simpa [prefixWord, tailWord_1536287, baseEnd_1536287] using wordTrace_append hprefix tailTrace_1536287
  have hstable : (prefixWord ++ tailWord_1536287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536287).length < 2 ^ (prefixWord ++ tailWord_1536287).sum := by decide
  have hdescent : baseEnd_1536287 < baseStart_1536287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536343 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 6, 4]
def baseStart_1536343 : Nat := 118140960795 + 1536343 * 2 ^ 59
def prefixEnd_1536343 : Nat := 4983230072969 + 3 ^ 40 * 1536343 * 2
def baseEnd_1536343 : Nat := 262960803056862594882331

theorem tailTrace_1536343 : CollatzResearch.WordTrace tailWord_1536343 prefixEnd_1536343 262960803056862594882331 := by
  unfold tailWord_1536343
  simp only [CollatzResearch.WordTrace]
  refine ⟨56035032673099172339853683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37356688448732781559902455 56035032673099172339853683)
  ·
    refine ⟨84052549009648758509780525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56035032673099172339853683 84052549009648758509780525)
    ·
      refine ⟨31519705878618284441167697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84052549009648758509780525 31519705878618284441167697)
      ·
        refine ⟨23639779408963713330875773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31519705878618284441167697 23639779408963713330875773)
        ·
          refine ⟨8864917278361392499078415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23639779408963713330875773 8864917278361392499078415)
          ·
            refine ⟨13297375917542088748617623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8864917278361392499078415 13297375917542088748617623)
            ·
              refine ⟨19946063876313133122926435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13297375917542088748617623 19946063876313133122926435)
              ·
                refine ⟨29919095814469699684389653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19946063876313133122926435 29919095814469699684389653)
                ·
                  refine ⟨1402457616303267172705765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29919095814469699684389653 1402457616303267172705765)
                  ·
                    refine ⟨262960803056862594882331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1402457616303267172705765 262960803056862594882331)
                    ·
                      rfl

theorem cell23_1536343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 6, 4].length) (baseStart_1536343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536343 prefixEnd_1536343 := by exact prefixLift 1536343
  have htrace : WordTrace (prefixWord ++ tailWord_1536343) baseStart_1536343 baseEnd_1536343 := by
    simpa [prefixWord, tailWord_1536343, baseEnd_1536343] using wordTrace_append hprefix tailTrace_1536343
  have hstable : (prefixWord ++ tailWord_1536343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536343).length < 2 ^ (prefixWord ++ tailWord_1536343).sum := by decide
  have hdescent : baseEnd_1536343 < baseStart_1536343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536353 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 7, 2, 3]
def baseStart_1536353 : Nat := 118140960795 + 1536353 * 2 ^ 59
def prefixEnd_1536353 : Nat := 4983230072969 + 3 ^ 40 * 1536353 * 2
def baseEnd_1536353 : Nat := 788887543977132745521947

theorem tailTrace_1536353 : CollatzResearch.WordTrace tailWord_1536353 prefixEnd_1536353 788887543977132745521947 := by
  unfold tailWord_1536353
  simp only [CollatzResearch.WordTrace]
  refine ⟨56035397403062944047717713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37356931602041962698478475 56035397403062944047717713)
  ·
    refine ⟨42026548052297208035788285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56035397403062944047717713 42026548052297208035788285)
    ·
      refine ⟨15759955519611453013420607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42026548052297208035788285 15759955519611453013420607)
      ·
        refine ⟨23639933279417179520130911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15759955519611453013420607 23639933279417179520130911)
        ·
          refine ⟨35459899919125769280196367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23639933279417179520130911 35459899919125769280196367)
          ·
            refine ⟨53189849878688653920294551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35459899919125769280196367 53189849878688653920294551)
            ·
              refine ⟨79784774818032980880441827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53189849878688653920294551 79784774818032980880441827)
              ·
                refine ⟨119677162227049471320662741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79784774818032980880441827 119677162227049471320662741)
                ·
                  refine ⟨2804933489696471984078033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 119677162227049471320662741 2804933489696471984078033)
                  ·
                    refine ⟨2103700117272353988058525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2804933489696471984078033 2103700117272353988058525)
                    ·
                      refine ⟨788887543977132745521947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2103700117272353988058525 788887543977132745521947)
                      ·
                        rfl

theorem cell23_1536353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_1536353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536353 prefixEnd_1536353 := by exact prefixLift 1536353
  have htrace : WordTrace (prefixWord ++ tailWord_1536353) baseStart_1536353 baseEnd_1536353 := by
    simpa [prefixWord, tailWord_1536353, baseEnd_1536353] using wordTrace_append hprefix tailTrace_1536353
  have hstable : (prefixWord ++ tailWord_1536353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536353).length < 2 ^ (prefixWord ++ tailWord_1536353).sum := by decide
  have hdescent : baseEnd_1536353 < baseStart_1536353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536360 : List Nat := [2, 1, 4, 2, 2, 1, 2, 1, 4, 4]
def baseStart_1536360 : Nat := 118140960795 + 1536360 * 2 ^ 59
def prefixEnd_1536360 : Nat := 4983230072969 + 3 ^ 40 * 1536360 * 2
def baseEnd_1536360 : Nat := 262963712780571406044805

theorem tailTrace_1536360 : CollatzResearch.WordTrace tailWord_1536360 prefixEnd_1536360 262963712780571406044805 := by
  unfold tailWord_1536360
  simp only [CollatzResearch.WordTrace]
  refine ⟨28017826357018792121611267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37357101809358389495481689 28017826357018792121611267)
  ·
    refine ⟨42026739535528188182416901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28017826357018792121611267 42026739535528188182416901)
    ·
      refine ⟨7880013662911535284203169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42026739535528188182416901 7880013662911535284203169)
      ·
        refine ⟨5910010247183651463152377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7880013662911535284203169 5910010247183651463152377)
        ·
          refine ⟨4432507685387738597364283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5910010247183651463152377 4432507685387738597364283)
          ·
            refine ⟨6648761528081607896046425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4432507685387738597364283 6648761528081607896046425)
            ·
              refine ⟨4986571146061205922034819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6648761528081607896046425 4986571146061205922034819)
              ·
                refine ⟨7479856719091808883052229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4986571146061205922034819 7479856719091808883052229)
                ·
                  refine ⟨1402473134829714165572293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7479856719091808883052229 1402473134829714165572293)
                  ·
                    refine ⟨262963712780571406044805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1402473134829714165572293 262963712780571406044805)
                    ·
                      rfl

theorem cell23_1536360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_1536360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536360 prefixEnd_1536360 := by exact prefixLift 1536360
  have htrace : WordTrace (prefixWord ++ tailWord_1536360) baseStart_1536360 baseEnd_1536360 := by
    simpa [prefixWord, tailWord_1536360, baseEnd_1536360] using wordTrace_append hprefix tailTrace_1536360
  have hstable : (prefixWord ++ tailWord_1536360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536360).length < 2 ^ (prefixWord ++ tailWord_1536360).sum := by decide
  have hdescent : baseEnd_1536360 < baseStart_1536360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536373 : List Nat := [1, 3, 4, 1, 2, 1, 1, 10]
def baseStart_1536373 : Nat := 118140960795 + 1536373 * 2 ^ 59
def prefixEnd_1536373 : Nat := 4983230072969 + 3 ^ 40 * 1536373 * 2
def baseEnd_1536373 : Nat := 29218437540378617306365

theorem tailTrace_1536373 : CollatzResearch.WordTrace tailWord_1536373 prefixEnd_1536373 29218437540378617306365 := by
  unfold tailWord_1536373
  simp only [CollatzResearch.WordTrace]
  refine ⟨56036126862990487463445773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37357417908660324975630515 56036126862990487463445773)
  ·
    refine ⟨21013547573621432798792165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56036126862990487463445773 21013547573621432798792165)
    ·
      refine ⟨3940040170054018649773531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21013547573621432798792165 3940040170054018649773531)
      ·
        refine ⟨5910060255081027974660297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3940040170054018649773531 5910060255081027974660297)
        ·
          refine ⟨4432545191310770980995223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5910060255081027974660297 4432545191310770980995223)
          ·
            refine ⟨6648817786966156471492835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4432545191310770980995223 6648817786966156471492835)
            ·
              refine ⟨9973226680449234707239253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6648817786966156471492835 9973226680449234707239253)
              ·
                refine ⟨29218437540378617306365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 9973226680449234707239253 29218437540378617306365)
                ·
                  rfl

theorem cell23_1536373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 10].length) (baseStart_1536373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536373 prefixEnd_1536373 := by exact prefixLift 1536373
  have htrace : WordTrace (prefixWord ++ tailWord_1536373) baseStart_1536373 baseEnd_1536373 := by
    simpa [prefixWord, tailWord_1536373, baseEnd_1536373] using wordTrace_append hprefix tailTrace_1536373
  have hstable : (prefixWord ++ tailWord_1536373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536373).length < 2 ^ (prefixWord ++ tailWord_1536373).sum := by decide
  have hdescent : baseEnd_1536373 < baseStart_1536373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536404 : List Nat := [2, 4, 2, 1, 4, 1, 1, 1, 1, 1, 5]
def baseStart_1536404 : Nat := 118140960795 + 1536404 * 2 ^ 59
def prefixEnd_1536404 : Nat := 4983230072969 + 3 ^ 40 * 1536404 * 2
def baseEnd_1536404 : Nat := 788913731490512045984213

theorem tailTrace_1536404 : CollatzResearch.WordTrace tailWord_1536404 prefixEnd_1536404 788913731490512045984213 := by
  unfold tailWord_1536404
  simp only [CollatzResearch.WordTrace]
  refine ⟨28018628762939089878912133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37358171683918786505216177 28018628762939089878912133)
  ·
    refine ⟨5253492893051079352296025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28018628762939089878912133 5253492893051079352296025)
    ·
      refine ⟨3940119669788309514222019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5253492893051079352296025 3940119669788309514222019)
      ·
        refine ⟨5910179504682464271333029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3940119669788309514222019 5910179504682464271333029)
        ·
          refine ⟨1108158657127962050874943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5910179504682464271333029 1108158657127962050874943)
          ·
            refine ⟨1662237985691943076312415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1108158657127962050874943 1662237985691943076312415)
            ·
              refine ⟨2493356978537914614468623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1662237985691943076312415 2493356978537914614468623)
              ·
                refine ⟨3740035467806871921702935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2493356978537914614468623 3740035467806871921702935)
                ·
                  refine ⟨5610053201710307882554403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3740035467806871921702935 5610053201710307882554403)
                  ·
                    refine ⟨8415079802565461823831605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5610053201710307882554403 8415079802565461823831605)
                    ·
                      refine ⟨788913731490512045984213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8415079802565461823831605 788913731490512045984213)
                      ·
                        rfl

theorem cell23_1536404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_1536404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536404 prefixEnd_1536404 := by exact prefixLift 1536404
  have htrace : WordTrace (prefixWord ++ tailWord_1536404) baseStart_1536404 baseEnd_1536404 := by
    simpa [prefixWord, tailWord_1536404, baseEnd_1536404] using wordTrace_append hprefix tailTrace_1536404
  have hstable : (prefixWord ++ tailWord_1536404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536404).length < 2 ^ (prefixWord ++ tailWord_1536404).sum := by decide
  have hdescent : baseEnd_1536404 < baseStart_1536404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536433 : List Nat := [1, 2, 2, 4, 1, 2, 1, 1, 1, 8]
def baseStart_1536433 : Nat := 118140960795 + 1536433 * 2 ^ 59
def prefixEnd_1536433 : Nat := 4983230072969 + 3 ^ 40 * 1536433 * 2
def baseEnd_1536433 : Nat := 262976207476497477507193

theorem tailTrace_1536433 : CollatzResearch.WordTrace tailWord_1536433 prefixEnd_1536433 262976207476497477507193 := by
  unfold tailWord_1536433
  simp only [CollatzResearch.WordTrace]
  refine ⟨56038315242773117710629953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37358876828515411807086635 56038315242773117710629953)
  ·
    refine ⟨42028736432079838282972465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56038315242773117710629953 42028736432079838282972465)
    ·
      refine ⟨31521552324059878712229349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42028736432079838282972465 31521552324059878712229349)
      ·
        refine ⟨5910291060761227258543003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31521552324059878712229349 5910291060761227258543003)
        ·
          refine ⟨8865436591141840887814505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5910291060761227258543003 8865436591141840887814505)
          ·
            refine ⟨6649077443356380665860879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8865436591141840887814505 6649077443356380665860879)
            ·
              refine ⟨9973616165034570998791319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6649077443356380665860879 9973616165034570998791319)
              ·
                refine ⟨14960424247551856498186979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9973616165034570998791319 14960424247551856498186979)
                ·
                  refine ⟨22440636371327784747280469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14960424247551856498186979 22440636371327784747280469)
                  ·
                    refine ⟨262976207476497477507193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 22440636371327784747280469 262976207476497477507193)
                    ·
                      rfl

theorem cell23_1536433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 8].length) (baseStart_1536433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536433 prefixEnd_1536433 := by exact prefixLift 1536433
  have htrace : WordTrace (prefixWord ++ tailWord_1536433) baseStart_1536433 baseEnd_1536433 := by
    simpa [prefixWord, tailWord_1536433, baseEnd_1536433] using wordTrace_append hprefix tailTrace_1536433
  have hstable : (prefixWord ++ tailWord_1536433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536433).length < 2 ^ (prefixWord ++ tailWord_1536433).sum := by decide
  have hdescent : baseEnd_1536433 < baseStart_1536433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536480 : List Nat := [2, 1, 1, 3, 1, 1, 3, 6, 5]
def baseStart_1536480 : Nat := 118140960795 + 1536480 * 2 ^ 59
def prefixEnd_1536480 : Nat := 4983230072969 + 3 ^ 40 * 1536480 * 2
def baseEnd_1536480 : Nat := 87661417335583749848207

theorem tailTrace_1536480 : CollatzResearch.WordTrace tailWord_1536480 prefixEnd_1536480 87661417335583749848207 := by
  unfold tailWord_1536480
  simp only [CollatzResearch.WordTrace]
  refine ⟨28020014736801422368795447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37360019649068563158393929 28020014736801422368795447)
  ·
    refine ⟨42030022105202133553193171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28020014736801422368795447 42030022105202133553193171)
    ·
      refine ⟨63045033157803200329789757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42030022105202133553193171 63045033157803200329789757)
      ·
        refine ⟨23641887434176200123671159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63045033157803200329789757 23641887434176200123671159)
        ·
          refine ⟨35462831151264300185506739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23641887434176200123671159 35462831151264300185506739)
          ·
            refine ⟨53194246726896450278260109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35462831151264300185506739 53194246726896450278260109)
            ·
              refine ⟨19947842522586168854347541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53194246726896450278260109 19947842522586168854347541)
              ·
                refine ⟨935055118246226665047541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19947842522586168854347541 935055118246226665047541)
                ·
                  refine ⟨87661417335583749848207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 935055118246226665047541 87661417335583749848207)
                  ·
                    rfl

theorem cell23_1536480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 6, 5].length) (baseStart_1536480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536480 prefixEnd_1536480 := by exact prefixLift 1536480
  have htrace : WordTrace (prefixWord ++ tailWord_1536480) baseStart_1536480 baseEnd_1536480 := by
    simpa [prefixWord, tailWord_1536480, baseEnd_1536480] using wordTrace_append hprefix tailTrace_1536480
  have hstable : (prefixWord ++ tailWord_1536480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536480).length < 2 ^ (prefixWord ++ tailWord_1536480).sum := by decide
  have hdescent : baseEnd_1536480 < baseStart_1536480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536567 : List Nat := [1, 1, 3, 1, 2, 3, 4, 1, 2, 2, 3]
def baseStart_1536567 : Nat := 118140960795 + 1536567 * 2 ^ 59
def prefixEnd_1536567 : Nat := 4983230072969 + 3 ^ 40 * 1536567 * 2
def baseEnd_1536567 : Nat := 788997428837194908245963

theorem tailTrace_1536567 : CollatzResearch.WordTrace tailWord_1536567 prefixEnd_1536567 788997428837194908245963 := by
  unfold tailWord_1536567
  simp only [CollatzResearch.WordTrace]
  refine ⟨56043202624287658596007955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37362135082858439064005303 56043202624287658596007955)
  ·
    refine ⟨84064803936431487894011933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56043202624287658596007955 84064803936431487894011933)
    ·
      refine ⟨31524301476161807960254475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84064803936431487894011933 31524301476161807960254475)
      ·
        refine ⟨47286452214242711940381713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31524301476161807960254475 47286452214242711940381713)
        ·
          refine ⟨35464839160682033955286285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47286452214242711940381713 35464839160682033955286285)
          ·
            refine ⟨13299314685255762733232357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35464839160682033955286285 13299314685255762733232357)
            ·
              refine ⟨2493621503485455512481067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13299314685255762733232357 2493621503485455512481067)
              ·
                refine ⟨3740432255228183268721601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2493621503485455512481067 3740432255228183268721601)
                ·
                  refine ⟨2805324191421137451541201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3740432255228183268721601 2805324191421137451541201)
                  ·
                    refine ⟨2103993143565853088655901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2805324191421137451541201 2103993143565853088655901)
                    ·
                      refine ⟨788997428837194908245963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2103993143565853088655901 788997428837194908245963)
                      ·
                        rfl

theorem cell23_1536567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 2, 3].length) (baseStart_1536567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536567 prefixEnd_1536567 := by exact prefixLift 1536567
  have htrace : WordTrace (prefixWord ++ tailWord_1536567) baseStart_1536567 baseEnd_1536567 := by
    simpa [prefixWord, tailWord_1536567, baseEnd_1536567] using wordTrace_append hprefix tailTrace_1536567
  have hstable : (prefixWord ++ tailWord_1536567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536567).length < 2 ^ (prefixWord ++ tailWord_1536567).sum := by decide
  have hdescent : baseEnd_1536567 < baseStart_1536567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536600 : List Nat := [2, 1, 2, 2, 1, 2, 3, 2, 3, 5]
def baseStart_1536600 : Nat := 118140960795 + 1536600 * 2 ^ 59
def prefixEnd_1536600 : Nat := 4983230072969 + 3 ^ 40 * 1536600 * 2
def baseEnd_1536600 : Nat := 263004791232931093044437

theorem tailTrace_1536600 : CollatzResearch.WordTrace tailWord_1536600 prefixEnd_1536600 263004791232931093044437 := by
  unfold tailWord_1536600
  simp only [CollatzResearch.WordTrace]
  refine ⟨28022203116584052615979627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37362937488778736821306169 28022203116584052615979627)
  ·
    refine ⟨42033304674876078923969441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28022203116584052615979627 42033304674876078923969441)
    ·
      refine ⟨31524978506157059192977081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42033304674876078923969441 31524978506157059192977081)
      ·
        refine ⟨23643733879617794394732811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31524978506157059192977081 23643733879617794394732811)
        ·
          refine ⟨35465600819426691592099217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23643733879617794394732811 35465600819426691592099217)
          ·
            refine ⟨26599200614570018694074413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35465600819426691592099217 26599200614570018694074413)
            ·
              refine ⟨9974700230463757010277905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26599200614570018694074413 9974700230463757010277905)
              ·
                refine ⟨7481025172847817757708429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9974700230463757010277905 7481025172847817757708429)
                ·
                  refine ⟨2805384439817931659140661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7481025172847817757708429 2805384439817931659140661)
                  ·
                    refine ⟨263004791232931093044437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2805384439817931659140661 263004791232931093044437)
                    ·
                      rfl

theorem cell23_1536600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 3, 5].length) (baseStart_1536600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536600 prefixEnd_1536600 := by exact prefixLift 1536600
  have htrace : WordTrace (prefixWord ++ tailWord_1536600) baseStart_1536600 baseEnd_1536600 := by
    simpa [prefixWord, tailWord_1536600, baseEnd_1536600] using wordTrace_append hprefix tailTrace_1536600
  have hstable : (prefixWord ++ tailWord_1536600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536600).length < 2 ^ (prefixWord ++ tailWord_1536600).sum := by decide
  have hdescent : baseEnd_1536600 < baseStart_1536600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536607 : List Nat := [1, 1, 2, 3, 1, 1, 1, 4, 4, 3, 2]
def baseStart_1536607 : Nat := 118140960795 + 1536607 * 2 ^ 59
def prefixEnd_1536607 : Nat := 4983230072969 + 3 ^ 40 * 1536607 * 2
def baseEnd_1536607 : Nat := 789017968063374751745779

theorem tailTrace_1536607 : CollatzResearch.WordTrace tailWord_1536607 prefixEnd_1536607 789017968063374751745779 := by
  unfold tailWord_1536607
  simp only [CollatzResearch.WordTrace]
  refine ⟨56044661544142745427464075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37363107696095163618309383 56044661544142745427464075)
  ·
    refine ⟨84066992316214118141196113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56044661544142745427464075 84066992316214118141196113)
    ·
      refine ⟨63050244237160588605897085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84066992316214118141196113 63050244237160588605897085)
      ·
        refine ⟨23643841588935220727211407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63050244237160588605897085 23643841588935220727211407)
        ·
          refine ⟨35465762383402831090817111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23643841588935220727211407 35465762383402831090817111)
          ·
            refine ⟨53198643575104246636225667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35465762383402831090817111 53198643575104246636225667)
            ·
              refine ⟨79797965362656369954338501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53198643575104246636225667 79797965362656369954338501)
              ·
                refine ⟨14962118505498069366438469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79797965362656369954338501 14962118505498069366438469)
                ·
                  refine ⟨2805397219780888006207213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14962118505498069366438469 2805397219780888006207213)
                  ·
                    refine ⟨1052023957417833002327705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2805397219780888006207213 1052023957417833002327705)
                    ·
                      refine ⟨789017968063374751745779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1052023957417833002327705 789017968063374751745779)
                      ·
                        rfl

theorem cell23_1536607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 3, 2].length) (baseStart_1536607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536607 prefixEnd_1536607 := by exact prefixLift 1536607
  have htrace : WordTrace (prefixWord ++ tailWord_1536607) baseStart_1536607 baseEnd_1536607 := by
    simpa [prefixWord, tailWord_1536607, baseEnd_1536607] using wordTrace_append hprefix tailTrace_1536607
  have hstable : (prefixWord ++ tailWord_1536607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536607).length < 2 ^ (prefixWord ++ tailWord_1536607).sum := by decide
  have hdescent : baseEnd_1536607 < baseStart_1536607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536624 : List Nat := [2, 1, 1, 1, 7, 1, 1, 1, 1, 5, 2]
def baseStart_1536624 : Nat := 118140960795 + 1536624 * 2 ^ 59
def prefixEnd_1536624 : Nat := 4983230072969 + 3 ^ 40 * 1536624 * 2
def baseEnd_1536624 : Nat := 789026697234501185233201

theorem tailTrace_1536624 : CollatzResearch.WordTrace tailWord_1536624 prefixEnd_1536624 789026697234501185233201 := by
  unfold tailWord_1536624
  simp only [CollatzResearch.WordTrace]
  refine ⟨28022640792540578665416463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37363521056720771553888617 28022640792540578665416463)
  ·
    refine ⟨42033961188810867998124695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28022640792540578665416463 42033961188810867998124695)
    ·
      refine ⟨63050941783216301997187043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42033961188810867998124695 63050941783216301997187043)
      ·
        refine ⟨94576412674824452995780565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63050941783216301997187043 94576412674824452995780565)
        ·
          refine ⟨2216634672066198117088607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 94576412674824452995780565 2216634672066198117088607)
          ·
            refine ⟨3324952008099297175632911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2216634672066198117088607 3324952008099297175632911)
            ·
              refine ⟨4987428012148945763449367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3324952008099297175632911 4987428012148945763449367)
              ·
                refine ⟨7481142018223418645174051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4987428012148945763449367 7481142018223418645174051)
                ·
                  refine ⟨11221713027335127967761077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7481142018223418645174051 11221713027335127967761077)
                  ·
                    refine ⟨1052035596312668246977601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11221713027335127967761077 1052035596312668246977601)
                    ·
                      refine ⟨789026697234501185233201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1052035596312668246977601 789026697234501185233201)
                      ·
                        rfl

theorem cell23_1536624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 1, 5, 2].length) (baseStart_1536624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536624 prefixEnd_1536624 := by exact prefixLift 1536624
  have htrace : WordTrace (prefixWord ++ tailWord_1536624) baseStart_1536624 baseEnd_1536624 := by
    simpa [prefixWord, tailWord_1536624, baseEnd_1536624] using wordTrace_append hprefix tailTrace_1536624
  have hstable : (prefixWord ++ tailWord_1536624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536624).length < 2 ^ (prefixWord ++ tailWord_1536624).sum := by decide
  have hdescent : baseEnd_1536624 < baseStart_1536624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536647 : List Nat := [1, 1, 4, 2, 1, 2, 3, 1, 4, 4]
def baseStart_1536647 : Nat := 118140960795 + 1536647 * 2 ^ 59
def prefixEnd_1536647 : Nat := 4983230072969 + 3 ^ 40 * 1536647 * 2
def baseEnd_1536647 : Nat := 263012835763184865081865

theorem tailTrace_1536647 : CollatzResearch.WordTrace tailWord_1536647 prefixEnd_1536647 263012835763184865081865 := by
  unfold tailWord_1536647
  simp only [CollatzResearch.WordTrace]
  refine ⟨56046120463997832258920195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37364080309331888172613463 56046120463997832258920195)
  ·
    refine ⟨84069180695996748388380293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56046120463997832258920195 84069180695996748388380293)
    ·
      refine ⟨15762971380499390322821305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84069180695996748388380293 15762971380499390322821305)
      ·
        refine ⟨11822228535374542742115979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15762971380499390322821305 11822228535374542742115979)
        ·
          refine ⟨17733342803061814113173969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11822228535374542742115979 17733342803061814113173969)
          ·
            refine ⟨13300007102296360584880477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17733342803061814113173969 13300007102296360584880477)
            ·
              refine ⟨4987502663361135219330179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13300007102296360584880477 4987502663361135219330179)
              ·
                refine ⟨7481253995041702828995269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4987502663361135219330179 7481253995041702828995269)
                ·
                  refine ⟨1402735124070319280436613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7481253995041702828995269 1402735124070319280436613)
                  ·
                    refine ⟨263012835763184865081865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1402735124070319280436613 263012835763184865081865)
                    ·
                      rfl

theorem cell23_1536647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_1536647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536647 prefixEnd_1536647 := by exact prefixLift 1536647
  have htrace : WordTrace (prefixWord ++ tailWord_1536647) baseStart_1536647 baseEnd_1536647 := by
    simpa [prefixWord, tailWord_1536647, baseEnd_1536647] using wordTrace_append hprefix tailTrace_1536647
  have hstable : (prefixWord ++ tailWord_1536647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536647).length < 2 ^ (prefixWord ++ tailWord_1536647).sum := by decide
  have hdescent : baseEnd_1536647 < baseStart_1536647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536682 : List Nat := [3, 1, 5, 2, 1, 2, 1, 3, 1, 1, 3]
def baseStart_1536682 : Nat := 118140960795 + 1536682 * 2 ^ 59
def prefixEnd_1536682 : Nat := 4983230072969 + 3 ^ 40 * 1536682 * 2
def baseEnd_1536682 : Nat := 789056479112461958307935

theorem tailTrace_1536682 : CollatzResearch.WordTrace tailWord_1536682 prefixEnd_1536682 789056479112461958307935 := by
  unfold tailWord_1536682
  simp only [CollatzResearch.WordTrace]
  refine ⟨14011849254717758309111075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37364931345914022157629533 14011849254717758309111075)
  ·
    refine ⟨21017773882076637463666613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14011849254717758309111075 21017773882076637463666613)
    ·
      refine ⟨1970416301444684762218745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21017773882076637463666613 1970416301444684762218745)
      ·
        refine ⟨1477812226083513571664059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1970416301444684762218745 1477812226083513571664059)
        ·
          refine ⟨2216718339125270357496089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1477812226083513571664059 2216718339125270357496089)
          ·
            refine ⟨1662538754343952768122067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2216718339125270357496089 1662538754343952768122067)
            ·
              refine ⟨2493808131515929152183101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1662538754343952768122067 2493808131515929152183101)
              ·
                refine ⟨935178049318473432068663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2493808131515929152183101 935178049318473432068663)
                ·
                  refine ⟨1402767073977710148102995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 935178049318473432068663 1402767073977710148102995)
                  ·
                    refine ⟨2104150610966565222154493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1402767073977710148102995 2104150610966565222154493)
                    ·
                      refine ⟨789056479112461958307935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2104150610966565222154493 789056479112461958307935)
                      ·
                        rfl

theorem cell23_1536682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_1536682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536682 prefixEnd_1536682 := by exact prefixLift 1536682
  have htrace : WordTrace (prefixWord ++ tailWord_1536682) baseStart_1536682 baseEnd_1536682 := by
    simpa [prefixWord, tailWord_1536682, baseEnd_1536682] using wordTrace_append hprefix tailTrace_1536682
  have hstable : (prefixWord ++ tailWord_1536682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536682).length < 2 ^ (prefixWord ++ tailWord_1536682).sum := by decide
  have hdescent : baseEnd_1536682 < baseStart_1536682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536690 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 1, 9]
def baseStart_1536690 : Nat := 118140960795 + 1536690 * 2 ^ 59
def prefixEnd_1536690 : Nat := 4983230072969 + 3 ^ 40 * 1536690 * 2
def baseEnd_1536690 : Nat := 263020195652565975669299

theorem tailTrace_1536690 : CollatzResearch.WordTrace tailWord_1536690 prefixEnd_1536690 263020195652565975669299 := by
  unfold tailWord_1536690
  simp only [CollatzResearch.WordTrace]
  refine ⟨14011922200710512650683881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37365125868561367068490349 14011922200710512650683881)
  ·
    refine ⟨10508941650532884488012911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14011922200710512650683881 10508941650532884488012911)
    ·
      refine ⟨15763412475799326732019367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10508941650532884488012911 15763412475799326732019367)
      ·
        refine ⟨23645118713698990098029051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15763412475799326732019367 23645118713698990098029051)
        ·
          refine ⟨35467678070548485147043577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23645118713698990098029051 35467678070548485147043577)
          ·
            refine ⟨26600758552911363860282683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35467678070548485147043577 26600758552911363860282683)
            ·
              refine ⟨39901137829367045790424025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26600758552911363860282683 39901137829367045790424025)
              ·
                refine ⟨29925853372025284342818019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39901137829367045790424025 29925853372025284342818019)
                ·
                  refine ⟨44888780058037926514227029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29925853372025284342818019 44888780058037926514227029)
                  ·
                    refine ⟨263020195652565975669299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 44888780058037926514227029 263020195652565975669299)
                    ·
                      rfl

theorem cell23_1536690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_1536690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536690 prefixEnd_1536690 := by exact prefixLift 1536690
  have htrace : WordTrace (prefixWord ++ tailWord_1536690) baseStart_1536690 baseEnd_1536690 := by
    simpa [prefixWord, tailWord_1536690, baseEnd_1536690] using wordTrace_append hprefix tailTrace_1536690
  have hstable : (prefixWord ++ tailWord_1536690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536690).length < 2 ^ (prefixWord ++ tailWord_1536690).sum := by decide
  have hdescent : baseEnd_1536690 < baseStart_1536690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536704 : List Nat := [2, 1, 1, 2, 4, 2, 2, 1, 4, 1, 3]
def baseStart_1536704 : Nat := 118140960795 + 1536704 * 2 ^ 59
def prefixEnd_1536704 : Nat := 4983230072969 + 3 ^ 40 * 1536704 * 2
def baseEnd_1536704 : Nat := 789067775686860872232833

theorem tailTrace_1536704 : CollatzResearch.WordTrace tailWord_1536704 prefixEnd_1536704 789067775686860872232833 := by
  unfold tailWord_1536704
  simp only [CollatzResearch.WordTrace]
  refine ⟨28024099712395665496872583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37365466283194220662496777 28024099712395665496872583)
  ·
    refine ⟨42036149568593498245308875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28024099712395665496872583 42036149568593498245308875)
    ·
      refine ⟨63054224352890247367963313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42036149568593498245308875 63054224352890247367963313)
      ·
        refine ⟨47290668264667685525972485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63054224352890247367963313 47290668264667685525972485)
        ·
          refine ⟨8867000299625191036119841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47290668264667685525972485 8867000299625191036119841)
          ·
            refine ⟨6650250224718893277089881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8867000299625191036119841 6650250224718893277089881)
            ·
              refine ⟨4987687668539169957817411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6650250224718893277089881 4987687668539169957817411)
              ·
                refine ⟨7481531502808754936726117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4987687668539169957817411 7481531502808754936726117)
                ·
                  refine ⟨1402787156776641550636147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7481531502808754936726117 1402787156776641550636147)
                  ·
                    refine ⟨2104180735164962325954221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1402787156776641550636147 2104180735164962325954221)
                    ·
                      refine ⟨789067775686860872232833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2104180735164962325954221 789067775686860872232833)
                      ·
                        rfl

theorem cell23_1536704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 4, 1, 3].length) (baseStart_1536704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536704 prefixEnd_1536704 := by exact prefixLift 1536704
  have htrace : WordTrace (prefixWord ++ tailWord_1536704) baseStart_1536704 baseEnd_1536704 := by
    simpa [prefixWord, tailWord_1536704, baseEnd_1536704] using wordTrace_append hprefix tailTrace_1536704
  have hstable : (prefixWord ++ tailWord_1536704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536704).length < 2 ^ (prefixWord ++ tailWord_1536704).sum := by decide
  have hdescent : baseEnd_1536704 < baseStart_1536704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536720 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 6, 6]
def baseStart_1536720 : Nat := 118140960795 + 1536720 * 2 ^ 59
def prefixEnd_1536720 : Nat := 4983230072969 + 3 ^ 40 * 1536720 * 2
def baseEnd_1536720 : Nat := 263025330459110936544253

theorem tailTrace_1536720 : CollatzResearch.WordTrace tailWord_1536720 prefixEnd_1536720 263025330459110936544253 := by
  unfold tailWord_1536720
  simp only [CollatzResearch.WordTrace]
  refine ⟨28024391496366682863163807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37365855328488910484218409 28024391496366682863163807)
  ·
    refine ⟨42036587244550024294745711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28024391496366682863163807 42036587244550024294745711)
    ·
      refine ⟨63054880866825036442118567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42036587244550024294745711 63054880866825036442118567)
      ·
        refine ⟨94582321300237554663177851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63054880866825036442118567 94582321300237554663177851)
        ·
          refine ⟨141873481950356331994766777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94582321300237554663177851 141873481950356331994766777)
          ·
            refine ⟨106405111462767248996075083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141873481950356331994766777 106405111462767248996075083)
            ·
              refine ⟨159607667194150873494112625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106405111462767248996075083 159607667194150873494112625)
              ·
                refine ⟨119705750395613155120584469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159607667194150873494112625 119705750395613155120584469)
                ·
                  refine ⟨5611207049794366646277397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 119705750395613155120584469 5611207049794366646277397)
                  ·
                    refine ⟨263025330459110936544253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5611207049794366646277397 263025330459110936544253)
                    ·
                      rfl

theorem cell23_1536720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 6, 6].length) (baseStart_1536720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536720 prefixEnd_1536720 := by exact prefixLift 1536720
  have htrace : WordTrace (prefixWord ++ tailWord_1536720) baseStart_1536720 baseEnd_1536720 := by
    simpa [prefixWord, tailWord_1536720, baseEnd_1536720] using wordTrace_append hprefix tailTrace_1536720
  have hstable : (prefixWord ++ tailWord_1536720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536720).length < 2 ^ (prefixWord ++ tailWord_1536720).sum := by decide
  have hdescent : baseEnd_1536720 < baseStart_1536720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536725 : List Nat := [1, 3, 2, 5, 2, 1, 1, 2, 1, 2, 3]
def baseStart_1536725 : Nat := 118140960795 + 1536725 * 2 ^ 59
def prefixEnd_1536725 : Nat := 4983230072969 + 3 ^ 40 * 1536725 * 2
def baseEnd_1536725 : Nat := 789078558780605290070237

theorem tailTrace_1536725 : CollatzResearch.WordTrace tailWord_1536725 prefixEnd_1536725 789078558780605290070237 := by
  unfold tailWord_1536725
  simp only [CollatzResearch.WordTrace]
  refine ⟨56048965357715251580259629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37365976905143501053506419 56048965357715251580259629)
  ·
    refine ⟨21018362009143219342597361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56048965357715251580259629 21018362009143219342597361)
    ·
      refine ⟨15763771506857414506948021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21018362009143219342597361 15763771506857414506948021)
      ·
        refine ⟨1477853578767882610026377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15763771506857414506948021 1477853578767882610026377)
        ·
          refine ⟨1108390184075911957519783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1477853578767882610026377 1108390184075911957519783)
          ·
            refine ⟨1662585276113867936279675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1108390184075911957519783 1662585276113867936279675)
            ·
              refine ⟨2493877914170801904419513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1662585276113867936279675 2493877914170801904419513)
              ·
                refine ⟨1870408435628101428314635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2493877914170801904419513 1870408435628101428314635)
                ·
                  refine ⟨2805612653442152142471953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1870408435628101428314635 2805612653442152142471953)
                  ·
                    refine ⟨2104209490081614106853965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2805612653442152142471953 2104209490081614106853965)
                    ·
                      refine ⟨789078558780605290070237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2104209490081614106853965 789078558780605290070237)
                      ·
                        rfl

theorem cell23_1536725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_1536725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536725 prefixEnd_1536725 := by exact prefixLift 1536725
  have htrace : WordTrace (prefixWord ++ tailWord_1536725) baseStart_1536725 baseEnd_1536725 := by
    simpa [prefixWord, tailWord_1536725, baseEnd_1536725] using wordTrace_append hprefix tailTrace_1536725
  have hstable : (prefixWord ++ tailWord_1536725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536725).length < 2 ^ (prefixWord ++ tailWord_1536725).sum := by decide
  have hdescent : baseEnd_1536725 < baseStart_1536725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536756 : List Nat := [2, 6, 1, 1, 2, 2, 2, 2, 1, 2, 2]
def baseStart_1536756 : Nat := 118140960795 + 1536756 * 2 ^ 59
def prefixEnd_1536756 : Nat := 4983230072969 + 3 ^ 40 * 1536756 * 2
def baseEnd_1536756 : Nat := 789094476680894668782595

theorem tailTrace_1536756 : CollatzResearch.WordTrace tailWord_1536756 prefixEnd_1536756 789094476680894668782595 := by
  unfold tailWord_1536756
  simp only [CollatzResearch.WordTrace]
  refine ⟨28025048010301471937319061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37366730680401962583092081 28025048010301471937319061)
  ·
    refine ⟨1313674125482881497061831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28025048010301471937319061 1313674125482881497061831)
    ·
      refine ⟨1970511188224322245592747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1313674125482881497061831 1970511188224322245592747)
      ·
        refine ⟨2955766782336483368389121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1970511188224322245592747 2955766782336483368389121)
        ·
          refine ⟨2216825086752362526291841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2955766782336483368389121 2216825086752362526291841)
          ·
            refine ⟨1662618815064271894718881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2216825086752362526291841 1662618815064271894718881)
            ·
              refine ⟨1246964111298203921039161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1662618815064271894718881 1246964111298203921039161)
              ·
                refine ⟨935223083473652940779371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1246964111298203921039161 935223083473652940779371)
                ·
                  refine ⟨1402834625210479411169057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 935223083473652940779371 1402834625210479411169057)
                  ·
                    refine ⟨1052125968907859558376793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1402834625210479411169057 1052125968907859558376793)
                    ·
                      refine ⟨789094476680894668782595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1052125968907859558376793 789094476680894668782595)
                      ·
                        rfl

theorem cell23_1536756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_1536756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536756 prefixEnd_1536756 := by exact prefixLift 1536756
  have htrace : WordTrace (prefixWord ++ tailWord_1536756) baseStart_1536756 baseEnd_1536756 := by
    simpa [prefixWord, tailWord_1536756, baseEnd_1536756] using wordTrace_append hprefix tailTrace_1536756
  have hstable : (prefixWord ++ tailWord_1536756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536756).length < 2 ^ (prefixWord ++ tailWord_1536756).sum := by decide
  have hdescent : baseEnd_1536756 < baseStart_1536756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536777 : List Nat := [1, 2, 1, 1, 3, 2, 3, 1, 1, 5, 3]
def baseStart_1536777 : Nat := 118140960795 + 1536777 * 2 ^ 59
def prefixEnd_1536777 : Nat := 4983230072969 + 3 ^ 40 * 1536777 * 2
def baseEnd_1536777 : Nat := 789105259774639086619997

theorem tailTrace_1536777 : CollatzResearch.WordTrace tailWord_1536777 prefixEnd_1536777 789105259774639086619997 := by
  unfold tailWord_1536777
  simp only [CollatzResearch.WordTrace]
  refine ⟨56050861953526864461152585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37367241302351242974101723 56050861953526864461152585)
  ·
    refine ⟨42038146465145148345864439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56050861953526864461152585 42038146465145148345864439)
    ·
      refine ⟨63057219697717722518796659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42038146465145148345864439 63057219697717722518796659)
      ·
        refine ⟨94585829546576583778194989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63057219697717722518796659 94585829546576583778194989)
        ·
          refine ⟨35469686079966218916823121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94585829546576583778194989 35469686079966218916823121)
          ·
            refine ⟨26602264559974664187617341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35469686079966218916823121 26602264559974664187617341)
            ·
              refine ⟨9975849209990499070356503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26602264559974664187617341 9975849209990499070356503)
              ·
                refine ⟨14963773814985748605534755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9975849209990499070356503 14963773814985748605534755)
                ·
                  refine ⟨22445660722478622908302133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14963773814985748605534755 22445660722478622908302133)
                  ·
                    refine ⟨2104280692732370897653325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22445660722478622908302133 2104280692732370897653325)
                    ·
                      refine ⟨789105259774639086619997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2104280692732370897653325 789105259774639086619997)
                      ·
                        rfl

theorem cell23_1536777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 5, 3].length) (baseStart_1536777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536777 prefixEnd_1536777 := by exact prefixLift 1536777
  have htrace : WordTrace (prefixWord ++ tailWord_1536777) baseStart_1536777 baseEnd_1536777 := by
    simpa [prefixWord, tailWord_1536777, baseEnd_1536777] using wordTrace_append hprefix tailTrace_1536777
  have hstable : (prefixWord ++ tailWord_1536777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536777).length < 2 ^ (prefixWord ++ tailWord_1536777).sum := by decide
  have hdescent : baseEnd_1536777 < baseStart_1536777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536857 : List Nat := [1, 2, 1, 2, 2, 4, 1, 2, 8]
def baseStart_1536857 : Nat := 118140960795 + 1536857 * 2 ^ 59
def prefixEnd_1536857 : Nat := 4983230072969 + 3 ^ 40 * 1536857 * 2
def baseEnd_1536857 : Nat := 87682926469666530402181

theorem tailTrace_1536857 : CollatzResearch.WordTrace tailWord_1536857 prefixEnd_1536857 87682926469666530402181 := by
  unfold tailWord_1536857
  simp only [CollatzResearch.WordTrace]
  refine ⟨56053779793237038124064825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37369186528824692082709883 56053779793237038124064825)
  ·
    refine ⟨42040334844927778593048619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56053779793237038124064825 42040334844927778593048619)
    ·
      refine ⟨63060502267391667889572929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42040334844927778593048619 63060502267391667889572929)
      ·
        refine ⟨47295376700543750917179697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63060502267391667889572929 47295376700543750917179697)
        ·
          refine ⟨35471532525407813187884773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47295376700543750917179697 35471532525407813187884773)
          ·
            refine ⟨6650912348513964972728395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35471532525407813187884773 6650912348513964972728395)
            ·
              refine ⟨9976368522770947459092593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6650912348513964972728395 9976368522770947459092593)
              ·
                refine ⟨7482276392078210594319445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9976368522770947459092593 7482276392078210594319445)
                ·
                  refine ⟨87682926469666530402181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7482276392078210594319445 87682926469666530402181)
                  ·
                    rfl

theorem cell23_1536857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 8].length) (baseStart_1536857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536857 prefixEnd_1536857 := by exact prefixLift 1536857
  have htrace : WordTrace (prefixWord ++ tailWord_1536857) baseStart_1536857 baseEnd_1536857 := by
    simpa [prefixWord, tailWord_1536857, baseEnd_1536857] using wordTrace_append hprefix tailTrace_1536857
  have hstable : (prefixWord ++ tailWord_1536857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536857).length < 2 ^ (prefixWord ++ tailWord_1536857).sum := by decide
  have hdescent : baseEnd_1536857 < baseStart_1536857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536871 : List Nat := [1, 1, 5, 1, 2, 3, 1, 2, 2, 2, 3]
def baseStart_1536871 : Nat := 118140960795 + 1536871 * 2 ^ 59
def prefixEnd_1536871 : Nat := 4983230072969 + 3 ^ 40 * 1536871 * 2
def baseEnd_1536871 : Nat := 789153526956161718844565

theorem tailTrace_1536871 : CollatzResearch.WordTrace tailWord_1536871 prefixEnd_1536871 789153526956161718844565 := by
  unfold tailWord_1536871
  simp only [CollatzResearch.WordTrace]
  refine ⟨56054290415186318515074467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37369526943457545676716311 56054290415186318515074467)
  ·
    refine ⟨84081435622779477772611701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56054290415186318515074467 84081435622779477772611701)
    ·
      refine ⟨7882634589635576041182347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84081435622779477772611701 7882634589635576041182347)
      ·
        refine ⟨11823951884453364061773521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7882634589635576041182347 11823951884453364061773521)
        ·
          refine ⟨8867963913340023046330141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11823951884453364061773521 8867963913340023046330141)
          ·
            refine ⟨3325486467502508642373803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8867963913340023046330141 3325486467502508642373803)
            ·
              refine ⟨4988229701253762963560705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3325486467502508642373803 4988229701253762963560705)
              ·
                refine ⟨3741172275940322222670529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4988229701253762963560705 3741172275940322222670529)
                ·
                  refine ⟨2805879206955241667002897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3741172275940322222670529 2805879206955241667002897)
                  ·
                    refine ⟨2104409405216431250252173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2805879206955241667002897 2104409405216431250252173)
                    ·
                      refine ⟨789153526956161718844565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2104409405216431250252173 789153526956161718844565)
                      ·
                        rfl

theorem cell23_1536871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_1536871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536871 prefixEnd_1536871 := by exact prefixLift 1536871
  have htrace : WordTrace (prefixWord ++ tailWord_1536871) baseStart_1536871 baseEnd_1536871 := by
    simpa [prefixWord, tailWord_1536871, baseEnd_1536871] using wordTrace_append hprefix tailTrace_1536871
  have hstable : (prefixWord ++ tailWord_1536871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536871).length < 2 ^ (prefixWord ++ tailWord_1536871).sum := by decide
  have hdescent : baseEnd_1536871 < baseStart_1536871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536947 : List Nat := [1, 1, 1, 2, 3, 1, 2, 12]
def baseStart_1536947 : Nat := 118140960795 + 1536947 * 2 ^ 59
def prefixEnd_1536947 : Nat := 4983230072969 + 3 ^ 40 * 1536947 * 2
def baseEnd_1536947 : Nat := 29229353758737163759045

theorem tailTrace_1536947 : CollatzResearch.WordTrace tailWord_1536947 prefixEnd_1536947 29229353758737163759045 := by
  unfold tailWord_1536947
  simp only [CollatzResearch.WordTrace]
  refine ⟨56057062362910983494841095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37371374908607322329894063 56057062362910983494841095)
  ·
    refine ⟨84085593544366475242261643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56057062362910983494841095 84085593544366475242261643)
    ·
      refine ⟨126128390316549712863392465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84085593544366475242261643 126128390316549712863392465)
      ·
        refine ⟨94596292737412284647544349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126128390316549712863392465 94596292737412284647544349)
        ·
          refine ⟨35473609776529606742829131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94596292737412284647544349 35473609776529606742829131)
          ·
            refine ⟨53210414664794410114243697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35473609776529606742829131 53210414664794410114243697)
            ·
              refine ⟨39907810998595807585682773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53210414664794410114243697 39907810998595807585682773)
              ·
                refine ⟨29229353758737163759045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 39907810998595807585682773 29229353758737163759045)
                ·
                  rfl

theorem cell23_1536947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 12].length) (baseStart_1536947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536947 prefixEnd_1536947 := by exact prefixLift 1536947
  have htrace : WordTrace (prefixWord ++ tailWord_1536947) baseStart_1536947 baseEnd_1536947 := by
    simpa [prefixWord, tailWord_1536947, baseEnd_1536947] using wordTrace_append hprefix tailTrace_1536947
  have hstable : (prefixWord ++ tailWord_1536947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536947).length < 2 ^ (prefixWord ++ tailWord_1536947).sum := by decide
  have hdescent : baseEnd_1536947 < baseStart_1536947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536951 : List Nat := [1, 1, 3, 1, 3, 1, 4, 3, 2, 4]
def baseStart_1536951 : Nat := 118140960795 + 1536951 * 2 ^ 59
def prefixEnd_1536951 : Nat := 4983230072969 + 3 ^ 40 * 1536951 * 2
def baseEnd_1536951 : Nat := 263064868469507135281399

theorem tailTrace_1536951 : CollatzResearch.WordTrace tailWord_1536951 prefixEnd_1536951 263064868469507135281399 := by
  unfold tailWord_1536951
  simp only [CollatzResearch.WordTrace]
  refine ⟨56057208254896492177986707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37371472169930994785324471 56057208254896492177986707)
  ·
    refine ⟨84085812382344738266980061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56057208254896492177986707 84085812382344738266980061)
    ·
      refine ⟨31532179643379276850117523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84085812382344738266980061 31532179643379276850117523)
      ·
        refine ⟨47298269465068915275176285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31532179643379276850117523 47298269465068915275176285)
        ·
          refine ⟨17736851049400843228191107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47298269465068915275176285 17736851049400843228191107)
          ·
            refine ⟨26605276574101264842286661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17736851049400843228191107 26605276574101264842286661)
            ·
              refine ⟨4988489357643987157928749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26605276574101264842286661 4988489357643987157928749)
              ·
                refine ⟨1870683509116495184223281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4988489357643987157928749 1870683509116495184223281)
                ·
                  refine ⟨1403012631837371388167461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1870683509116495184223281 1403012631837371388167461)
                  ·
                    refine ⟨263064868469507135281399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1403012631837371388167461 263064868469507135281399)
                    ·
                      rfl

theorem cell23_1536951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 2, 4].length) (baseStart_1536951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536951 prefixEnd_1536951 := by exact prefixLift 1536951
  have htrace : WordTrace (prefixWord ++ tailWord_1536951) baseStart_1536951 baseEnd_1536951 := by
    simpa [prefixWord, tailWord_1536951, baseEnd_1536951] using wordTrace_append hprefix tailTrace_1536951
  have hstable : (prefixWord ++ tailWord_1536951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536951).length < 2 ^ (prefixWord ++ tailWord_1536951).sum := by decide
  have hdescent : baseEnd_1536951 < baseStart_1536951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536975 : List Nat := [1, 1, 2, 1, 1, 6, 1, 5, 1, 2, 2]
def baseStart_1536975 : Nat := 118140960795 + 1536975 * 2 ^ 59
def prefixEnd_1536975 : Nat := 4983230072969 + 3 ^ 40 * 1536975 * 2
def baseEnd_1536975 : Nat := 789206928944229311944087

theorem tailTrace_1536975 : CollatzResearch.WordTrace tailWord_1536975 prefixEnd_1536975 789206928944229311944087 := by
  unfold tailWord_1536975
  simp only [CollatzResearch.WordTrace]
  refine ⟨56058083606809544276860379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37372055737873029517906919 56058083606809544276860379)
  ·
    refine ⟨84087125410214316415290569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56058083606809544276860379 84087125410214316415290569)
    ·
      refine ⟨63065344057660737311467927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84087125410214316415290569 63065344057660737311467927)
      ·
        refine ⟨94598016086491105967201891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63065344057660737311467927 94598016086491105967201891)
        ·
          refine ⟨141897024129736658950802837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94598016086491105967201891 141897024129736658950802837)
          ·
            refine ⟨6651423006081405888318883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 141897024129736658950802837 6651423006081405888318883)
            ·
              refine ⟨9977134509122108832478325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6651423006081405888318883 9977134509122108832478325)
              ·
                refine ⟨935356360230197703044843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9977134509122108832478325 935356360230197703044843)
                ·
                  refine ⟨1403034540345296554567265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 935356360230197703044843 1403034540345296554567265)
                  ·
                    refine ⟨1052275905258972415925449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1403034540345296554567265 1052275905258972415925449)
                    ·
                      refine ⟨789206928944229311944087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1052275905258972415925449 789206928944229311944087)
                      ·
                        rfl

theorem cell23_1536975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 5, 1, 2, 2].length) (baseStart_1536975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1536975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1536975 prefixEnd_1536975 := by exact prefixLift 1536975
  have htrace : WordTrace (prefixWord ++ tailWord_1536975) baseStart_1536975 baseEnd_1536975 := by
    simpa [prefixWord, tailWord_1536975, baseEnd_1536975] using wordTrace_append hprefix tailTrace_1536975
  have hstable : (prefixWord ++ tailWord_1536975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536975).length < 2 ^ (prefixWord ++ tailWord_1536975).sum := by decide
  have hdescent : baseEnd_1536975 < baseStart_1536975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537108 : List Nat := [2, 4, 1, 1, 1, 1, 3, 1, 2, 5, 2]
def baseStart_1537108 : Nat := 118140960795 + 1537108 * 2 ^ 59
def prefixEnd_1537108 : Nat := 4983230072969 + 3 ^ 40 * 1537108 * 2
def baseEnd_1537108 : Nat := 789275221871277291580975

theorem tailTrace_1537108 : CollatzResearch.WordTrace tailWord_1537108 prefixEnd_1537108 789275221871277291580975 := by
  unfold tailWord_1537108
  simp only [CollatzResearch.WordTrace]
  refine ⟨28031467257663853995725989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37375289676885138660967985 28031467257663853995725989)
  ·
    refine ⟨5255900110811972624198623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28031467257663853995725989 5255900110811972624198623)
    ·
      refine ⟨7883850166217958936297935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5255900110811972624198623 7883850166217958936297935)
      ·
        refine ⟨11825775249326938404446903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7883850166217958936297935 11825775249326938404446903)
        ·
          refine ⟨17738662873990407606670355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11825775249326938404446903 17738662873990407606670355)
          ·
            refine ⟨26607994310985611410005533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17738662873990407606670355 26607994310985611410005533)
            ·
              refine ⟨9977997866619604278752075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26607994310985611410005533 9977997866619604278752075)
              ·
                refine ⟨14966996799929406418128113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9977997866619604278752075 14966996799929406418128113)
                ·
                  refine ⟨11225247599947054813596085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14966996799929406418128113 11225247599947054813596085)
                  ·
                    refine ⟨1052366962495036388774633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11225247599947054813596085 1052366962495036388774633)
                    ·
                      refine ⟨789275221871277291580975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1052366962495036388774633 789275221871277291580975)
                      ·
                        rfl

theorem cell23_1537108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_1537108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537108 prefixEnd_1537108 := by exact prefixLift 1537108
  have htrace : WordTrace (prefixWord ++ tailWord_1537108) baseStart_1537108 baseEnd_1537108 := by
    simpa [prefixWord, tailWord_1537108, baseEnd_1537108] using wordTrace_append hprefix tailTrace_1537108
  have hstable : (prefixWord ++ tailWord_1537108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537108).length < 2 ^ (prefixWord ++ tailWord_1537108).sum := by decide
  have hdescent : baseEnd_1537108 < baseStart_1537108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537121 : List Nat := [1, 2, 3, 1, 1, 2, 2, 2, 4, 1, 4]
def baseStart_1537121 : Nat := 118140960795 + 1537121 * 2 ^ 59
def prefixEnd_1537121 : Nat := 4983230072969 + 3 ^ 40 * 1537121 * 2
def baseEnd_1537121 : Nat := 789281897119785740718415

theorem tailTrace_1537121 : CollatzResearch.WordTrace tailWord_1537121 prefixEnd_1537121 789281897119785740718415 := by
  unfold tailWord_1537121
  simp only [CollatzResearch.WordTrace]
  refine ⟨56063408664280611211675217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37375605776187074141116811 56063408664280611211675217)
  ·
    refine ⟨42047556498210458408756413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56063408664280611211675217 42047556498210458408756413)
    ·
      refine ⟨15767833686828921903283655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42047556498210458408756413 15767833686828921903283655)
      ·
        refine ⟨23651750530243382854925483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15767833686828921903283655 23651750530243382854925483)
        ·
          refine ⟨35477625795365074282388225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23651750530243382854925483 35477625795365074282388225)
          ·
            refine ⟨26608219346523805711791169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35477625795365074282388225 26608219346523805711791169)
            ·
              refine ⟨19956164509892854283843377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26608219346523805711791169 19956164509892854283843377)
              ·
                refine ⟨14967123382419640712882533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19956164509892854283843377 14967123382419640712882533)
                ·
                  refine ⟨2806335634203682633665475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14967123382419640712882533 2806335634203682633665475)
                  ·
                    refine ⟨4209503451305523950498213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2806335634203682633665475 4209503451305523950498213)
                    ·
                      refine ⟨789281897119785740718415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4209503451305523950498213 789281897119785740718415)
                      ·
                        rfl

theorem cell23_1537121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_1537121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537121 prefixEnd_1537121 := by exact prefixLift 1537121
  have htrace : WordTrace (prefixWord ++ tailWord_1537121) baseStart_1537121 baseEnd_1537121 := by
    simpa [prefixWord, tailWord_1537121, baseEnd_1537121] using wordTrace_append hprefix tailTrace_1537121
  have hstable : (prefixWord ++ tailWord_1537121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537121).length < 2 ^ (prefixWord ++ tailWord_1537121).sum := by decide
  have hdescent : baseEnd_1537121 < baseStart_1537121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537138 : List Nat := [3, 2, 1, 2, 2, 1, 1, 2, 1, 6, 2]
def baseStart_1537138 : Nat := 118140960795 + 1537138 * 2 ^ 59
def prefixEnd_1537138 : Nat := 4983230072969 + 3 ^ 40 * 1537138 * 2
def baseEnd_1537138 : Nat := 789290626290912174205837

theorem tailTrace_1537138 : CollatzResearch.WordTrace tailWord_1537138 prefixEnd_1537138 789290626290912174205837 := by
  unfold tailWord_1537138
  simp only [CollatzResearch.WordTrace]
  refine ⟨14016007176304755778761017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37376019136812682076696045 14016007176304755778761017)
  ·
    refine ⟨10512005382228566834070763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14016007176304755778761017 10512005382228566834070763)
    ·
      refine ⟨15768008073342850251106145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10512005382228566834070763 15768008073342850251106145)
      ·
        refine ⟨11826006055007137688329609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15768008073342850251106145 11826006055007137688329609)
        ·
          refine ⟨8869504541255353266247207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11826006055007137688329609 8869504541255353266247207)
          ·
            refine ⟨13304256811883029899370811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8869504541255353266247207 13304256811883029899370811)
            ·
              refine ⟨19956385217824544849056217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13304256811883029899370811 19956385217824544849056217)
              ·
                refine ⟨14967288913368408636792163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19956385217824544849056217 14967288913368408636792163)
                ·
                  refine ⟨22450933370052612955188245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14967288913368408636792163 22450933370052612955188245)
                  ·
                    refine ⟨1052387501721216232274449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22450933370052612955188245 1052387501721216232274449)
                    ·
                      refine ⟨789290626290912174205837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1052387501721216232274449 789290626290912174205837)
                      ·
                        rfl

theorem cell23_1537138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_1537138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537138 prefixEnd_1537138 := by exact prefixLift 1537138
  have htrace : WordTrace (prefixWord ++ tailWord_1537138) baseStart_1537138 baseEnd_1537138 := by
    simpa [prefixWord, tailWord_1537138, baseEnd_1537138] using wordTrace_append hprefix tailTrace_1537138
  have hstable : (prefixWord ++ tailWord_1537138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537138).length < 2 ^ (prefixWord ++ tailWord_1537138).sum := by decide
  have hdescent : baseEnd_1537138 < baseStart_1537138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537150 : List Nat := [4, 2, 4, 1, 2, 1, 1, 2, 2, 2, 2]
def baseStart_1537150 : Nat := 118140960795 + 1537150 * 2 ^ 59
def prefixEnd_1537150 : Nat := 4983230072969 + 3 ^ 40 * 1537150 * 2
def baseEnd_1537150 : Nat := 789296788058766127255783

theorem tailTrace_1537150 : CollatzResearch.WordTrace tailWord_1537150 prefixEnd_1537150 789296788058766127255783 := by
  unfold tailWord_1537150
  simp only [CollatzResearch.WordTrace]
  refine ⟨7008058297646943645560113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37376310920783699442987269 7008058297646943645560113)
  ·
    refine ⟨5256043723235207734170085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7008058297646943645560113 5256043723235207734170085)
    ·
      refine ⟨985508198106601450156891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5256043723235207734170085 985508198106601450156891)
      ·
        refine ⟨1478262297159902175235337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 985508198106601450156891 1478262297159902175235337)
        ·
          refine ⟨1108696722869926631426503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1478262297159902175235337 1108696722869926631426503)
          ·
            refine ⟨1663045084304889947139755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1108696722869926631426503 1663045084304889947139755)
            ·
              refine ⟨2494567626457334920709633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1663045084304889947139755 2494567626457334920709633)
              ·
                refine ⟨1870925719843001190532225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2494567626457334920709633 1870925719843001190532225)
                ·
                  refine ⟨1403194289882250892899169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1870925719843001190532225 1403194289882250892899169)
                  ·
                    refine ⟨1052395717411688169674377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1403194289882250892899169 1052395717411688169674377)
                    ·
                      refine ⟨789296788058766127255783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1052395717411688169674377 789296788058766127255783)
                      ·
                        rfl

theorem cell23_1537150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_1537150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537150 prefixEnd_1537150 := by exact prefixLift 1537150
  have htrace : WordTrace (prefixWord ++ tailWord_1537150) baseStart_1537150 baseEnd_1537150 := by
    simpa [prefixWord, tailWord_1537150, baseEnd_1537150] using wordTrace_append hprefix tailTrace_1537150
  have hstable : (prefixWord ++ tailWord_1537150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537150).length < 2 ^ (prefixWord ++ tailWord_1537150).sum := by decide
  have hdescent : baseEnd_1537150 < baseStart_1537150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537161 : List Nat := [1, 2, 1, 1, 4, 4, 1, 1, 8]
def baseStart_1537161 : Nat := 118140960795 + 1537161 * 2 ^ 59
def prefixEnd_1537161 : Nat := 4983230072969 + 3 ^ 40 * 1537161 * 2
def baseEnd_1537161 : Nat := 87700270705107287135359

theorem tailTrace_1537161 : CollatzResearch.WordTrace tailWord_1537161 prefixEnd_1537161 87700270705107287135359 := by
  unfold tailWord_1537161
  simp only [CollatzResearch.WordTrace]
  refine ⟨56064867584135698043131337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37376578389423798695420891 56064867584135698043131337)
  ·
    refine ⟨42048650688101773532348503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56064867584135698043131337 42048650688101773532348503)
    ·
      refine ⟨63072976032152660298522755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42048650688101773532348503 63072976032152660298522755)
      ·
        refine ⟨94609464048228990447784133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63072976032152660298522755 94609464048228990447784133)
        ·
          refine ⟨17739274509042935708959525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94609464048228990447784133 17739274509042935708959525)
          ·
            refine ⟨3326113970445550445429911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17739274509042935708959525 3326113970445550445429911)
            ·
              refine ⟨4989170955668325668144867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3326113970445550445429911 4989170955668325668144867)
              ·
                refine ⟨7483756433502488502217301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4989170955668325668144867 7483756433502488502217301)
                ·
                  refine ⟨87700270705107287135359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7483756433502488502217301 87700270705107287135359)
                  ·
                    rfl

theorem cell23_1537161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 8].length) (baseStart_1537161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537161 prefixEnd_1537161 := by exact prefixLift 1537161
  have htrace : WordTrace (prefixWord ++ tailWord_1537161) baseStart_1537161 baseEnd_1537161 := by
    simpa [prefixWord, tailWord_1537161, baseEnd_1537161] using wordTrace_append hprefix tailTrace_1537161
  have hstable : (prefixWord ++ tailWord_1537161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537161).length < 2 ^ (prefixWord ++ tailWord_1537161).sum := by decide
  have hdescent : baseEnd_1537161 < baseStart_1537161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537181 : List Nat := [1, 4, 2, 1, 1, 2, 1, 2, 1, 2, 6]
def baseStart_1537181 : Nat := 118140960795 + 1537181 * 2 ^ 59
def prefixEnd_1537181 : Nat := 4983230072969 + 3 ^ 40 * 1537181 * 2
def baseEnd_1537181 : Nat := 789312705959055505968139

theorem tailTrace_1537181 : CollatzResearch.WordTrace tailWord_1537181 prefixEnd_1537181 789312705959055505968139 := by
  unfold tailWord_1537181
  simp only [CollatzResearch.WordTrace]
  refine ⟨56065597044063241458859397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37377064696042160972572931 56065597044063241458859397)
  ·
    refine ⟨10512299445761857773536137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56065597044063241458859397 10512299445761857773536137)
    ·
      refine ⟨7884224584321393330152103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10512299445761857773536137 7884224584321393330152103)
      ·
        refine ⟨11826336876482089995228155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7884224584321393330152103 11826336876482089995228155)
        ·
          refine ⟨17739505314723134992842233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11826336876482089995228155 17739505314723134992842233)
          ·
            refine ⟨13304628986042351244631675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17739505314723134992842233 13304628986042351244631675)
            ·
              refine ⟨19956943479063526866947513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13304628986042351244631675 19956943479063526866947513)
              ·
                refine ⟨14967707609297645150210635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19956943479063526866947513 14967707609297645150210635)
                ·
                  refine ⟨22451561413946467725315953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14967707609297645150210635 22451561413946467725315953)
                  ·
                    refine ⟨16838671060459850793986965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22451561413946467725315953 16838671060459850793986965)
                    ·
                      refine ⟨789312705959055505968139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16838671060459850793986965 789312705959055505968139)
                      ·
                        rfl

theorem cell23_1537181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_1537181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537181 prefixEnd_1537181 := by exact prefixLift 1537181
  have htrace : WordTrace (prefixWord ++ tailWord_1537181) baseStart_1537181 baseEnd_1537181 := by
    simpa [prefixWord, tailWord_1537181, baseEnd_1537181] using wordTrace_append hprefix tailTrace_1537181
  have hstable : (prefixWord ++ tailWord_1537181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537181).length < 2 ^ (prefixWord ++ tailWord_1537181).sum := by decide
  have hdescent : baseEnd_1537181 < baseStart_1537181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537231 : List Nat := [1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 5]
def baseStart_1537231 : Nat := 118140960795 + 1537231 * 2 ^ 59
def prefixEnd_1537231 : Nat := 4983230072969 + 3 ^ 40 * 1537231 * 2
def baseEnd_1537231 : Nat := 789338379991780310342909

theorem tailTrace_1537231 : CollatzResearch.WordTrace tailWord_1537231 prefixEnd_1537231 789338379991780310342909 := by
  unfold tailWord_1537231
  simp only [CollatzResearch.WordTrace]
  refine ⟨56067420693882099998179547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37378280462588066665453031 56067420693882099998179547)
  ·
    refine ⟨84101131040823149997269321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56067420693882099998179547 84101131040823149997269321)
    ·
      refine ⟨63075848280617362497951991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84101131040823149997269321 63075848280617362497951991)
      ·
        refine ⟨94613772420926043746927987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63075848280617362497951991 94613772420926043746927987)
        ·
          refine ⟨141920658631389065620391981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94613772420926043746927987 141920658631389065620391981)
          ·
            refine ⟨53220246986770899607646993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141920658631389065620391981 53220246986770899607646993)
            ·
              refine ⟨39915185240078174705735245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53220246986770899607646993 39915185240078174705735245)
              ·
                refine ⟨14968194465029315514650717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39915185240078174705735245 14968194465029315514650717)
                ·
                  refine ⟨5613072924385993317994019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14968194465029315514650717 5613072924385993317994019)
                  ·
                    refine ⟨8419609386578989976991029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5613072924385993317994019 8419609386578989976991029)
                    ·
                      refine ⟨789338379991780310342909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8419609386578989976991029 789338379991780310342909)
                      ·
                        rfl

theorem cell23_1537231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 5].length) (baseStart_1537231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537231 prefixEnd_1537231 := by exact prefixLift 1537231
  have htrace : WordTrace (prefixWord ++ tailWord_1537231) baseStart_1537231 baseEnd_1537231 := by
    simpa [prefixWord, tailWord_1537231, baseEnd_1537231] using wordTrace_append hprefix tailTrace_1537231
  have hstable : (prefixWord ++ tailWord_1537231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537231).length < 2 ^ (prefixWord ++ tailWord_1537231).sum := by decide
  have hdescent : baseEnd_1537231 < baseStart_1537231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537255 : List Nat := [1, 1, 5, 3, 2, 1, 1, 2, 1, 6]
def baseStart_1537255 : Nat := 118140960795 + 1537255 * 2 ^ 59
def prefixEnd_1537255 : Nat := 4983230072969 + 3 ^ 40 * 1537255 * 2
def baseEnd_1537255 : Nat := 263116901175829405480933

theorem tailTrace_1537255 : CollatzResearch.WordTrace tailWord_1537255 prefixEnd_1537255 263116901175829405480933 := by
  unfold tailWord_1537255
  simp only [CollatzResearch.WordTrace]
  refine ⟨56068296045795152097053219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37378864030530101398035479 56068296045795152097053219)
  ·
    refine ⟨84102444068692728145579829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56068296045795152097053219 84102444068692728145579829)
    ·
      refine ⟨7884604131439943263648109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84102444068692728145579829 7884604131439943263648109)
      ·
        refine ⟨2956726549289978723868041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7884604131439943263648109 2956726549289978723868041)
        ·
          refine ⟨2217544911967484042901031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2956726549289978723868041 2217544911967484042901031)
          ·
            refine ⟨3326317367951226064351547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2217544911967484042901031 3326317367951226064351547)
            ·
              refine ⟨4989476051926839096527321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3326317367951226064351547 4989476051926839096527321)
              ·
                refine ⟨3742107038945129322395491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4989476051926839096527321 3742107038945129322395491)
                ·
                  refine ⟨5613160558417693983593237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3742107038945129322395491 5613160558417693983593237)
                  ·
                    refine ⟨263116901175829405480933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5613160558417693983593237 263116901175829405480933)
                    ·
                      rfl

theorem cell23_1537255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_1537255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537255 prefixEnd_1537255 := by exact prefixLift 1537255
  have htrace : WordTrace (prefixWord ++ tailWord_1537255) baseStart_1537255 baseEnd_1537255 := by
    simpa [prefixWord, tailWord_1537255, baseEnd_1537255] using wordTrace_append hprefix tailTrace_1537255
  have hstable : (prefixWord ++ tailWord_1537255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537255).length < 2 ^ (prefixWord ++ tailWord_1537255).sum := by decide
  have hdescent : baseEnd_1537255 < baseStart_1537255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537258 : List Nat := [3, 1, 3, 1, 1, 3, 1, 1, 3, 2, 4]
def baseStart_1537258 : Nat := 118140960795 + 1537258 * 2 ^ 59
def prefixEnd_1537258 : Nat := 4983230072969 + 3 ^ 40 * 1537258 * 2
def baseEnd_1537258 : Nat := 789352243969451704705285

theorem tailTrace_1537258 : CollatzResearch.WordTrace tailWord_1537258 prefixEnd_1537258 789352243969451704705285 := by
  unfold tailWord_1537258
  simp only [CollatzResearch.WordTrace]
  refine ⟨14017101366196070902353107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37378936976522855739608285 14017101366196070902353107)
  ·
    refine ⟨21025652049294106353529661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14017101366196070902353107 21025652049294106353529661)
    ·
      refine ⟨7884619518485289882573623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21025652049294106353529661 7884619518485289882573623)
      ·
        refine ⟨11826929277727934823860435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7884619518485289882573623 11826929277727934823860435)
        ·
          refine ⟨17740393916591902235790653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11826929277727934823860435 17740393916591902235790653)
          ·
            refine ⟨6652647718721963338421495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17740393916591902235790653 6652647718721963338421495)
            ·
              refine ⟨9978971578082945007632243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6652647718721963338421495 9978971578082945007632243)
              ·
                refine ⟨14968457367124417511448365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9978971578082945007632243 14968457367124417511448365)
                ·
                  refine ⟨5613171512671656566793137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14968457367124417511448365 5613171512671656566793137)
                  ·
                    refine ⟨4209878634503742425094853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5613171512671656566793137 4209878634503742425094853)
                    ·
                      refine ⟨789352243969451704705285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4209878634503742425094853 789352243969451704705285)
                      ·
                        rfl

theorem cell23_1537258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_1537258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537258 prefixEnd_1537258 := by exact prefixLift 1537258
  have htrace : WordTrace (prefixWord ++ tailWord_1537258) baseStart_1537258 baseEnd_1537258 := by
    simpa [prefixWord, tailWord_1537258, baseEnd_1537258] using wordTrace_append hprefix tailTrace_1537258
  have hstable : (prefixWord ++ tailWord_1537258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537258).length < 2 ^ (prefixWord ++ tailWord_1537258).sum := by decide
  have hdescent : baseEnd_1537258 < baseStart_1537258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537279 : List Nat := [1, 1, 2, 2, 1, 6, 1, 4, 1, 2, 2]
def baseStart_1537279 : Nat := 118140960795 + 1537279 * 2 ^ 59
def prefixEnd_1537279 : Nat := 4983230072969 + 3 ^ 40 * 1537279 * 2
def baseEnd_1537279 : Nat := 789363027063196122542689

theorem tailTrace_1537279 : CollatzResearch.WordTrace tailWord_1537279 prefixEnd_1537279 789363027063196122542689 := by
  unfold tailWord_1537279
  simp only [CollatzResearch.WordTrace]
  refine ⟨56069171397708204195926891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37379447598472136130617927 56069171397708204195926891)
  ·
    refine ⟨84103757096562306293890337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56069171397708204195926891 84103757096562306293890337)
    ·
      refine ⟨63077817822421729720417753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84103757096562306293890337 63077817822421729720417753)
      ·
        refine ⟨47308363366816297290313315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63077817822421729720417753 47308363366816297290313315)
        ·
          refine ⟨70962545050224445935469973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47308363366816297290313315 70962545050224445935469973)
          ·
            refine ⟨3326369299229270903225155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 70962545050224445935469973 3326369299229270903225155)
            ·
              refine ⟨4989553948843906354837733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3326369299229270903225155 4989553948843906354837733)
              ·
                refine ⟨935541365408232441532075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4989553948843906354837733 935541365408232441532075)
                ·
                  refine ⟨1403312048112348662298113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 935541365408232441532075 1403312048112348662298113)
                  ·
                    refine ⟨1052484036084261496723585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1403312048112348662298113 1052484036084261496723585)
                    ·
                      refine ⟨789363027063196122542689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1052484036084261496723585 789363027063196122542689)
                      ·
                        rfl

theorem cell23_1537279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 4, 1, 2, 2].length) (baseStart_1537279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537279 prefixEnd_1537279 := by exact prefixLift 1537279
  have htrace : WordTrace (prefixWord ++ tailWord_1537279) baseStart_1537279 baseEnd_1537279 := by
    simpa [prefixWord, tailWord_1537279, baseEnd_1537279] using wordTrace_append hprefix tailTrace_1537279
  have hstable : (prefixWord ++ tailWord_1537279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537279).length < 2 ^ (prefixWord ++ tailWord_1537279).sum := by decide
  have hdescent : baseEnd_1537279 < baseStart_1537279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537321 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 9]
def baseStart_1537321 : Nat := 118140960795 + 1537321 * 2 ^ 59
def prefixEnd_1537321 : Nat := 4983230072969 + 3 ^ 40 * 1537321 * 2
def baseEnd_1537321 : Nat := 789384593250684958217495

theorem tailTrace_1537321 : CollatzResearch.WordTrace tailWord_1537321 prefixEnd_1537321 789384593250684958217495 := by
  unfold tailWord_1537321
  simp only [CollatzResearch.WordTrace]
  refine ⟨56070703263556045368955817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37380468842370696912637211 56070703263556045368955817)
  ·
    refine ⟨42053027447667034026716863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56070703263556045368955817 42053027447667034026716863)
    ·
      refine ⟨63079541171500551040075295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42053027447667034026716863 63079541171500551040075295)
      ·
        refine ⟨94619311757250826560112943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63079541171500551040075295 94619311757250826560112943)
        ·
          refine ⟨141928967635876239840169415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94619311757250826560112943 141928967635876239840169415)
          ·
            refine ⟨212893451453814359760254123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141928967635876239840169415 212893451453814359760254123)
            ·
              refine ⟨319340177180721539640381185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212893451453814359760254123 319340177180721539640381185)
              ·
                refine ⟨239505132885541154730285889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 319340177180721539640381185 239505132885541154730285889)
                ·
                  refine ⟨179628849664155866047714417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 239505132885541154730285889 179628849664155866047714417)
                  ·
                    refine ⟨134721637248116899535785813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 179628849664155866047714417 134721637248116899535785813)
                    ·
                      refine ⟨789384593250684958217495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 134721637248116899535785813 789384593250684958217495)
                      ·
                        rfl

theorem cell23_1537321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 9].length) (baseStart_1537321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537321 prefixEnd_1537321 := by exact prefixLift 1537321
  have htrace : WordTrace (prefixWord ++ tailWord_1537321) baseStart_1537321 baseEnd_1537321 := by
    simpa [prefixWord, tailWord_1537321, baseEnd_1537321] using wordTrace_append hprefix tailTrace_1537321
  have hstable : (prefixWord ++ tailWord_1537321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537321).length < 2 ^ (prefixWord ++ tailWord_1537321).sum := by decide
  have hdescent : baseEnd_1537321 < baseStart_1537321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537329 : List Nat := [1, 2, 2, 3, 3, 3, 1, 2, 2, 1, 3]
def baseStart_1537329 : Nat := 118140960795 + 1537329 * 2 ^ 59
def prefixEnd_1537329 : Nat := 4983230072969 + 3 ^ 40 * 1537329 * 2
def baseEnd_1537329 : Nat := 789388701095920926917459

theorem tailTrace_1537329 : CollatzResearch.WordTrace tailWord_1537329 prefixEnd_1537329 789388701095920926917459 := by
  unfold tailWord_1537329
  simp only [CollatzResearch.WordTrace]
  refine ⟨56070995047527062735247041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37380663365018041823498027 56070995047527062735247041)
  ·
    refine ⟨42053246285645297051435281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56070995047527062735247041 42053246285645297051435281)
    ·
      refine ⟨31539934714233972788576461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42053246285645297051435281 31539934714233972788576461)
      ·
        refine ⟨11827475517837739795716173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31539934714233972788576461 11827475517837739795716173)
        ·
          refine ⟨4435303319189152423393565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11827475517837739795716173 4435303319189152423393565)
          ·
            refine ⟨1663238744695932158772587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4435303319189152423393565 1663238744695932158772587)
            ·
              refine ⟨2494858117043898238158881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1663238744695932158772587 2494858117043898238158881)
              ·
                refine ⟨1871143587782923678619161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2494858117043898238158881 1871143587782923678619161)
                ·
                  refine ⟨1403357690837192758964371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1871143587782923678619161 1403357690837192758964371)
                  ·
                    refine ⟨2105036536255789138446557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1403357690837192758964371 2105036536255789138446557)
                    ·
                      refine ⟨789388701095920926917459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2105036536255789138446557 789388701095920926917459)
                      ·
                        rfl

theorem cell23_1537329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_1537329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537329 prefixEnd_1537329 := by exact prefixLift 1537329
  have htrace : WordTrace (prefixWord ++ tailWord_1537329) baseStart_1537329 baseEnd_1537329 := by
    simpa [prefixWord, tailWord_1537329, baseEnd_1537329] using wordTrace_append hprefix tailTrace_1537329
  have hstable : (prefixWord ++ tailWord_1537329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537329).length < 2 ^ (prefixWord ++ tailWord_1537329).sum := by decide
  have hdescent : baseEnd_1537329 < baseStart_1537329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537345 : List Nat := [1, 2, 5, 2, 1, 1, 2, 1, 2, 6]
def baseStart_1537345 : Nat := 118140960795 + 1537345 * 2 ^ 59
def prefixEnd_1537345 : Nat := 4983230072969 + 3 ^ 40 * 1537345 * 2
def baseEnd_1537345 : Nat := 263132305595464288105795

theorem tailTrace_1537345 : CollatzResearch.WordTrace tailWord_1537345 prefixEnd_1537345 263132305595464288105795 := by
  unfold tailWord_1537345
  simp only [CollatzResearch.WordTrace]
  refine ⟨56071578615469097467829489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37381052410312731645219659 56071578615469097467829489)
  ·
    refine ⟨42053683961601823100872117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56071578615469097467829489 42053683961601823100872117)
    ·
      refine ⟨3942532871400170915706761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42053683961601823100872117 3942532871400170915706761)
      ·
        refine ⟨2956899653550128186780071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3942532871400170915706761 2956899653550128186780071)
        ·
          refine ⟨4435349480325192280170107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2956899653550128186780071 4435349480325192280170107)
          ·
            refine ⟨6653024220487788420255161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4435349480325192280170107 6653024220487788420255161)
            ·
              refine ⟨4989768165365841315191371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6653024220487788420255161 4989768165365841315191371)
              ·
                refine ⟨7484652248048761972787057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4989768165365841315191371 7484652248048761972787057)
                ·
                  refine ⟨5613489186036571479590293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7484652248048761972787057 5613489186036571479590293)
                  ·
                    refine ⟨263132305595464288105795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5613489186036571479590293 263132305595464288105795)
                    ·
                      rfl

theorem cell23_1537345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_1537345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537345 prefixEnd_1537345 := by exact prefixLift 1537345
  have htrace : WordTrace (prefixWord ++ tailWord_1537345) baseStart_1537345 baseEnd_1537345 := by
    simpa [prefixWord, tailWord_1537345, baseEnd_1537345] using wordTrace_append hprefix tailTrace_1537345
  have hstable : (prefixWord ++ tailWord_1537345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537345).length < 2 ^ (prefixWord ++ tailWord_1537345).sum := by decide
  have hdescent : baseEnd_1537345 < baseStart_1537345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537358 : List Nat := [4, 1, 1, 1, 1, 1, 3, 4, 7]
def baseStart_1537358 : Nat := 118140960795 + 1537358 * 2 ^ 59
def prefixEnd_1537358 : Nat := 4983230072969 + 3 ^ 40 * 1537358 * 2
def baseEnd_1537358 : Nat := 87711510226100145939425

theorem tailTrace_1537358 : CollatzResearch.WordTrace tailWord_1537358 prefixEnd_1537358 87711510226100145939425 := by
  unfold tailWord_1537358
  simp only [CollatzResearch.WordTrace]
  refine ⟨7009006595552750086006591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37381368509614667125368485 7009006595552750086006591)
  ·
    refine ⟨10513509893329125129009887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7009006595552750086006591 10513509893329125129009887)
    ·
      refine ⟨15770264839993687693514831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10513509893329125129009887 15770264839993687693514831)
      ·
        refine ⟨23655397259990531540272247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15770264839993687693514831 23655397259990531540272247)
        ·
          refine ⟨35483095889985797310408371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23655397259990531540272247 35483095889985797310408371)
          ·
            refine ⟨53224643834978695965612557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35483095889985797310408371 53224643834978695965612557)
            ·
              refine ⟨19959241438117010987104709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53224643834978695965612557 19959241438117010987104709)
              ·
                refine ⟨3742357769646939560082133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19959241438117010987104709 3742357769646939560082133)
                ·
                  refine ⟨87711510226100145939425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3742357769646939560082133 87711510226100145939425)
                  ·
                    rfl

theorem cell23_1537358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 7].length) (baseStart_1537358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537358 prefixEnd_1537358 := by exact prefixLift 1537358
  have htrace : WordTrace (prefixWord ++ tailWord_1537358) baseStart_1537358 baseEnd_1537358 := by
    simpa [prefixWord, tailWord_1537358, baseEnd_1537358] using wordTrace_append hprefix tailTrace_1537358
  have hstable : (prefixWord ++ tailWord_1537358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537358).length < 2 ^ (prefixWord ++ tailWord_1537358).sum := by decide
  have hdescent : baseEnd_1537358 < baseStart_1537358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537392 : List Nat := [2, 1, 1, 1, 4, 2, 5, 2, 5]
def baseStart_1537392 : Nat := 118140960795 + 1537392 * 2 ^ 59
def prefixEnd_1537392 : Nat := 4983230072969 + 3 ^ 40 * 1537392 * 2
def baseEnd_1537392 : Nat := 87713450041906020047741

theorem tailTrace_1537392 : CollatzResearch.WordTrace tailWord_1537392 prefixEnd_1537392 87713450041906020047741 := by
  unfold tailWord_1537392
  simp only [CollatzResearch.WordTrace]
  refine ⟨28036646423149412247395215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37382195230865882996526953 28036646423149412247395215)
  ·
    refine ⟨42054969634724118371092823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28036646423149412247395215 42054969634724118371092823)
    ·
      refine ⟨63082454452086177556639235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42054969634724118371092823 63082454452086177556639235)
      ·
        refine ⟨94623681678129266334958853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63082454452086177556639235 94623681678129266334958853)
        ·
          refine ⟨17741940314649237437804785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94623681678129266334958853 17741940314649237437804785)
          ·
            refine ⟨13306455235986928078353589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17741940314649237437804785 13306455235986928078353589)
            ·
              refine ⟨1247480178373774507345649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13306455235986928078353589 1247480178373774507345649)
              ·
                refine ⟨935610133780330880509237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1247480178373774507345649 935610133780330880509237)
                ·
                  refine ⟨87713450041906020047741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 935610133780330880509237 87713450041906020047741)
                  ·
                    rfl

theorem cell23_1537392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 2, 5].length) (baseStart_1537392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537392 prefixEnd_1537392 := by exact prefixLift 1537392
  have htrace : WordTrace (prefixWord ++ tailWord_1537392) baseStart_1537392 baseEnd_1537392 := by
    simpa [prefixWord, tailWord_1537392, baseEnd_1537392] using wordTrace_append hprefix tailTrace_1537392
  have hstable : (prefixWord ++ tailWord_1537392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537392).length < 2 ^ (prefixWord ++ tailWord_1537392).sum := by decide
  have hdescent : baseEnd_1537392 < baseStart_1537392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537408 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 4]
def baseStart_1537408 : Nat := 118140960795 + 1537408 * 2 ^ 59
def prefixEnd_1537408 : Nat := 4983230072969 + 3 ^ 40 * 1537408 * 2
def baseEnd_1537408 : Nat := 789429266067626117829595

theorem tailTrace_1537408 : CollatzResearch.WordTrace tailWord_1537408 prefixEnd_1537408 789429266067626117829595 := by
  unfold tailWord_1537408
  simp only [CollatzResearch.WordTrace]
  refine ⟨28036938207120429613686439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37382584276160572818248585 28036938207120429613686439)
  ·
    refine ⟨42055407310680644420529659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28036938207120429613686439 42055407310680644420529659)
    ·
      refine ⟨63083110966020966630794489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42055407310680644420529659 63083110966020966630794489)
      ·
        refine ⟨47312333224515724973095867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63083110966020966630794489 47312333224515724973095867)
        ·
          refine ⟨70968499836773587459643801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47312333224515724973095867 70968499836773587459643801)
          ·
            refine ⟨53226374877580190594732851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70968499836773587459643801 53226374877580190594732851)
            ·
              refine ⟨79839562316370285892099277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53226374877580190594732851 79839562316370285892099277)
              ·
                refine ⟨29939835868638857209537229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79839562316370285892099277 29939835868638857209537229)
                ·
                  refine ⟨11227438450739571453576461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29939835868638857209537229 11227438450739571453576461)
                  ·
                    refine ⟨4210289419027339295091173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11227438450739571453576461 4210289419027339295091173)
                    ·
                      refine ⟨789429266067626117829595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4210289419027339295091173 789429266067626117829595)
                      ·
                        rfl

theorem cell23_1537408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_1537408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537408 prefixEnd_1537408 := by exact prefixLift 1537408
  have htrace : WordTrace (prefixWord ++ tailWord_1537408) baseStart_1537408 baseEnd_1537408 := by
    simpa [prefixWord, tailWord_1537408, baseEnd_1537408] using wordTrace_append hprefix tailTrace_1537408
  have hstable : (prefixWord ++ tailWord_1537408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537408).length < 2 ^ (prefixWord ++ tailWord_1537408).sum := by decide
  have hdescent : baseEnd_1537408 < baseStart_1537408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537425 : List Nat := [1, 2, 2, 1, 1, 1, 2, 4, 1, 6, 2]
def baseStart_1537425 : Nat := 118140960795 + 1537425 * 2 ^ 59
def prefixEnd_1537425 : Nat := 4983230072969 + 3 ^ 40 * 1537425 * 2
def baseEnd_1537425 : Nat := 789437995238752551317017

theorem tailTrace_1537425 : CollatzResearch.WordTrace tailWord_1537425 prefixEnd_1537425 789437995238752551317017 := by
  unfold tailWord_1537425
  simp only [CollatzResearch.WordTrace]
  refine ⟨56074496455179271130741729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37382997636786180753827819 56074496455179271130741729)
  ·
    refine ⟨42055872341384453348056297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56074496455179271130741729 42055872341384453348056297)
    ·
      refine ⟨31541904256038340011042223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42055872341384453348056297 31541904256038340011042223)
      ·
        refine ⟨47312856384057510016563335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31541904256038340011042223 47312856384057510016563335)
        ·
          refine ⟨70969284576086265024845003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47312856384057510016563335 70969284576086265024845003)
          ·
            refine ⟨106453926864129397537267505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70969284576086265024845003 106453926864129397537267505)
            ·
              refine ⟨79840445148097048152950629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106453926864129397537267505 79840445148097048152950629)
              ·
                refine ⟨14970083465268196528678243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79840445148097048152950629 14970083465268196528678243)
                ·
                  refine ⟨22455125197902294793017365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14970083465268196528678243 22455125197902294793017365)
                  ·
                    refine ⟨1052583993651670068422689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22455125197902294793017365 1052583993651670068422689)
                    ·
                      refine ⟨789437995238752551317017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1052583993651670068422689 789437995238752551317017)
                      ·
                        rfl

theorem cell23_1537425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 6, 2].length) (baseStart_1537425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537425 prefixEnd_1537425 := by exact prefixLift 1537425
  have htrace : WordTrace (prefixWord ++ tailWord_1537425) baseStart_1537425 baseEnd_1537425 := by
    simpa [prefixWord, tailWord_1537425, baseEnd_1537425] using wordTrace_append hprefix tailTrace_1537425
  have hstable : (prefixWord ++ tailWord_1537425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537425).length < 2 ^ (prefixWord ++ tailWord_1537425).sum := by decide
  have hdescent : baseEnd_1537425 < baseStart_1537425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537442 : List Nat := [3, 3, 1, 2, 1, 2, 2, 2, 2, 1, 4]
def baseStart_1537442 : Nat := 118140960795 + 1537442 * 2 ^ 59
def prefixEnd_1537442 : Nat := 4983230072969 + 3 ^ 40 * 1537442 * 2
def baseEnd_1537442 : Nat := 789446724409878984804439

theorem tailTrace_1537442 : CollatzResearch.WordTrace tailWord_1537442 prefixEnd_1537442 789446724409878984804439 := by
  unfold tailWord_1537442
  simp only [CollatzResearch.WordTrace]
  refine ⟨14018779124029420758527645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37383410997411788689407053 14018779124029420758527645)
  ·
    refine ⟨5257042171511032784447867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14018779124029420758527645 5257042171511032784447867)
    ·
      refine ⟨7885563257266549176671801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5257042171511032784447867 7885563257266549176671801)
      ·
        refine ⟨5914172442949911882503851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7885563257266549176671801 5914172442949911882503851)
        ·
          refine ⟨8871258664424867823755777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5914172442949911882503851 8871258664424867823755777)
          ·
            refine ⟨6653443998318650867816833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8871258664424867823755777 6653443998318650867816833)
            ·
              refine ⟨4990082998738988150862625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6653443998318650867816833 4990082998738988150862625)
              ·
                refine ⟨3742562249054241113146969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4990082998738988150862625 3742562249054241113146969)
                ·
                  refine ⟨2806921686790680834860227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3742562249054241113146969 2806921686790680834860227)
                  ·
                    refine ⟨4210382530186021252290341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2806921686790680834860227 4210382530186021252290341)
                    ·
                      refine ⟨789446724409878984804439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4210382530186021252290341 789446724409878984804439)
                      ·
                        rfl

theorem cell23_1537442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_1537442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537442 prefixEnd_1537442 := by exact prefixLift 1537442
  have htrace : WordTrace (prefixWord ++ tailWord_1537442) baseStart_1537442 baseEnd_1537442 := by
    simpa [prefixWord, tailWord_1537442, baseEnd_1537442] using wordTrace_append hprefix tailTrace_1537442
  have hstable : (prefixWord ++ tailWord_1537442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537442).length < 2 ^ (prefixWord ++ tailWord_1537442).sum := by decide
  have hdescent : baseEnd_1537442 < baseStart_1537442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537445 : List Nat := [1, 3, 1, 2, 1, 1, 2, 3, 4, 2, 3]
def baseStart_1537445 : Nat := 118140960795 + 1537445 * 2 ^ 59
def prefixEnd_1537445 : Nat := 4983230072969 + 3 ^ 40 * 1537445 * 2
def baseEnd_1537445 : Nat := 789448264851842473066925

theorem tailTrace_1537445 : CollatzResearch.WordTrace tailWord_1537445 prefixEnd_1537445 789448264851842473066925 := by
  unfold tailWord_1537445
  simp only [CollatzResearch.WordTrace]
  refine ⟨56075225915106814546469789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37383483943404543030979859 56075225915106814546469789)
  ·
    refine ⟨21028209718165055454926171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56075225915106814546469789 21028209718165055454926171)
    ·
      refine ⟨31542314577247583182389257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21028209718165055454926171 31542314577247583182389257)
      ·
        refine ⟨23656735932935687386791943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31542314577247583182389257 23656735932935687386791943)
        ·
          refine ⟨35485103899403531080187915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23656735932935687386791943 35485103899403531080187915)
          ·
            refine ⟨53227655849105296620281873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35485103899403531080187915 53227655849105296620281873)
            ·
              refine ⟨39920741886828972465211405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53227655849105296620281873 39920741886828972465211405)
              ·
                refine ⟨14970278207560864674454277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39920741886828972465211405 14970278207560864674454277)
                ·
                  refine ⟨2806927163917662126460177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14970278207560864674454277 2806927163917662126460177)
                  ·
                    refine ⟨2105195372938246594845133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2806927163917662126460177 2105195372938246594845133)
                    ·
                      refine ⟨789448264851842473066925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2105195372938246594845133 789448264851842473066925)
                      ·
                        rfl

theorem cell23_1537445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_1537445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537445 prefixEnd_1537445 := by exact prefixLift 1537445
  have htrace : WordTrace (prefixWord ++ tailWord_1537445) baseStart_1537445 baseEnd_1537445 := by
    simpa [prefixWord, tailWord_1537445, baseEnd_1537445] using wordTrace_append hprefix tailTrace_1537445
  have hstable : (prefixWord ++ tailWord_1537445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537445).length < 2 ^ (prefixWord ++ tailWord_1537445).sum := by decide
  have hdescent : baseEnd_1537445 < baseStart_1537445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537488 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 7]
def baseStart_1537488 : Nat := 118140960795 + 1537488 * 2 ^ 59
def prefixEnd_1537488 : Nat := 4983230072969 + 3 ^ 40 * 1537488 * 2
def baseEnd_1537488 : Nat := 789470344519985804829227

theorem tailTrace_1537488 : CollatzResearch.WordTrace tailWord_1537488 prefixEnd_1537488 789470344519985804829227 := by
  unfold tailWord_1537488
  simp only [CollatzResearch.WordTrace]
  refine ⟨28038397126975516445142559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37384529502634021926856745 28038397126975516445142559)
  ·
    refine ⟨42057595690463274667713839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28038397126975516445142559 42057595690463274667713839)
    ·
      refine ⟨63086393535694912001570759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42057595690463274667713839 63086393535694912001570759)
      ·
        refine ⟨94629590303542368002356139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63086393535694912001570759 94629590303542368002356139)
        ·
          refine ⟨141944385455313552003534209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94629590303542368002356139 141944385455313552003534209)
          ·
            refine ⟨106458289091485164002650657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141944385455313552003534209 106458289091485164002650657)
            ·
              refine ⟨79843716818613873001987993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106458289091485164002650657 79843716818613873001987993)
              ·
                refine ⟨59882787613960404751490995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79843716818613873001987993 59882787613960404751490995)
                ·
                  refine ⟨89824181420940607127236493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59882787613960404751490995 89824181420940607127236493)
                  ·
                    refine ⟨33684068032852727672713685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89824181420940607127236493 33684068032852727672713685)
                    ·
                      refine ⟨789470344519985804829227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 33684068032852727672713685 789470344519985804829227)
                      ·
                        rfl

theorem cell23_1537488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 7].length) (baseStart_1537488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537488 prefixEnd_1537488 := by exact prefixLift 1537488
  have htrace : WordTrace (prefixWord ++ tailWord_1537488) baseStart_1537488 baseEnd_1537488 := by
    simpa [prefixWord, tailWord_1537488, baseEnd_1537488] using wordTrace_append hprefix tailTrace_1537488
  have hstable : (prefixWord ++ tailWord_1537488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537488).length < 2 ^ (prefixWord ++ tailWord_1537488).sum := by decide
  have hdescent : baseEnd_1537488 < baseStart_1537488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537509 : List Nat := [1, 3, 1, 5, 1, 1, 1, 3, 3, 1, 3]
def baseStart_1537509 : Nat := 118140960795 + 1537509 * 2 ^ 59
def prefixEnd_1537509 : Nat := 4983230072969 + 3 ^ 40 * 1537509 * 2
def baseEnd_1537509 : Nat := 789481127613730222666631

theorem tailTrace_1537509 : CollatzResearch.WordTrace tailWord_1537509 prefixEnd_1537509 789481127613730222666631 := by
  unfold tailWord_1537509
  simp only [CollatzResearch.WordTrace]
  refine ⟨56077560186874953476799581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37385040124583302317866387 56077560186874953476799581)
  ·
    refine ⟨21029085070078107553799843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56077560186874953476799581 21029085070078107553799843)
    ·
      refine ⟨31543627605117161330699765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21029085070078107553799843 31543627605117161330699765)
      ·
        refine ⟨2957215087979733874753103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31543627605117161330699765 2957215087979733874753103)
        ·
          refine ⟨4435822631969600812129655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2957215087979733874753103 4435822631969600812129655)
          ·
            refine ⟨6653733947954401218194483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4435822631969600812129655 6653733947954401218194483)
            ·
              refine ⟨9980600921931601827291725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6653733947954401218194483 9980600921931601827291725)
              ·
                refine ⟨3742725345724350685234397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9980600921931601827291725 3742725345724350685234397)
                ·
                  refine ⟨1403522004646631506962899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3742725345724350685234397 1403522004646631506962899)
                  ·
                    refine ⟨2105283006969947260444349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1403522004646631506962899 2105283006969947260444349)
                    ·
                      refine ⟨789481127613730222666631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2105283006969947260444349 789481127613730222666631)
                      ·
                        rfl

theorem cell23_1537509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_1537509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537509 prefixEnd_1537509 := by exact prefixLift 1537509
  have htrace : WordTrace (prefixWord ++ tailWord_1537509) baseStart_1537509 baseEnd_1537509 := by
    simpa [prefixWord, tailWord_1537509, baseEnd_1537509] using wordTrace_append hprefix tailTrace_1537509
  have hstable : (prefixWord ++ tailWord_1537509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537509).length < 2 ^ (prefixWord ++ tailWord_1537509).sum := by decide
  have hdescent : baseEnd_1537509 < baseStart_1537509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537515 : List Nat := [1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 4]
def baseStart_1537515 : Nat := 118140960795 + 1537515 * 2 ^ 59
def prefixEnd_1537515 : Nat := 4983230072969 + 3 ^ 40 * 1537515 * 2
def baseEnd_1537515 : Nat := 789484208497657199191603

theorem tailTrace_1537515 : CollatzResearch.WordTrace tailWord_1537515 prefixEnd_1537515 789484208497657199191603 := by
  unfold tailWord_1537515
  simp only [CollatzResearch.WordTrace]
  refine ⟨56077779024853216501517999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37385186016568811001011999 56077779024853216501517999)
  ·
    refine ⟨84116668537279824752276999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56077779024853216501517999 84116668537279824752276999)
    ·
      refine ⟨126175002805919737128415499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84116668537279824752276999 126175002805919737128415499)
      ·
        refine ⟨189262504208879605692623249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126175002805919737128415499 189262504208879605692623249)
        ·
          refine ⟨141946878156659704269467437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189262504208879605692623249 141946878156659704269467437)
          ·
            refine ⟨53230079308747389101050289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141946878156659704269467437 53230079308747389101050289)
            ·
              refine ⟨39922559481560541825787717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53230079308747389101050289 39922559481560541825787717)
              ·
                refine ⟨7485479902792601592335197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39922559481560541825787717 7485479902792601592335197)
                ·
                  refine ⟨2807054963547225597125699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7485479902792601592335197 2807054963547225597125699)
                  ·
                    refine ⟨4210582445320838395688549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2807054963547225597125699 4210582445320838395688549)
                    ·
                      refine ⟨789484208497657199191603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4210582445320838395688549 789484208497657199191603)
                      ·
                        rfl

theorem cell23_1537515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 4].length) (baseStart_1537515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537515 prefixEnd_1537515 := by exact prefixLift 1537515
  have htrace : WordTrace (prefixWord ++ tailWord_1537515) baseStart_1537515 baseEnd_1537515 := by
    simpa [prefixWord, tailWord_1537515, baseEnd_1537515] using wordTrace_append hprefix tailTrace_1537515
  have hstable : (prefixWord ++ tailWord_1537515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537515).length < 2 ^ (prefixWord ++ tailWord_1537515).sum := by decide
  have hdescent : baseEnd_1537515 < baseStart_1537515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537532 : List Nat := [2, 2, 2, 1, 2, 1, 3, 4, 1, 1, 4]
def baseStart_1537532 : Nat := 118140960795 + 1537532 * 2 ^ 59
def prefixEnd_1537532 : Nat := 4983230072969 + 3 ^ 40 * 1537532 * 2
def baseEnd_1537532 : Nat := 789492937668783632679025

theorem tailTrace_1537532 : CollatzResearch.WordTrace tailWord_1537532 prefixEnd_1537532 789492937668783632679025 := by
  unfold tailWord_1537532
  simp only [CollatzResearch.WordTrace]
  refine ⟨28039199532895814202443425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37385599377194418936591233 28039199532895814202443425)
  ·
    refine ⟨21029399649671860651832569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28039199532895814202443425 21029399649671860651832569)
    ·
      refine ⟨15772049737253895488874427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21029399649671860651832569 15772049737253895488874427)
      ·
        refine ⟨23658074605880843233311641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15772049737253895488874427 23658074605880843233311641)
        ·
          refine ⟨17743555954410632424983731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23658074605880843233311641 17743555954410632424983731)
          ·
            refine ⟨26615333931615948637475597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17743555954410632424983731 26615333931615948637475597)
            ·
              refine ⟨9980750224355980739053349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26615333931615948637475597 9980750224355980739053349)
              ·
                refine ⟨1871390667066746388572503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9980750224355980739053349 1871390667066746388572503)
                ·
                  refine ⟨2807086000600119582858755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1871390667066746388572503 2807086000600119582858755)
                  ·
                    refine ⟨4210629000900179374288133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2807086000600119582858755 4210629000900179374288133)
                    ·
                      refine ⟨789492937668783632679025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4210629000900179374288133 789492937668783632679025)
                      ·
                        rfl

theorem cell23_1537532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 1, 1, 4].length) (baseStart_1537532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537532 prefixEnd_1537532 := by exact prefixLift 1537532
  have htrace : WordTrace (prefixWord ++ tailWord_1537532) baseStart_1537532 baseEnd_1537532 := by
    simpa [prefixWord, tailWord_1537532, baseEnd_1537532] using wordTrace_append hprefix tailTrace_1537532
  have hstable : (prefixWord ++ tailWord_1537532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537532).length < 2 ^ (prefixWord ++ tailWord_1537532).sum := by decide
  have hdescent : baseEnd_1537532 < baseStart_1537532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537543 : List Nat := [1, 1, 4, 3, 2, 3, 1, 3, 1, 1, 3]
def baseStart_1537543 : Nat := 118140960795 + 1537543 * 2 ^ 59
def prefixEnd_1537543 : Nat := 4983230072969 + 3 ^ 40 * 1537543 * 2
def baseEnd_1537543 : Nat := 789498585955983089641475

theorem tailTrace_1537543 : CollatzResearch.WordTrace tailWord_1537543 prefixEnd_1537543 789498585955983089641475 := by
  unfold tailWord_1537543
  simp only [CollatzResearch.WordTrace]
  refine ⟨56078800268751777283537283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37385866845834518189024855 56078800268751777283537283)
  ·
    refine ⟨84118200403127665925305925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56078800268751777283537283 84118200403127665925305925)
    ·
      refine ⟨15772162575586437360994861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84118200403127665925305925 15772162575586437360994861)
      ·
        refine ⟨5914560965844914010373073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15772162575586437360994861 5914560965844914010373073)
        ·
          refine ⟨4435920724383685507779805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5914560965844914010373073 4435920724383685507779805)
          ·
            refine ⟨1663470271643882065417427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4435920724383685507779805 1663470271643882065417427)
            ·
              refine ⟨2495205407465823098126141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1663470271643882065417427 2495205407465823098126141)
              ·
                refine ⟨935702027799683661797303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2495205407465823098126141 935702027799683661797303)
                ·
                  refine ⟨1403553041699525492695955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 935702027799683661797303 1403553041699525492695955)
                  ·
                    refine ⟨2105329562549288239043933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1403553041699525492695955 2105329562549288239043933)
                    ·
                      refine ⟨789498585955983089641475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2105329562549288239043933 789498585955983089641475)
                      ·
                        rfl

theorem cell23_1537543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_1537543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537543 prefixEnd_1537543 := by exact prefixLift 1537543
  have htrace : WordTrace (prefixWord ++ tailWord_1537543) baseStart_1537543 baseEnd_1537543 := by
    simpa [prefixWord, tailWord_1537543, baseEnd_1537543] using wordTrace_append hprefix tailTrace_1537543
  have hstable : (prefixWord ++ tailWord_1537543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537543).length < 2 ^ (prefixWord ++ tailWord_1537543).sum := by decide
  have hdescent : baseEnd_1537543 < baseStart_1537543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537545 : List Nat := [1, 2, 1, 1, 3, 1, 4, 1, 3, 2, 4]
def baseStart_1537545 : Nat := 118140960795 + 1537545 * 2 ^ 59
def prefixEnd_1537545 : Nat := 4983230072969 + 3 ^ 40 * 1537545 * 2
def baseEnd_1537545 : Nat := 789499612917292081816465

theorem tailTrace_1537545 : CollatzResearch.WordTrace tailWord_1537545 prefixEnd_1537545 789499612917292081816465 := by
  unfold tailWord_1537545
  simp only [CollatzResearch.WordTrace]
  refine ⟨56078873214744531625110089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37385915476496354416740059 56078873214744531625110089)
  ·
    refine ⟨42059154911058398718832567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56078873214744531625110089 42059154911058398718832567)
    ·
      refine ⟨63088732366587598078248851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42059154911058398718832567 63088732366587598078248851)
      ·
        refine ⟨94633098549881397117373277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63088732366587598078248851 94633098549881397117373277)
        ·
          refine ⟨35487411956205523919014979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94633098549881397117373277 35487411956205523919014979)
          ·
            refine ⟨53231117934308285878522469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35487411956205523919014979 53231117934308285878522469)
            ·
              refine ⟨9980834612682803602222963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53231117934308285878522469 9980834612682803602222963)
              ·
                refine ⟨14971251919024205403334445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9980834612682803602222963 14971251919024205403334445)
                ·
                  refine ⟨5614219469634077026250417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14971251919024205403334445 5614219469634077026250417)
                  ·
                    refine ⟨4210664602225557769687813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5614219469634077026250417 4210664602225557769687813)
                    ·
                      refine ⟨789499612917292081816465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4210664602225557769687813 789499612917292081816465)
                      ·
                        rfl

theorem cell23_1537545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 2, 4].length) (baseStart_1537545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537545 prefixEnd_1537545 := by exact prefixLift 1537545
  have htrace : WordTrace (prefixWord ++ tailWord_1537545) baseStart_1537545 baseEnd_1537545 := by
    simpa [prefixWord, tailWord_1537545, baseEnd_1537545] using wordTrace_append hprefix tailTrace_1537545
  have hstable : (prefixWord ++ tailWord_1537545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537545).length < 2 ^ (prefixWord ++ tailWord_1537545).sum := by decide
  have hdescent : baseEnd_1537545 < baseStart_1537545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537555 : List Nat := [1, 1, 1, 2, 1, 8, 9]
def baseStart_1537555 : Nat := 118140960795 + 1537555 * 2 ^ 59
def prefixEnd_1537555 : Nat := 4983230072969 + 3 ^ 40 * 1537555 * 2
def baseEnd_1537555 : Nat := 9746972194121444971499

theorem tailTrace_1537555 : CollatzResearch.WordTrace tailWord_1537555 prefixEnd_1537555 9746972194121444971499 := by
  unfold tailWord_1537555
  simp only [CollatzResearch.WordTrace]
  refine ⟨56079237944708303332974119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37386158629805535555316079 56079237944708303332974119)
  ·
    refine ⟨84118856917062454999461179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56079237944708303332974119 84118856917062454999461179)
    ·
      refine ⟨126178285375593682499191769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84118856917062454999461179 126178285375593682499191769)
      ·
        refine ⟨94633714031695261874393827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126178285375593682499191769 94633714031695261874393827)
        ·
          refine ⟨141950571047542892811590741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94633714031695261874393827 141950571047542892811590741)
          ·
            refine ⟨1663483254463393275135829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 141950571047542892811590741 1663483254463393275135829)
            ·
              refine ⟨9746972194121444971499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1663483254463393275135829 9746972194121444971499)
              ·
                rfl

theorem cell23_1537555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 9].length) (baseStart_1537555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537555 prefixEnd_1537555 := by exact prefixLift 1537555
  have htrace : WordTrace (prefixWord ++ tailWord_1537555) baseStart_1537555 baseEnd_1537555 := by
    simpa [prefixWord, tailWord_1537555, baseEnd_1537555] using wordTrace_append hprefix tailTrace_1537555
  have hstable : (prefixWord ++ tailWord_1537555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537555).length < 2 ^ (prefixWord ++ tailWord_1537555).sum := by decide
  have hdescent : baseEnd_1537555 < baseStart_1537555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537576 : List Nat := [2, 1, 5, 2, 2, 1, 1, 3, 2, 4]
def baseStart_1537576 : Nat := 118140960795 + 1537576 * 2 ^ 59
def prefixEnd_1537576 : Nat := 4983230072969 + 3 ^ 40 * 1537576 * 2
def baseEnd_1537576 : Nat := 263171843605860486842941

theorem tailTrace_1537576 : CollatzResearch.WordTrace tailWord_1537576 prefixEnd_1537576 263171843605860486842941 := by
  unfold tailWord_1537576
  simp only [CollatzResearch.WordTrace]
  refine ⟨28040001938816111959744291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37386669251754815946325721 28040001938816111959744291)
  ·
    refine ⟨42060002908224167939616437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28040001938816111959744291 42060002908224167939616437)
    ·
      refine ⟨3943125272646015744339041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42060002908224167939616437 3943125272646015744339041)
      ·
        refine ⟨2957343954484511808254281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3943125272646015744339041 2957343954484511808254281)
        ·
          refine ⟨2218007965863383856190711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2957343954484511808254281 2218007965863383856190711)
          ·
            refine ⟨3327011948795075784286067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2218007965863383856190711 3327011948795075784286067)
            ·
              refine ⟨4990517923192613676429101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3327011948795075784286067 4990517923192613676429101)
              ·
                refine ⟨1871444221197230128660913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4990517923192613676429101 1871444221197230128660913)
                ·
                  refine ⟨1403583165897922596495685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1871444221197230128660913 1403583165897922596495685)
                  ·
                    refine ⟨263171843605860486842941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1403583165897922596495685 263171843605860486842941)
                    ·
                      rfl

theorem cell23_1537576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_1537576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537576 prefixEnd_1537576 := by exact prefixLift 1537576
  have htrace : WordTrace (prefixWord ++ tailWord_1537576) baseStart_1537576 baseEnd_1537576 := by
    simpa [prefixWord, tailWord_1537576, baseEnd_1537576] using wordTrace_append hprefix tailTrace_1537576
  have hstable : (prefixWord ++ tailWord_1537576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537576).length < 2 ^ (prefixWord ++ tailWord_1537576).sum := by decide
  have hdescent : baseEnd_1537576 < baseStart_1537576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537609 : List Nat := [1, 2, 1, 1, 2, 2, 1, 7, 1, 3, 2]
def baseStart_1537609 : Nat := 118140960795 + 1537609 * 2 ^ 59
def prefixEnd_1537609 : Nat := 4983230072969 + 3 ^ 40 * 1537609 * 2
def baseEnd_1537609 : Nat := 789532475679179831416171

theorem tailTrace_1537609 : CollatzResearch.WordTrace tailWord_1537609 prefixEnd_1537609 789532475679179831416171 := by
  unfold tailWord_1537609
  simp only [CollatzResearch.WordTrace]
  refine ⟨56081207486512670555439881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37387471657675113703626587 56081207486512670555439881)
  ·
    refine ⟨42060905614884502916579911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56081207486512670555439881 42060905614884502916579911)
    ·
      refine ⟨63091358422326754374869867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42060905614884502916579911 63091358422326754374869867)
      ·
        refine ⟨94637037633490131562304801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63091358422326754374869867 94637037633490131562304801)
        ·
          refine ⟨70977778225117598671728601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94637037633490131562304801 70977778225117598671728601)
          ·
            refine ⟨53233333668838199003796451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70977778225117598671728601 53233333668838199003796451)
            ·
              refine ⟨79850000503257298505694677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53233333668838199003796451 79850000503257298505694677)
              ·
                refine ⟨1871484386795092933727219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 79850000503257298505694677 1871484386795092933727219)
                ·
                  refine ⟨2807226580192639400590829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1871484386795092933727219 2807226580192639400590829)
                  ·
                    refine ⟨1052709967572239775221561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2807226580192639400590829 1052709967572239775221561)
                    ·
                      refine ⟨789532475679179831416171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1052709967572239775221561 789532475679179831416171)
                      ·
                        rfl

theorem cell23_1537609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 3, 2].length) (baseStart_1537609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537609 prefixEnd_1537609 := by exact prefixLift 1537609
  have htrace : WordTrace (prefixWord ++ tailWord_1537609) baseStart_1537609 baseEnd_1537609 := by
    simpa [prefixWord, tailWord_1537609, baseEnd_1537609] using wordTrace_append hprefix tailTrace_1537609
  have hstable : (prefixWord ++ tailWord_1537609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537609).length < 2 ^ (prefixWord ++ tailWord_1537609).sum := by decide
  have hdescent : baseEnd_1537609 < baseStart_1537609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537615 : List Nat := [1, 1, 2, 1, 1, 2, 3, 4, 2, 6]
def baseStart_1537615 : Nat := 118140960795 + 1537615 * 2 ^ 59
def prefixEnd_1537615 : Nat := 4983230072969 + 3 ^ 40 * 1537615 * 2
def baseEnd_1537615 : Nat := 263178518854368935980381

theorem tailTrace_1537615 : CollatzResearch.WordTrace tailWord_1537615 prefixEnd_1537615 263178518854368935980381 := by
  unfold tailWord_1537615
  simp only [CollatzResearch.WordTrace]
  refine ⟨56081426324490933580158299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37387617549660622386772199 56081426324490933580158299)
  ·
    refine ⟨84122139486736400370237449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56081426324490933580158299 84122139486736400370237449)
    ·
      refine ⟨63091604615052300277678087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84122139486736400370237449 63091604615052300277678087)
      ·
        refine ⟨94637406922578450416517131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63091604615052300277678087 94637406922578450416517131)
        ·
          refine ⟨141956110383867675624775697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94637406922578450416517131 141956110383867675624775697)
          ·
            refine ⟨106467082787900756718581773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141956110383867675624775697 106467082787900756718581773)
            ·
              refine ⟨39925156045462783769468165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106467082787900756718581773 39925156045462783769468165)
              ·
                refine ⟨7485966758524271956775281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39925156045462783769468165 7485966758524271956775281)
                ·
                  refine ⟨5614475068893203967581461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7485966758524271956775281 5614475068893203967581461)
                  ·
                    refine ⟨263178518854368935980381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5614475068893203967581461 263178518854368935980381)
                    ·
                      rfl

theorem cell23_1537615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 6].length) (baseStart_1537615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537615 prefixEnd_1537615 := by exact prefixLift 1537615
  have htrace : WordTrace (prefixWord ++ tailWord_1537615) baseStart_1537615 baseEnd_1537615 := by
    simpa [prefixWord, tailWord_1537615, baseEnd_1537615] using wordTrace_append hprefix tailTrace_1537615
  have hstable : (prefixWord ++ tailWord_1537615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537615).length < 2 ^ (prefixWord ++ tailWord_1537615).sum := by decide
  have hdescent : baseEnd_1537615 < baseStart_1537615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537625 : List Nat := [1, 2, 1, 2, 2, 1, 1, 4, 1, 3, 5]
def baseStart_1537625 : Nat := 118140960795 + 1537625 * 2 ^ 59
def prefixEnd_1537625 : Nat := 4983230072969 + 3 ^ 40 * 1537625 * 2
def baseEnd_1537625 : Nat := 789540691369651768816097

theorem tailTrace_1537625 : CollatzResearch.WordTrace tailWord_1537625 prefixEnd_1537625 789540691369651768816097 := by
  unfold tailWord_1537625
  simp only [CollatzResearch.WordTrace]
  refine ⟨56081791054454705288022329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37387860702969803525348219 56081791054454705288022329)
  ·
    refine ⟨42061343290841028966016747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56081791054454705288022329 42061343290841028966016747)
    ·
      refine ⟨63092014936261543449025121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42061343290841028966016747 63092014936261543449025121)
      ·
        refine ⟨47319011202196157586768841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63092014936261543449025121 47319011202196157586768841)
        ·
          refine ⟨35489258401647118190076631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47319011202196157586768841 35489258401647118190076631)
          ·
            refine ⟨53233887602470677285114947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35489258401647118190076631 53233887602470677285114947)
            ·
              refine ⟨79850831403706015927672421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53233887602470677285114947 79850831403706015927672421)
              ·
                refine ⟨14972030888194877986438579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79850831403706015927672421 14972030888194877986438579)
                ·
                  refine ⟨22458046332292316979657869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14972030888194877986438579 22458046332292316979657869)
                  ·
                    refine ⟨8421767374609618867371701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22458046332292316979657869 8421767374609618867371701)
                    ·
                      refine ⟨789540691369651768816097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8421767374609618867371701 789540691369651768816097)
                      ·
                        rfl

theorem cell23_1537625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_1537625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537625 prefixEnd_1537625 := by exact prefixLift 1537625
  have htrace : WordTrace (prefixWord ++ tailWord_1537625) baseStart_1537625 baseEnd_1537625 := by
    simpa [prefixWord, tailWord_1537625, baseEnd_1537625] using wordTrace_append hprefix tailTrace_1537625
  have hstable : (prefixWord ++ tailWord_1537625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537625).length < 2 ^ (prefixWord ++ tailWord_1537625).sum := by decide
  have hdescent : baseEnd_1537625 < baseStart_1537625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537639 : List Nat := [1, 1, 5, 1, 1, 1, 3, 3, 1, 4, 2]
def baseStart_1537639 : Nat := 118140960795 + 1537639 * 2 ^ 59
def prefixEnd_1537639 : Nat := 4983230072969 + 3 ^ 40 * 1537639 * 2
def baseEnd_1537639 : Nat := 789547880098814714041033

theorem tailTrace_1537639 : CollatzResearch.WordTrace tailWord_1537639 prefixEnd_1537639 789547880098814714041033 := by
  unfold tailWord_1537639
  simp only [CollatzResearch.WordTrace]
  refine ⟨56082301676403985679031971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37388201117602657119354647 56082301676403985679031971)
  ·
    refine ⟨84123452514605978518547957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56082301676403985679031971 84123452514605978518547957)
    ·
      refine ⟨7886573673244310486113871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84123452514605978518547957 7886573673244310486113871)
      ·
        refine ⟨11829860509866465729170807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7886573673244310486113871 11829860509866465729170807)
        ·
          refine ⟨17744790764799698593756211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11829860509866465729170807 17744790764799698593756211)
          ·
            refine ⟨26617186147199547890634317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17744790764799698593756211 26617186147199547890634317)
            ·
              refine ⟨9981444805199830458987869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26617186147199547890634317 9981444805199830458987869)
              ·
                refine ⟨3743041801949936422120451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9981444805199830458987869 3743041801949936422120451)
                ·
                  refine ⟨5614562702924904633180677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3743041801949936422120451 5614562702924904633180677)
                  ·
                    refine ⟨1052730506798419618721377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5614562702924904633180677 1052730506798419618721377)
                    ·
                      refine ⟨789547880098814714041033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1052730506798419618721377 789547880098814714041033)
                      ·
                        rfl

theorem cell23_1537639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_1537639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537639 prefixEnd_1537639 := by exact prefixLift 1537639
  have htrace : WordTrace (prefixWord ++ tailWord_1537639) baseStart_1537639 baseEnd_1537639 := by
    simpa [prefixWord, tailWord_1537639, baseEnd_1537639] using wordTrace_append hprefix tailTrace_1537639
  have hstable : (prefixWord ++ tailWord_1537639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537639).length < 2 ^ (prefixWord ++ tailWord_1537639).sum := by decide
  have hdescent : baseEnd_1537639 < baseStart_1537639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537655 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 7]
def baseStart_1537655 : Nat := 118140960795 + 1537655 * 2 ^ 59
def prefixEnd_1537655 : Nat := 4983230072969 + 3 ^ 40 * 1537655 * 2
def baseEnd_1537655 : Nat := 789556095789286651440959

theorem tailTrace_1537655 : CollatzResearch.WordTrace tailWord_1537655 prefixEnd_1537655 789556095789286651440959 := by
  unfold tailWord_1537655
  simp only [CollatzResearch.WordTrace]
  refine ⟨56082885244346020411614419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37388590162897346941076279 56082885244346020411614419)
  ·
    refine ⟨84124327866519030617421629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56082885244346020411614419 84124327866519030617421629)
    ·
      refine ⟨31546622949944636481533111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84124327866519030617421629 31546622949944636481533111)
      ·
        refine ⟨47319934424916954722299667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31546622949944636481533111 47319934424916954722299667)
        ·
          refine ⟨70979901637375432083449501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47319934424916954722299667 70979901637375432083449501)
          ·
            refine ⟨26617463114015787031293563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70979901637375432083449501 26617463114015787031293563)
            ·
              refine ⟨39926194671023680546940345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26617463114015787031293563 39926194671023680546940345)
              ·
                refine ⟨29944646003267760410205259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39926194671023680546940345 29944646003267760410205259)
                ·
                  refine ⟨44916969004901640615307889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29944646003267760410205259 44916969004901640615307889)
                  ·
                    refine ⟨33687726753676230461480917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44916969004901640615307889 33687726753676230461480917)
                    ·
                      refine ⟨789556095789286651440959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 33687726753676230461480917 789556095789286651440959)
                      ·
                        rfl

theorem cell23_1537655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_1537655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537655 prefixEnd_1537655 := by exact prefixLift 1537655
  have htrace : WordTrace (prefixWord ++ tailWord_1537655) baseStart_1537655 baseEnd_1537655 := by
    simpa [prefixWord, tailWord_1537655, baseEnd_1537655] using wordTrace_append hprefix tailTrace_1537655
  have hstable : (prefixWord ++ tailWord_1537655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537655).length < 2 ^ (prefixWord ++ tailWord_1537655).sum := by decide
  have hdescent : baseEnd_1537655 < baseStart_1537655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537709 : List Nat := [1, 5, 2, 1, 1, 1, 2, 3, 2, 5]
def baseStart_1537709 : Nat := 118140960795 + 1537709 * 2 ^ 59
def prefixEnd_1537709 : Nat := 4983230072969 + 3 ^ 40 * 1537709 * 2
def baseEnd_1537709 : Nat := 263194607914876480055237

theorem tailTrace_1537709 : CollatzResearch.WordTrace tailWord_1537709 prefixEnd_1537709 263194607914876480055237 := by
  unfold tailWord_1537709
  simp only [CollatzResearch.WordTrace]
  refine ⟨56084854786150387634080181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37389903190766925089386787 56084854786150387634080181)
  ·
    refine ⟨5257955136201598840695017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56084854786150387634080181 5257955136201598840695017)
    ·
      refine ⟨3943466352151199130521263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5257955136201598840695017 3943466352151199130521263)
      ·
        refine ⟨5915199528226798695781895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3943466352151199130521263 5915199528226798695781895)
        ·
          refine ⟨8872799292340198043672843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5915199528226798695781895 8872799292340198043672843)
          ·
            refine ⟨13309198938510297065509265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8872799292340198043672843 13309198938510297065509265)
            ·
              refine ⟨9981899203882722799131949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13309198938510297065509265 9981899203882722799131949)
              ·
                refine ⟨3743212201456021049674481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9981899203882722799131949 3743212201456021049674481)
                ·
                  refine ⟨2807409151092015787255861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3743212201456021049674481 2807409151092015787255861)
                  ·
                    refine ⟨263194607914876480055237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2807409151092015787255861 263194607914876480055237)
                    ·
                      rfl

theorem cell23_1537709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_1537709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537709 prefixEnd_1537709 := by exact prefixLift 1537709
  have htrace : WordTrace (prefixWord ++ tailWord_1537709) baseStart_1537709 baseEnd_1537709 := by
    simpa [prefixWord, tailWord_1537709, baseEnd_1537709] using wordTrace_append hprefix tailTrace_1537709
  have hstable : (prefixWord ++ tailWord_1537709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537709).length < 2 ^ (prefixWord ++ tailWord_1537709).sum := by decide
  have hdescent : baseEnd_1537709 < baseStart_1537709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537712 : List Nat := [2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 4]
def baseStart_1537712 : Nat := 118140960795 + 1537712 * 2 ^ 59
def prefixEnd_1537712 : Nat := 4983230072969 + 3 ^ 40 * 1537712 * 2
def baseEnd_1537712 : Nat := 789585364186592928428197

theorem tailTrace_1537712 : CollatzResearch.WordTrace tailWord_1537712 prefixEnd_1537712 789585364186592928428197 := by
  unfold tailWord_1537712
  simp only [CollatzResearch.WordTrace]
  refine ⟨28042482102569759573219695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37389976136759679430959593 28042482102569759573219695)
  ·
    refine ⟨42063723153854639359829543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28042482102569759573219695 42063723153854639359829543)
    ·
      refine ⟨63095584730781959039744315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42063723153854639359829543 63095584730781959039744315)
      ·
        refine ⟨94643377096172938559616473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63095584730781959039744315 94643377096172938559616473)
        ·
          refine ⟨70982532822129703919712355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94643377096172938559616473 70982532822129703919712355)
          ·
            refine ⟨106473799233194555879568533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70982532822129703919712355 106473799233194555879568533)
            ·
              refine ⟨4990959339055994806854775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 106473799233194555879568533 4990959339055994806854775)
              ·
                refine ⟨7486439008583992210282163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4990959339055994806854775 7486439008583992210282163)
                ·
                  refine ⟨11229658512875988315423245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7486439008583992210282163 11229658512875988315423245)
                  ·
                    refine ⟨4211121942328495618283717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11229658512875988315423245 4211121942328495618283717)
                    ·
                      refine ⟨789585364186592928428197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4211121942328495618283717 789585364186592928428197)
                      ·
                        rfl

theorem cell23_1537712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 4].length) (baseStart_1537712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537712 prefixEnd_1537712 := by exact prefixLift 1537712
  have htrace : WordTrace (prefixWord ++ tailWord_1537712) baseStart_1537712 baseEnd_1537712 := by
    simpa [prefixWord, tailWord_1537712, baseEnd_1537712] using wordTrace_append hprefix tailTrace_1537712
  have hstable : (prefixWord ++ tailWord_1537712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537712).length < 2 ^ (prefixWord ++ tailWord_1537712).sum := by decide
  have hdescent : baseEnd_1537712 < baseStart_1537712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537730 : List Nat := [3, 5, 1, 2, 1, 2, 1, 1, 7]
def baseStart_1537730 : Nat := 118140960795 + 1537730 * 2 ^ 59
def prefixEnd_1537730 : Nat := 4983230072969 + 3 ^ 40 * 1537730 * 2
def baseEnd_1537730 : Nat := 87732734093152650889235

theorem tailTrace_1537730 : CollatzResearch.WordTrace tailWord_1537730 prefixEnd_1537730 87732734093152650889235 := by
  unfold tailWord_1537730
  simp only [CollatzResearch.WordTrace]
  refine ⟨14021405179768577055148661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37390413812716205480396429 14021405179768577055148661)
  ·
    refine ⟨1314506735603304098920187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14021405179768577055148661 1314506735603304098920187)
    ·
      refine ⟨1971760103404956148380281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1314506735603304098920187 1971760103404956148380281)
      ·
        refine ⟨1478820077553717111285211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1971760103404956148380281 1478820077553717111285211)
        ·
          refine ⟨2218230116330575666927817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1478820077553717111285211 2218230116330575666927817)
          ·
            refine ⟨1663672587247931750195863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2218230116330575666927817 1663672587247931750195863)
            ·
              refine ⟨2495508880871897625293795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1663672587247931750195863 2495508880871897625293795)
              ·
                refine ⟨3743263321307846437940693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2495508880871897625293795 3743263321307846437940693)
                ·
                  refine ⟨87732734093152650889235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3743263321307846437940693 87732734093152650889235)
                  ·
                    rfl

theorem cell23_1537730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_1537730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537730 prefixEnd_1537730 := by exact prefixLift 1537730
  have htrace : WordTrace (prefixWord ++ tailWord_1537730) baseStart_1537730 baseEnd_1537730 := by
    simpa [prefixWord, tailWord_1537730, baseEnd_1537730] using wordTrace_append hprefix tailTrace_1537730
  have hstable : (prefixWord ++ tailWord_1537730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537730).length < 2 ^ (prefixWord ++ tailWord_1537730).sum := by decide
  have hdescent : baseEnd_1537730 < baseStart_1537730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537790 : List Nat := [4, 2, 2, 1, 3, 1, 1, 4, 1, 4]
def baseStart_1537790 : Nat := 118140960795 + 1537790 * 2 ^ 59
def prefixEnd_1537790 : Nat := 4983230072969 + 3 ^ 40 * 1537790 * 2
def baseEnd_1537790 : Nat := 263208471892547874417613

theorem tailTrace_1537790 : CollatzResearch.WordTrace tailWord_1537790 prefixEnd_1537790 263208471892547874417613 := by
  unfold tailWord_1537790
  simp only [CollatzResearch.WordTrace]
  refine ⟨7010976137357117308472353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37391872732571292311852549 7010976137357117308472353)
  ·
    refine ⟨5258232103017837981354265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7010976137357117308472353 5258232103017837981354265)
    ·
      refine ⟨3943674077263378486015699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5258232103017837981354265 3943674077263378486015699)
      ·
        refine ⟨5915511115895067729023549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3943674077263378486015699 5915511115895067729023549)
        ·
          refine ⟨2218316668460650398383831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5915511115895067729023549 2218316668460650398383831)
          ·
            refine ⟨3327475002690975597575747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2218316668460650398383831 3327475002690975597575747)
            ·
              refine ⟨4991212504036463396363621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3327475002690975597575747 4991212504036463396363621)
              ·
                refine ⟨935852344506836886818179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4991212504036463396363621 935852344506836886818179)
                ·
                  refine ⟨1403778516760255330227269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 935852344506836886818179 1403778516760255330227269)
                  ·
                    refine ⟨263208471892547874417613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1403778516760255330227269 263208471892547874417613)
                    ·
                      rfl

theorem cell23_1537790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_1537790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537790 prefixEnd_1537790 := by exact prefixLift 1537790
  have htrace : WordTrace (prefixWord ++ tailWord_1537790) baseStart_1537790 baseEnd_1537790 := by
    simpa [prefixWord, tailWord_1537790, baseEnd_1537790] using wordTrace_append hprefix tailTrace_1537790
  have hstable : (prefixWord ++ tailWord_1537790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537790).length < 2 ^ (prefixWord ++ tailWord_1537790).sum := by decide
  have hdescent : baseEnd_1537790 < baseStart_1537790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537806 : List Nat := [4, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2]
def baseStart_1537806 : Nat := 118140960795 + 1537806 * 2 ^ 59
def prefixEnd_1537806 : Nat := 4983230072969 + 3 ^ 40 * 1537806 * 2
def baseEnd_1537806 : Nat := 789633631368115560652765

theorem tailTrace_1537806 : CollatzResearch.WordTrace tailWord_1537806 prefixEnd_1537806 789633631368115560652765 := by
  unfold tailWord_1537806
  simp only [CollatzResearch.WordTrace]
  refine ⟨7011049083349871650045159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37392261777865982133574181 7011049083349871650045159)
  ·
    refine ⟨10516573625024807475067739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7011049083349871650045159 10516573625024807475067739)
    ·
      refine ⟨15774860437537211212601609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10516573625024807475067739 15774860437537211212601609)
      ·
        refine ⟨11831145328152908409451207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15774860437537211212601609 11831145328152908409451207)
        ·
          refine ⟨17746717992229362614176811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11831145328152908409451207 17746717992229362614176811)
          ·
            refine ⟨26620076988344043921265217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17746717992229362614176811 26620076988344043921265217)
            ·
              refine ⟨19965057741258032940948913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26620076988344043921265217 19965057741258032940948913)
              ·
                refine ⟨14973793305943524705711685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19965057741258032940948913 14973793305943524705711685)
                ·
                  refine ⟨2807586244864410882320941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14973793305943524705711685 2807586244864410882320941)
                  ·
                    refine ⟨1052844841824154080870353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2807586244864410882320941 1052844841824154080870353)
                    ·
                      refine ⟨789633631368115560652765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1052844841824154080870353 789633631368115560652765)
                      ·
                        rfl

theorem cell23_1537806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_1537806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537806 prefixEnd_1537806 := by exact prefixLift 1537806
  have htrace : WordTrace (prefixWord ++ tailWord_1537806) baseStart_1537806 baseEnd_1537806 := by
    simpa [prefixWord, tailWord_1537806, baseEnd_1537806] using wordTrace_append hprefix tailTrace_1537806
  have hstable : (prefixWord ++ tailWord_1537806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537806).length < 2 ^ (prefixWord ++ tailWord_1537806).sum := by decide
  have hdescent : baseEnd_1537806 < baseStart_1537806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537819 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 2, 6, 2]
def baseStart_1537819 : Nat := 118140960795 + 1537819 * 2 ^ 59
def prefixEnd_1537819 : Nat := 4983230072969 + 3 ^ 40 * 1537819 * 2
def baseEnd_1537819 : Nat := 789640306616624009790205

theorem tailTrace_1537819 : CollatzResearch.WordTrace tailWord_1537819 prefixEnd_1537819 789640306616624009790205 := by
  unfold tailWord_1537819
  simp only [CollatzResearch.WordTrace]
  refine ⟨56088866815751876420584511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37392577877167917613723007 56088866815751876420584511)
  ·
    refine ⟨84133300223627814630876767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56088866815751876420584511 84133300223627814630876767)
    ·
      refine ⟨126199950335441721946315151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84133300223627814630876767 126199950335441721946315151)
      ·
        refine ⟨189299925503162582919472727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126199950335441721946315151 189299925503162582919472727)
        ·
          refine ⟨283949888254743874379209091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189299925503162582919472727 283949888254743874379209091)
          ·
            refine ⟨425924832382115811568813637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283949888254743874379209091 425924832382115811568813637)
            ·
              refine ⟨79860906071646714669152557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 425924832382115811568813637 79860906071646714669152557)
              ·
                refine ⟨29947839776867518000932209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79860906071646714669152557 29947839776867518000932209)
                ·
                  refine ⟨22460879832650638500699157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29947839776867518000932209 22460879832650638500699157)
                  ·
                    refine ⟨1052853742155498679720273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22460879832650638500699157 1052853742155498679720273)
                    ·
                      refine ⟨789640306616624009790205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1052853742155498679720273 789640306616624009790205)
                      ·
                        rfl

theorem cell23_1537819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 6, 2].length) (baseStart_1537819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537819 prefixEnd_1537819 := by exact prefixLift 1537819
  have htrace : WordTrace (prefixWord ++ tailWord_1537819) baseStart_1537819 baseEnd_1537819 := by
    simpa [prefixWord, tailWord_1537819, baseEnd_1537819] using wordTrace_append hprefix tailTrace_1537819
  have hstable : (prefixWord ++ tailWord_1537819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537819).length < 2 ^ (prefixWord ++ tailWord_1537819).sum := by decide
  have hdescent : baseEnd_1537819 < baseStart_1537819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537829 : List Nat := [1, 3, 1, 2, 3, 2, 2, 2, 1, 6]
def baseStart_1537829 : Nat := 118140960795 + 1537829 * 2 ^ 59
def prefixEnd_1537829 : Nat := 4983230072969 + 3 ^ 40 * 1537829 * 2
def baseEnd_1537829 : Nat := 263215147141056323555053

theorem tailTrace_1537829 : CollatzResearch.WordTrace tailWord_1537829 prefixEnd_1537829 263215147141056323555053 := by
  unfold tailWord_1537829
  simp only [CollatzResearch.WordTrace]
  refine ⟨56089231545715648128448541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37392821030477098752299027 56089231545715648128448541)
  ·
    refine ⟨21033461829643368048168203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56089231545715648128448541 21033461829643368048168203)
    ·
      refine ⟨31550192744465052072252305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21033461829643368048168203 31550192744465052072252305)
      ·
        refine ⟨23662644558348789054189229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31550192744465052072252305 23662644558348789054189229)
        ·
          refine ⟨8873491709380795895320961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23662644558348789054189229 8873491709380795895320961)
          ·
            refine ⟨6655118782035596921490721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8873491709380795895320961 6655118782035596921490721)
            ·
              refine ⟨4991339086526697691118041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6655118782035596921490721 4991339086526697691118041)
              ·
                refine ⟨3743504314895023268338531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4991339086526697691118041 3743504314895023268338531)
                ·
                  refine ⟨5615256472342534902507797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3743504314895023268338531 5615256472342534902507797)
                  ·
                    refine ⟨263215147141056323555053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5615256472342534902507797 263215147141056323555053)
                    ·
                      rfl

theorem cell23_1537829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 6].length) (baseStart_1537829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537829 prefixEnd_1537829 := by exact prefixLift 1537829
  have htrace : WordTrace (prefixWord ++ tailWord_1537829) baseStart_1537829 baseEnd_1537829 := by
    simpa [prefixWord, tailWord_1537829, baseEnd_1537829] using wordTrace_append hprefix tailTrace_1537829
  have hstable : (prefixWord ++ tailWord_1537829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537829).length < 2 ^ (prefixWord ++ tailWord_1537829).sum := by decide
  have hdescent : baseEnd_1537829 < baseStart_1537829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537836 : List Nat := [2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 4]
def baseStart_1537836 : Nat := 118140960795 + 1537836 * 2 ^ 59
def prefixEnd_1537836 : Nat := 4983230072969 + 3 ^ 40 * 1537836 * 2
def baseEnd_1537836 : Nat := 789649035787750443277627

theorem tailTrace_1537836 : CollatzResearch.WordTrace tailWord_1537836 prefixEnd_1537836 789649035787750443277627 := by
  unfold tailWord_1537836
  simp only [CollatzResearch.WordTrace]
  refine ⟨28044743428345144161976681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37392991237793525549302241 28044743428345144161976681)
  ·
    refine ⟨21033557571258858121482511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28044743428345144161976681 21033557571258858121482511)
    ·
      refine ⟨31550336356888287182223767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21033557571258858121482511 31550336356888287182223767)
      ·
        refine ⟨47325504535332430773335651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31550336356888287182223767 47325504535332430773335651)
        ·
          refine ⟨70988256802998646160003477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47325504535332430773335651 70988256802998646160003477)
          ·
            refine ⟨3327574537640561538750163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 70988256802998646160003477 3327574537640561538750163)
            ·
              refine ⟨4991361806460842308125245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3327574537640561538750163 4991361806460842308125245)
              ·
                refine ⟨1871760677422815865546967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4991361806460842308125245 1871760677422815865546967)
                ·
                  refine ⟨2807641016134223798320451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1871760677422815865546967 2807641016134223798320451)
                  ·
                    refine ⟨4211461524201335697480677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2807641016134223798320451 4211461524201335697480677)
                    ·
                      refine ⟨789649035787750443277627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4211461524201335697480677 789649035787750443277627)
                      ·
                        rfl

theorem cell23_1537836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 4].length) (baseStart_1537836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537836 prefixEnd_1537836 := by exact prefixLift 1537836
  have htrace : WordTrace (prefixWord ++ tailWord_1537836) baseStart_1537836 baseEnd_1537836 := by
    simpa [prefixWord, tailWord_1537836, baseEnd_1537836] using wordTrace_append hprefix tailTrace_1537836
  have hstable : (prefixWord ++ tailWord_1537836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537836).length < 2 ^ (prefixWord ++ tailWord_1537836).sum := by decide
  have hdescent : baseEnd_1537836 < baseStart_1537836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537873 : List Nat := [1, 2, 2, 1, 5, 2, 2, 2, 1, 2, 3]
def baseStart_1537873 : Nat := 118140960795 + 1537873 * 2 ^ 59
def prefixEnd_1537873 : Nat := 4983230072969 + 3 ^ 40 * 1537873 * 2
def baseEnd_1537873 : Nat := 789668034571966798514957

theorem tailTrace_1537873 : CollatzResearch.WordTrace tailWord_1537873 prefixEnd_1537873 789668034571966798514957 := by
  unfold tailWord_1537873
  simp only [CollatzResearch.WordTrace]
  refine ⟨56090836357556243643050273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37393890905037495762033515 56090836357556243643050273)
  ·
    refine ⟨42068127268167182732287705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56090836357556243643050273 42068127268167182732287705)
    ·
      refine ⟨31551095451125387049215779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42068127268167182732287705 31551095451125387049215779)
      ·
        refine ⟨47326643176688080573823669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31551095451125387049215779 47326643176688080573823669)
        ·
          refine ⟨4436872797814507553795969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47326643176688080573823669 4436872797814507553795969)
          ·
            refine ⟨3327654598360880665346977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4436872797814507553795969 3327654598360880665346977)
            ·
              refine ⟨2495740948770660499010233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3327654598360880665346977 2495740948770660499010233)
              ·
                refine ⟨1871805711577995374257675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2495740948770660499010233 1871805711577995374257675)
                ·
                  refine ⟨2807708567366993061386513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1871805711577995374257675 2807708567366993061386513)
                  ·
                    refine ⟨2105781425525244796039885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2807708567366993061386513 2105781425525244796039885)
                    ·
                      refine ⟨789668034571966798514957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2105781425525244796039885 789668034571966798514957)
                      ·
                        rfl

theorem cell23_1537873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 2, 3].length) (baseStart_1537873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537873 prefixEnd_1537873 := by exact prefixLift 1537873
  have htrace : WordTrace (prefixWord ++ tailWord_1537873) baseStart_1537873 baseEnd_1537873 := by
    simpa [prefixWord, tailWord_1537873, baseEnd_1537873] using wordTrace_append hprefix tailTrace_1537873
  have hstable : (prefixWord ++ tailWord_1537873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537873).length < 2 ^ (prefixWord ++ tailWord_1537873).sum := by decide
  have hdescent : baseEnd_1537873 < baseStart_1537873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537876 : List Nat := [2, 4, 1, 1, 3, 1, 4, 7]
def baseStart_1537876 : Nat := 118140960795 + 1537876 * 2 ^ 59
def prefixEnd_1537876 : Nat := 4983230072969 + 3 ^ 40 * 1537876 * 2
def baseEnd_1537876 : Nat := 29247021296812232843609

theorem tailTrace_1537876 : CollatzResearch.WordTrace tailWord_1537876 prefixEnd_1537876 29247021296812232843609 := by
  unfold tailWord_1537876
  simp only [CollatzResearch.WordTrace]
  refine ⟨28045472888272687577704741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37393963851030250103606321 28045472888272687577704741)
  ·
    refine ⟨5258526166551128920819639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28045472888272687577704741 5258526166551128920819639)
    ·
      refine ⟨7887789249826693381229459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5258526166551128920819639 7887789249826693381229459)
      ·
        refine ⟨11831683874740040071844189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7887789249826693381229459 11831683874740040071844189)
        ·
          refine ⟨4436881453027515026941571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11831683874740040071844189 4436881453027515026941571)
          ·
            refine ⟨6655322179541272540412357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4436881453027515026941571 6655322179541272540412357)
            ·
              refine ⟨1247872908663988601327317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6655322179541272540412357 1247872908663988601327317)
              ·
                refine ⟨29247021296812232843609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1247872908663988601327317 29247021296812232843609)
                ·
                  rfl

theorem cell23_1537876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 7].length) (baseStart_1537876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537876 prefixEnd_1537876 := by exact prefixLift 1537876
  have htrace : WordTrace (prefixWord ++ tailWord_1537876) baseStart_1537876 baseEnd_1537876 := by
    simpa [prefixWord, tailWord_1537876, baseEnd_1537876] using wordTrace_append hprefix tailTrace_1537876
  have hstable : (prefixWord ++ tailWord_1537876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537876).length < 2 ^ (prefixWord ++ tailWord_1537876).sum := by decide
  have hdescent : baseEnd_1537876 < baseStart_1537876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537887 : List Nat := [1, 1, 2, 3, 1, 6, 1, 3, 1, 2, 2]
def baseStart_1537887 : Nat := 118140960795 + 1537887 * 2 ^ 59
def prefixEnd_1537887 : Nat := 4983230072969 + 3 ^ 40 * 1537887 * 2
def baseEnd_1537887 : Nat := 789675223301129743739893

theorem tailTrace_1537887 : CollatzResearch.WordTrace tailWord_1537887 prefixEnd_1537887 789675223301129743739893 := by
  unfold tailWord_1537887
  simp only [CollatzResearch.WordTrace]
  refine ⟨56091346979505524034059915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37394231319670349356039943 56091346979505524034059915)
  ·
    refine ⟨84137020469258286051089873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56091346979505524034059915 84137020469258286051089873)
    ·
      refine ⟨63102765351943714538317405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84137020469258286051089873 63102765351943714538317405)
      ·
        refine ⟨23663537006978892951869027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63102765351943714538317405 23663537006978892951869027)
        ·
          refine ⟨35495305510468339427803541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23663537006978892951869027 35495305510468339427803541)
          ·
            refine ⟨1663842445803203410678291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35495305510468339427803541 1663842445803203410678291)
            ·
              refine ⟨2495763668704805116017437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1663842445803203410678291 2495763668704805116017437)
              ·
                refine ⟨935911375764301918506539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2495763668704805116017437 935911375764301918506539)
                ·
                  refine ⟨1403867063646452877759809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 935911375764301918506539 1403867063646452877759809)
                  ·
                    refine ⟨1052900297734839658319857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1403867063646452877759809 1052900297734839658319857)
                    ·
                      refine ⟨789675223301129743739893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1052900297734839658319857 789675223301129743739893)
                      ·
                        rfl

theorem cell23_1537887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 3, 1, 2, 2].length) (baseStart_1537887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537887 prefixEnd_1537887 := by exact prefixLift 1537887
  have htrace : WordTrace (prefixWord ++ tailWord_1537887) baseStart_1537887 baseEnd_1537887 := by
    simpa [prefixWord, tailWord_1537887, baseEnd_1537887] using wordTrace_append hprefix tailTrace_1537887
  have hstable : (prefixWord ++ tailWord_1537887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537887).length < 2 ^ (prefixWord ++ tailWord_1537887).sum := by decide
  have hdescent : baseEnd_1537887 < baseStart_1537887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537929 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 4, 1, 5]
def baseStart_1537929 : Nat := 118140960795 + 1537929 * 2 ^ 59
def prefixEnd_1537929 : Nat := 4983230072969 + 3 ^ 40 * 1537929 * 2
def baseEnd_1537929 : Nat := 789696789488618579414699

theorem tailTrace_1537929 : CollatzResearch.WordTrace tailWord_1537929 prefixEnd_1537929 789696789488618579414699 := by
  unfold tailWord_1537929
  simp only [CollatzResearch.WordTrace]
  refine ⟨56092878845353365207088841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37395252563568910138059227 56092878845353365207088841)
  ·
    refine ⟨42069659134015023905316631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56092878845353365207088841 42069659134015023905316631)
    ·
      refine ⟨63104488701022535857974947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42069659134015023905316631 63104488701022535857974947)
      ·
        refine ⟨94656733051533803786962421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63104488701022535857974947 94656733051533803786962421)
        ·
          refine ⟨8874068723581294105027727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94656733051533803786962421 8874068723581294105027727)
          ·
            refine ⟨13311103085371941157541591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8874068723581294105027727 13311103085371941157541591)
            ·
              refine ⟨19966654628057911736312387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13311103085371941157541591 19966654628057911736312387)
              ·
                refine ⟨29949981942086867604468581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19966654628057911736312387 29949981942086867604468581)
                ·
                  refine ⟨5615621614141287675837859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29949981942086867604468581 5615621614141287675837859)
                  ·
                    refine ⟨8423432421211931513756789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5615621614141287675837859 8423432421211931513756789)
                    ·
                      refine ⟨789696789488618579414699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8423432421211931513756789 789696789488618579414699)
                      ·
                        rfl

theorem cell23_1537929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 1, 5].length) (baseStart_1537929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537929 prefixEnd_1537929 := by exact prefixLift 1537929
  have htrace : WordTrace (prefixWord ++ tailWord_1537929) baseStart_1537929 baseEnd_1537929 := by
    simpa [prefixWord, tailWord_1537929, baseEnd_1537929] using wordTrace_append hprefix tailTrace_1537929
  have hstable : (prefixWord ++ tailWord_1537929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537929).length < 2 ^ (prefixWord ++ tailWord_1537929).sum := by decide
  have hdescent : baseEnd_1537929 < baseStart_1537929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537930 : List Nat := [3, 1, 2, 4, 2, 1, 1, 1, 3, 3, 2]
def baseStart_1537930 : Nat := 118140960795 + 1537930 * 2 ^ 59
def prefixEnd_1537930 : Nat := 4983230072969 + 3 ^ 40 * 1537930 * 2
def baseEnd_1537930 : Nat := 789697302969273075502195

theorem tailTrace_1537930 : CollatzResearch.WordTrace tailWord_1537930 prefixEnd_1537930 789697302969273075502195 := by
  unfold tailWord_1537930
  simp only [CollatzResearch.WordTrace]
  refine ⟨14023228829587435594468811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37395276878899828251916829 14023228829587435594468811)
  ·
    refine ⟨21034843244381153391703217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14023228829587435594468811 21034843244381153391703217)
    ·
      refine ⟨15776132433285865043777413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21034843244381153391703217 15776132433285865043777413)
      ·
        refine ⟨2958024831241099695708265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15776132433285865043777413 2958024831241099695708265)
        ·
          refine ⟨2218518623430824771781199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2958024831241099695708265 2218518623430824771781199)
          ·
            refine ⟨3327777935146237157671799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2218518623430824771781199 3327777935146237157671799)
            ·
              refine ⟨4991666902719355736507699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3327777935146237157671799 4991666902719355736507699)
              ·
                refine ⟨7487500354079033604761549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4991666902719355736507699 7487500354079033604761549)
                ·
                  refine ⟨2807812632779637601785581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7487500354079033604761549 2807812632779637601785581)
                  ·
                    refine ⟨1052929737292364100669593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2807812632779637601785581 1052929737292364100669593)
                    ·
                      refine ⟨789697302969273075502195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1052929737292364100669593 789697302969273075502195)
                      ·
                        rfl

theorem cell23_1537930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_1537930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537930 prefixEnd_1537930 := by exact prefixLift 1537930
  have htrace : WordTrace (prefixWord ++ tailWord_1537930) baseStart_1537930 baseEnd_1537930 := by
    simpa [prefixWord, tailWord_1537930, baseEnd_1537930] using wordTrace_append hprefix tailTrace_1537930
  have hstable : (prefixWord ++ tailWord_1537930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537930).length < 2 ^ (prefixWord ++ tailWord_1537930).sum := by decide
  have hdescent : baseEnd_1537930 < baseStart_1537930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537943 : List Nat := [1, 1, 3, 3, 1, 4, 1, 2, 1, 4, 2]
def baseStart_1537943 : Nat := 118140960795 + 1537943 * 2 ^ 59
def prefixEnd_1537943 : Nat := 4983230072969 + 3 ^ 40 * 1537943 * 2
def baseEnd_1537943 : Nat := 789703978217781524639635

theorem tailTrace_1537943 : CollatzResearch.WordTrace tailWord_1537943 prefixEnd_1537943 789703978217781524639635 := by
  unfold tailWord_1537943
  simp only [CollatzResearch.WordTrace]
  refine ⟨56093389467302645598098483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37395592978201763732065655 56093389467302645598098483)
  ·
    refine ⟨84140084200953968397147725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56093389467302645598098483 84140084200953968397147725)
    ·
      refine ⟨31552531575357738148930397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84140084200953968397147725 31552531575357738148930397)
      ·
        refine ⟨11832199340759151805848899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31552531575357738148930397 11832199340759151805848899)
        ·
          refine ⟨17748299011138727708773349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11832199340759151805848899 17748299011138727708773349)
          ·
            refine ⟨3327806064588511445395003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17748299011138727708773349 3327806064588511445395003)
            ·
              refine ⟨4991709096882767168092505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3327806064588511445395003 4991709096882767168092505)
              ·
                refine ⟨3743781822662075376069379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4991709096882767168092505 3743781822662075376069379)
                ·
                  refine ⟨5615672733993113064104069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3743781822662075376069379 5615672733993113064104069)
                  ·
                    refine ⟨1052938637623708699519513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5615672733993113064104069 1052938637623708699519513)
                    ·
                      refine ⟨789703978217781524639635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1052938637623708699519513 789703978217781524639635)
                      ·
                        rfl

theorem cell23_1537943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_1537943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537943 prefixEnd_1537943 := by exact prefixLift 1537943
  have htrace : WordTrace (prefixWord ++ tailWord_1537943) baseStart_1537943 baseEnd_1537943 := by
    simpa [prefixWord, tailWord_1537943, baseEnd_1537943] using wordTrace_append hprefix tailTrace_1537943
  have hstable : (prefixWord ++ tailWord_1537943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537943).length < 2 ^ (prefixWord ++ tailWord_1537943).sum := by decide
  have hdescent : baseEnd_1537943 < baseStart_1537943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537946 : List Nat := [3, 1, 1, 4, 2, 1, 2, 1, 2, 1, 5]
def baseStart_1537946 : Nat := 118140960795 + 1537946 * 2 ^ 59
def prefixEnd_1537946 : Nat := 4983230072969 + 3 ^ 40 * 1537946 * 2
def baseEnd_1537946 : Nat := 789705518659745012902121

theorem tailTrace_1537946 : CollatzResearch.WordTrace tailWord_1537946 prefixEnd_1537946 789705518659745012902121 := by
  unfold tailWord_1537946
  simp only [CollatzResearch.WordTrace]
  refine ⟨14023374721572944277614423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37395665924194518073638461 14023374721572944277614423)
  ·
    refine ⟨21035062082359416416421635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14023374721572944277614423 21035062082359416416421635)
    ·
      refine ⟨31552593123539124624632453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21035062082359416416421635 31552593123539124624632453)
      ·
        refine ⟨5916111210663585867118585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31552593123539124624632453 5916111210663585867118585)
        ·
          refine ⟨4437083407997689400338939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5916111210663585867118585 4437083407997689400338939)
          ·
            refine ⟨6655625111996534100508409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4437083407997689400338939 6655625111996534100508409)
            ·
              refine ⟨4991718833997400575381307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6655625111996534100508409 4991718833997400575381307)
              ·
                refine ⟨7487578250996100863071961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4991718833997400575381307 7487578250996100863071961)
                ·
                  refine ⟨5615683688247075647303971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7487578250996100863071961 5615683688247075647303971)
                  ·
                    refine ⟨8423525532370613470955957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5615683688247075647303971 8423525532370613470955957)
                    ·
                      refine ⟨789705518659745012902121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8423525532370613470955957 789705518659745012902121)
                      ·
                        rfl

theorem cell23_1537946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_1537946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537946 prefixEnd_1537946 := by exact prefixLift 1537946
  have htrace : WordTrace (prefixWord ++ tailWord_1537946) baseStart_1537946 baseEnd_1537946 := by
    simpa [prefixWord, tailWord_1537946, baseEnd_1537946] using wordTrace_append hprefix tailTrace_1537946
  have hstable : (prefixWord ++ tailWord_1537946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537946).length < 2 ^ (prefixWord ++ tailWord_1537946).sum := by decide
  have hdescent : baseEnd_1537946 < baseStart_1537946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537976 : List Nat := [2, 1, 2, 1, 2, 3, 3, 1, 2, 3, 3]
def baseStart_1537976 : Nat := 118140960795 + 1537976 * 2 ^ 59
def prefixEnd_1537976 : Nat := 4983230072969 + 3 ^ 40 * 1537976 * 2
def baseEnd_1537976 : Nat := 789720923079379895526983

theorem tailTrace_1537976 : CollatzResearch.WordTrace tailWord_1537976 prefixEnd_1537976 789720923079379895526983 := by
  unfold tailWord_1537976
  simp only [CollatzResearch.WordTrace]
  refine ⟨28047296538091546117024891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37396395384122061489366521 28047296538091546117024891)
  ·
    refine ⟨42070944807137319175537337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28047296538091546117024891 42070944807137319175537337)
    ·
      refine ⟨31553208605352989381653003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42070944807137319175537337 31553208605352989381653003)
      ·
        refine ⟨47329812908029484072479505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31553208605352989381653003 47329812908029484072479505)
        ·
          refine ⟨35497359681022113054359629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47329812908029484072479505 35497359681022113054359629)
          ·
            refine ⟨13311509880383292395384861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35497359681022113054359629 13311509880383292395384861)
            ·
              refine ⟨4991816205143734648269323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13311509880383292395384861 4991816205143734648269323)
              ·
                refine ⟨7487724307715601972403985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4991816205143734648269323 7487724307715601972403985)
                ·
                  refine ⟨5615793230786701479302989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7487724307715601972403985 5615793230786701479302989)
                  ·
                    refine ⟨2105922461545013054738621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5615793230786701479302989 2105922461545013054738621)
                    ·
                      refine ⟨789720923079379895526983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2105922461545013054738621 789720923079379895526983)
                      ·
                        rfl

theorem cell23_1537976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 2, 3, 3].length) (baseStart_1537976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537976 prefixEnd_1537976 := by exact prefixLift 1537976
  have htrace : WordTrace (prefixWord ++ tailWord_1537976) baseStart_1537976 baseEnd_1537976 := by
    simpa [prefixWord, tailWord_1537976, baseEnd_1537976] using wordTrace_append hprefix tailTrace_1537976
  have hstable : (prefixWord ++ tailWord_1537976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537976).length < 2 ^ (prefixWord ++ tailWord_1537976).sum := by decide
  have hdescent : baseEnd_1537976 < baseStart_1537976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537979 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 6, 5]
def baseStart_1537979 : Nat := 118140960795 + 1537979 * 2 ^ 59
def prefixEnd_1537979 : Nat := 4983230072969 + 3 ^ 40 * 1537979 * 2
def baseEnd_1537979 : Nat := 263240821173781127929823

theorem tailTrace_1537979 : CollatzResearch.WordTrace tailWord_1537979 prefixEnd_1537979 263240821173781127929823 := by
  unfold tailWord_1537979
  simp only [CollatzResearch.WordTrace]
  refine ⟨56094702495172223746408991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37396468330114815830939327 56094702495172223746408991)
  ·
    refine ⟨84142053742758335619613487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56094702495172223746408991 84142053742758335619613487)
    ·
      refine ⟨126213080614137503429420231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84142053742758335619613487 126213080614137503429420231)
      ·
        refine ⟨189319620921206255144130347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126213080614137503429420231 189319620921206255144130347)
        ·
          refine ⟨283979431381809382716195521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189319620921206255144130347 283979431381809382716195521)
          ·
            refine ⟨212984573536357037037146641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283979431381809382716195521 212984573536357037037146641)
            ·
              refine ⟨159738430152267777777859981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212984573536357037037146641 159738430152267777777859981)
              ·
                refine ⟨59901911307100416666697493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 159738430152267777777859981 59901911307100416666697493)
                ·
                  refine ⟨2807902092520332031251445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 59901911307100416666697493 2807902092520332031251445)
                  ·
                    refine ⟨263240821173781127929823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2807902092520332031251445 263240821173781127929823)
                    ·
                      rfl

theorem cell23_1537979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 5].length) (baseStart_1537979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537979 prefixEnd_1537979 := by exact prefixLift 1537979
  have htrace : WordTrace (prefixWord ++ tailWord_1537979) baseStart_1537979 baseEnd_1537979 := by
    simpa [prefixWord, tailWord_1537979, baseEnd_1537979] using wordTrace_append hprefix tailTrace_1537979
  have hstable : (prefixWord ++ tailWord_1537979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537979).length < 2 ^ (prefixWord ++ tailWord_1537979).sum := by decide
  have hdescent : baseEnd_1537979 < baseStart_1537979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537989 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 3, 2, 5]
def baseStart_1537989 : Nat := 118140960795 + 1537989 * 2 ^ 59
def prefixEnd_1537989 : Nat := 4983230072969 + 3 ^ 40 * 1537989 * 2
def baseEnd_1537989 : Nat := 789727598327888344664423

theorem tailTrace_1537989 : CollatzResearch.WordTrace tailWord_1537989 prefixEnd_1537989 789727598327888344664423 := by
  unfold tailWord_1537989
  simp only [CollatzResearch.WordTrace]
  refine ⟨56095067225135995454273021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37396711483423996969515347 56095067225135995454273021)
  ·
    refine ⟨21035650209425998295352383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56095067225135995454273021 21035650209425998295352383)
    ·
      refine ⟨31553475314138997443028575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21035650209425998295352383 31553475314138997443028575)
      ·
        refine ⟨47330212971208496164542863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31553475314138997443028575 47330212971208496164542863)
        ·
          refine ⟨70995319456812744246814295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47330212971208496164542863 70995319456812744246814295)
          ·
            refine ⟨106492979185219116370221443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70995319456812744246814295 106492979185219116370221443)
            ·
              refine ⟨159739468777828674555332165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106492979185219116370221443 159739468777828674555332165)
              ·
                refine ⟨29951150395842876479124781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159739468777828674555332165 29951150395842876479124781)
                ·
                  refine ⟨11231681398441078679671793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29951150395842876479124781 11231681398441078679671793)
                  ·
                    refine ⟨8423761048830809009753845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11231681398441078679671793 8423761048830809009753845)
                    ·
                      refine ⟨789727598327888344664423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8423761048830809009753845 789727598327888344664423)
                      ·
                        rfl

theorem cell23_1537989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_1537989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537989 prefixEnd_1537989 := by exact prefixLift 1537989
  have htrace : WordTrace (prefixWord ++ tailWord_1537989) baseStart_1537989 baseEnd_1537989 := by
    simpa [prefixWord, tailWord_1537989, baseEnd_1537989] using wordTrace_append hprefix tailTrace_1537989
  have hstable : (prefixWord ++ tailWord_1537989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537989).length < 2 ^ (prefixWord ++ tailWord_1537989).sum := by decide
  have hdescent : baseEnd_1537989 < baseStart_1537989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537996 : List Nat := [2, 2, 1, 4, 1, 3, 1, 1, 1, 7]
def baseStart_1537996 : Nat := 118140960795 + 1537996 * 2 ^ 59
def prefixEnd_1537996 : Nat := 4983230072969 + 3 ^ 40 * 1537996 * 2
def baseEnd_1537996 : Nat := 263243730897489939092297

theorem tailTrace_1537996 : CollatzResearch.WordTrace tailWord_1537996 prefixEnd_1537996 263243730897489939092297 := by
  unfold tailWord_1537996
  simp only [CollatzResearch.WordTrace]
  refine ⟨28047661268055317824888921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37396881690740423766518561 28047661268055317824888921)
  ·
    refine ⟨21035745951041488368666691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28047661268055317824888921 21035745951041488368666691)
    ·
      refine ⟨31553618926562232553000037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21035745951041488368666691 31553618926562232553000037)
      ·
        refine ⟨5916303548730418603687507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31553618926562232553000037 5916303548730418603687507)
        ·
          refine ⟨8874455323095627905531261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5916303548730418603687507 8874455323095627905531261)
          ·
            refine ⟨3327920746160860464574223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8874455323095627905531261 3327920746160860464574223)
            ·
              refine ⟨4991881119241290696861335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3327920746160860464574223 4991881119241290696861335)
              ·
                refine ⟨7487821678861936045292003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4991881119241290696861335 7487821678861936045292003)
                ·
                  refine ⟨11231732518292904067938005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7487821678861936045292003 11231732518292904067938005)
                  ·
                    refine ⟨263243730897489939092297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11231732518292904067938005 263243730897489939092297)
                    ·
                      rfl

theorem cell23_1537996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 1, 7].length) (baseStart_1537996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1537996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1537996 prefixEnd_1537996 := by exact prefixLift 1537996
  have htrace : WordTrace (prefixWord ++ tailWord_1537996) baseStart_1537996 baseEnd_1537996 := by
    simpa [prefixWord, tailWord_1537996, baseEnd_1537996] using wordTrace_append hprefix tailTrace_1537996
  have hstable : (prefixWord ++ tailWord_1537996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537996).length < 2 ^ (prefixWord ++ tailWord_1537996).sum := by decide
  have hdescent : baseEnd_1537996 < baseStart_1537996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538016 : List Nat := [2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 4]
def baseStart_1538016 : Nat := 118140960795 + 1538016 * 2 ^ 59
def prefixEnd_1538016 : Nat := 4983230072969 + 3 ^ 40 * 1538016 * 2
def baseEnd_1538016 : Nat := 789741462305559739026799

theorem tailTrace_1538016 : CollatzResearch.WordTrace tailWord_1538016 prefixEnd_1538016 789741462305559739026799 := by
  unfold tailWord_1538016
  simp only [CollatzResearch.WordTrace]
  refine ⟨28048025998019089532752951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37397367997358786043670601 28048025998019089532752951)
  ·
    refine ⟨42072038997028634299129427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28048025998019089532752951 42072038997028634299129427)
    ·
      refine ⟨63108058495542951448694141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42072038997028634299129427 63108058495542951448694141)
      ·
        refine ⟨23665521935828606793260303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63108058495542951448694141 23665521935828606793260303)
        ·
          refine ⟨35498282903742910189890455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23665521935828606793260303 35498282903742910189890455)
          ·
            refine ⟨53247424355614365284835683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35498282903742910189890455 53247424355614365284835683)
            ·
              refine ⟨79871136533421547927253525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53247424355614365284835683 79871136533421547927253525)
              ·
                refine ⟨3743959525004135059090009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 79871136533421547927253525 3743959525004135059090009)
                ·
                  refine ⟨2807969643753101294317507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3743959525004135059090009 2807969643753101294317507)
                  ·
                    refine ⟨4211954465629651941476261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2807969643753101294317507 4211954465629651941476261)
                    ·
                      refine ⟨789741462305559739026799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4211954465629651941476261 789741462305559739026799)
                      ·
                        rfl

theorem cell23_1538016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_1538016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1538016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1538016 prefixEnd_1538016 := by exact prefixLift 1538016
  have htrace : WordTrace (prefixWord ++ tailWord_1538016) baseStart_1538016 baseEnd_1538016 := by
    simpa [prefixWord, tailWord_1538016, baseEnd_1538016] using wordTrace_append hprefix tailTrace_1538016
  have hstable : (prefixWord ++ tailWord_1538016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538016).length < 2 ^ (prefixWord ++ tailWord_1538016).sum := by decide
  have hdescent : baseEnd_1538016 < baseStart_1538016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538090 : List Nat := [3, 1, 4, 1, 2, 1, 4, 1, 6]
def baseStart_1538090 : Nat := 118140960795 + 1538090 * 2 ^ 59
def prefixEnd_1538090 : Nat := 4983230072969 + 3 ^ 40 * 1538090 * 2
def baseEnd_1538090 : Nat := 87753273319332494389051

theorem tailTrace_1538090 : CollatzResearch.WordTrace tailWord_1538090 prefixEnd_1538090 87753273319332494389051 := by
  unfold tailWord_1538090
  simp only [CollatzResearch.WordTrace]
  refine ⟨14024687749442522425924931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37399167331846726469133149 14024687749442522425924931)
  ·
    refine ⟨21037031624163783638887397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14024687749442522425924931 21037031624163783638887397)
    ·
      refine ⟨3944443429530709432291387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21037031624163783638887397 3944443429530709432291387)
      ·
        refine ⟨5916665144296064148437081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3944443429530709432291387 5916665144296064148437081)
        ·
          refine ⟨4437498858222048111327811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5916665144296064148437081 4437498858222048111327811)
          ·
            refine ⟨6656248287333072166991717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4437498858222048111327811 6656248287333072166991717)
            ·
              refine ⟨1248046553874951031310947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6656248287333072166991717 1248046553874951031310947)
              ·
                refine ⟨1872069830812426546966421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1248046553874951031310947 1872069830812426546966421)
                ·
                  refine ⟨87753273319332494389051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1872069830812426546966421 87753273319332494389051)
                  ·
                    rfl

theorem cell23_1538090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 6].length) (baseStart_1538090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1538090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1538090 prefixEnd_1538090 := by exact prefixLift 1538090
  have htrace : WordTrace (prefixWord ++ tailWord_1538090) baseStart_1538090 baseEnd_1538090 := by
    simpa [prefixWord, tailWord_1538090, baseEnd_1538090] using wordTrace_append hprefix tailTrace_1538090
  have hstable : (prefixWord ++ tailWord_1538090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538090).length < 2 ^ (prefixWord ++ tailWord_1538090).sum := by decide
  have hdescent : baseEnd_1538090 < baseStart_1538090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538103 : List Nat := [1, 1, 3, 1, 2, 2, 5, 2, 1, 5]
def baseStart_1538103 : Nat := 118140960795 + 1538103 * 2 ^ 59
def prefixEnd_1538103 : Nat := 4983230072969 + 3 ^ 40 * 1538103 * 2
def baseEnd_1538103 : Nat := 263262045040833632879633

theorem tailTrace_1538103 : CollatzResearch.WordTrace tailWord_1538103 prefixEnd_1538103 263262045040833632879633 := by
  unfold tailWord_1538103
  simp only [CollatzResearch.WordTrace]
  refine ⟨56099225146722992923922963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37399483431148661949281975 56099225146722992923922963)
  ·
    refine ⟨84148837720084489385884445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56099225146722992923922963 84148837720084489385884445)
    ·
      refine ⟨31555814145031683519706667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84148837720084489385884445 31555814145031683519706667)
      ·
        refine ⟨47333721217547525279560001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31555814145031683519706667 47333721217547525279560001)
        ·
          refine ⟨35500290913160643959670001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47333721217547525279560001 35500290913160643959670001)
          ·
            refine ⟨26625218184870482969752501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35500290913160643959670001 26625218184870482969752501)
            ·
              refine ⟨2496114204831607778414297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26625218184870482969752501 2496114204831607778414297)
              ·
                refine ⟨1872085653623705833810723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2496114204831607778414297 1872085653623705833810723)
                ·
                  refine ⟨2808128480435558750716085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1872085653623705833810723 2808128480435558750716085)
                  ·
                    refine ⟨263262045040833632879633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2808128480435558750716085 263262045040833632879633)
                    ·
                      rfl

theorem cell23_1538103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 5].length) (baseStart_1538103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1538103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1538103 prefixEnd_1538103 := by exact prefixLift 1538103
  have htrace : WordTrace (prefixWord ++ tailWord_1538103) baseStart_1538103 baseEnd_1538103 := by
    simpa [prefixWord, tailWord_1538103, baseEnd_1538103] using wordTrace_append hprefix tailTrace_1538103
  have hstable : (prefixWord ++ tailWord_1538103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538103).length < 2 ^ (prefixWord ++ tailWord_1538103).sum := by decide
  have hdescent : baseEnd_1538103 < baseStart_1538103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538153 : List Nat := [1, 2, 1, 1, 1, 5, 4, 1, 1, 2, 4]
def baseStart_1538153 : Nat := 118140960795 + 1538153 * 2 ^ 59
def prefixEnd_1538153 : Nat := 4983230072969 + 3 ^ 40 * 1538153 * 2
def baseEnd_1538153 : Nat := 789811809155225703013669

theorem tailTrace_1538153 : CollatzResearch.WordTrace tailWord_1538153 prefixEnd_1538153 789811809155225703013669 := by
  unfold tailWord_1538153
  simp only [CollatzResearch.WordTrace]
  refine ⟨56101048796541851463243113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37400699197694567642162075 56101048796541851463243113)
  ·
    refine ⟨42075786597406388597432335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56101048796541851463243113 42075786597406388597432335)
    ·
      refine ⟨63113679896109582896148503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42075786597406388597432335 63113679896109582896148503)
      ·
        refine ⟨94670519844164374344222755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63113679896109582896148503 94670519844164374344222755)
        ·
          refine ⟨142005779766246561516334133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94670519844164374344222755 142005779766246561516334133)
          ·
            refine ⟨13313041853085615142156325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142005779766246561516334133 13313041853085615142156325)
            ·
              refine ⟨2496195347453552839154311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13313041853085615142156325 2496195347453552839154311)
              ·
                refine ⟨3744293021180329258731467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2496195347453552839154311 3744293021180329258731467)
                ·
                  refine ⟨5616439531770493888097201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3744293021180329258731467 5616439531770493888097201)
                  ·
                    refine ⟨4212329648827870416072901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5616439531770493888097201 4212329648827870416072901)
                    ·
                      refine ⟨789811809155225703013669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4212329648827870416072901 789811809155225703013669)
                      ·
                        rfl

theorem cell23_1538153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 2, 4].length) (baseStart_1538153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1538153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1538153 prefixEnd_1538153 := by exact prefixLift 1538153
  have htrace : WordTrace (prefixWord ++ tailWord_1538153) baseStart_1538153 baseEnd_1538153 := by
    simpa [prefixWord, tailWord_1538153, baseEnd_1538153] using wordTrace_append hprefix tailTrace_1538153
  have hstable : (prefixWord ++ tailWord_1538153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538153).length < 2 ^ (prefixWord ++ tailWord_1538153).sum := by decide
  have hdescent : baseEnd_1538153 < baseStart_1538153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538157 : List Nat := [1, 5, 1, 1, 2, 1, 3, 2, 3, 2, 2]
def baseStart_1538157 : Nat := 118140960795 + 1538157 * 2 ^ 59
def prefixEnd_1538157 : Nat := 4983230072969 + 3 ^ 40 * 1538157 * 2
def baseEnd_1538157 : Nat := 789813863077843687363651

theorem tailTrace_1538157 : CollatzResearch.WordTrace tailWord_1538157 prefixEnd_1538157 789813863077843687363651 := by
  unfold tailWord_1538157
  simp only [CollatzResearch.WordTrace]
  refine ⟨56101194688527360146388725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37400796459018240097592483 56101194688527360146388725)
  ·
    refine ⟨5259487002049440013723943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56101194688527360146388725 5259487002049440013723943)
    ·
      refine ⟨7889230503074160020585915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5259487002049440013723943 7889230503074160020585915)
      ·
        refine ⟨11833845754611240030878873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7889230503074160020585915 11833845754611240030878873)
        ·
          refine ⟨8875384315958430023159155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11833845754611240030878873 8875384315958430023159155)
          ·
            refine ⟨13313076473937645034738733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8875384315958430023159155 13313076473937645034738733)
            ·
              refine ⟨4992403677726616888027025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13313076473937645034738733 4992403677726616888027025)
              ·
                refine ⟨3744302758294962666020269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4992403677726616888027025 3744302758294962666020269)
                ·
                  refine ⟨1404113534360610999757601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3744302758294962666020269 1404113534360610999757601)
                  ·
                    refine ⟨1053085150770458249818201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1404113534360610999757601 1053085150770458249818201)
                    ·
                      refine ⟨789813863077843687363651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1053085150770458249818201 789813863077843687363651)
                      ·
                        rfl

theorem cell23_1538157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_1538157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1538157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1538157 prefixEnd_1538157 := by exact prefixLift 1538157
  have htrace : WordTrace (prefixWord ++ tailWord_1538157) baseStart_1538157 baseEnd_1538157 := by
    simpa [prefixWord, tailWord_1538157, baseEnd_1538157] using wordTrace_append hprefix tailTrace_1538157
  have hstable : (prefixWord ++ tailWord_1538157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538157).length < 2 ^ (prefixWord ++ tailWord_1538157).sum := by decide
  have hdescent : baseEnd_1538157 < baseStart_1538157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538177 : List Nat := [1, 2, 4, 2, 3, 1, 1, 3, 1, 2, 3]
def baseStart_1538177 : Nat := 118140960795 + 1538177 * 2 ^ 59
def prefixEnd_1538177 : Nat := 4983230072969 + 3 ^ 40 * 1538177 * 2
def baseEnd_1538177 : Nat := 789824132690933609113559

theorem tailTrace_1538177 : CollatzResearch.WordTrace tailWord_1538177 prefixEnd_1538177 789824132690933609113559 := by
  unfold tailWord_1538177
  simp only [CollatzResearch.WordTrace]
  refine ⟨56101924148454903562116785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37401282765636602374744523 56101924148454903562116785)
  ·
    refine ⟨42076443111341177671587589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56101924148454903562116785 42076443111341177671587589)
    ·
      refine ⟨7889333083376470813422673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42076443111341177671587589 7889333083376470813422673)
      ·
        refine ⟨5916999812532353110067005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7889333083376470813422673 5916999812532353110067005)
        ·
          refine ⟨2218874929699632416275127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5916999812532353110067005 2218874929699632416275127)
          ·
            refine ⟨3328312394549448624412691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2218874929699632416275127 3328312394549448624412691)
            ·
              refine ⟨4992468591824172936619037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3328312394549448624412691 4992468591824172936619037)
              ·
                refine ⟨1872175721934064851232139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4992468591824172936619037 1872175721934064851232139)
                ·
                  refine ⟨2808263582901097276848209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1872175721934064851232139 2808263582901097276848209)
                  ·
                    refine ⟨2106197687175822957636157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2808263582901097276848209 2106197687175822957636157)
                    ·
                      refine ⟨789824132690933609113559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2106197687175822957636157 789824132690933609113559)
                      ·
                        rfl

theorem cell23_1538177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_1538177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1538177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1538177 prefixEnd_1538177 := by exact prefixLift 1538177
  have htrace : WordTrace (prefixWord ++ tailWord_1538177) baseStart_1538177 baseEnd_1538177 := by
    simpa [prefixWord, tailWord_1538177, baseEnd_1538177] using wordTrace_append hprefix tailTrace_1538177
  have hstable : (prefixWord ++ tailWord_1538177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538177).length < 2 ^ (prefixWord ++ tailWord_1538177).sum := by decide
  have hdescent : baseEnd_1538177 < baseStart_1538177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
