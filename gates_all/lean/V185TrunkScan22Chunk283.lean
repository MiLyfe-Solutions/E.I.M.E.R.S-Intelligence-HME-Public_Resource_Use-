import V185TrunkScan22Chunk282

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2524878 : List Nat := [4, 1, 1, 1, 3, 1, 4, 1, 3, 3]
def baseStart_2524878 : Nat := 118140960795 + 2524878 * 2 ^ 59
def prefixEnd_2524878 : Nat := 4983230072969 + 3 ^ 40 * 2524878 * 2
def baseEnd_2524878 : Nat := 864317338641918424608869

theorem tailTrace_2524878 : CollatzResearch.WordTrace tailWord_2524878 prefixEnd_2524878 864317338641918424608869 := by
  unfold tailWord_2524878
  simp only [CollatzResearch.WordTrace]
  refine ⟨11511233268350711959592911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61393244097870463784495525 11511233268350711959592911)
  ·
    refine ⟨17266849902526067939389367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11511233268350711959592911 17266849902526067939389367)
    ·
      refine ⟨25900274853789101909084051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17266849902526067939389367 25900274853789101909084051)
      ·
        refine ⟨38850412280683652863626077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25900274853789101909084051 38850412280683652863626077)
        ·
          refine ⟨14568904605256369823859779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38850412280683652863626077 14568904605256369823859779)
          ·
            refine ⟨21853356907884554735789669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14568904605256369823859779 21853356907884554735789669)
            ·
              refine ⟨4097504420228354012960563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21853356907884554735789669 4097504420228354012960563)
              ·
                refine ⟨6146256630342531019440845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4097504420228354012960563 6146256630342531019440845)
                ·
                  refine ⟨2304846236378449132290317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6146256630342531019440845 2304846236378449132290317)
                  ·
                    refine ⟨864317338641918424608869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2304846236378449132290317 864317338641918424608869)
                    ·
                      rfl

theorem cell22_2524878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_2524878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2524878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2524878 prefixEnd_2524878 := by exact prefixLift 2524878
  have htrace : WordTrace (prefixWord ++ tailWord_2524878) baseStart_2524878 baseEnd_2524878 := by
    simpa [prefixWord, tailWord_2524878, baseEnd_2524878] using wordTrace_append hprefix tailTrace_2524878
  have hstable : (prefixWord ++ tailWord_2524878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524878).length < 2 ^ (prefixWord ++ tailWord_2524878).sum := by decide
  have hdescent : baseEnd_2524878 < baseStart_2524878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524919 : List Nat := [1, 1, 3, 1, 1, 1, 4, 2, 8]
def baseStart_2524919 : Nat := 118140960795 + 2524919 * 2 ^ 59
def prefixEnd_2524919 : Nat := 4983230072969 + 3 ^ 40 * 2524919 * 2
def baseEnd_2524919 : Nat := 288110457926602661444581

theorem tailTrace_2524919 : CollatzResearch.WordTrace tailWord_2524919 prefixEnd_2524919 288110457926602661444581 := by
  unfold tailWord_2524919
  simp only [CollatzResearch.WordTrace]
  refine ⟨92091361539657159678985811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61394241026438106452657207 92091361539657159678985811)
  ·
    refine ⟨138137042309485739518478717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92091361539657159678985811 138137042309485739518478717)
    ·
      refine ⟨51801390866057152319429519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138137042309485739518478717 51801390866057152319429519)
      ·
        refine ⟨77702086299085728479144279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51801390866057152319429519 77702086299085728479144279)
        ·
          refine ⟨116553129448628592718716419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77702086299085728479144279 116553129448628592718716419)
          ·
            refine ⟨174829694172942889078074629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116553129448628592718716419 174829694172942889078074629)
            ·
              refine ⟨32780567657426791702138993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 174829694172942889078074629 32780567657426791702138993)
              ·
                refine ⟨24585425743070093776604245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32780567657426791702138993 24585425743070093776604245)
                ·
                  refine ⟨288110457926602661444581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24585425743070093776604245 288110457926602661444581)
                  ·
                    rfl

theorem cell22_2524919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 8].length) (baseStart_2524919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2524919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2524919 prefixEnd_2524919 := by exact prefixLift 2524919
  have htrace : WordTrace (prefixWord ++ tailWord_2524919) baseStart_2524919 baseEnd_2524919 := by
    simpa [prefixWord, tailWord_2524919, baseEnd_2524919] using wordTrace_append hprefix tailTrace_2524919
  have hstable : (prefixWord ++ tailWord_2524919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524919).length < 2 ^ (prefixWord ++ tailWord_2524919).sum := by decide
  have hdescent : baseEnd_2524919 < baseStart_2524919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524968 : List Nat := [2, 1, 5, 1, 1, 3, 1, 2, 1, 5]
def baseStart_2524968 : Nat := 118140960795 + 2524968 * 2 ^ 59
def prefixEnd_2524968 : Nat := 4983230072969 + 3 ^ 40 * 2524968 * 2
def baseEnd_2524968 : Nat := 864348147481188189858593

theorem tailTrace_2524968 : CollatzResearch.WordTrace tailWord_2524968 prefixEnd_2524968 864348147481188189858593 := by
  unfold tailWord_2524968
  simp only [CollatzResearch.WordTrace]
  refine ⟨46046574358239820523759779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61395432477653094031679705 46046574358239820523759779)
  ·
    refine ⟨69069861537359730785639669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46046574358239820523759779 69069861537359730785639669)
    ·
      refine ⟨6475299519127474761153719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69069861537359730785639669 6475299519127474761153719)
      ·
        refine ⟨9712949278691212141730579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6475299519127474761153719 9712949278691212141730579)
        ·
          refine ⟨14569423918036818212595869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9712949278691212141730579 14569423918036818212595869)
          ·
            refine ⟨5463533969263806829723451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14569423918036818212595869 5463533969263806829723451)
            ·
              refine ⟨8195300953895710244585177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5463533969263806829723451 8195300953895710244585177)
              ·
                refine ⟨6146475715421782683438883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8195300953895710244585177 6146475715421782683438883)
                ·
                  refine ⟨9219713573132674025158325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6146475715421782683438883 9219713573132674025158325)
                  ·
                    refine ⟨864348147481188189858593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9219713573132674025158325 864348147481188189858593)
                    ·
                      rfl

theorem cell22_2524968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_2524968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2524968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2524968 prefixEnd_2524968 := by exact prefixLift 2524968
  have htrace : WordTrace (prefixWord ++ tailWord_2524968) baseStart_2524968 baseEnd_2524968 := by
    simpa [prefixWord, tailWord_2524968, baseEnd_2524968] using wordTrace_append hprefix tailTrace_2524968
  have hstable : (prefixWord ++ tailWord_2524968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524968).length < 2 ^ (prefixWord ++ tailWord_2524968).sum := by decide
  have hdescent : baseEnd_2524968 < baseStart_2524968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2524981 : List Nat := [1, 3, 3, 1, 4, 10]
def baseStart_2524981 : Nat := 118140960795 + 2524981 * 2 ^ 59
def prefixEnd_2524981 : Nat := 4983230072969 + 3 ^ 40 * 2524981 * 2
def baseEnd_2524981 : Nat := 10671019724035314682513

theorem tailTrace_2524981 : CollatzResearch.WordTrace tailWord_2524981 prefixEnd_2524981 10671019724035314682513 := by
  unfold tailWord_2524981
  simp only [CollatzResearch.WordTrace]
  refine ⟨92093622865432544267742797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61395748576955029511828531 92093622865432544267742797)
  ·
    refine ⟨34535108574537204100403549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92093622865432544267742797 34535108574537204100403549)
    ·
      refine ⟨12950665715451451537651331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34535108574537204100403549 12950665715451451537651331)
      ·
        refine ⟨19425998573177177306476997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12950665715451451537651331 19425998573177177306476997)
        ·
          refine ⟨3642374732470720744964437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19425998573177177306476997 3642374732470720744964437)
          ·
            refine ⟨10671019724035314682513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3642374732470720744964437 10671019724035314682513)
            ·
              rfl

theorem cell22_2524981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 10].length) (baseStart_2524981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2524981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2524981 prefixEnd_2524981 := by exact prefixLift 2524981
  have htrace : WordTrace (prefixWord ++ tailWord_2524981) baseStart_2524981 baseEnd_2524981 := by
    simpa [prefixWord, tailWord_2524981, baseEnd_2524981] using wordTrace_append hprefix tailTrace_2524981
  have hstable : (prefixWord ++ tailWord_2524981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2524981).length < 2 ^ (prefixWord ++ tailWord_2524981).sum := by decide
  have hdescent : baseEnd_2524981 < baseStart_2524981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2524981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525013 : List Nat := [1, 3, 2, 2, 2, 2, 1, 1, 5, 3]
def baseStart_2525013 : Nat := 118140960795 + 2525013 * 2 ^ 59
def prefixEnd_2525013 : Nat := 4983230072969 + 3 ^ 40 * 2525013 * 2
def baseEnd_2525013 : Nat := 864363551900823072483455

theorem tailTrace_2525013 : CollatzResearch.WordTrace tailWord_2525013 prefixEnd_2525013 864363551900823072483455 := by
  unfold tailWord_2525013
  simp only [CollatzResearch.WordTrace]
  refine ⟨92094790001316613732907693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61396526667544409155271795 92094790001316613732907693)
  ·
    refine ⟨34535546250493730149840385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92094790001316613732907693 34535546250493730149840385)
    ·
      refine ⟨25901659687870297612380289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34535546250493730149840385 25901659687870297612380289)
      ·
        refine ⟨19426244765902723209285217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25901659687870297612380289 19426244765902723209285217)
        ·
          refine ⟨14569683574427042406963913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19426244765902723209285217 14569683574427042406963913)
          ·
            refine ⟨10927262680820281805222935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14569683574427042406963913 10927262680820281805222935)
            ·
              refine ⟨16390894021230422707834403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10927262680820281805222935 16390894021230422707834403)
              ·
                refine ⟨24586341031845634061751605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16390894021230422707834403 24586341031845634061751605)
                ·
                  refine ⟨2304969471735528193289213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24586341031845634061751605 2304969471735528193289213)
                  ·
                    refine ⟨864363551900823072483455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2304969471735528193289213 864363551900823072483455)
                    ·
                      rfl

theorem cell22_2525013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_2525013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2525013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2525013 prefixEnd_2525013 := by exact prefixLift 2525013
  have htrace : WordTrace (prefixWord ++ tailWord_2525013) baseStart_2525013 baseEnd_2525013 := by
    simpa [prefixWord, tailWord_2525013, baseEnd_2525013] using wordTrace_append hprefix tailTrace_2525013
  have hstable : (prefixWord ++ tailWord_2525013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525013).length < 2 ^ (prefixWord ++ tailWord_2525013).sum := by decide
  have hdescent : baseEnd_2525013 < baseStart_2525013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525041 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 4, 5]
def baseStart_2525041 : Nat := 118140960795 + 2525041 * 2 ^ 59
def prefixEnd_2525041 : Nat := 4983230072969 + 3 ^ 40 * 2525041 * 2
def baseEnd_2525041 : Nat := 864373136873040332783369

theorem tailTrace_2525041 : CollatzResearch.WordTrace tailWord_2525041 prefixEnd_2525041 864373136873040332783369 := by
  unfold tailWord_2525041
  simp only [CollatzResearch.WordTrace]
  refine ⟨92095811245215174514926977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61397207496810116343284651 92095811245215174514926977)
  ·
    refine ⟨69071858433911380886195233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92095811245215174514926977 69071858433911380886195233)
    ·
      refine ⟨51803893825433535664646425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69071858433911380886195233 51803893825433535664646425)
      ·
        refine ⟨38852920369075151748484819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51803893825433535664646425 38852920369075151748484819)
        ·
          refine ⟨58279380553612727622727229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38852920369075151748484819 58279380553612727622727229)
          ·
            refine ⟨21854767707604772858522711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58279380553612727622727229 21854767707604772858522711)
            ·
              refine ⟨32782151561407159287784067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21854767707604772858522711 32782151561407159287784067)
              ·
                refine ⟨49173227342110738931676101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32782151561407159287784067 49173227342110738931676101)
                ·
                  refine ⟨9219980126645763549689269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49173227342110738931676101 9219980126645763549689269)
                  ·
                    refine ⟨864373136873040332783369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9219980126645763549689269 864373136873040332783369)
                    ·
                      rfl

theorem cell22_2525041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_2525041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2525041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2525041 prefixEnd_2525041 := by exact prefixLift 2525041
  have htrace : WordTrace (prefixWord ++ tailWord_2525041) baseStart_2525041 baseEnd_2525041 := by
    simpa [prefixWord, tailWord_2525041, baseEnd_2525041] using wordTrace_append hprefix tailTrace_2525041
  have hstable : (prefixWord ++ tailWord_2525041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525041).length < 2 ^ (prefixWord ++ tailWord_2525041).sum := by decide
  have hdescent : baseEnd_2525041 < baseStart_2525041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525073 : List Nat := [1, 2, 2, 1, 1, 1, 5, 4, 1, 4]
def baseStart_2525073 : Nat := 118140960795 + 2525073 * 2 ^ 59
def prefixEnd_2525073 : Nat := 4983230072969 + 3 ^ 40 * 2525073 * 2
def baseEnd_2525073 : Nat := 864384091127002915983271

theorem tailTrace_2525073 : CollatzResearch.WordTrace tailWord_2525073 prefixEnd_2525073 864384091127002915983271 := by
  unfold tailWord_2525073
  simp only [CollatzResearch.WordTrace]
  refine ⟨92096978381099243980091873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61397985587399495986727915 92096978381099243980091873)
  ·
    refine ⟨69072733785824432985068905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92096978381099243980091873 69072733785824432985068905)
    ·
      refine ⟨51804550339368324738801679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69072733785824432985068905 51804550339368324738801679)
      ·
        refine ⟨77706825509052487108202519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51804550339368324738801679 77706825509052487108202519)
        ·
          refine ⟨116560238263578730662303779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77706825509052487108202519 116560238263578730662303779)
          ·
            refine ⟨174840357395368095993455669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116560238263578730662303779 174840357395368095993455669)
            ·
              refine ⟨16391283505815758999386469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 174840357395368095993455669 16391283505815758999386469)
              ·
                refine ⟨3073365657340454812384963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16391283505815758999386469 3073365657340454812384963)
                ·
                  refine ⟨4610048486010682218577445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3073365657340454812384963 4610048486010682218577445)
                  ·
                    refine ⟨864384091127002915983271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4610048486010682218577445 864384091127002915983271)
                    ·
                      rfl

theorem cell22_2525073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 4].length) (baseStart_2525073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2525073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2525073 prefixEnd_2525073 := by exact prefixLift 2525073
  have htrace : WordTrace (prefixWord ++ tailWord_2525073) baseStart_2525073 baseEnd_2525073 := by
    simpa [prefixWord, tailWord_2525073, baseEnd_2525073] using wordTrace_append hprefix tailTrace_2525073
  have hstable : (prefixWord ++ tailWord_2525073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525073).length < 2 ^ (prefixWord ++ tailWord_2525073).sum := by decide
  have hdescent : baseEnd_2525073 < baseStart_2525073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525103 : List Nat := [1, 1, 2, 1, 2, 2, 3, 3, 4, 3]
def baseStart_2525103 : Nat := 118140960795 + 2525103 * 2 ^ 59
def prefixEnd_2525103 : Nat := 4983230072969 + 3 ^ 40 * 2525103 * 2
def baseEnd_2525103 : Nat := 864394360740092837733179

theorem tailTrace_2525103 : CollatzResearch.WordTrace tailWord_2525103 prefixEnd_2525103 864394360740092837733179 := by
  unfold tailWord_2525103
  simp only [CollatzResearch.WordTrace]
  refine ⟨92098072570990559103683963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61398715047327039402455975 92098072570990559103683963)
  ·
    refine ⟨138147108856485838655525945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92098072570990559103683963 138147108856485838655525945)
    ·
      refine ⟨103610331642364378991644459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138147108856485838655525945 103610331642364378991644459)
      ·
        refine ⟨155415497463546568487466689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103610331642364378991644459 155415497463546568487466689)
        ·
          refine ⟨116561623097659926365600017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155415497463546568487466689 116561623097659926365600017)
          ·
            refine ⟨87421217323244944774200013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116561623097659926365600017 87421217323244944774200013)
            ·
              refine ⟨32782956496216854290325005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87421217323244944774200013 32782956496216854290325005)
              ·
                refine ⟨12293608686081320358871877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32782956496216854290325005 12293608686081320358871877)
                ·
                  refine ⟨2305051628640247567288477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12293608686081320358871877 2305051628640247567288477)
                  ·
                    refine ⟨864394360740092837733179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2305051628640247567288477 864394360740092837733179)
                    ·
                      rfl

theorem cell22_2525103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 4, 3].length) (baseStart_2525103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2525103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2525103 prefixEnd_2525103 := by exact prefixLift 2525103
  have htrace : WordTrace (prefixWord ++ tailWord_2525103) baseStart_2525103 baseEnd_2525103 := by
    simpa [prefixWord, tailWord_2525103, baseEnd_2525103] using wordTrace_append hprefix tailTrace_2525103
  have hstable : (prefixWord ++ tailWord_2525103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525103).length < 2 ^ (prefixWord ++ tailWord_2525103).sum := by decide
  have hdescent : baseEnd_2525103 < baseStart_2525103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525105 : List Nat := [1, 2, 2, 4, 2, 3, 1, 1, 6]
def baseStart_2525105 : Nat := 118140960795 + 2525105 * 2 ^ 59
def prefixEnd_2525105 : Nat := 4983230072969 + 3 ^ 40 * 2525105 * 2
def baseEnd_2525105 : Nat := 288131681793655166394391

theorem tailTrace_2525105 : CollatzResearch.WordTrace tailWord_2525105 prefixEnd_2525105 288131681793655166394391 := by
  unfold tailWord_2525105
  simp only [CollatzResearch.WordTrace]
  refine ⟨92098145516983313445256769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61398763677988875630171179 92098145516983313445256769)
  ·
    refine ⟨69073609137737485083942577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92098145516983313445256769 69073609137737485083942577)
    ·
      refine ⟨51805206853303113812956933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69073609137737485083942577 51805206853303113812956933)
      ·
        refine ⟨9713476284994333839929425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51805206853303113812956933 9713476284994333839929425)
        ·
          refine ⟨7285107213745750379947069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9713476284994333839929425 7285107213745750379947069)
          ·
            refine ⟨2731915205154656392480151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7285107213745750379947069 2731915205154656392480151)
            ·
              refine ⟨4097872807731984588720227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2731915205154656392480151 4097872807731984588720227)
              ·
                refine ⟨6146809211597976883080341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4097872807731984588720227 6146809211597976883080341)
                ·
                  refine ⟨288131681793655166394391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6146809211597976883080341 288131681793655166394391)
                  ·
                    rfl

theorem cell22_2525105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 6].length) (baseStart_2525105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2525105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2525105 prefixEnd_2525105 := by exact prefixLift 2525105
  have htrace : WordTrace (prefixWord ++ tailWord_2525105) baseStart_2525105 baseEnd_2525105 := by
    simpa [prefixWord, tailWord_2525105, baseEnd_2525105] using wordTrace_append hprefix tailTrace_2525105
  have hstable : (prefixWord ++ tailWord_2525105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525105).length < 2 ^ (prefixWord ++ tailWord_2525105).sum := by decide
  have hdescent : baseEnd_2525105 < baseStart_2525105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525120 : List Nat := [2, 1, 1, 2, 3, 2, 3, 3, 2, 3]
def baseStart_2525120 : Nat := 118140960795 + 2525120 * 2 ^ 59
def prefixEnd_2525120 : Nat := 4983230072969 + 3 ^ 40 * 2525120 * 2
def baseEnd_2525120 : Nat := 864400180187510460058127

theorem tailTrace_2525120 : CollatzResearch.WordTrace tailWord_2525120 prefixEnd_2525120 864400180187510460058127 := by
  unfold tailWord_2525120
  simp only [CollatzResearch.WordTrace]
  refine ⟨46049346305964485503526407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61399128407952647338035209 46049346305964485503526407)
  ·
    refine ⟨69074019458946728255289611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46049346305964485503526407 69074019458946728255289611)
    ·
      refine ⟨103611029188420092382934417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69074019458946728255289611 103611029188420092382934417)
      ·
        refine ⟨77708271891315069287200813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103611029188420092382934417 77708271891315069287200813)
        ·
          refine ⟨29140601959243150982700305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77708271891315069287200813 29140601959243150982700305)
          ·
            refine ⟨21855451469432363237025229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29140601959243150982700305 21855451469432363237025229)
            ·
              refine ⟨8195794301037136213884461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21855451469432363237025229 8195794301037136213884461)
              ·
                refine ⟨3073422862888926080206673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8195794301037136213884461 3073422862888926080206673)
                ·
                  refine ⟨2305067147166694560155005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3073422862888926080206673 2305067147166694560155005)
                  ·
                    refine ⟨864400180187510460058127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2305067147166694560155005 864400180187510460058127)
                    ·
                      rfl

theorem cell22_2525120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 2, 3].length) (baseStart_2525120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2525120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2525120 prefixEnd_2525120 := by exact prefixLift 2525120
  have htrace : WordTrace (prefixWord ++ tailWord_2525120) baseStart_2525120 baseEnd_2525120 := by
    simpa [prefixWord, tailWord_2525120, baseEnd_2525120] using wordTrace_append hprefix tailTrace_2525120
  have hstable : (prefixWord ++ tailWord_2525120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525120).length < 2 ^ (prefixWord ++ tailWord_2525120).sum := by decide
  have hdescent : baseEnd_2525120 < baseStart_2525120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525182 : List Nat := [4, 2, 2, 2, 1, 1, 1, 1, 5, 3]
def baseStart_2525182 : Nat := 118140960795 + 2525182 * 2 ^ 59
def prefixEnd_2525182 : Nat := 4983230072969 + 3 ^ 40 * 2525182 * 2
def baseEnd_2525182 : Nat := 864421404054562965007937

theorem tailTrace_2525182 : CollatzResearch.WordTrace tailWord_2525182 prefixEnd_2525182 864421404054562965007937 := by
  unfold tailWord_2525182
  simp only [CollatzResearch.WordTrace]
  refine ⟨11512619242213044449476225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61400635958469570397206533 11512619242213044449476225)
  ·
    refine ⟨8634464431659783337107169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11512619242213044449476225 8634464431659783337107169)
    ·
      refine ⟨6475848323744837502830377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8634464431659783337107169 6475848323744837502830377)
      ·
        refine ⟨4856886242808628127122783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6475848323744837502830377 4856886242808628127122783)
        ·
          refine ⟨7285329364212942190684175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4856886242808628127122783 7285329364212942190684175)
          ·
            refine ⟨10927994046319413286026263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7285329364212942190684175 10927994046319413286026263)
            ·
              refine ⟨16391991069479119929039395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10927994046319413286026263 16391991069479119929039395)
              ·
                refine ⟨24587986604218679893559093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16391991069479119929039395 24587986604218679893559093)
                ·
                  refine ⟨2305123744145501240021165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24587986604218679893559093 2305123744145501240021165)
                  ·
                    refine ⟨864421404054562965007937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2305123744145501240021165 864421404054562965007937)
                    ·
                      rfl

theorem cell22_2525182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_2525182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2525182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2525182 prefixEnd_2525182 := by exact prefixLift 2525182
  have htrace : WordTrace (prefixWord ++ tailWord_2525182) baseStart_2525182 baseEnd_2525182 := by
    simpa [prefixWord, tailWord_2525182, baseEnd_2525182] using wordTrace_append hprefix tailTrace_2525182
  have hstable : (prefixWord ++ tailWord_2525182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525182).length < 2 ^ (prefixWord ++ tailWord_2525182).sum := by decide
  have hdescent : baseEnd_2525182 < baseStart_2525182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525212 : List Nat := [2, 2, 3, 1, 3, 3, 1, 2, 5]
def baseStart_2525212 : Nat := 118140960795 + 2525212 * 2 ^ 59
def prefixEnd_2525212 : Nat := 4983230072969 + 3 ^ 40 * 2525212 * 2
def baseEnd_2525212 : Nat := 288143891222550962252615

theorem tailTrace_2525212 : CollatzResearch.WordTrace tailWord_2525212 prefixEnd_2525212 288143891222550962252615 := by
  unfold tailWord_2525212
  simp only [CollatzResearch.WordTrace]
  refine ⟨46051024063797835359700945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61401365418397113812934593 46051024063797835359700945)
  ·
    refine ⟨34538268047848376519775709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46051024063797835359700945 34538268047848376519775709)
    ·
      refine ⟨12951850517943141194915891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34538268047848376519775709 12951850517943141194915891)
      ·
        refine ⟨19427775776914711792373837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12951850517943141194915891 19427775776914711792373837)
        ·
          refine ⟨7285415916343016922140189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19427775776914711792373837 7285415916343016922140189)
          ·
            refine ⟨2732030968628631345802571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7285415916343016922140189 2732030968628631345802571)
            ·
              refine ⟨4098046452942947018703857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2732030968628631345802571 4098046452942947018703857)
              ·
                refine ⟨3073534839707210264027893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4098046452942947018703857 3073534839707210264027893)
                ·
                  refine ⟨288143891222550962252615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3073534839707210264027893 288143891222550962252615)
                  ·
                    rfl

theorem cell22_2525212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 2, 5].length) (baseStart_2525212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2525212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2525212 prefixEnd_2525212 := by exact prefixLift 2525212
  have htrace : WordTrace (prefixWord ++ tailWord_2525212) baseStart_2525212 baseEnd_2525212 := by
    simpa [prefixWord, tailWord_2525212, baseEnd_2525212] using wordTrace_append hprefix tailTrace_2525212
  have hstable : (prefixWord ++ tailWord_2525212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525212).length < 2 ^ (prefixWord ++ tailWord_2525212).sum := by decide
  have hdescent : baseEnd_2525212 < baseStart_2525212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525255 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 6, 3]
def baseStart_2525255 : Nat := 118140960795 + 2525255 * 2 ^ 59
def prefixEnd_2525255 : Nat := 4983230072969 + 3 ^ 40 * 2525255 * 2
def baseEnd_2525255 : Nat := 864446393446415107932713

theorem tailTrace_2525255 : CollatzResearch.WordTrace tailWord_2525255 prefixEnd_2525255 864446393446415107932713 := by
  unfold tailWord_2525255
  simp only [CollatzResearch.WordTrace]
  refine ⟨92103616466439889063217219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61402410977626592708811479 92103616466439889063217219)
  ·
    refine ⟨138155424699659833594825829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92103616466439889063217219 138155424699659833594825829)
    ·
      refine ⟨25904142131186218799029843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138155424699659833594825829 25904142131186218799029843)
      ·
        refine ⟨38856213196779328198544765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25904142131186218799029843 38856213196779328198544765)
        ·
          refine ⟨14571079948792248074454287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38856213196779328198544765 14571079948792248074454287)
          ·
            refine ⟨21856619923188372111681431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14571079948792248074454287 21856619923188372111681431)
            ·
              refine ⟨32784929884782558167522147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21856619923188372111681431 32784929884782558167522147)
              ·
                refine ⟨49177394827173837251283221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32784929884782558167522147 49177394827173837251283221)
                ·
                  refine ⟨2305190382523773621153901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 49177394827173837251283221 2305190382523773621153901)
                  ·
                    refine ⟨864446393446415107932713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2305190382523773621153901 864446393446415107932713)
                    ·
                      rfl

theorem cell22_2525255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_2525255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2525255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2525255 prefixEnd_2525255 := by exact prefixLift 2525255
  have htrace : WordTrace (prefixWord ++ tailWord_2525255) baseStart_2525255 baseEnd_2525255 := by
    simpa [prefixWord, tailWord_2525255, baseEnd_2525255] using wordTrace_append hprefix tailTrace_2525255
  have hstable : (prefixWord ++ tailWord_2525255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525255).length < 2 ^ (prefixWord ++ tailWord_2525255).sum := by decide
  have hdescent : baseEnd_2525255 < baseStart_2525255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525285 : List Nat := [1, 3, 1, 3, 2, 3, 2, 7]
def baseStart_2525285 : Nat := 118140960795 + 2525285 * 2 ^ 59
def prefixEnd_2525285 : Nat := 4983230072969 + 3 ^ 40 * 2525285 * 2
def baseEnd_2525285 : Nat := 96050740339945003298069

theorem tailTrace_2525285 : CollatzResearch.WordTrace tailWord_2525285 prefixEnd_2525285 96050740339945003298069 := by
  unfold tailWord_2525285
  simp only [CollatzResearch.WordTrace]
  refine ⟨92104710656331204186809309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61403140437554136124539539 92104710656331204186809309)
  ·
    refine ⟨34539266496124201570053491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92104710656331204186809309 34539266496124201570053491)
    ·
      refine ⟨51808899744186302355080237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34539266496124201570053491 51808899744186302355080237)
      ·
        refine ⟨19428337404069863383155089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51808899744186302355080237 19428337404069863383155089)
        ·
          refine ⟨14571253053052397537366317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19428337404069863383155089 14571253053052397537366317)
          ·
            refine ⟨5464219894894649076512369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14571253053052397537366317 5464219894894649076512369)
            ·
              refine ⟨4098164921170986807384277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5464219894894649076512369 4098164921170986807384277)
              ·
                refine ⟨96050740339945003298069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4098164921170986807384277 96050740339945003298069)
                ·
                  rfl

theorem cell22_2525285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 7].length) (baseStart_2525285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2525285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2525285 prefixEnd_2525285 := by exact prefixLift 2525285
  have htrace : WordTrace (prefixWord ++ tailWord_2525285) baseStart_2525285 baseEnd_2525285 := by
    simpa [prefixWord, tailWord_2525285, baseEnd_2525285] using wordTrace_append hprefix tailTrace_2525285
  have hstable : (prefixWord ++ tailWord_2525285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525285).length < 2 ^ (prefixWord ++ tailWord_2525285).sum := by decide
  have hdescent : baseEnd_2525285 < baseStart_2525285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525345 : List Nat := [1, 2, 3, 3, 1, 2, 1, 1, 1, 7]
def baseStart_2525345 : Nat := 118140960795 + 2525345 * 2 ^ 59
def prefixEnd_2525345 : Nat := 4983230072969 + 3 ^ 40 * 2525345 * 2
def baseEnd_2525345 : Nat := 864477202285684873182437

theorem tailTrace_2525345 : CollatzResearch.WordTrace tailWord_2525345 prefixEnd_2525345 864477202285684873182437 := by
  unfold tailWord_2525345
  simp only [CollatzResearch.WordTrace]
  refine ⟨92106899036113834433993489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61404599357409222955995659 92106899036113834433993489)
  ·
    refine ⟨69080174277085375825495117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92106899036113834433993489 69080174277085375825495117)
    ·
      refine ⟨25905065353907015934560669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69080174277085375825495117 25905065353907015934560669)
      ·
        refine ⟨9714399507715130975460251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25905065353907015934560669 9714399507715130975460251)
        ·
          refine ⟨14571599261572696463190377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9714399507715130975460251 14571599261572696463190377)
          ·
            refine ⟨10928699446179522347392783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14571599261572696463190377 10928699446179522347392783)
            ·
              refine ⟨16393049169269283521089175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10928699446179522347392783 16393049169269283521089175)
              ·
                refine ⟨24589573753903925281633763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16393049169269283521089175 24589573753903925281633763)
                ·
                  refine ⟨36884360630855887922450645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24589573753903925281633763 36884360630855887922450645)
                  ·
                    refine ⟨864477202285684873182437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36884360630855887922450645 864477202285684873182437)
                    ·
                      rfl

theorem cell22_2525345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_2525345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2525345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2525345 prefixEnd_2525345 := by exact prefixLift 2525345
  have htrace : WordTrace (prefixWord ++ tailWord_2525345) baseStart_2525345 baseEnd_2525345 := by
    simpa [prefixWord, tailWord_2525345, baseEnd_2525345] using wordTrace_append hprefix tailTrace_2525345
  have hstable : (prefixWord ++ tailWord_2525345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525345).length < 2 ^ (prefixWord ++ tailWord_2525345).sum := by decide
  have hdescent : baseEnd_2525345 < baseStart_2525345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525411 : List Nat := [1, 1, 1, 8, 1, 1, 2, 2, 1, 4]
def baseStart_2525411 : Nat := 118140960795 + 2525411 * 2 ^ 59
def prefixEnd_2525411 : Nat := 4983230072969 + 3 ^ 40 * 2525411 * 2
def baseEnd_2525411 : Nat := 864499795434482701032235

theorem tailTrace_2525411 : CollatzResearch.WordTrace tailWord_2525411 prefixEnd_2525411 864499795434482701032235 := by
  unfold tailWord_2525411
  simp only [CollatzResearch.WordTrace]
  refine ⟨92109306253874727705896087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61406204169249818470597391 92109306253874727705896087)
  ·
    refine ⟨138163959380812091558844131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92109306253874727705896087 138163959380812091558844131)
    ·
      refine ⟨207245939071218137338266197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138163959380812091558844131 207245939071218137338266197)
      ·
        refine ⟨2428663348490837546932807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 207245939071218137338266197 2428663348490837546932807)
        ·
          refine ⟨3642995022736256320399211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2428663348490837546932807 3642995022736256320399211)
          ·
            refine ⟨5464492534104384480598817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3642995022736256320399211 5464492534104384480598817)
            ·
              refine ⟨4098369400578288360449113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5464492534104384480598817 4098369400578288360449113)
              ·
                refine ⟨3073777050433716270336835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4098369400578288360449113 3073777050433716270336835)
                ·
                  refine ⟨4610665575650574405505253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3073777050433716270336835 4610665575650574405505253)
                  ·
                    refine ⟨864499795434482701032235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4610665575650574405505253 864499795434482701032235)
                    ·
                      rfl

theorem cell22_2525411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 4].length) (baseStart_2525411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2525411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2525411 prefixEnd_2525411 := by exact prefixLift 2525411
  have htrace : WordTrace (prefixWord ++ tailWord_2525411) baseStart_2525411 baseEnd_2525411 := by
    simpa [prefixWord, tailWord_2525411, baseEnd_2525411] using wordTrace_append hprefix tailTrace_2525411
  have hstable : (prefixWord ++ tailWord_2525411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525411).length < 2 ^ (prefixWord ++ tailWord_2525411).sum := by decide
  have hdescent : baseEnd_2525411 < baseStart_2525411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525420 : List Nat := [2, 2, 1, 1, 2, 3, 3, 8]
def baseStart_2525420 : Nat := 118140960795 + 2525420 * 2 ^ 59
def prefixEnd_2525420 : Nat := 4983230072969 + 3 ^ 40 * 2525420 * 2
def baseEnd_2525420 : Nat := 96055875146489964173023

theorem tailTrace_2525420 : CollatzResearch.WordTrace tailWord_2525420 prefixEnd_2525420 96055875146489964173023 := by
  unfold tailWord_2525420
  simp only [CollatzResearch.WordTrace]
  refine ⟨46054817255421061121486857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61406423007228081495315809 46054817255421061121486857)
  ·
    refine ⟨34541112941565795841115143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46054817255421061121486857 34541112941565795841115143)
    ·
      refine ⟨51811669412348693761672715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34541112941565795841115143 51811669412348693761672715)
      ·
        refine ⟨77717504118523040642509073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51811669412348693761672715 77717504118523040642509073)
        ·
          refine ⟨58288128088892280481881805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77717504118523040642509073 58288128088892280481881805)
          ·
            refine ⟨21858048033334605180705677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58288128088892280481881805 21858048033334605180705677)
            ·
              refine ⟨8196768012500476942764629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21858048033334605180705677 8196768012500476942764629)
              ·
                refine ⟨96055875146489964173023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8196768012500476942764629 96055875146489964173023)
                ·
                  rfl

theorem cell22_2525420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 8].length) (baseStart_2525420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2525420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2525420 prefixEnd_2525420 := by exact prefixLift 2525420
  have htrace : WordTrace (prefixWord ++ tailWord_2525420) baseStart_2525420 baseEnd_2525420 := by
    simpa [prefixWord, tailWord_2525420, baseEnd_2525420] using wordTrace_append hprefix tailTrace_2525420
  have hstable : (prefixWord ++ tailWord_2525420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525420).length < 2 ^ (prefixWord ++ tailWord_2525420).sum := by decide
  have hdescent : baseEnd_2525420 < baseStart_2525420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525422 : List Nat := [4, 1, 2, 1, 1, 1, 1, 5, 2, 4]
def baseStart_2525422 : Nat := 118140960795 + 2525422 * 2 ^ 59
def prefixEnd_2525422 : Nat := 4983230072969 + 3 ^ 40 * 2525422 * 2
def baseEnd_2525422 : Nat := 864503560959282339007201

theorem tailTrace_2525422 : CollatzResearch.WordTrace tailWord_2525422 prefixEnd_2525422 864503560959282339007201 := by
  unfold tailWord_2525422
  simp only [CollatzResearch.WordTrace]
  refine ⟨11513713432104359573068315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61406471637889917723031013 11513713432104359573068315)
  ·
    refine ⟨17270570148156539359602473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11513713432104359573068315 17270570148156539359602473)
    ·
      refine ⟨12952927611117404519701855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17270570148156539359602473 12952927611117404519701855)
      ·
        refine ⟨19429391416676106779552783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12952927611117404519701855 19429391416676106779552783)
        ·
          refine ⟨29144087125014160169329175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19429391416676106779552783 29144087125014160169329175)
          ·
            refine ⟨43716130687521240253993763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29144087125014160169329175 43716130687521240253993763)
            ·
              refine ⟨65574196031281860380990645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43716130687521240253993763 65574196031281860380990645)
              ·
                refine ⟨6147580877932674410717873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65574196031281860380990645 6147580877932674410717873)
                ·
                  refine ⟨4610685658449505808038405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6147580877932674410717873 4610685658449505808038405)
                  ·
                    refine ⟨864503560959282339007201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4610685658449505808038405 864503560959282339007201)
                    ·
                      rfl

theorem cell22_2525422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_2525422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2525422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2525422 prefixEnd_2525422 := by exact prefixLift 2525422
  have htrace : WordTrace (prefixWord ++ tailWord_2525422) baseStart_2525422 baseEnd_2525422 := by
    simpa [prefixWord, tailWord_2525422, baseEnd_2525422] using wordTrace_append hprefix tailTrace_2525422
  have hstable : (prefixWord ++ tailWord_2525422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525422).length < 2 ^ (prefixWord ++ tailWord_2525422).sum := by decide
  have hdescent : baseEnd_2525422 < baseStart_2525422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525426 : List Nat := [3, 2, 1, 3, 2, 3, 1, 3, 4]
def baseStart_2525426 : Nat := 118140960795 + 2525426 * 2 ^ 59
def prefixEnd_2525426 : Nat := 4983230072969 + 3 ^ 40 * 2525426 * 2
def baseEnd_2525426 : Nat := 288168310080342553969063

theorem tailTrace_2525426 : CollatzResearch.WordTrace tailWord_2525426 prefixEnd_2525426 288168310080342553969063 := by
  unfold tailWord_2525426
  simp only [CollatzResearch.WordTrace]
  refine ⟨23027463337205096316923033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61406568899213590178461421 23027463337205096316923033)
  ·
    refine ⟨17270597502903822237692275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23027463337205096316923033 17270597502903822237692275)
    ·
      refine ⟨25905896254355733356538413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17270597502903822237692275 25905896254355733356538413)
      ·
        refine ⟨9714711095383400008701905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25905896254355733356538413 9714711095383400008701905)
        ·
          refine ⟨7286033321537550006526429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9714711095383400008701905 7286033321537550006526429)
          ·
            refine ⟨2732262495576581252447411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7286033321537550006526429 2732262495576581252447411)
            ·
              refine ⟨4098393743364871878671117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2732262495576581252447411 4098393743364871878671117)
              ·
                refine ⟨1536897653761826954501669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4098393743364871878671117 1536897653761826954501669)
                ·
                  refine ⟨288168310080342553969063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1536897653761826954501669 288168310080342553969063)
                  ·
                    rfl

theorem cell22_2525426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_2525426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2525426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2525426 prefixEnd_2525426 := by exact prefixLift 2525426
  have htrace : WordTrace (prefixWord ++ tailWord_2525426) baseStart_2525426 baseEnd_2525426 := by
    simpa [prefixWord, tailWord_2525426, baseEnd_2525426] using wordTrace_append hprefix tailTrace_2525426
  have hstable : (prefixWord ++ tailWord_2525426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525426).length < 2 ^ (prefixWord ++ tailWord_2525426).sum := by decide
  have hdescent : baseEnd_2525426 < baseStart_2525426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525512 : List Nat := [2, 1, 3, 1, 1, 2, 3, 2, 3, 4]
def baseStart_2525512 : Nat := 118140960795 + 2525512 * 2 ^ 59
def prefixEnd_2525512 : Nat := 4983230072969 + 3 ^ 40 * 2525512 * 2
def baseEnd_2525512 : Nat := 864534369798552104256925

theorem tailTrace_2525512 : CollatzResearch.WordTrace tailWord_2525512 prefixEnd_2525512 864534369798552104256925 := by
  unfold tailWord_2525512
  simp only [CollatzResearch.WordTrace]
  refine ⟨46056495013254410977661395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61408660017672547970215193 46056495013254410977661395)
  ·
    refine ⟨69084742519881616466492093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46056495013254410977661395 69084742519881616466492093)
    ·
      refine ⟨25906778444955606174934535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69084742519881616466492093 25906778444955606174934535)
      ·
        refine ⟨38860167667433409262401803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25906778444955606174934535 38860167667433409262401803)
        ·
          refine ⟨58290251501150113893602705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38860167667433409262401803 58290251501150113893602705)
          ·
            refine ⟨43717688625862585420202029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58290251501150113893602705 43717688625862585420202029)
            ·
              refine ⟨16394133234698469532575761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43717688625862585420202029 16394133234698469532575761)
              ·
                refine ⟨12295599926023852149431821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16394133234698469532575761 12295599926023852149431821)
                ·
                  refine ⟨4610849972258944556036933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12295599926023852149431821 4610849972258944556036933)
                  ·
                    refine ⟨864534369798552104256925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4610849972258944556036933 864534369798552104256925)
                    ·
                      rfl

theorem cell22_2525512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_2525512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2525512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2525512 prefixEnd_2525512 := by exact prefixLift 2525512
  have htrace : WordTrace (prefixWord ++ tailWord_2525512) baseStart_2525512 baseEnd_2525512 := by
    simpa [prefixWord, tailWord_2525512, baseEnd_2525512] using wordTrace_append hprefix tailTrace_2525512
  have hstable : (prefixWord ++ tailWord_2525512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525512).length < 2 ^ (prefixWord ++ tailWord_2525512).sum := by decide
  have hdescent : baseEnd_2525512 < baseStart_2525512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525527 : List Nat := [1, 1, 3, 2, 3, 1, 3, 2, 6]
def baseStart_2525527 : Nat := 118140960795 + 2525527 * 2 ^ 59
def prefixEnd_2525527 : Nat := 4983230072969 + 3 ^ 40 * 2525527 * 2
def baseEnd_2525527 : Nat := 288179834868365688377293

theorem tailTrace_2525527 : CollatzResearch.WordTrace tailWord_2525527 prefixEnd_2525527 288179834868365688377293 := by
  unfold tailWord_2525527
  simp only [CollatzResearch.WordTrace]
  refine ⟨92113537121454479517118835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61409024747636319678079223 92113537121454479517118835)
  ·
    refine ⟨138170305682181719275678253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92113537121454479517118835 138170305682181719275678253)
    ·
      refine ⟨51813864630818144728379345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138170305682181719275678253 51813864630818144728379345)
      ·
        refine ⟨38860398473113608546284509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51813864630818144728379345 38860398473113608546284509)
        ·
          refine ⟨14572649427417603204856691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38860398473113608546284509 14572649427417603204856691)
          ·
            refine ⟨21858974141126404807285037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14572649427417603204856691 21858974141126404807285037)
            ·
              refine ⟨8197115302922401802731889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21858974141126404807285037 8197115302922401802731889)
              ·
                refine ⟨6147836477191801352048917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8197115302922401802731889 6147836477191801352048917)
                ·
                  refine ⟨288179834868365688377293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6147836477191801352048917 288179834868365688377293)
                  ·
                    rfl

theorem cell22_2525527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 6].length) (baseStart_2525527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2525527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2525527 prefixEnd_2525527 := by exact prefixLift 2525527
  have htrace : WordTrace (prefixWord ++ tailWord_2525527) baseStart_2525527 baseEnd_2525527 := by
    simpa [prefixWord, tailWord_2525527, baseEnd_2525527] using wordTrace_append hprefix tailTrace_2525527
  have hstable : (prefixWord ++ tailWord_2525527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525527).length < 2 ^ (prefixWord ++ tailWord_2525527).sum := by decide
  have hdescent : baseEnd_2525527 < baseStart_2525527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525546 : List Nat := [3, 1, 3, 3, 1, 2, 1, 3, 1, 4]
def baseStart_2525546 : Nat := 118140960795 + 2525546 * 2 ^ 59
def prefixEnd_2525546 : Nat := 4983230072969 + 3 ^ 40 * 2525546 * 2
def baseEnd_2525546 : Nat := 864546008693387348906821

theorem tailTrace_2525546 : CollatzResearch.WordTrace tailWord_2525546 prefixEnd_2525546 864546008693387348906821 := by
  unfold tailWord_2525546
  simp only [CollatzResearch.WordTrace]
  refine ⟨23028557527096411440515123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61409486738923763841373661 23028557527096411440515123)
  ·
    refine ⟨34542836290644617160772685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23028557527096411440515123 34542836290644617160772685)
    ·
      refine ⟨12953563608991731435289757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34542836290644617160772685 12953563608991731435289757)
      ·
        refine ⟨4857586353371899288233659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12953563608991731435289757 4857586353371899288233659)
        ·
          refine ⟨7286379530057848932350489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4857586353371899288233659 7286379530057848932350489)
          ·
            refine ⟨5464784647543386699262867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7286379530057848932350489 5464784647543386699262867)
            ·
              refine ⟨8197176971315080048894301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5464784647543386699262867 8197176971315080048894301)
              ·
                refine ⟨3073941364243155018335363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8197176971315080048894301 3073941364243155018335363)
                ·
                  refine ⟨4610912046364732527503045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3073941364243155018335363 4610912046364732527503045)
                  ·
                    refine ⟨864546008693387348906821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4610912046364732527503045 864546008693387348906821)
                    ·
                      rfl

theorem cell22_2525546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_2525546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2525546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2525546 prefixEnd_2525546 := by exact prefixLift 2525546
  have htrace : WordTrace (prefixWord ++ tailWord_2525546) baseStart_2525546 baseEnd_2525546 := by
    simpa [prefixWord, tailWord_2525546, baseEnd_2525546] using wordTrace_append hprefix tailTrace_2525546
  have hstable : (prefixWord ++ tailWord_2525546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525546).length < 2 ^ (prefixWord ++ tailWord_2525546).sum := by decide
  have hdescent : baseEnd_2525546 < baseStart_2525546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525559 : List Nat := [1, 1, 3, 1, 1, 2, 2, 6, 2, 3]
def baseStart_2525559 : Nat := 118140960795 + 2525559 * 2 ^ 59
def prefixEnd_2525559 : Nat := 4983230072969 + 3 ^ 40 * 2525559 * 2
def baseEnd_2525559 : Nat := 864550458859059648331781

theorem tailTrace_2525559 : CollatzResearch.WordTrace tailWord_2525559 prefixEnd_2525559 864550458859059648331781 := by
  unfold tailWord_2525559
  simp only [CollatzResearch.WordTrace]
  refine ⟨92114704257338548982283731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61409802838225699321522487 92114704257338548982283731)
  ·
    refine ⟨138172056386007823473425597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92114704257338548982283731 138172056386007823473425597)
    ·
      refine ⟨51814521144752933802534599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138172056386007823473425597 51814521144752933802534599)
      ·
        refine ⟨77721781717129400703801899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51814521144752933802534599 77721781717129400703801899)
        ·
          refine ⟨116582672575694101055702849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77721781717129400703801899 116582672575694101055702849)
          ·
            refine ⟨87437004431770575791777137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116582672575694101055702849 87437004431770575791777137)
            ·
              refine ⟨65577753323827931843832853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87437004431770575791777137 65577753323827931843832853)
              ·
                refine ⟨3073957187054434305179665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65577753323827931843832853 3073957187054434305179665)
                ·
                  refine ⟨2305467890290825728884749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3073957187054434305179665 2305467890290825728884749)
                  ·
                    refine ⟨864550458859059648331781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2305467890290825728884749 864550458859059648331781)
                    ·
                      rfl

theorem cell22_2525559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 2, 3].length) (baseStart_2525559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2525559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2525559 prefixEnd_2525559 := by exact prefixLift 2525559
  have htrace : WordTrace (prefixWord ++ tailWord_2525559) baseStart_2525559 baseEnd_2525559 := by
    simpa [prefixWord, tailWord_2525559, baseEnd_2525559] using wordTrace_append hprefix tailTrace_2525559
  have hstable : (prefixWord ++ tailWord_2525559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525559).length < 2 ^ (prefixWord ++ tailWord_2525559).sum := by decide
  have hdescent : baseEnd_2525559 < baseStart_2525559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525572 : List Nat := [2, 3, 2, 1, 1, 2, 2, 9]
def baseStart_2525572 : Nat := 118140960795 + 2525572 * 2 ^ 59
def prefixEnd_2525572 : Nat := 4983230072969 + 3 ^ 40 * 2525572 * 2
def baseEnd_2525572 : Nat := 96061656558303549750749

theorem tailTrace_2525572 : CollatzResearch.WordTrace tailWord_2525572 prefixEnd_2525572 96061656558303549750749 := by
  unfold tailWord_2525572
  simp only [CollatzResearch.WordTrace]
  refine ⟨46057589203145726101253485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61410118937527634801671313 46057589203145726101253485)
  ·
    refine ⟨17271595951179647287970057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46057589203145726101253485 17271595951179647287970057)
    ·
      refine ⟨12953696963384735465977543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17271595951179647287970057 12953696963384735465977543)
      ·
        refine ⟨19430545445077103198966315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12953696963384735465977543 19430545445077103198966315)
        ·
          refine ⟨29145818167615654798449473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19430545445077103198966315 29145818167615654798449473)
          ·
            refine ⟨21859363625711741098837105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29145818167615654798449473 21859363625711741098837105)
            ·
              refine ⟨16394522719283805824127829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21859363625711741098837105 16394522719283805824127829)
              ·
                refine ⟨96061656558303549750749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16394522719283805824127829 96061656558303549750749)
                ·
                  rfl

theorem cell22_2525572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 9].length) (baseStart_2525572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2525572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2525572 prefixEnd_2525572 := by exact prefixLift 2525572
  have htrace : WordTrace (prefixWord ++ tailWord_2525572) baseStart_2525572 baseEnd_2525572 := by
    simpa [prefixWord, tailWord_2525572, baseEnd_2525572] using wordTrace_append hprefix tailTrace_2525572
  have hstable : (prefixWord ++ tailWord_2525572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525572).length < 2 ^ (prefixWord ++ tailWord_2525572).sum := by decide
  have hdescent : baseEnd_2525572 < baseStart_2525572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525604 : List Nat := [2, 3, 1, 2, 1, 1, 2, 2, 5, 3]
def baseStart_2525604 : Nat := 118140960795 + 2525604 * 2 ^ 59
def prefixEnd_2525604 : Nat := 4983230072969 + 3 ^ 40 * 2525604 * 2
def baseEnd_2525604 : Nat := 864565863278694530956643

theorem tailTrace_2525604 : CollatzResearch.WordTrace tailWord_2525604 prefixEnd_2525604 864565863278694530956643 := by
  unfold tailWord_2525604
  simp only [CollatzResearch.WordTrace]
  refine ⟨46058172771087760833835933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61410897028117014445114577 46058172771087760833835933)
  ·
    refine ⟨17271814789157910312688475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46058172771087760833835933 17271814789157910312688475)
    ·
      refine ⟨25907722183736865469032713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17271814789157910312688475 25907722183736865469032713)
      ·
        refine ⟨19430791637802649101774535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25907722183736865469032713 19430791637802649101774535)
        ·
          refine ⟨29146187456703973652661803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19430791637802649101774535 29146187456703973652661803)
          ·
            refine ⟨43719281185055960478992705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29146187456703973652661803 43719281185055960478992705)
            ·
              refine ⟨32789460888791970359244529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43719281185055960478992705 32789460888791970359244529)
              ·
                refine ⟨24592095666593977769433397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32789460888791970359244529 24592095666593977769433397)
                ·
                  refine ⟨2305508968743185415884381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24592095666593977769433397 2305508968743185415884381)
                  ·
                    refine ⟨864565863278694530956643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2305508968743185415884381 864565863278694530956643)
                    ·
                      rfl

theorem cell22_2525604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_2525604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2525604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2525604 prefixEnd_2525604 := by exact prefixLift 2525604
  have htrace : WordTrace (prefixWord ++ tailWord_2525604) baseStart_2525604 baseEnd_2525604 := by
    simpa [prefixWord, tailWord_2525604, baseEnd_2525604] using wordTrace_append hprefix tailTrace_2525604
  have hstable : (prefixWord ++ tailWord_2525604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525604).length < 2 ^ (prefixWord ++ tailWord_2525604).sum := by decide
  have hdescent : baseEnd_2525604 < baseStart_2525604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525632 : List Nat := [2, 1, 1, 2, 3, 1, 1, 3, 1, 7]
def baseStart_2525632 : Nat := 118140960795 + 2525632 * 2 ^ 59
def prefixEnd_2525632 : Nat := 4983230072969 + 3 ^ 40 * 2525632 * 2
def baseEnd_2525632 : Nat := 864575448250911791256557

theorem tailTrace_2525632 : CollatzResearch.WordTrace tailWord_2525632 prefixEnd_2525632 864575448250911791256557 := by
  unfold tailWord_2525632
  simp only [CollatzResearch.WordTrace]
  refine ⟨46058683393037041224845575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61411577857382721633127433 46058683393037041224845575)
  ·
    refine ⟨69088025089555561837268363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46058683393037041224845575 69088025089555561837268363)
    ·
      refine ⟨103632037634333342755902545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69088025089555561837268363 103632037634333342755902545)
      ·
        refine ⟨77724028225750007066926909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103632037634333342755902545 77724028225750007066926909)
        ·
          refine ⟨29146510584656252650097591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77724028225750007066926909 29146510584656252650097591)
          ·
            refine ⟨43719765876984378975146387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29146510584656252650097591 43719765876984378975146387)
            ·
              refine ⟨65579648815476568462719581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43719765876984378975146387 65579648815476568462719581)
              ·
                refine ⟨24592368305803713173519843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65579648815476568462719581 24592368305803713173519843)
                ·
                  refine ⟨36888552458705569760279765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24592368305803713173519843 36888552458705569760279765)
                  ·
                    refine ⟨864575448250911791256557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36888552458705569760279765 864575448250911791256557)
                    ·
                      rfl

theorem cell22_2525632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 1, 7].length) (baseStart_2525632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2525632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2525632 prefixEnd_2525632 := by exact prefixLift 2525632
  have htrace : WordTrace (prefixWord ++ tailWord_2525632) baseStart_2525632 baseEnd_2525632 := by
    simpa [prefixWord, tailWord_2525632, baseEnd_2525632] using wordTrace_append hprefix tailTrace_2525632
  have hstable : (prefixWord ++ tailWord_2525632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525632).length < 2 ^ (prefixWord ++ tailWord_2525632).sum := by decide
  have hdescent : baseEnd_2525632 < baseStart_2525632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525724 : List Nat := [2, 2, 3, 1, 2, 3, 9]
def baseStart_2525724 : Nat := 118140960795 + 2525724 * 2 ^ 59
def prefixEnd_2525724 : Nat := 4983230072969 + 3 ^ 40 * 2525724 * 2
def baseEnd_2525724 : Nat := 32022479323372378442825

theorem tailTrace_2525724 : CollatzResearch.WordTrace tailWord_2525724 prefixEnd_2525724 32022479323372378442825 := by
  unfold tailWord_2525724
  simp only [CollatzResearch.WordTrace]
  refine ⟨46060361150870391081020113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61413814867827188108026817 46060361150870391081020113)
  ·
    refine ⟨34545270863152793310765085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46060361150870391081020113 34545270863152793310765085)
    ·
      refine ⟨12954476573682297491536907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34545270863152793310765085 12954476573682297491536907)
      ·
        refine ⟨19431714860523446237305361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12954476573682297491536907 19431714860523446237305361)
        ·
          refine ⟨14573786145392584677979021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19431714860523446237305361 14573786145392584677979021)
          ·
            refine ⟨5465169804522219254242133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14573786145392584677979021 5465169804522219254242133)
            ·
              refine ⟨32022479323372378442825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5465169804522219254242133 32022479323372378442825)
              ·
                rfl

theorem cell22_2525724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 9].length) (baseStart_2525724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2525724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2525724 prefixEnd_2525724 := by exact prefixLift 2525724
  have htrace : WordTrace (prefixWord ++ tailWord_2525724) baseStart_2525724 baseEnd_2525724 := by
    simpa [prefixWord, tailWord_2525724, baseEnd_2525724] using wordTrace_append hprefix tailTrace_2525724
  have hstable : (prefixWord ++ tailWord_2525724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525724).length < 2 ^ (prefixWord ++ tailWord_2525724).sum := by decide
  have hdescent : baseEnd_2525724 < baseStart_2525724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525728 : List Nat := [2, 1, 1, 6, 2, 1, 1, 1, 4, 3]
def baseStart_2525728 : Nat := 118140960795 + 2525728 * 2 ^ 59
def prefixEnd_2525728 : Nat := 4983230072969 + 3 ^ 40 * 2525728 * 2
def baseEnd_2525728 : Nat := 864608311012799540856263

theorem tailTrace_2525728 : CollatzResearch.WordTrace tailWord_2525728 prefixEnd_2525728 864608311012799540856263 := by
  unfold tailWord_2525728
  simp only [CollatzResearch.WordTrace]
  refine ⟨46060434096863145422592919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61413912129150860563457225 46060434096863145422592919)
  ·
    refine ⟨69090651145294718133889379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46060434096863145422592919 69090651145294718133889379)
    ·
      refine ⟨103635976717942077200834069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69090651145294718133889379 103635976717942077200834069)
      ·
        refine ⟨4857936408653534868789097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 103635976717942077200834069 4857936408653534868789097)
        ·
          refine ⟨3643452306490151151591823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4857936408653534868789097 3643452306490151151591823)
          ·
            refine ⟨5465178459735226727387735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3643452306490151151591823 5465178459735226727387735)
            ·
              refine ⟨8197767689602840091081603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5465178459735226727387735 8197767689602840091081603)
              ·
                refine ⟨12296651534404260136622405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8197767689602840091081603 12296651534404260136622405)
                ·
                  refine ⟨2305622162700798775616701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12296651534404260136622405 2305622162700798775616701)
                  ·
                    refine ⟨864608311012799540856263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2305622162700798775616701 864608311012799540856263)
                    ·
                      rfl

theorem cell22_2525728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 4, 3].length) (baseStart_2525728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2525728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2525728 prefixEnd_2525728 := by exact prefixLift 2525728
  have htrace : WordTrace (prefixWord ++ tailWord_2525728) baseStart_2525728 baseEnd_2525728 := by
    simpa [prefixWord, tailWord_2525728, baseEnd_2525728] using wordTrace_append hprefix tailTrace_2525728
  have hstable : (prefixWord ++ tailWord_2525728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525728).length < 2 ^ (prefixWord ++ tailWord_2525728).sum := by decide
  have hdescent : baseEnd_2525728 < baseStart_2525728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525758 : List Nat := [4, 2, 1, 4, 1, 1, 1, 8]
def baseStart_2525758 : Nat := 118140960795 + 2525758 * 2 ^ 59
def prefixEnd_2525758 : Nat := 4983230072969 + 3 ^ 40 * 2525758 * 2
def baseEnd_2525758 : Nat := 96068731180654384734019

theorem tailTrace_2525758 : CollatzResearch.WordTrace tailWord_2525758 prefixEnd_2525758 96068731180654384734019 := by
  unfold tailWord_2525758
  simp only [CollatzResearch.WordTrace]
  refine ⟨11515245297952200746097241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61414641589078403979185285 11515245297952200746097241)
  ·
    refine ⟨8636433973464150559572931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11515245297952200746097241 8636433973464150559572931)
    ·
      refine ⟨12954650960196225839359397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8636433973464150559572931 12954650960196225839359397)
      ·
        refine ⟨2428997055036792344879887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12954650960196225839359397 2428997055036792344879887)
        ·
          refine ⟨3643495582555188517319831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2428997055036792344879887 3643495582555188517319831)
          ·
            refine ⟨5465243373832782775979747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3643495582555188517319831 5465243373832782775979747)
            ·
              refine ⟨8197865060749174163969621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5465243373832782775979747 8197865060749174163969621)
              ·
                refine ⟨96068731180654384734019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8197865060749174163969621 96068731180654384734019)
                ·
                  rfl

theorem cell22_2525758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 8].length) (baseStart_2525758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2525758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2525758 prefixEnd_2525758 := by exact prefixLift 2525758
  have htrace : WordTrace (prefixWord ++ tailWord_2525758) baseStart_2525758 baseEnd_2525758 := by
    simpa [prefixWord, tailWord_2525758, baseEnd_2525758] using wordTrace_append hprefix tailTrace_2525758
  have hstable : (prefixWord ++ tailWord_2525758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525758).length < 2 ^ (prefixWord ++ tailWord_2525758).sum := by decide
  have hdescent : baseEnd_2525758 < baseStart_2525758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525764 : List Nat := [2, 3, 5, 1, 1, 2, 1, 3, 4]
def baseStart_2525764 : Nat := 118140960795 + 2525764 * 2 ^ 59
def prefixEnd_2525764 : Nat := 4983230072969 + 3 ^ 40 * 2525764 * 2
def baseEnd_2525764 : Nat := 288206878182835815652051

theorem tailTrace_2525764 : CollatzResearch.WordTrace tailWord_2525764 prefixEnd_2525764 288206878182835815652051 := by
  unfold tailWord_2525764
  simp only [CollatzResearch.WordTrace]
  refine ⟨46061090610797934496748173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61414787481063912662330897 46061090610797934496748173)
  ·
    refine ⟨17272908979049225436280565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46061090610797934496748173 17272908979049225436280565)
    ·
      refine ⟨1619335216785864884651303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17272908979049225436280565 1619335216785864884651303)
      ·
        refine ⟨2429002825178797326976955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1619335216785864884651303 2429002825178797326976955)
        ·
          refine ⟨3643504237768195990465433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2429002825178797326976955 3643504237768195990465433)
          ·
            refine ⟨2732628178326146992849075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3643504237768195990465433 2732628178326146992849075)
            ·
              refine ⟨4098942267489220489273613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2732628178326146992849075 4098942267489220489273613)
              ·
                refine ⟨1537103350308457683477605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4098942267489220489273613 1537103350308457683477605)
                ·
                  refine ⟨288206878182835815652051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1537103350308457683477605 288206878182835815652051)
                  ·
                    rfl

theorem cell22_2525764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_2525764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2525764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2525764 prefixEnd_2525764 := by exact prefixLift 2525764
  have htrace : WordTrace (prefixWord ++ tailWord_2525764) baseStart_2525764 baseEnd_2525764 := by
    simpa [prefixWord, tailWord_2525764, baseEnd_2525764] using wordTrace_append hprefix tailTrace_2525764
  have hstable : (prefixWord ++ tailWord_2525764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525764).length < 2 ^ (prefixWord ++ tailWord_2525764).sum := by decide
  have hdescent : baseEnd_2525764 < baseStart_2525764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525784 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 4, 5]
def baseStart_2525784 : Nat := 118140960795 + 2525784 * 2 ^ 59
def prefixEnd_2525784 : Nat := 4983230072969 + 3 ^ 40 * 2525784 * 2
def baseEnd_2525784 : Nat := 864627480957234061456091

theorem tailTrace_2525784 : CollatzResearch.WordTrace tailWord_2525784 prefixEnd_2525784 864627480957234061456091 := by
  unfold tailWord_2525784
  simp only [CollatzResearch.WordTrace]
  refine ⟨46061455340761706204612203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61415273787682274939482937 46061455340761706204612203)
  ·
    refine ⟨69092183011142559306918305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46061455340761706204612203 69092183011142559306918305)
    ·
      refine ⟨51819137258356919480188729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69092183011142559306918305 51819137258356919480188729)
      ·
        refine ⟨38864352943767689610141547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51819137258356919480188729 38864352943767689610141547)
        ·
          refine ⟨58296529415651534415212321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38864352943767689610141547 58296529415651534415212321)
          ·
            refine ⟨43722397061738650811409241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58296529415651534415212321 43722397061738650811409241)
            ·
              refine ⟨32791797796303988108556931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43722397061738650811409241 32791797796303988108556931)
              ·
                refine ⟨49187696694455982162835397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32791797796303988108556931 49187696694455982162835397)
                ·
                  refine ⟨9222693130210496655531637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49187696694455982162835397 9222693130210496655531637)
                  ·
                    refine ⟨864627480957234061456091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9222693130210496655531637 864627480957234061456091)
                    ·
                      rfl

theorem cell22_2525784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_2525784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2525784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2525784 prefixEnd_2525784 := by exact prefixLift 2525784
  have htrace : WordTrace (prefixWord ++ tailWord_2525784) baseStart_2525784 baseEnd_2525784 := by
    simpa [prefixWord, tailWord_2525784, baseEnd_2525784] using wordTrace_append hprefix tailTrace_2525784
  have hstable : (prefixWord ++ tailWord_2525784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525784).length < 2 ^ (prefixWord ++ tailWord_2525784).sum := by decide
  have hdescent : baseEnd_2525784 < baseStart_2525784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525799 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 2, 8]
def baseStart_2525799 : Nat := 118140960795 + 2525799 * 2 ^ 59
def prefixEnd_2525799 : Nat := 4983230072969 + 3 ^ 40 * 2525799 * 2
def baseEnd_2525799 : Nat := 864632615763779022331045

theorem tailTrace_2525799 : CollatzResearch.WordTrace tailWord_2525799 prefixEnd_2525799 864632615763779022331045 := by
  unfold tailWord_2525799
  simp only [CollatzResearch.WordTrace]
  refine ⟨92123457776469069971020451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61415638517646046647346967 92123457776469069971020451)
  ·
    refine ⟨138185186664703604956530677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92123457776469069971020451 138185186664703604956530677)
    ·
      refine ⟨12954861249815962964674751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 138185186664703604956530677 12954861249815962964674751)
      ·
        refine ⟨19432291874723944447012127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12954861249815962964674751 19432291874723944447012127)
        ·
          refine ⟨29148437812085916670518191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19432291874723944447012127 29148437812085916670518191)
          ·
            refine ⟨43722656718128875005777287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29148437812085916670518191 43722656718128875005777287)
            ·
              refine ⟨65583985077193312508665931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43722656718128875005777287 65583985077193312508665931)
              ·
                refine ⟨98375977615789968762998897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65583985077193312508665931 98375977615789968762998897)
                ·
                  refine ⟨73781983211842476572249173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98375977615789968762998897 73781983211842476572249173)
                  ·
                    refine ⟨864632615763779022331045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 73781983211842476572249173 864632615763779022331045)
                    ·
                      rfl

theorem cell22_2525799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_2525799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2525799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2525799 prefixEnd_2525799 := by exact prefixLift 2525799
  have htrace : WordTrace (prefixWord ++ tailWord_2525799) baseStart_2525799 baseEnd_2525799 := by
    simpa [prefixWord, tailWord_2525799, baseEnd_2525799] using wordTrace_append hprefix tailTrace_2525799
  have hstable : (prefixWord ++ tailWord_2525799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525799).length < 2 ^ (prefixWord ++ tailWord_2525799).sum := by decide
  have hdescent : baseEnd_2525799 < baseStart_2525799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525848 : List Nat := [2, 1, 2, 4, 1, 1, 3, 4, 4]
def baseStart_2525848 : Nat := 118140960795 + 2525848 * 2 ^ 59
def prefixEnd_2525848 : Nat := 4983230072969 + 3 ^ 40 * 2525848 * 2
def baseEnd_2525848 : Nat := 288216463155053075951965

theorem tailTrace_2525848 : CollatzResearch.WordTrace tailWord_2525848 prefixEnd_2525848 288216463155053075951965 := by
  unfold tailWord_2525848
  simp only [CollatzResearch.WordTrace]
  refine ⟨46062622476645775669777099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61416829968861034226369465 46062622476645775669777099)
  ·
    refine ⟨69093933714968663504665649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46062622476645775669777099 69093933714968663504665649)
    ·
      refine ⟨51820450286226497628499237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69093933714968663504665649 51820450286226497628499237)
      ·
        refine ⟨9716334428667468305343607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51820450286226497628499237 9716334428667468305343607)
        ·
          refine ⟨14574501643001202458015411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9716334428667468305343607 14574501643001202458015411)
          ·
            refine ⟨21861752464501803687023117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14574501643001202458015411 21861752464501803687023117)
            ·
              refine ⟨8198157174188176382633669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21861752464501803687023117 8198157174188176382633669)
              ·
                refine ⟨1537154470160283071743813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8198157174188176382633669 1537154470160283071743813)
                ·
                  refine ⟨288216463155053075951965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1537154470160283071743813 288216463155053075951965)
                  ·
                    rfl

theorem cell22_2525848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 4, 4].length) (baseStart_2525848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2525848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2525848 prefixEnd_2525848 := by exact prefixLift 2525848
  have htrace : WordTrace (prefixWord ++ tailWord_2525848) baseStart_2525848 baseEnd_2525848 := by
    simpa [prefixWord, tailWord_2525848, baseEnd_2525848] using wordTrace_append hprefix tailTrace_2525848
  have hstable : (prefixWord ++ tailWord_2525848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525848).length < 2 ^ (prefixWord ++ tailWord_2525848).sum := by decide
  have hdescent : baseEnd_2525848 < baseStart_2525848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525859 : List Nat := [1, 1, 1, 4, 1, 1, 2, 11]
def baseStart_2525859 : Nat := 118140960795 + 2525859 * 2 ^ 59
def prefixEnd_2525859 : Nat := 4983230072969 + 3 ^ 40 * 2525859 * 2
def baseEnd_2525859 : Nat := 96072572776662096203429

theorem tailTrace_2525859 : CollatzResearch.WordTrace tailWord_2525859 prefixEnd_2525859 96072572776662096203429 := by
  unfold tailWord_2525859
  simp only [CollatzResearch.WordTrace]
  refine ⟨92125646156251700218204631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61417097437501133478803087 92125646156251700218204631)
  ·
    refine ⟨138188469234377550327306947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92125646156251700218204631 138188469234377550327306947)
    ·
      refine ⟨207282703851566325490960421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138188469234377550327306947 207282703851566325490960421)
      ·
        refine ⟨38865506972168686029555079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 207282703851566325490960421 38865506972168686029555079)
        ·
          refine ⟨58298260458253029044332619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38865506972168686029555079 58298260458253029044332619)
          ·
            refine ⟨87447390687379543566498929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58298260458253029044332619 87447390687379543566498929)
            ·
              refine ⟨65585543015534657674874197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87447390687379543566498929 65585543015534657674874197)
              ·
                refine ⟨96072572776662096203429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 65585543015534657674874197 96072572776662096203429)
                ·
                  rfl

theorem cell22_2525859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 11].length) (baseStart_2525859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2525859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2525859 prefixEnd_2525859 := by exact prefixLift 2525859
  have htrace : WordTrace (prefixWord ++ tailWord_2525859) baseStart_2525859 baseEnd_2525859 := by
    simpa [prefixWord, tailWord_2525859, baseEnd_2525859] using wordTrace_append hprefix tailTrace_2525859
  have hstable : (prefixWord ++ tailWord_2525859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525859).length < 2 ^ (prefixWord ++ tailWord_2525859).sum := by decide
  have hdescent : baseEnd_2525859 < baseStart_2525859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525951 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 5, 4]
def baseStart_2525951 : Nat := 118140960795 + 2525951 * 2 ^ 59
def prefixEnd_2525951 : Nat := 4983230072969 + 3 ^ 40 * 2525951 * 2
def baseEnd_2525951 : Nat := 864684648470101292530579

theorem tailTrace_2525951 : CollatzResearch.WordTrace tailWord_2525951 prefixEnd_2525951 864684648470101292530579 := by
  unfold tailWord_2525951
  simp only [CollatzResearch.WordTrace]
  refine ⟨92129001671918399930553707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61419334447945599953702471 92129001671918399930553707)
  ·
    refine ⟨138193502507877599895830561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92129001671918399930553707 138193502507877599895830561)
    ·
      refine ⟨103645126880908199921872921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138193502507877599895830561 103645126880908199921872921)
      ·
        refine ⟨77733845160681149941404691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103645126880908199921872921 77733845160681149941404691)
        ·
          refine ⟨116600767741021724912107037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77733845160681149941404691 116600767741021724912107037)
          ·
            refine ⟨43725287902883146842040139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116600767741021724912107037 43725287902883146842040139)
            ·
              refine ⟨65587931854324720263060209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43725287902883146842040139 65587931854324720263060209)
              ·
                refine ⟨49190948890743540197295157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65587931854324720263060209 49190948890743540197295157)
                ·
                  refine ⟨4611651458507206893496421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49190948890743540197295157 4611651458507206893496421)
                  ·
                    refine ⟨864684648470101292530579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4611651458507206893496421 864684648470101292530579)
                    ·
                      rfl

theorem cell22_2525951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 4].length) (baseStart_2525951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2525951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2525951 prefixEnd_2525951 := by exact prefixLift 2525951
  have htrace : WordTrace (prefixWord ++ tailWord_2525951) baseStart_2525951 baseEnd_2525951 := by
    simpa [prefixWord, tailWord_2525951, baseEnd_2525951] using wordTrace_append hprefix tailTrace_2525951
  have hstable : (prefixWord ++ tailWord_2525951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525951).length < 2 ^ (prefixWord ++ tailWord_2525951).sum := by decide
  have hdescent : baseEnd_2525951 < baseStart_2525951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2525959 : List Nat := [1, 1, 4, 4, 1, 2, 3, 2, 1, 3]
def baseStart_2525959 : Nat := 118140960795 + 2525959 * 2 ^ 59
def prefixEnd_2525959 : Nat := 4983230072969 + 3 ^ 40 * 2525959 * 2
def baseEnd_2525959 : Nat := 864687387033591938330555

theorem tailTrace_2525959 : CollatzResearch.WordTrace tailWord_2525959 prefixEnd_2525959 864687387033591938330555 := by
  unfold tailWord_2525959
  simp only [CollatzResearch.WordTrace]
  refine ⟨92129293455889417296844931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61419528970592944864563287 92129293455889417296844931)
  ·
    refine ⟨138193940183834125945267397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92129293455889417296844931 138193940183834125945267397)
    ·
      refine ⟨25911363784468898614737637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138193940183834125945267397 25911363784468898614737637)
      ·
        refine ⟨4858380709587918490263307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25911363784468898614737637 4858380709587918490263307)
        ·
          refine ⟨7287571064381877735394961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4858380709587918490263307 7287571064381877735394961)
          ·
            refine ⟨5465678298286408301546221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7287571064381877735394961 5465678298286408301546221)
            ·
              refine ⟨2049629361857403113079833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5465678298286408301546221 2049629361857403113079833)
              ·
                refine ⟨1537222021393052334809875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2049629361857403113079833 1537222021393052334809875)
                ·
                  refine ⟨2305833032089578502214813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1537222021393052334809875 2305833032089578502214813)
                  ·
                    refine ⟨864687387033591938330555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2305833032089578502214813 864687387033591938330555)
                    ·
                      rfl

theorem cell22_2525959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 2, 1, 3].length) (baseStart_2525959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2525959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2525959 prefixEnd_2525959 := by exact prefixLift 2525959
  have htrace : WordTrace (prefixWord ++ tailWord_2525959) baseStart_2525959 baseEnd_2525959 := by
    simpa [prefixWord, tailWord_2525959, baseEnd_2525959] using wordTrace_append hprefix tailTrace_2525959
  have hstable : (prefixWord ++ tailWord_2525959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2525959).length < 2 ^ (prefixWord ++ tailWord_2525959).sum := by decide
  have hdescent : baseEnd_2525959 < baseStart_2525959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2525959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526015 : List Nat := [1, 1, 2, 2, 5, 1, 1, 4, 2, 3]
def baseStart_2526015 : Nat := 118140960795 + 2526015 * 2 ^ 59
def prefixEnd_2526015 : Nat := 4983230072969 + 3 ^ 40 * 2526015 * 2
def baseEnd_2526015 : Nat := 864706556978026458930383

theorem tailTrace_2526015 : CollatzResearch.WordTrace tailWord_2526015 prefixEnd_2526015 864706556978026458930383 := by
  unfold tailWord_2526015
  simp only [CollatzResearch.WordTrace]
  refine ⟨92131335943686538860883499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61420890629124359240588999 92131335943686538860883499)
  ·
    refine ⟨138197003915529808291325249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92131335943686538860883499 138197003915529808291325249)
    ·
      refine ⟨103647752936647356218493937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138197003915529808291325249 103647752936647356218493937)
      ·
        refine ⟨77735814702485517163870453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103647752936647356218493937 77735814702485517163870453)
        ·
          refine ⟨7287732628358017234112855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77735814702485517163870453 7287732628358017234112855)
          ·
            refine ⟨10931598942537025851169283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7287732628358017234112855 10931598942537025851169283)
            ·
              refine ⟨16397398413805538776753925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10931598942537025851169283 16397398413805538776753925)
              ·
                refine ⟨3074512202588538520641361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16397398413805538776753925 3074512202588538520641361)
                ·
                  refine ⟨2305884151941403890481021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3074512202588538520641361 2305884151941403890481021)
                  ·
                    refine ⟨864706556978026458930383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2305884151941403890481021 864706556978026458930383)
                    ·
                      rfl

theorem cell22_2526015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 2, 3].length) (baseStart_2526015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2526015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2526015 prefixEnd_2526015 := by exact prefixLift 2526015
  have htrace : WordTrace (prefixWord ++ tailWord_2526015) baseStart_2526015 baseEnd_2526015 := by
    simpa [prefixWord, tailWord_2526015, baseEnd_2526015] using wordTrace_append hprefix tailTrace_2526015
  have hstable : (prefixWord ++ tailWord_2526015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526015).length < 2 ^ (prefixWord ++ tailWord_2526015).sum := by decide
  have hdescent : baseEnd_2526015 < baseStart_2526015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526028 : List Nat := [2, 2, 1, 3, 3, 1, 3, 7]
def baseStart_2526028 : Nat := 118140960795 + 2526028 * 2 ^ 59
def prefixEnd_2526028 : Nat := 4983230072969 + 3 ^ 40 * 2526028 * 2
def baseEnd_2526028 : Nat := 96079000793744306483927

theorem tailTrace_2526028 : CollatzResearch.WordTrace tailWord_2526028 prefixEnd_2526028 96079000793744306483927 := by
  unfold tailWord_2526028
  simp only [CollatzResearch.WordTrace]
  refine ⟨46065905046319721040553369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61421206728426294720737825 46065905046319721040553369)
  ·
    refine ⟨34549428784739790780415027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46065905046319721040553369 34549428784739790780415027)
    ·
      refine ⟨51824143177109686170622541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34549428784739790780415027 51824143177109686170622541)
      ·
        refine ⟨19434053691416132313983453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51824143177109686170622541 19434053691416132313983453)
        ·
          refine ⟨7287770134281049617743795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19434053691416132313983453 7287770134281049617743795)
          ·
            refine ⟨10931655201421574426615693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7287770134281049617743795 10931655201421574426615693)
            ·
              refine ⟨4099370700533090409980885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10931655201421574426615693 4099370700533090409980885)
              ·
                refine ⟨96079000793744306483927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4099370700533090409980885 96079000793744306483927)
                ·
                  rfl

theorem cell22_2526028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 7].length) (baseStart_2526028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2526028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2526028 prefixEnd_2526028 := by exact prefixLift 2526028
  have htrace : WordTrace (prefixWord ++ tailWord_2526028) baseStart_2526028 baseEnd_2526028 := by
    simpa [prefixWord, tailWord_2526028, baseEnd_2526028] using wordTrace_append hprefix tailTrace_2526028
  have hstable : (prefixWord ++ tailWord_2526028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526028).length < 2 ^ (prefixWord ++ tailWord_2526028).sum := by decide
  have hdescent : baseEnd_2526028 < baseStart_2526028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526073 : List Nat := [1, 2, 1, 3, 2, 4, 1, 1, 7]
def baseStart_2526073 : Nat := 118140960795 + 2526073 * 2 ^ 59
def prefixEnd_2526073 : Nat := 4983230072969 + 3 ^ 40 * 2526073 * 2
def baseEnd_2526073 : Nat := 288242137187777880326735

theorem tailTrace_2526073 : CollatzResearch.WordTrace tailWord_2526073 prefixEnd_2526073 288242137187777880326735 := by
  unfold tailWord_2526073
  simp only [CollatzResearch.WordTrace]
  refine ⟨92133451377476414766494873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61422300918317609844329915 92133451377476414766494873)
  ·
    refine ⟨69100088533107311074871155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92133451377476414766494873 69100088533107311074871155)
    ·
      refine ⟨103650132799660966612306733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69100088533107311074871155 103650132799660966612306733)
      ·
        refine ⟨38868799799872862479615025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103650132799660966612306733 38868799799872862479615025)
        ·
          refine ⟨29151599849904646859711269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38868799799872862479615025 29151599849904646859711269)
          ·
            refine ⟨5465924971857121286195863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29151599849904646859711269 5465924971857121286195863)
            ·
              refine ⟨8198887457785681929293795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5465924971857121286195863 8198887457785681929293795)
              ·
                refine ⟨12298331186678522893940693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8198887457785681929293795 12298331186678522893940693)
                ·
                  refine ⟨288242137187777880326735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12298331186678522893940693 288242137187777880326735)
                  ·
                    rfl

theorem cell22_2526073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 7].length) (baseStart_2526073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2526073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2526073 prefixEnd_2526073 := by exact prefixLift 2526073
  have htrace : WordTrace (prefixWord ++ tailWord_2526073) baseStart_2526073 baseEnd_2526073 := by
    simpa [prefixWord, tailWord_2526073, baseEnd_2526073] using wordTrace_append hprefix tailTrace_2526073
  have hstable : (prefixWord ++ tailWord_2526073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526073).length < 2 ^ (prefixWord ++ tailWord_2526073).sum := by decide
  have hdescent : baseEnd_2526073 < baseStart_2526073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526077 : List Nat := [1, 4, 1, 1, 2, 1, 4, 4, 1, 3]
def baseStart_2526077 : Nat := 118140960795 + 2526077 * 2 ^ 59
def prefixEnd_2526077 : Nat := 4983230072969 + 3 ^ 40 * 2526077 * 2
def baseEnd_2526077 : Nat := 864727780845078963880193

theorem tailTrace_2526077 : CollatzResearch.WordTrace tailWord_2526077 prefixEnd_2526077 864727780845078963880193 := by
  unfold tailWord_2526077
  simp only [CollatzResearch.WordTrace]
  refine ⟨92133597269461923449640485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61422398179641282299760323 92133597269461923449640485)
  ·
    refine ⟨17275049488024110646807591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92133597269461923449640485 17275049488024110646807591)
    ·
      refine ⟨25912574232036165970211387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17275049488024110646807591 25912574232036165970211387)
      ·
        refine ⟨38868861348054248955317081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25912574232036165970211387 38868861348054248955317081)
        ·
          refine ⟨29151646011040686716487811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38868861348054248955317081 29151646011040686716487811)
          ·
            refine ⟨43727469016561030074731717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29151646011040686716487811 43727469016561030074731717)
            ·
              refine ⟨8198900440605193139012197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43727469016561030074731717 8198900440605193139012197)
              ·
                refine ⟨1537293832613473713564787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8198900440605193139012197 1537293832613473713564787)
                ·
                  refine ⟨2305940748920210570347181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1537293832613473713564787 2305940748920210570347181)
                  ·
                    refine ⟨864727780845078963880193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2305940748920210570347181 864727780845078963880193)
                    ·
                      rfl

theorem cell22_2526077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 4, 1, 3].length) (baseStart_2526077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2526077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2526077 prefixEnd_2526077 := by exact prefixLift 2526077
  have htrace : WordTrace (prefixWord ++ tailWord_2526077) baseStart_2526077 baseEnd_2526077 := by
    simpa [prefixWord, tailWord_2526077, baseEnd_2526077] using wordTrace_append hprefix tailTrace_2526077
  have hstable : (prefixWord ++ tailWord_2526077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526077).length < 2 ^ (prefixWord ++ tailWord_2526077).sum := by decide
  have hdescent : baseEnd_2526077 < baseStart_2526077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526135 : List Nat := [1, 1, 3, 1, 3, 1, 2, 6, 4]
def baseStart_2526135 : Nat := 118140960795 + 2526135 * 2 ^ 59
def prefixEnd_2526135 : Nat := 4983230072969 + 3 ^ 40 * 2526135 * 2
def baseEnd_2526135 : Nat := 288249211810128715310005

theorem tailTrace_2526135 : CollatzResearch.WordTrace tailWord_2526135 prefixEnd_2526135 288249211810128715310005 := by
  unfold tailWord_2526135
  simp only [CollatzResearch.WordTrace]
  refine ⟨92135712703251799355251859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61423808468834532903501239 92135712703251799355251859)
  ·
    refine ⟨138203569054877699032877789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92135712703251799355251859 138203569054877699032877789)
    ·
      refine ⟨51826338395579137137329171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138203569054877699032877789 51826338395579137137329171)
      ·
        refine ⟨77739507593368705705993757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51826338395579137137329171 77739507593368705705993757)
        ·
          refine ⟨29152315347513264639747659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77739507593368705705993757 29152315347513264639747659)
          ·
            refine ⟨43728473021269896959621489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29152315347513264639747659 43728473021269896959621489)
            ·
              refine ⟨32796354765952422719716117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43728473021269896959621489 32796354765952422719716117)
              ·
                refine ⟨1537329129654019814986693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32796354765952422719716117 1537329129654019814986693)
                ·
                  refine ⟨288249211810128715310005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1537329129654019814986693 288249211810128715310005)
                  ·
                    rfl

theorem cell22_2526135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 6, 4].length) (baseStart_2526135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2526135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2526135 prefixEnd_2526135 := by exact prefixLift 2526135
  have htrace : WordTrace (prefixWord ++ tailWord_2526135) baseStart_2526135 baseEnd_2526135 := by
    simpa [prefixWord, tailWord_2526135, baseEnd_2526135] using wordTrace_append hprefix tailTrace_2526135
  have hstable : (prefixWord ++ tailWord_2526135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526135).length < 2 ^ (prefixWord ++ tailWord_2526135).sum := by decide
  have hdescent : baseEnd_2526135 < baseStart_2526135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526229 : List Nat := [1, 3, 2, 1, 4, 1, 1, 5, 1, 3]
def baseStart_2526229 : Nat := 118140960795 + 2526229 * 2 ^ 59
def prefixEnd_2526229 : Nat := 4983230072969 + 3 ^ 40 * 2526229 * 2
def baseEnd_2526229 : Nat := 864779813551401234079727

theorem tailTrace_2526229 : CollatzResearch.WordTrace tailWord_2526229 prefixEnd_2526229 864779813551401234079727 := by
  unfold tailWord_2526229
  simp only [CollatzResearch.WordTrace]
  refine ⟨92139141164911253409173741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61426094109940835606115827 92139141164911253409173741)
  ·
    refine ⟨34552177936841720028440153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92139141164911253409173741 34552177936841720028440153)
    ·
      refine ⟨25914133452631290021330115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34552177936841720028440153 25914133452631290021330115)
      ·
        refine ⟨38871200178946935031995173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25914133452631290021330115 38871200178946935031995173)
        ·
          refine ⟨7288350033552550318499095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38871200178946935031995173 7288350033552550318499095)
          ·
            refine ⟨10932525050328825477748643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7288350033552550318499095 10932525050328825477748643)
            ·
              refine ⟨16398787575493238216622965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10932525050328825477748643 16398787575493238216622965)
              ·
                refine ⟨1537386335202491082808403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16398787575493238216622965 1537386335202491082808403)
                ·
                  refine ⟨2306079502803736624212605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1537386335202491082808403 2306079502803736624212605)
                  ·
                    refine ⟨864779813551401234079727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2306079502803736624212605 864779813551401234079727)
                    ·
                      rfl

theorem cell22_2526229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 5, 1, 3].length) (baseStart_2526229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2526229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2526229 prefixEnd_2526229 := by exact prefixLift 2526229
  have htrace : WordTrace (prefixWord ++ tailWord_2526229) baseStart_2526229 baseEnd_2526229 := by
    simpa [prefixWord, tailWord_2526229, baseEnd_2526229] using wordTrace_append hprefix tailTrace_2526229
  have hstable : (prefixWord ++ tailWord_2526229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526229).length < 2 ^ (prefixWord ++ tailWord_2526229).sum := by decide
  have hdescent : baseEnd_2526229 < baseStart_2526229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526242 : List Nat := [3, 3, 1, 1, 1, 3, 3, 2, 5]
def baseStart_2526242 : Nat := 118140960795 + 2526242 * 2 ^ 59
def prefixEnd_2526242 : Nat := 4983230072969 + 3 ^ 40 * 2526242 * 2
def baseEnd_2526242 : Nat := 288261421239024511168229

theorem tailTrace_2526242 : CollatzResearch.WordTrace tailWord_2526242 prefixEnd_2526242 288261421239024511168229 := by
  unfold tailWord_2526242
  simp only [CollatzResearch.WordTrace]
  refine ⟨23034903828466039157349245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61426410209242771086264653 23034903828466039157349245)
  ·
    refine ⟨8638088935674764684005967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23034903828466039157349245 8638088935674764684005967)
    ·
      refine ⟨12957133403512147026008951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8638088935674764684005967 12957133403512147026008951)
      ·
        refine ⟨19435700105268220539013427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12957133403512147026008951 19435700105268220539013427)
        ·
          refine ⟨29153550157902330808520141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19435700105268220539013427 29153550157902330808520141)
          ·
            refine ⟨10932581309213374053195053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29153550157902330808520141 10932581309213374053195053)
            ·
              refine ⟨4099717990955015269948145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10932581309213374053195053 4099717990955015269948145)
              ·
                refine ⟨3074788493216261452461109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4099717990955015269948145 3074788493216261452461109)
                ·
                  refine ⟨288261421239024511168229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3074788493216261452461109 288261421239024511168229)
                  ·
                    rfl

theorem cell22_2526242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_2526242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2526242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2526242 prefixEnd_2526242 := by exact prefixLift 2526242
  have htrace : WordTrace (prefixWord ++ tailWord_2526242) baseStart_2526242 baseEnd_2526242 := by
    simpa [prefixWord, tailWord_2526242, baseEnd_2526242] using wordTrace_append hprefix tailTrace_2526242
  have hstable : (prefixWord ++ tailWord_2526242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526242).length < 2 ^ (prefixWord ++ tailWord_2526242).sum := by decide
  have hdescent : baseEnd_2526242 < baseStart_2526242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526272 : List Nat := [2, 1, 1, 2, 2, 3, 4, 2, 1, 4]
def baseStart_2526272 : Nat := 118140960795 + 2526272 * 2 ^ 59
def prefixEnd_2526272 : Nat := 4983230072969 + 3 ^ 40 * 2526272 * 2
def baseEnd_2526272 : Nat := 864794533330163455254595

theorem tailTrace_2526272 : CollatzResearch.WordTrace tailWord_2526272 prefixEnd_2526272 864794533330163455254595 := by
  unfold tailWord_2526272
  simp only [CollatzResearch.WordTrace]
  refine ⟨46070354751877735876494535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61427139669170314501992713 46070354751877735876494535)
  ·
    refine ⟨69105532127816603814741803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46070354751877735876494535 69105532127816603814741803)
    ·
      refine ⟨103658298191724905722112705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69105532127816603814741803 103658298191724905722112705)
      ·
        refine ⟨77743723643793679291584529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103658298191724905722112705 77743723643793679291584529)
        ·
          refine ⟨58307792732845259468688397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77743723643793679291584529 58307792732845259468688397)
          ·
            refine ⟨21865422274816972300758149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58307792732845259468688397 21865422274816972300758149)
            ·
              refine ⟨4099766676528182306392153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21865422274816972300758149 4099766676528182306392153)
              ·
                refine ⟨3074825007396136729794115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4099766676528182306392153 3074825007396136729794115)
                ·
                  refine ⟨4612237511094205094691173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3074825007396136729794115 4612237511094205094691173)
                  ·
                    refine ⟨864794533330163455254595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4612237511094205094691173 864794533330163455254595)
                    ·
                      rfl

theorem cell22_2526272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 1, 4].length) (baseStart_2526272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2526272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2526272 prefixEnd_2526272 := by exact prefixLift 2526272
  have htrace : WordTrace (prefixWord ++ tailWord_2526272) baseStart_2526272 baseEnd_2526272 := by
    simpa [prefixWord, tailWord_2526272, baseEnd_2526272] using wordTrace_append hprefix tailTrace_2526272
  have hstable : (prefixWord ++ tailWord_2526272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526272).length < 2 ^ (prefixWord ++ tailWord_2526272).sum := by decide
  have hdescent : baseEnd_2526272 < baseStart_2526272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526304 : List Nat := [2, 1, 1, 3, 2, 2, 5, 2, 4]
def baseStart_2526304 : Nat := 118140960795 + 2526304 * 2 ^ 59
def prefixEnd_2526304 : Nat := 4983230072969 + 3 ^ 40 * 2526304 * 2
def baseEnd_2526304 : Nat := 288268495861375346151499

theorem tailTrace_2526304 : CollatzResearch.WordTrace tailWord_2526304 prefixEnd_2526304 288268495861375346151499 := by
  unfold tailWord_2526304
  simp only [CollatzResearch.WordTrace]
  refine ⟨46070938319819770609076983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61427917759759694145435977 46070938319819770609076983)
  ·
    refine ⟨69106407479729655913615475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46070938319819770609076983 69106407479729655913615475)
    ·
      refine ⟨103659611219594483870423213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69106407479729655913615475 103659611219594483870423213)
      ·
        refine ⟨38872354207347931451408705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103659611219594483870423213 38872354207347931451408705)
        ·
          refine ⟨29154265655510948588556529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38872354207347931451408705 29154265655510948588556529)
          ·
            refine ⟨21865699241633211441417397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29154265655510948588556529 21865699241633211441417397)
            ·
              refine ⟨2049909303903113572632881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21865699241633211441417397 2049909303903113572632881)
              ·
                refine ⟨1537431977927335179474661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2049909303903113572632881 1537431977927335179474661)
                ·
                  refine ⟨288268495861375346151499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1537431977927335179474661 288268495861375346151499)
                  ·
                    rfl

theorem cell22_2526304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 2, 4].length) (baseStart_2526304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2526304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2526304 prefixEnd_2526304 := by exact prefixLift 2526304
  have htrace : WordTrace (prefixWord ++ tailWord_2526304) baseStart_2526304 baseEnd_2526304 := by
    simpa [prefixWord, tailWord_2526304, baseEnd_2526304] using wordTrace_append hprefix tailTrace_2526304
  have hstable : (prefixWord ++ tailWord_2526304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526304).length < 2 ^ (prefixWord ++ tailWord_2526304).sum := by decide
  have hdescent : baseEnd_2526304 < baseStart_2526304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526362 : List Nat := [3, 1, 1, 5, 1, 1, 1, 1, 2, 6]
def baseStart_2526362 : Nat := 118140960795 + 2526362 * 2 ^ 59
def prefixEnd_2526362 : Nat := 4983230072969 + 3 ^ 40 * 2526362 * 2
def baseEnd_2526362 : Nat := 864825342169433220504319

theorem tailTrace_2526362 : CollatzResearch.WordTrace tailWord_2526362 prefixEnd_2526362 864825342169433220504319 := by
  unfold tailWord_2526362
  simp only [CollatzResearch.WordTrace]
  refine ⟨23035998018357354280941335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61429328048952944749176893 23035998018357354280941335)
  ·
    refine ⟨34553997027536031421412003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23035998018357354280941335 34553997027536031421412003)
    ·
      refine ⟨51830995541304047132118005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34553997027536031421412003 51830995541304047132118005)
      ·
        refine ⟨4859155831997254418636063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51830995541304047132118005 4859155831997254418636063)
        ·
          refine ⟨7288733747995881627954095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4859155831997254418636063 7288733747995881627954095)
          ·
            refine ⟨10933100621993822441931143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7288733747995881627954095 10933100621993822441931143)
            ·
              refine ⟨16399650932990733662896715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10933100621993822441931143 16399650932990733662896715)
              ·
                refine ⟨24599476399486100494345073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16399650932990733662896715 24599476399486100494345073)
                ·
                  refine ⟨18449607299614575370758805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24599476399486100494345073 18449607299614575370758805)
                  ·
                    refine ⟨864825342169433220504319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18449607299614575370758805 864825342169433220504319)
                    ·
                      rfl

theorem cell22_2526362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_2526362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2526362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2526362 prefixEnd_2526362 := by exact prefixLift 2526362
  have htrace : WordTrace (prefixWord ++ tailWord_2526362) baseStart_2526362 baseEnd_2526362 := by
    simpa [prefixWord, tailWord_2526362, baseEnd_2526362] using wordTrace_append hprefix tailTrace_2526362
  have hstable : (prefixWord ++ tailWord_2526362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526362).length < 2 ^ (prefixWord ++ tailWord_2526362).sum := by decide
  have hdescent : baseEnd_2526362 < baseStart_2526362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526381 : List Nat := [1, 5, 2, 1, 3, 1, 1, 2, 3, 3]
def baseStart_2526381 : Nat := 118140960795 + 2526381 * 2 ^ 59
def prefixEnd_2526381 : Nat := 4983230072969 + 3 ^ 40 * 2526381 * 2
def baseEnd_2526381 : Nat := 864831846257723504279261

theorem tailTrace_2526381 : CollatzResearch.WordTrace tailWord_2526381 prefixEnd_2526381 864831846257723504279261 := by
  unfold tailWord_2526381
  simp only [CollatzResearch.WordTrace]
  refine ⟨92144685060360583368706997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61429790040240388912471331 92144685060360583368706997)
  ·
    refine ⟨8638564224408804690816281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92144685060360583368706997 8638564224408804690816281)
    ·
      refine ⟨6478923168306603518112211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8638564224408804690816281 6478923168306603518112211)
      ·
        refine ⟨9718384752459905277168317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6478923168306603518112211 9718384752459905277168317)
        ·
          refine ⟨3644394282172464478938119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9718384752459905277168317 3644394282172464478938119)
          ·
            refine ⟨5466591423258696718407179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3644394282172464478938119 5466591423258696718407179)
            ·
              refine ⟨8199887134888045077610769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5466591423258696718407179 8199887134888045077610769)
              ·
                refine ⟨6149915351166033808208077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8199887134888045077610769 6149915351166033808208077)
                ·
                  refine ⟨2306218256687262678078029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6149915351166033808208077 2306218256687262678078029)
                  ·
                    refine ⟨864831846257723504279261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2306218256687262678078029 864831846257723504279261)
                    ·
                      rfl

theorem cell22_2526381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_2526381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2526381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2526381 prefixEnd_2526381 := by exact prefixLift 2526381
  have htrace : WordTrace (prefixWord ++ tailWord_2526381) baseStart_2526381 baseEnd_2526381 := by
    simpa [prefixWord, tailWord_2526381, baseEnd_2526381] using wordTrace_append hprefix tailTrace_2526381
  have hstable : (prefixWord ++ tailWord_2526381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526381).length < 2 ^ (prefixWord ++ tailWord_2526381).sum := by decide
  have hdescent : baseEnd_2526381 < baseStart_2526381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526398 : List Nat := [4, 2, 1, 1, 3, 2, 2, 3, 1, 3]
def baseStart_2526398 : Nat := 118140960795 + 2526398 * 2 ^ 59
def prefixEnd_2526398 : Nat := 4983230072969 + 3 ^ 40 * 2526398 * 2
def baseEnd_2526398 : Nat := 864837665705141126604209

theorem tailTrace_2526398 : CollatzResearch.WordTrace tailWord_2526398 prefixEnd_2526398 864837665705141126604209 := by
  unfold tailWord_2526398
  simp only [CollatzResearch.WordTrace]
  refine ⟨11518163137662374409009481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61430203400865996848050565 11518163137662374409009481)
  ·
    refine ⟨8638622353246780806757111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11518163137662374409009481 8638622353246780806757111)
    ·
      refine ⟨12957933529870171210135667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8638622353246780806757111 12957933529870171210135667)
      ·
        refine ⟨19436900294805256815203501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12957933529870171210135667 19436900294805256815203501)
        ·
          refine ⟨7288837610551971305701313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19436900294805256815203501 7288837610551971305701313)
          ·
            refine ⟨5466628207913978479275985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7288837610551971305701313 5466628207913978479275985)
            ·
              refine ⟨4099971155935483859456989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5466628207913978479275985 4099971155935483859456989)
              ·
                refine ⟨1537489183475806447296371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4099971155935483859456989 1537489183475806447296371)
                ·
                  refine ⟨2306233775213709670944557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1537489183475806447296371 2306233775213709670944557)
                  ·
                    refine ⟨864837665705141126604209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2306233775213709670944557 864837665705141126604209)
                    ·
                      rfl

theorem cell22_2526398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_2526398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2526398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2526398 prefixEnd_2526398 := by exact prefixLift 2526398
  have htrace : WordTrace (prefixWord ++ tailWord_2526398) baseStart_2526398 baseEnd_2526398 := by
    simpa [prefixWord, tailWord_2526398, baseEnd_2526398] using wordTrace_append hprefix tailTrace_2526398
  have hstable : (prefixWord ++ tailWord_2526398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526398).length < 2 ^ (prefixWord ++ tailWord_2526398).sum := by decide
  have hdescent : baseEnd_2526398 < baseStart_2526398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526405 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 10]
def baseStart_2526405 : Nat := 118140960795 + 2526405 * 2 ^ 59
def prefixEnd_2526405 : Nat := 4983230072969 + 3 ^ 40 * 2526405 * 2
def baseEnd_2526405 : Nat := 288280020649398480559729

theorem tailTrace_2526405 : CollatzResearch.WordTrace tailWord_2526405 prefixEnd_2526405 288280020649398480559729 := by
  unfold tailWord_2526405
  simp only [CollatzResearch.WordTrace]
  refine ⟨92145560412273635467580669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61430373608182423645053779 92145560412273635467580669)
  ·
    refine ⟨34554585154602613300342751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92145560412273635467580669 34554585154602613300342751)
    ·
      refine ⟨51831877731903919950514127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34554585154602613300342751 51831877731903919950514127)
      ·
        refine ⟨77747816597855879925771191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51831877731903919950514127 77747816597855879925771191)
        ·
          refine ⟨116621724896783819888656787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77747816597855879925771191 116621724896783819888656787)
          ·
            refine ⟨174932587345175729832985181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116621724896783819888656787 174932587345175729832985181)
            ·
              refine ⟨65599720254440898687369443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174932587345175729832985181 65599720254440898687369443)
              ·
                refine ⟨98399580381661348031054165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65599720254440898687369443 98399580381661348031054165)
                ·
                  refine ⟨288280020649398480559729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 98399580381661348031054165 288280020649398480559729)
                  ·
                    rfl

theorem cell22_2526405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 10].length) (baseStart_2526405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2526405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2526405 prefixEnd_2526405 := by exact prefixLift 2526405
  have htrace : WordTrace (prefixWord ++ tailWord_2526405) baseStart_2526405 baseEnd_2526405 := by
    simpa [prefixWord, tailWord_2526405, baseEnd_2526405] using wordTrace_append hprefix tailTrace_2526405
  have hstable : (prefixWord ++ tailWord_2526405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526405).length < 2 ^ (prefixWord ++ tailWord_2526405).sum := by decide
  have hdescent : baseEnd_2526405 < baseStart_2526405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526467 : List Nat := [1, 1, 1, 3, 2, 6, 8]
def baseStart_2526467 : Nat := 118140960795 + 2526467 * 2 ^ 59
def prefixEnd_2526467 : Nat := 4983230072969 + 3 ^ 40 * 2526467 * 2
def baseEnd_2526467 : Nat := 32031899474638812838111

theorem tailTrace_2526467 : CollatzResearch.WordTrace tailWord_2526467 prefixEnd_2526467 32031899474638812838111 := by
  unfold tailWord_2526467
  simp only [CollatzResearch.WordTrace]
  refine ⟨92147821738049020056337655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61431881158699346704225103 92147821738049020056337655)
  ·
    refine ⟨138221732607073530084506483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92147821738049020056337655 138221732607073530084506483)
    ·
      refine ⟨207332598910610295126759725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138221732607073530084506483 207332598910610295126759725)
      ·
        refine ⟨77749724591478860672534897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207332598910610295126759725 77749724591478860672534897)
        ·
          refine ⟨58312293443609145504401173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77749724591478860672534897 58312293443609145504401173)
          ·
            refine ⟨2733388755169178695518805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58312293443609145504401173 2733388755169178695518805)
            ·
              refine ⟨32031899474638812838111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2733388755169178695518805 32031899474638812838111)
              ·
                rfl

theorem cell22_2526467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 8].length) (baseStart_2526467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2526467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2526467 prefixEnd_2526467 := by exact prefixLift 2526467
  have htrace : WordTrace (prefixWord ++ tailWord_2526467) baseStart_2526467 baseEnd_2526467 := by
    simpa [prefixWord, tailWord_2526467, baseEnd_2526467] using wordTrace_append hprefix tailTrace_2526467
  have hstable : (prefixWord ++ tailWord_2526467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526467).length < 2 ^ (prefixWord ++ tailWord_2526467).sum := by decide
  have hdescent : baseEnd_2526467 < baseStart_2526467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526488 : List Nat := [2, 1, 2, 3, 1, 5, 2, 1, 2, 3]
def baseStart_2526488 : Nat := 118140960795 + 2526488 * 2 ^ 59
def prefixEnd_2526488 : Nat := 4983230072969 + 3 ^ 40 * 2526488 * 2
def baseEnd_2526488 : Nat := 864868474544410891853933

theorem tailTrace_2526488 : CollatzResearch.WordTrace tailWord_2526488 prefixEnd_2526488 864868474544410891853933 := by
  unfold tailWord_2526488
  simp only [CollatzResearch.WordTrace]
  refine ⟨46074293835486470321426059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61432391780648627095234745 46074293835486470321426059)
  ·
    refine ⟨69111440753229705482139089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46074293835486470321426059 69111440753229705482139089)
    ·
      refine ⟨51833580564922279111604317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69111440753229705482139089 51833580564922279111604317)
      ·
        refine ⟨19437592711845854666851619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51833580564922279111604317 19437592711845854666851619)
        ·
          refine ⟨29156389067768782000277429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19437592711845854666851619 29156389067768782000277429)
          ·
            refine ⟨2733411475103323312526009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29156389067768782000277429 2733411475103323312526009)
            ·
              refine ⟨2050058606327492484394507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2733411475103323312526009 2050058606327492484394507)
              ·
                refine ⟨3075087909491238726591761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2050058606327492484394507 3075087909491238726591761)
                ·
                  refine ⟨2306315932118429044943821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3075087909491238726591761 2306315932118429044943821)
                  ·
                    refine ⟨864868474544410891853933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2306315932118429044943821 864868474544410891853933)
                    ·
                      rfl

theorem cell22_2526488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 2, 3].length) (baseStart_2526488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2526488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2526488 prefixEnd_2526488 := by exact prefixLift 2526488
  have htrace : WordTrace (prefixWord ++ tailWord_2526488) baseStart_2526488 baseEnd_2526488 := by
    simpa [prefixWord, tailWord_2526488, baseEnd_2526488] using wordTrace_append hprefix tailTrace_2526488
  have hstable : (prefixWord ++ tailWord_2526488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526488).length < 2 ^ (prefixWord ++ tailWord_2526488).sum := by decide
  have hdescent : baseEnd_2526488 < baseStart_2526488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526559 : List Nat := [1, 1, 2, 3, 1, 2, 1, 6, 1, 4]
def baseStart_2526559 : Nat := 118140960795 + 2526559 * 2 ^ 59
def prefixEnd_2526559 : Nat := 4983230072969 + 3 ^ 40 * 2526559 * 2
def baseEnd_2526559 : Nat := 864892779295390373328715

theorem tailTrace_2526559 : CollatzResearch.WordTrace tailWord_2526559 prefixEnd_2526559 864892779295390373328715 := by
  unfold tailWord_2526559
  simp only [CollatzResearch.WordTrace]
  refine ⟨92151177253715719768686731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61434118169143813179124487 92151177253715719768686731)
  ·
    refine ⟨138226765880573579653030097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92151177253715719768686731 138226765880573579653030097)
    ·
      refine ⟨103670074410430184739772573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138226765880573579653030097 103670074410430184739772573)
      ·
        refine ⟨38876277903911319277414715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103670074410430184739772573 38876277903911319277414715)
        ·
          refine ⟨58314416855866978916122073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38876277903911319277414715 58314416855866978916122073)
          ·
            refine ⟨43735812641900234187091555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58314416855866978916122073 43735812641900234187091555)
            ·
              refine ⟨65603718962850351280637333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43735812641900234187091555 65603718962850351280637333)
              ·
                refine ⟨3075174326383610216279875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65603718962850351280637333 3075174326383610216279875)
                ·
                  refine ⟨4612761489575415324419813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3075174326383610216279875 4612761489575415324419813)
                  ·
                    refine ⟨864892779295390373328715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4612761489575415324419813 864892779295390373328715)
                    ·
                      rfl

theorem cell22_2526559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 4].length) (baseStart_2526559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2526559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2526559 prefixEnd_2526559 := by exact prefixLift 2526559
  have htrace : WordTrace (prefixWord ++ tailWord_2526559) baseStart_2526559 baseEnd_2526559 := by
    simpa [prefixWord, tailWord_2526559, baseEnd_2526559] using wordTrace_append hprefix tailTrace_2526559
  have hstable : (prefixWord ++ tailWord_2526559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526559).length < 2 ^ (prefixWord ++ tailWord_2526559).sum := by decide
  have hdescent : baseEnd_2526559 < baseStart_2526559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526610 : List Nat := [3, 2, 3, 3, 1, 1, 2, 2, 1, 4]
def baseStart_2526610 : Nat := 118140960795 + 2526610 * 2 ^ 59
def prefixEnd_2526610 : Nat := 4983230072969 + 3 ^ 40 * 2526610 * 2
def baseEnd_2526610 : Nat := 864910237637643240303559

theorem tailTrace_2526610 : CollatzResearch.WordTrace tailWord_2526610 prefixEnd_2526610 864910237637643240303559 := by
  unfold tailWord_2526610
  simp only [CollatzResearch.WordTrace]
  refine ⟨23038259344132738869698321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61435358251020636985862189 23038259344132738869698321)
  ·
    refine ⟨17278694508099554152273741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23038259344132738869698321 17278694508099554152273741)
    ·
      refine ⟨6479510440537332807102653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17278694508099554152273741 6479510440537332807102653)
      ·
        refine ⟨2429816415201499802663495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6479510440537332807102653 2429816415201499802663495)
        ·
          refine ⟨3644724622802249703995243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2429816415201499802663495 3644724622802249703995243)
          ·
            refine ⟨5467086934203374555992865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3644724622802249703995243 5467086934203374555992865)
            ·
              refine ⟨4100315200652530916994649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5467086934203374555992865 4100315200652530916994649)
              ·
                refine ⟨3075236400489398187745987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4100315200652530916994649 3075236400489398187745987)
                ·
                  refine ⟨4612854600734097281618981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3075236400489398187745987 4612854600734097281618981)
                  ·
                    refine ⟨864910237637643240303559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4612854600734097281618981 864910237637643240303559)
                    ·
                      rfl

theorem cell22_2526610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_2526610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2526610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2526610 prefixEnd_2526610 := by exact prefixLift 2526610
  have htrace : WordTrace (prefixWord ++ tailWord_2526610) baseStart_2526610 baseEnd_2526610 := by
    simpa [prefixWord, tailWord_2526610, baseEnd_2526610] using wordTrace_append hprefix tailTrace_2526610
  have hstable : (prefixWord ++ tailWord_2526610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526610).length < 2 ^ (prefixWord ++ tailWord_2526610).sum := by decide
  have hdescent : baseEnd_2526610 < baseStart_2526610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526698 : List Nat := [3, 1, 3, 1, 4, 1, 2, 2, 5]
def baseStart_2526698 : Nat := 118140960795 + 2526698 * 2 ^ 59
def prefixEnd_2526698 : Nat := 4983230072969 + 3 ^ 40 * 2526698 * 2
def baseEnd_2526698 : Nat := 288313453945346781367763

theorem tailTrace_2526698 : CollatzResearch.WordTrace tailWord_2526698 prefixEnd_2526698 288313453945346781367763 := by
  unfold tailWord_2526698
  simp only [CollatzResearch.WordTrace]
  refine ⟨23039061750053036626999187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61437498000141431005331165 23039061750053036626999187)
  ·
    refine ⟨34558592625079554940498781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23039061750053036626999187 34558592625079554940498781)
    ·
      refine ⟨12959472234404833102687043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34558592625079554940498781 12959472234404833102687043)
      ·
        refine ⟨19439208351607249654030565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12959472234404833102687043 19439208351607249654030565)
        ·
          refine ⟨3644851565926359310130731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19439208351607249654030565 3644851565926359310130731)
          ·
            refine ⟨5467277348889538965196097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3644851565926359310130731 5467277348889538965196097)
            ·
              refine ⟨4100458011667154223897073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5467277348889538965196097 4100458011667154223897073)
              ·
                refine ⟨3075343508750365667922805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4100458011667154223897073 3075343508750365667922805)
                ·
                  refine ⟨288313453945346781367763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3075343508750365667922805 288313453945346781367763)
                  ·
                    rfl

theorem cell22_2526698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 5].length) (baseStart_2526698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2526698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2526698 prefixEnd_2526698 := by exact prefixLift 2526698
  have htrace : WordTrace (prefixWord ++ tailWord_2526698) baseStart_2526698 baseEnd_2526698 := by
    simpa [prefixWord, tailWord_2526698, baseEnd_2526698] using wordTrace_append hprefix tailTrace_2526698
  have hstable : (prefixWord ++ tailWord_2526698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526698).length < 2 ^ (prefixWord ++ tailWord_2526698).sum := by decide
  have hdescent : baseEnd_2526698 < baseStart_2526698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526741 : List Nat := [1, 3, 2, 1, 3, 2, 2, 2, 1, 5]
def baseStart_2526741 : Nat := 118140960795 + 2526741 * 2 ^ 59
def prefixEnd_2526741 : Nat := 4983230072969 + 3 ^ 40 * 2526741 * 2
def baseEnd_2526741 : Nat := 864955081614802565278157

theorem tailTrace_2526741 : CollatzResearch.WordTrace tailWord_2526741 prefixEnd_2526741 864955081614802565278157 := by
  unfold tailWord_2526741
  simp only [CollatzResearch.WordTrace]
  refine ⟨92157815339056364851812077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61438543559370909901208051 92157815339056364851812077)
  ·
    refine ⟨34559180752146136819429529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92157815339056364851812077 34559180752146136819429529)
    ·
      refine ⟨25919385564109602614572147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34559180752146136819429529 25919385564109602614572147)
      ·
        refine ⟨38879078346164403921858221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25919385564109602614572147 38879078346164403921858221)
        ·
          refine ⟨14579654379811651470696833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38879078346164403921858221 14579654379811651470696833)
          ·
            refine ⟨10934740784858738603022625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14579654379811651470696833 10934740784858738603022625)
            ·
              refine ⟨8201055588644053952266969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10934740784858738603022625 8201055588644053952266969)
              ·
                refine ⟨6150791691483040464200227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8201055588644053952266969 6150791691483040464200227)
                ·
                  refine ⟨9226187537224560696300341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6150791691483040464200227 9226187537224560696300341)
                  ·
                    refine ⟨864955081614802565278157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9226187537224560696300341 864955081614802565278157)
                    ·
                      rfl

theorem cell22_2526741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_2526741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2526741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2526741 prefixEnd_2526741 := by exact prefixLift 2526741
  have htrace : WordTrace (prefixWord ++ tailWord_2526741) baseStart_2526741 baseEnd_2526741 := by
    simpa [prefixWord, tailWord_2526741, baseEnd_2526741] using wordTrace_append hprefix tailTrace_2526741
  have hstable : (prefixWord ++ tailWord_2526741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526741).length < 2 ^ (prefixWord ++ tailWord_2526741).sum := by decide
  have hdescent : baseEnd_2526741 < baseStart_2526741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526775 : List Nat := [1, 1, 3, 1, 2, 5, 3, 1, 2, 3]
def baseStart_2526775 : Nat := 118140960795 + 2526775 * 2 ^ 59
def prefixEnd_2526775 : Nat := 4983230072969 + 3 ^ 40 * 2526775 * 2
def baseEnd_2526775 : Nat := 864966720509637809928053

theorem tailTrace_2526775 : CollatzResearch.WordTrace tailWord_2526775 prefixEnd_2526775 864966720509637809928053 := by
  unfold tailWord_2526775
  simp only [CollatzResearch.WordTrace]
  refine ⟨92159055420933188658549779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61439370280622125772366519 92159055420933188658549779)
  ·
    refine ⟨138238583131399782987824669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92159055420933188658549779 138238583131399782987824669)
    ·
      refine ⟨51839468674274918620434251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138238583131399782987824669 51839468674274918620434251)
      ·
        refine ⟨77759203011412377930651377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51839468674274918620434251 77759203011412377930651377)
        ·
          refine ⟨58319402258559283447988533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77759203011412377930651377 58319402258559283447988533)
          ·
            refine ⟨5467443961739932823248925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58319402258559283447988533 5467443961739932823248925)
            ·
              refine ⟨2050291485652474808718347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5467443961739932823248925 2050291485652474808718347)
              ·
                refine ⟨3075437228478712213077521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2050291485652474808718347 3075437228478712213077521)
                ·
                  refine ⟨2306577921359034159808141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3075437228478712213077521 2306577921359034159808141)
                  ·
                    refine ⟨864966720509637809928053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2306577921359034159808141 864966720509637809928053)
                    ·
                      rfl

theorem cell22_2526775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 2, 3].length) (baseStart_2526775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2526775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2526775 prefixEnd_2526775 := by exact prefixLift 2526775
  have htrace : WordTrace (prefixWord ++ tailWord_2526775) baseStart_2526775 baseEnd_2526775 := by
    simpa [prefixWord, tailWord_2526775, baseEnd_2526775] using wordTrace_append hprefix tailTrace_2526775
  have hstable : (prefixWord ++ tailWord_2526775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526775).length < 2 ^ (prefixWord ++ tailWord_2526775).sum := by decide
  have hdescent : baseEnd_2526775 < baseStart_2526775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526816 : List Nat := [2, 1, 1, 3, 2, 1, 1, 6, 5]
def baseStart_2526816 : Nat := 118140960795 + 2526816 * 2 ^ 59
def prefixEnd_2526816 : Nat := 4983230072969 + 3 ^ 40 * 2526816 * 2
def baseEnd_2526816 : Nat := 288326918549175789884309

theorem tailTrace_2526816 : CollatzResearch.WordTrace tailWord_2526816 prefixEnd_2526816 288326918549175789884309 := by
  unfold tailWord_2526816
  simp only [CollatzResearch.WordTrace]
  refine ⟨46080275406892326330396151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61440367209189768440528201 46080275406892326330396151)
  ·
    refine ⟨69120413110338489495594227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46080275406892326330396151 69120413110338489495594227)
    ·
      refine ⟨103680619665507734243391341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69120413110338489495594227 103680619665507734243391341)
      ·
        refine ⟨38880232374565400341271753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103680619665507734243391341 38880232374565400341271753)
        ·
          refine ⟨29160174280924050255953815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38880232374565400341271753 29160174280924050255953815)
          ·
            refine ⟨43740261421386075383930723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29160174280924050255953815 43740261421386075383930723)
            ·
              refine ⟨65610392132079113075896085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43740261421386075383930723 65610392132079113075896085)
              ·
                refine ⟨3075487131191208425432629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65610392132079113075896085 3075487131191208425432629)
                ·
                  refine ⟨288326918549175789884309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3075487131191208425432629 288326918549175789884309)
                  ·
                    rfl

theorem cell22_2526816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 5].length) (baseStart_2526816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2526816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2526816 prefixEnd_2526816 := by exact prefixLift 2526816
  have htrace : WordTrace (prefixWord ++ tailWord_2526816) baseStart_2526816 baseEnd_2526816 := by
    simpa [prefixWord, tailWord_2526816, baseEnd_2526816] using wordTrace_append hprefix tailTrace_2526816
  have hstable : (prefixWord ++ tailWord_2526816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526816).length < 2 ^ (prefixWord ++ tailWord_2526816).sum := by decide
  have hdescent : baseEnd_2526816 < baseStart_2526816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526820 : List Nat := [2, 3, 1, 1, 2, 5, 1, 1, 3, 3]
def baseStart_2526820 : Nat := 118140960795 + 2526820 * 2 ^ 59
def prefixEnd_2526820 : Nat := 4983230072969 + 3 ^ 40 * 2526820 * 2
def baseEnd_2526820 : Nat := 864982124929272692552915

theorem tailTrace_2526820 : CollatzResearch.WordTrace tailWord_2526820 prefixEnd_2526820 864982124929272692552915 := by
  unfold tailWord_2526820
  simp only [CollatzResearch.WordTrace]
  refine ⟨46080348352885080671968957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61440464470513440895958609 46080348352885080671968957)
  ·
    refine ⟨17280130632331905251988359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46080348352885080671968957 17280130632331905251988359)
    ·
      refine ⟨25920195948497857877982539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17280130632331905251988359 25920195948497857877982539)
      ·
        refine ⟨38880293922746786816973809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25920195948497857877982539 38880293922746786816973809)
        ·
          refine ⟨29160220442060090112730357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38880293922746786816973809 29160220442060090112730357)
          ·
            refine ⟨2733770666443133448068471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29160220442060090112730357 2733770666443133448068471)
            ·
              refine ⟨4100655999664700172102707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2733770666443133448068471 4100655999664700172102707)
              ·
                refine ⟨6150983999497050258154061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4100655999664700172102707 6150983999497050258154061)
                ·
                  refine ⟨2306618999811393846807773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6150983999497050258154061 2306618999811393846807773)
                  ·
                    refine ⟨864982124929272692552915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2306618999811393846807773 864982124929272692552915)
                    ·
                      rfl

theorem cell22_2526820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_2526820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2526820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2526820 prefixEnd_2526820 := by exact prefixLift 2526820
  have htrace : WordTrace (prefixWord ++ tailWord_2526820) baseStart_2526820 baseEnd_2526820 := by
    simpa [prefixWord, tailWord_2526820, baseEnd_2526820] using wordTrace_append hprefix tailTrace_2526820
  have hstable : (prefixWord ++ tailWord_2526820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526820).length < 2 ^ (prefixWord ++ tailWord_2526820).sum := by decide
  have hdescent : baseEnd_2526820 < baseStart_2526820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2526908 : List Nat := [2, 2, 2, 3, 1, 3, 1, 1, 1, 6]
def baseStart_2526908 : Nat := 118140960795 + 2526908 * 2 ^ 59
def prefixEnd_2526908 : Nat := 4983230072969 + 3 ^ 40 * 2526908 * 2
def baseEnd_2526908 : Nat := 865012249127669796352645

theorem tailTrace_2526908 : CollatzResearch.WordTrace tailWord_2526908 prefixEnd_2526908 865012249127669796352645 := by
  unfold tailWord_2526908
  simp only [CollatzResearch.WordTrace]
  refine ⟨46081953164725676186570689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61442604219634234915427585 46081953164725676186570689)
  ·
    refine ⟨34561464873544257139928017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46081953164725676186570689 34561464873544257139928017)
    ·
      refine ⟨25921098655158192854946013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34561464873544257139928017 25921098655158192854946013)
      ·
        refine ⟨9720411995684322320604755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25921098655158192854946013 9720411995684322320604755)
        ·
          refine ⟨14580617993526483480907133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9720411995684322320604755 14580617993526483480907133)
          ·
            refine ⟨5467731747572431305340175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14580617993526483480907133 5467731747572431305340175)
            ·
              refine ⟨8201597621358646958010263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5467731747572431305340175 8201597621358646958010263)
              ·
                refine ⟨12302396432037970437015395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8201597621358646958010263 12302396432037970437015395)
                ·
                  refine ⟨18453594648056955655523093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12302396432037970437015395 18453594648056955655523093)
                  ·
                    refine ⟨865012249127669796352645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18453594648056955655523093 865012249127669796352645)
                    ·
                      rfl

theorem cell22_2526908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_2526908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2526908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2526908 prefixEnd_2526908 := by exact prefixLift 2526908
  have htrace : WordTrace (prefixWord ++ tailWord_2526908) baseStart_2526908 baseEnd_2526908 := by
    simpa [prefixWord, tailWord_2526908, baseEnd_2526908] using wordTrace_append hprefix tailTrace_2526908
  have hstable : (prefixWord ++ tailWord_2526908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2526908).length < 2 ^ (prefixWord ++ tailWord_2526908).sum := by decide
  have hdescent : baseEnd_2526908 < baseStart_2526908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2526908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527002 : List Nat := [3, 1, 1, 3, 2, 4, 2, 1, 5]
def baseStart_2527002 : Nat := 118140960795 + 2527002 * 2 ^ 59
def prefixEnd_2527002 : Nat := 4983230072969 + 3 ^ 40 * 2527002 * 2
def baseEnd_2527002 : Nat := 288348142416228294834119

theorem tailTrace_2527002 : CollatzResearch.WordTrace tailWord_2527002 prefixEnd_2527002 288348142416228294834119 := by
  unfold tailWord_2527002
  simp only [CollatzResearch.WordTrace]
  refine ⟨23041833697777701606765815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61444889860740537618042173 23041833697777701606765815)
  ·
    refine ⟨34562750546666552410148723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23041833697777701606765815 34562750546666552410148723)
    ·
      refine ⟨51844125819999828615223085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34562750546666552410148723 51844125819999828615223085)
      ·
        refine ⟨19441547182499935730708657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51844125819999828615223085 19441547182499935730708657)
        ·
          refine ⟨14581160386874951798031493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19441547182499935730708657 14581160386874951798031493)
          ·
            refine ⟨2733967572539053462130905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14581160386874951798031493 2733967572539053462130905)
            ·
              refine ⟨2050475679404290096598179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2733967572539053462130905 2050475679404290096598179)
              ·
                refine ⟨3075713519106435144897269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2050475679404290096598179 3075713519106435144897269)
                ·
                  refine ⟨288348142416228294834119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3075713519106435144897269 288348142416228294834119)
                  ·
                    rfl

theorem cell22_2527002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 1, 5].length) (baseStart_2527002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2527002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2527002 prefixEnd_2527002 := by exact prefixLift 2527002
  have htrace : WordTrace (prefixWord ++ tailWord_2527002) baseStart_2527002 baseEnd_2527002 := by
    simpa [prefixWord, tailWord_2527002, baseEnd_2527002] using wordTrace_append hprefix tailTrace_2527002
  have hstable : (prefixWord ++ tailWord_2527002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527002).length < 2 ^ (prefixWord ++ tailWord_2527002).sum := by decide
  have hdescent : baseEnd_2527002 < baseStart_2527002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527032 : List Nat := [2, 1, 2, 1, 3, 4, 3, 1, 1, 4]
def baseStart_2527032 : Nat := 118140960795 + 2527032 * 2 ^ 59
def prefixEnd_2527032 : Nat := 4983230072969 + 3 ^ 40 * 2527032 * 2
def baseEnd_2527032 : Nat := 865054696861774806252265

theorem tailTrace_2527032 : CollatzResearch.WordTrace tailWord_2527032 prefixEnd_2527032 865054696861774806252265 := by
  unfold tailWord_2527032
  simp only [CollatzResearch.WordTrace]
  refine ⟨46084214490501060775327675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61445619320668081033770233 46084214490501060775327675)
  ·
    refine ⟨69126321735751591162991513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46084214490501060775327675 69126321735751591162991513)
    ·
      refine ⟨51844741301813693372243635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69126321735751591162991513 51844741301813693372243635)
      ·
        refine ⟨77767111952720540058365453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51844741301813693372243635 77767111952720540058365453)
        ·
          refine ⟨29162666982270202521887045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77767111952720540058365453 29162666982270202521887045)
          ·
            refine ⟨5468000059175662972853821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29162666982270202521887045 5468000059175662972853821)
            ·
              refine ⟨2050500022190873614820183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5468000059175662972853821 2050500022190873614820183)
              ·
                refine ⟨3075750033286310422230275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2050500022190873614820183 3075750033286310422230275)
                ·
                  refine ⟨4613625049929465633345413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3075750033286310422230275 4613625049929465633345413)
                  ·
                    refine ⟨865054696861774806252265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4613625049929465633345413 865054696861774806252265)
                    ·
                      rfl

theorem cell22_2527032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 1, 4].length) (baseStart_2527032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2527032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2527032 prefixEnd_2527032 := by exact prefixLift 2527032
  have htrace : WordTrace (prefixWord ++ tailWord_2527032) baseStart_2527032 baseEnd_2527032 := by
    simpa [prefixWord, tailWord_2527032, baseEnd_2527032] using wordTrace_append hprefix tailTrace_2527032
  have hstable : (prefixWord ++ tailWord_2527032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527032).length < 2 ^ (prefixWord ++ tailWord_2527032).sum := by decide
  have hdescent : baseEnd_2527032 < baseStart_2527032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527047 : List Nat := [1, 1, 4, 1, 2, 1, 6, 2, 4]
def baseStart_2527047 : Nat := 118140960795 + 2527047 * 2 ^ 59
def prefixEnd_2527047 : Nat := 4983230072969 + 3 ^ 40 * 2527047 * 2
def baseEnd_2527047 : Nat := 288353277222773255709073

theorem tailTrace_2527047 : CollatzResearch.WordTrace tailWord_2527047 prefixEnd_2527047 288353277222773255709073 := by
  unfold tailWord_2527047
  simp only [CollatzResearch.WordTrace]
  refine ⟨92168976075947779112451395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61445984050631852741634263 92168976075947779112451395)
  ·
    refine ⟨138253464113921668668677093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92168976075947779112451395 138253464113921668668677093)
    ·
      refine ⟨25922524521360312875376955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138253464113921668668677093 25922524521360312875376955)
      ·
        refine ⟨38883786782040469313065433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25922524521360312875376955 38883786782040469313065433)
        ·
          refine ⟨29162840086530351984799075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38883786782040469313065433 29162840086530351984799075)
          ·
            refine ⟨43744260129795527977198613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29162840086530351984799075 43744260129795527977198613)
            ·
              refine ⟨2050512193584165373931185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43744260129795527977198613 2050512193584165373931185)
              ·
                refine ⟨1537884145188124030448389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2050512193584165373931185 1537884145188124030448389)
                ·
                  refine ⟨288353277222773255709073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1537884145188124030448389 288353277222773255709073)
                  ·
                    rfl

theorem cell22_2527047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 2, 4].length) (baseStart_2527047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2527047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2527047 prefixEnd_2527047 := by exact prefixLift 2527047
  have htrace : WordTrace (prefixWord ++ tailWord_2527047) baseStart_2527047 baseEnd_2527047 := by
    simpa [prefixWord, tailWord_2527047, baseEnd_2527047] using wordTrace_append hprefix tailTrace_2527047
  have hstable : (prefixWord ++ tailWord_2527047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527047).length < 2 ^ (prefixWord ++ tailWord_2527047).sum := by decide
  have hdescent : baseEnd_2527047 < baseStart_2527047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527090 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 7, 3]
def baseStart_2527090 : Nat := 118140960795 + 2527090 * 2 ^ 59
def prefixEnd_2527090 : Nat := 4983230072969 + 3 ^ 40 * 2527090 * 2
def baseEnd_2527090 : Nat := 865074551447081988302087

theorem tailTrace_2527090 : CollatzResearch.WordTrace tailWord_2527090 prefixEnd_2527090 865074551447081988302087 := by
  unfold tailWord_2527090
  simp only [CollatzResearch.WordTrace]
  refine ⟨23042636103697999364066681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61447029609861331637511149 23042636103697999364066681)
  ·
    refine ⟨17281977077773499523050011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23042636103697999364066681 17281977077773499523050011)
    ·
      refine ⟨25922965616660249284575017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17281977077773499523050011 25922965616660249284575017)
      ·
        refine ⟨19442224212495186963431263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25922965616660249284575017 19442224212495186963431263)
        ·
          refine ⟨29163336318742780445146895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19442224212495186963431263 29163336318742780445146895)
          ·
            refine ⟨43745004478114170667720343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29163336318742780445146895 43745004478114170667720343)
            ·
              refine ⟨65617506717171256001580515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43745004478114170667720343 65617506717171256001580515)
              ·
                refine ⟨98426260075756884002370773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65617506717171256001580515 98426260075756884002370773)
                ·
                  refine ⟨2306865470525551968805565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 98426260075756884002370773 2306865470525551968805565)
                  ·
                    refine ⟨865074551447081988302087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2306865470525551968805565 865074551447081988302087)
                    ·
                      rfl

theorem cell22_2527090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_2527090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2527090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2527090 prefixEnd_2527090 := by exact prefixLift 2527090
  have htrace : WordTrace (prefixWord ++ tailWord_2527090) baseStart_2527090 baseEnd_2527090 := by
    simpa [prefixWord, tailWord_2527090, baseEnd_2527090] using wordTrace_append hprefix tailTrace_2527090
  have hstable : (prefixWord ++ tailWord_2527090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527090).length < 2 ^ (prefixWord ++ tailWord_2527090).sum := by decide
  have hdescent : baseEnd_2527090 < baseStart_2527090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527107 : List Nat := [1, 1, 1, 3, 4, 3, 2, 1, 3, 3]
def baseStart_2527107 : Nat := 118140960795 + 2527107 * 2 ^ 59
def prefixEnd_2527107 : Nat := 4983230072969 + 3 ^ 40 * 2527107 * 2
def baseEnd_2527107 : Nat := 865080370894499610627035

theorem tailTrace_2527107 : CollatzResearch.WordTrace tailWord_2527107 prefixEnd_2527107 865080370894499610627035 := by
  unfold tailWord_2527107
  simp only [CollatzResearch.WordTrace]
  refine ⟨92171164455730409359635575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61447442970486939573090383 92171164455730409359635575)
  ·
    refine ⟨138256746683595614039453363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92171164455730409359635575 138256746683595614039453363)
    ·
      refine ⟨207385120025393421059180045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138256746683595614039453363 207385120025393421059180045)
      ·
        refine ⟨77769420009522532897192517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207385120025393421059180045 77769420009522532897192517)
        ·
          refine ⟨14581766251785474918223597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77769420009522532897192517 14581766251785474918223597)
          ·
            refine ⟨5468162344419553094333849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14581766251785474918223597 5468162344419553094333849)
            ·
              refine ⟨4101121758314664820750387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5468162344419553094333849 4101121758314664820750387)
              ·
                refine ⟨6151682637471997231125581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4101121758314664820750387 6151682637471997231125581)
                ·
                  refine ⟨2306880989051998961672093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6151682637471997231125581 2306880989051998961672093)
                  ·
                    refine ⟨865080370894499610627035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2306880989051998961672093 865080370894499610627035)
                    ·
                      rfl

theorem cell22_2527107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 3, 3].length) (baseStart_2527107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2527107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2527107 prefixEnd_2527107 := by exact prefixLift 2527107
  have htrace : WordTrace (prefixWord ++ tailWord_2527107) baseStart_2527107 baseEnd_2527107 := by
    simpa [prefixWord, tailWord_2527107, baseEnd_2527107] using wordTrace_append hprefix tailTrace_2527107
  have hstable : (prefixWord ++ tailWord_2527107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527107).length < 2 ^ (prefixWord ++ tailWord_2527107).sum := by decide
  have hdescent : baseEnd_2527107 < baseStart_2527107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527214 : List Nat := [4, 1, 2, 1, 3, 1, 1, 4, 2, 3]
def baseStart_2527214 : Nat := 118140960795 + 2527214 * 2 ^ 59
def prefixEnd_2527214 : Nat := 4983230072969 + 3 ^ 40 * 2527214 * 2
def baseEnd_2527214 : Nat := 865116999181186998201707

theorem tailTrace_2527214 : CollatzResearch.WordTrace tailWord_2527214 prefixEnd_2527214 865116999181186998201707 := by
  unfold tailWord_2527214
  simp only [CollatzResearch.WordTrace]
  refine ⟨11521883383292845829222587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61450044710895177755853797 11521883383292845829222587)
  ·
    refine ⟨17282825074939268743833881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11521883383292845829222587 17282825074939268743833881)
    ·
      refine ⟨12962118806204451557875411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17282825074939268743833881 12962118806204451557875411)
      ·
        refine ⟨19443178209306677336813117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12962118806204451557875411 19443178209306677336813117)
        ·
          refine ⟨7291191828490004001304919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19443178209306677336813117 7291191828490004001304919)
          ·
            refine ⟨10936787742735006001957379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7291191828490004001304919 10936787742735006001957379)
            ·
              refine ⟨16405181614102509002936069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10936787742735006001957379 16405181614102509002936069)
              ·
                refine ⟨3075971552644220438050513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16405181614102509002936069 3075971552644220438050513)
                ·
                  refine ⟨2306978664483165328537885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3075971552644220438050513 2306978664483165328537885)
                  ·
                    refine ⟨865116999181186998201707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2306978664483165328537885 865116999181186998201707)
                    ·
                      rfl

theorem cell22_2527214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_2527214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2527214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2527214 prefixEnd_2527214 := by exact prefixLift 2527214
  have htrace : WordTrace (prefixWord ++ tailWord_2527214) baseStart_2527214 baseEnd_2527214 := by
    simpa [prefixWord, tailWord_2527214, baseEnd_2527214] using wordTrace_append hprefix tailTrace_2527214
  have hstable : (prefixWord ++ tailWord_2527214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527214).length < 2 ^ (prefixWord ++ tailWord_2527214).sum := by decide
  have hdescent : baseEnd_2527214 < baseStart_2527214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527240 : List Nat := [2, 1, 3, 2, 1, 2, 1, 2, 2, 6]
def baseStart_2527240 : Nat := 118140960795 + 2527240 * 2 ^ 59
def prefixEnd_2527240 : Nat := 4983230072969 + 3 ^ 40 * 2527240 * 2
def baseEnd_2527240 : Nat := 865125899512531597051627

theorem tailTrace_2527240 : CollatzResearch.WordTrace tailWord_2527240 prefixEnd_2527240 865125899512531597051627 := by
  unfold tailWord_2527240
  simp only [CollatzResearch.WordTrace]
  refine ⟨46088007682124286537113587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61450676909499048716151449 46088007682124286537113587)
  ·
    refine ⟨69132011523186429805670381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46088007682124286537113587 69132011523186429805670381)
    ·
      refine ⟨25924504321194911177126393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69132011523186429805670381 25924504321194911177126393)
      ·
        refine ⟨19443378240896183382844795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25924504321194911177126393 19443378240896183382844795)
        ·
          refine ⟨29165067361344275074267193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19443378240896183382844795 29165067361344275074267193)
          ·
            refine ⟨21873800521008206305700395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29165067361344275074267193 21873800521008206305700395)
            ·
              refine ⟨32810700781512309458550593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21873800521008206305700395 32810700781512309458550593)
              ·
                refine ⟨24608025586134232093912945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32810700781512309458550593 24608025586134232093912945)
                ·
                  refine ⟨18456019189600674070434709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24608025586134232093912945 18456019189600674070434709)
                  ·
                    refine ⟨865125899512531597051627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18456019189600674070434709 865125899512531597051627)
                    ·
                      rfl

theorem cell22_2527240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_2527240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2527240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2527240 prefixEnd_2527240 := by exact prefixLift 2527240
  have htrace : WordTrace (prefixWord ++ tailWord_2527240) baseStart_2527240 baseEnd_2527240 := by
    simpa [prefixWord, tailWord_2527240, baseEnd_2527240] using wordTrace_append hprefix tailTrace_2527240
  have hstable : (prefixWord ++ tailWord_2527240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527240).length < 2 ^ (prefixWord ++ tailWord_2527240).sum := by decide
  have hdescent : baseEnd_2527240 < baseStart_2527240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527364 : List Nat := [2, 3, 2, 1, 2, 1, 4, 1, 2, 4]
def baseStart_2527364 : Nat := 118140960795 + 2527364 * 2 ^ 59
def prefixEnd_2527364 : Nat := 4983230072969 + 3 ^ 40 * 2527364 * 2
def baseEnd_2527364 : Nat := 865168347246636606951247

theorem tailTrace_2527364 : CollatzResearch.WordTrace tailWord_2527364 prefixEnd_2527364 865168347246636606951247 := by
  unfold tailWord_2527364
  simp only [CollatzResearch.WordTrace]
  refine ⟨46090269007899671125870573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61453692010532894834494097 46090269007899671125870573)
  ·
    refine ⟨17283850877962376672201465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46090269007899671125870573 17283850877962376672201465)
    ·
      refine ⟨12962888158471782504151099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17283850877962376672201465 12962888158471782504151099)
      ·
        refine ⟨19444332237707673756226649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12962888158471782504151099 19444332237707673756226649)
        ·
          refine ⟨14583249178280755317169987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19444332237707673756226649 14583249178280755317169987)
          ·
            refine ⟨21874873767421132975754981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14583249178280755317169987 21874873767421132975754981)
            ·
              refine ⟨4101538831391462432954059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21874873767421132975754981 4101538831391462432954059)
              ·
                refine ⟨6152308247087193649431089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4101538831391462432954059 6152308247087193649431089)
                ·
                  refine ⟨4614231185315395237073317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6152308247087193649431089 4614231185315395237073317)
                  ·
                    refine ⟨865168347246636606951247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4614231185315395237073317 865168347246636606951247)
                    ·
                      rfl

theorem cell22_2527364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_2527364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2527364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2527364 prefixEnd_2527364 := by exact prefixLift 2527364
  have htrace : WordTrace (prefixWord ++ tailWord_2527364) baseStart_2527364 baseEnd_2527364 := by
    simpa [prefixWord, tailWord_2527364, baseEnd_2527364] using wordTrace_append hprefix tailTrace_2527364
  have hstable : (prefixWord ++ tailWord_2527364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527364).length < 2 ^ (prefixWord ++ tailWord_2527364).sum := by decide
  have hdescent : baseEnd_2527364 < baseStart_2527364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527392 : List Nat := [2, 1, 1, 4, 2, 2, 1, 1, 2, 6]
def baseStart_2527392 : Nat := 118140960795 + 2527392 * 2 ^ 59
def prefixEnd_2527392 : Nat := 4983230072969 + 3 ^ 40 * 2527392 * 2
def baseEnd_2527392 : Nat := 865177932218853867251161

theorem tailTrace_2527392 : CollatzResearch.WordTrace tailWord_2527392 prefixEnd_2527392 865177932218853867251161 := by
  unfold tailWord_2527392
  simp only [CollatzResearch.WordTrace]
  refine ⟨46090779629848951516880215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61454372839798602022506953 46090779629848951516880215)
  ·
    refine ⟨69136169444773427275320323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46090779629848951516880215 69136169444773427275320323)
    ·
      refine ⟨103704254167160140912980485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69136169444773427275320323 103704254167160140912980485)
      ·
        refine ⟨19444547656342526421183841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103704254167160140912980485 19444547656342526421183841)
        ·
          refine ⟨14583410742256894815887881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19444547656342526421183841 14583410742256894815887881)
          ·
            refine ⟨10937558056692671111915911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14583410742256894815887881 10937558056692671111915911)
            ·
              refine ⟨16406337085039006667873867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10937558056692671111915911 16406337085039006667873867)
              ·
                refine ⟨24609505627558510001810801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16406337085039006667873867 24609505627558510001810801)
                ·
                  refine ⟨18457129220668882501358101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24609505627558510001810801 18457129220668882501358101)
                  ·
                    refine ⟨865177932218853867251161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18457129220668882501358101 865177932218853867251161)
                    ·
                      rfl

theorem cell22_2527392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 2, 6].length) (baseStart_2527392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2527392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2527392 prefixEnd_2527392 := by exact prefixLift 2527392
  have htrace : WordTrace (prefixWord ++ tailWord_2527392) baseStart_2527392 baseEnd_2527392 := by
    simpa [prefixWord, tailWord_2527392, baseEnd_2527392] using wordTrace_append hprefix tailTrace_2527392
  have hstable : (prefixWord ++ tailWord_2527392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527392).length < 2 ^ (prefixWord ++ tailWord_2527392).sum := by decide
  have hdescent : baseEnd_2527392 < baseStart_2527392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527396 : List Nat := [2, 3, 1, 2, 5, 1, 1, 7]
def baseStart_2527396 : Nat := 118140960795 + 2527396 * 2 ^ 59
def prefixEnd_2527396 : Nat := 4983230072969 + 3 ^ 40 * 2527396 * 2
def baseEnd_2527396 : Nat := 96131033500066576683461

theorem tailTrace_2527396 : CollatzResearch.WordTrace tailWord_2527396 prefixEnd_2527396 96131033500066576683461 := by
  unfold tailWord_2527396
  simp only [CollatzResearch.WordTrace]
  refine ⟨46090852575841705858453021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61454470101122274477937361 46090852575841705858453021)
  ·
    refine ⟨17284069715940639696919883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46090852575841705858453021 17284069715940639696919883)
    ·
      refine ⟨25926104573910959545379825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17284069715940639696919883 25926104573910959545379825)
      ·
        refine ⟨19444578430433219659034869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25926104573910959545379825 19444578430433219659034869)
        ·
          refine ⟨1822929227853114343034519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19444578430433219659034869 1822929227853114343034519)
          ·
            refine ⟨2734393841779671514551779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1822929227853114343034519 2734393841779671514551779)
            ·
              refine ⟨4101590762669507271827669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2734393841779671514551779 4101590762669507271827669)
              ·
                refine ⟨96131033500066576683461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4101590762669507271827669 96131033500066576683461)
                ·
                  rfl

theorem cell22_2527396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 7].length) (baseStart_2527396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2527396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2527396 prefixEnd_2527396 := by exact prefixLift 2527396
  have htrace : WordTrace (prefixWord ++ tailWord_2527396) baseStart_2527396 baseEnd_2527396 := by
    simpa [prefixWord, tailWord_2527396, baseEnd_2527396] using wordTrace_append hprefix tailTrace_2527396
  have hstable : (prefixWord ++ tailWord_2527396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527396).length < 2 ^ (prefixWord ++ tailWord_2527396).sum := by decide
  have hdescent : baseEnd_2527396 < baseStart_2527396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527428 : List Nat := [2, 3, 3, 1, 2, 1, 1, 5, 1, 3]
def baseStart_2527428 : Nat := 118140960795 + 2527428 * 2 ^ 59
def prefixEnd_2527428 : Nat := 4983230072969 + 3 ^ 40 * 2527428 * 2
def baseEnd_2527428 : Nat := 865190255754561773351051

theorem tailTrace_2527428 : CollatzResearch.WordTrace tailWord_2527428 prefixEnd_2527428 865190255754561773351051 := by
  unfold tailWord_2527428
  simp only [CollatzResearch.WordTrace]
  refine ⟨46091436143783740591035469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61455248191711654121380625 46091436143783740591035469)
  ·
    refine ⟨17284288553918902721638301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46091436143783740591035469 17284288553918902721638301)
    ·
      refine ⟨6481608207719588520614363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17284288553918902721638301 6481608207719588520614363)
      ·
        refine ⟨9722412311579382780921545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6481608207719588520614363 9722412311579382780921545)
        ·
          refine ⟨7291809233684537085691159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9722412311579382780921545 7291809233684537085691159)
          ·
            refine ⟨10937713850526805628536739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7291809233684537085691159 10937713850526805628536739)
            ·
              refine ⟨16406570775790208442805109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10937713850526805628536739 16406570775790208442805109)
              ·
                refine ⟨1538116010230332041512979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16406570775790208442805109 1538116010230332041512979)
                ·
                  refine ⟨2307174015345498062269469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1538116010230332041512979 2307174015345498062269469)
                  ·
                    refine ⟨865190255754561773351051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2307174015345498062269469 865190255754561773351051)
                    ·
                      rfl

theorem cell22_2527428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_2527428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2527428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2527428 prefixEnd_2527428 := by exact prefixLift 2527428
  have htrace : WordTrace (prefixWord ++ tailWord_2527428) baseStart_2527428 baseEnd_2527428 := by
    simpa [prefixWord, tailWord_2527428, baseEnd_2527428] using wordTrace_append hprefix tailTrace_2527428
  have hstable : (prefixWord ++ tailWord_2527428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527428).length < 2 ^ (prefixWord ++ tailWord_2527428).sum := by decide
  have hdescent : baseEnd_2527428 < baseStart_2527428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527471 : List Nat := [1, 1, 2, 1, 6, 2, 2, 2, 1, 4]
def baseStart_2527471 : Nat := 118140960795 + 2527471 * 2 ^ 59
def prefixEnd_2527471 : Nat := 4983230072969 + 3 ^ 40 * 2527471 * 2
def baseEnd_2527471 : Nat := 865204975533323994525919

theorem tailTrace_2527471 : CollatzResearch.WordTrace tailWord_2527471 prefixEnd_2527471 865204975533323994525919 := by
  unfold tailWord_2527471
  simp only [CollatzResearch.WordTrace]
  refine ⟨92184440626411699525886267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61456293750941133017257511 92184440626411699525886267)
  ·
    refine ⟨138276660939617549288829401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92184440626411699525886267 138276660939617549288829401)
    ·
      refine ⟨103707495704713161966622051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138276660939617549288829401 103707495704713161966622051)
      ·
        refine ⟨155561243557069742949933077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103707495704713161966622051 155561243557069742949933077)
        ·
          refine ⟨7291933291737644200778113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 155561243557069742949933077 7291933291737644200778113)
          ·
            refine ⟨5468949968803233150583585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7291933291737644200778113 5468949968803233150583585)
            ·
              refine ⟨4101712476602424862937689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5468949968803233150583585 4101712476602424862937689)
              ·
                refine ⟨3076284357451818647203267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4101712476602424862937689 3076284357451818647203267)
                ·
                  refine ⟨4614426536177727970804901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3076284357451818647203267 4614426536177727970804901)
                  ·
                    refine ⟨865204975533323994525919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4614426536177727970804901 865204975533323994525919)
                    ·
                      rfl

theorem cell22_2527471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 4].length) (baseStart_2527471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2527471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2527471 prefixEnd_2527471 := by exact prefixLift 2527471
  have htrace : WordTrace (prefixWord ++ tailWord_2527471) baseStart_2527471 baseEnd_2527471 := by
    simpa [prefixWord, tailWord_2527471, baseEnd_2527471] using wordTrace_append hprefix tailTrace_2527471
  have hstable : (prefixWord ++ tailWord_2527471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527471).length < 2 ^ (prefixWord ++ tailWord_2527471).sum := by decide
  have hdescent : baseEnd_2527471 < baseStart_2527471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527497 : List Nat := [1, 2, 1, 1, 3, 4, 10]
def baseStart_2527497 : Nat := 118140960795 + 2527497 * 2 ^ 59
def prefixEnd_2527497 : Nat := 4983230072969 + 3 ^ 40 * 2527497 * 2
def baseEnd_2527497 : Nat := 32044958365358096050957

theorem tailTrace_2527497 : CollatzResearch.WordTrace tailWord_2527497 prefixEnd_2527497 32044958365358096050957 := by
  unfold tailWord_2527497
  simp only [CollatzResearch.WordTrace]
  refine ⟨92185388924317505966332745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61456925949545003977555163 92185388924317505966332745)
  ·
    refine ⟨69139041693238129474749559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92185388924317505966332745 69139041693238129474749559)
    ·
      refine ⟨103708562539857194212124339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69139041693238129474749559 103708562539857194212124339)
      ·
        refine ⟨155562843809785791318186509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103708562539857194212124339 155562843809785791318186509)
        ·
          refine ⟨58336066428669671744319941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155562843809785791318186509 58336066428669671744319941)
          ·
            refine ⟨10938012455375563452059989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58336066428669671744319941 10938012455375563452059989)
            ·
              refine ⟨32044958365358096050957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10938012455375563452059989 32044958365358096050957)
              ·
                rfl

theorem cell22_2527497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 10].length) (baseStart_2527497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2527497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2527497 prefixEnd_2527497 := by exact prefixLift 2527497
  have htrace : WordTrace (prefixWord ++ tailWord_2527497) baseStart_2527497 baseEnd_2527497 := by
    simpa [prefixWord, tailWord_2527497, baseEnd_2527497] using wordTrace_append hprefix tailTrace_2527497
  have hstable : (prefixWord ++ tailWord_2527497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527497).length < 2 ^ (prefixWord ++ tailWord_2527497).sum := by decide
  have hdescent : baseEnd_2527497 < baseStart_2527497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527499 : List Nat := [1, 1, 1, 1, 5, 2, 3, 2, 2, 4]
def baseStart_2527499 : Nat := 118140960795 + 2527499 * 2 ^ 59
def prefixEnd_2527499 : Nat := 4983230072969 + 3 ^ 40 * 2527499 * 2
def baseEnd_2527499 : Nat := 865214560505541254825833

theorem tailTrace_2527499 : CollatzResearch.WordTrace tailWord_2527499 prefixEnd_2527499 865214560505541254825833 := by
  unfold tailWord_2527499
  simp only [CollatzResearch.WordTrace]
  refine ⟨92185461870310260307905551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61456974580206840205270367 92185461870310260307905551)
  ·
    refine ⟨138278192805465390461858327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92185461870310260307905551 138278192805465390461858327)
    ·
      refine ⟨207417289208198085692787491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138278192805465390461858327 207417289208198085692787491)
      ·
        refine ⟨311125933812297128539181237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207417289208198085692787491 311125933812297128539181237)
        ·
          refine ⟨29168056294902855800548241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 311125933812297128539181237 29168056294902855800548241)
          ·
            refine ⟨21876042221177141850411181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29168056294902855800548241 21876042221177141850411181)
            ·
              refine ⟨8203515832941428193904193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21876042221177141850411181 8203515832941428193904193)
              ·
                refine ⟨6152636874706071145428145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8203515832941428193904193 6152636874706071145428145)
                ·
                  refine ⟨4614477656029553359071109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6152636874706071145428145 4614477656029553359071109)
                  ·
                    refine ⟨865214560505541254825833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4614477656029553359071109 865214560505541254825833)
                    ·
                      rfl

theorem cell22_2527499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 4].length) (baseStart_2527499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2527499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2527499 prefixEnd_2527499 := by exact prefixLift 2527499
  have htrace : WordTrace (prefixWord ++ tailWord_2527499) baseStart_2527499 baseEnd_2527499 := by
    simpa [prefixWord, tailWord_2527499, baseEnd_2527499] using wordTrace_append hprefix tailTrace_2527499
  have hstable : (prefixWord ++ tailWord_2527499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527499).length < 2 ^ (prefixWord ++ tailWord_2527499).sum := by decide
  have hdescent : baseEnd_2527499 < baseStart_2527499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527580 : List Nat := [2, 2, 4, 3, 1, 1, 1, 2, 3, 3]
def baseStart_2527580 : Nat := 118140960795 + 2527580 * 2 ^ 59
def prefixEnd_2527580 : Nat := 4983230072969 + 3 ^ 40 * 2527580 * 2
def baseEnd_2527580 : Nat := 865242288460884043550585

theorem tailTrace_2527580 : CollatzResearch.WordTrace tailWord_2527580 prefixEnd_2527580 865242288460884043550585 := by
  unfold tailWord_2527580
  simp only [CollatzResearch.WordTrace]
  refine ⟨46094208091508405570802097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61458944122011207427736129 46094208091508405570802097)
  ·
    refine ⟨34570656068631304178101573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46094208091508405570802097 34570656068631304178101573)
    ·
      refine ⟨6481998012868369533394045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34570656068631304178101573 6481998012868369533394045)
      ·
        refine ⟨2430749254825638575022767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6481998012868369533394045 2430749254825638575022767)
        ·
          refine ⟨3646123882238457862534151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2430749254825638575022767 3646123882238457862534151)
          ·
            refine ⟨5469185823357686793801227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3646123882238457862534151 5469185823357686793801227)
            ·
              refine ⟨8203778735036530190701841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5469185823357686793801227 8203778735036530190701841)
              ·
                refine ⟨6152834051277397643026381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8203778735036530190701841 6152834051277397643026381)
                ·
                  refine ⟨2307312769229024116134893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6152834051277397643026381 2307312769229024116134893)
                  ·
                    refine ⟨865242288460884043550585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2307312769229024116134893 865242288460884043550585)
                    ·
                      rfl

theorem cell22_2527580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_2527580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2527580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2527580 prefixEnd_2527580 := by exact prefixLift 2527580
  have htrace : WordTrace (prefixWord ++ tailWord_2527580) baseStart_2527580 baseEnd_2527580 := by
    simpa [prefixWord, tailWord_2527580, baseEnd_2527580] using wordTrace_append hprefix tailTrace_2527580
  have hstable : (prefixWord ++ tailWord_2527580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527580).length < 2 ^ (prefixWord ++ tailWord_2527580).sum := by decide
  have hdescent : baseEnd_2527580 < baseStart_2527580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527655 : List Nat := [1, 1, 6, 1, 1, 4, 1, 3, 4]
def baseStart_2527655 : Nat := 118140960795 + 2527655 * 2 ^ 59
def prefixEnd_2527655 : Nat := 4983230072969 + 3 ^ 40 * 2527655 * 2
def baseEnd_2527655 : Nat := 288422654164536282641785

theorem tailTrace_2527655 : CollatzResearch.WordTrace tailWord_2527655 prefixEnd_2527655 288422654164536282641785 := by
  unfold tailWord_2527655
  simp only [CollatzResearch.WordTrace]
  refine ⟨92191151657745098950584419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61460767771830065967056279 92191151657745098950584419)
  ·
    refine ⟨138286727486617648425876629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92191151657745098950584419 138286727486617648425876629)
    ·
      refine ⟨6482190350935202269962967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 138286727486617648425876629 6482190350935202269962967)
      ·
        refine ⟨9723285526402803404944451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6482190350935202269962967 9723285526402803404944451)
        ·
          refine ⟨14584928289604205107416677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9723285526402803404944451 14584928289604205107416677)
          ·
            refine ⟨2734674054300788457640627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14584928289604205107416677 2734674054300788457640627)
            ·
              refine ⟨4102011081451182686460941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2734674054300788457640627 4102011081451182686460941)
              ·
                refine ⟨1538254155544193507422853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4102011081451182686460941 1538254155544193507422853)
                ·
                  refine ⟨288422654164536282641785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1538254155544193507422853 288422654164536282641785)
                  ·
                    rfl

theorem cell22_2527655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 3, 4].length) (baseStart_2527655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2527655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2527655 prefixEnd_2527655 := by exact prefixLift 2527655
  have htrace : WordTrace (prefixWord ++ tailWord_2527655) baseStart_2527655 baseEnd_2527655 := by
    simpa [prefixWord, tailWord_2527655, baseEnd_2527655] using wordTrace_append hprefix tailTrace_2527655
  have hstable : (prefixWord ++ tailWord_2527655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527655).length < 2 ^ (prefixWord ++ tailWord_2527655).sum := by decide
  have hdescent : baseEnd_2527655 < baseStart_2527655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527741 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 5, 4]
def baseStart_2527741 : Nat := 118140960795 + 2527741 * 2 ^ 59
def prefixEnd_2527741 : Nat := 4983230072969 + 3 ^ 40 * 2527741 * 2
def baseEnd_2527741 : Nat := 865297402051133290275091

theorem tailTrace_2527741 : CollatzResearch.WordTrace tailWord_2527741 prefixEnd_2527741 865297402051133290275091 := by
  unfold tailWord_2527741
  simp only [CollatzResearch.WordTrace]
  refine ⟨92194288335433535638215077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61462858890289023758810051 92194288335433535638215077)
  ·
    refine ⟨17286429062893787932165327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92194288335433535638215077 17286429062893787932165327)
    ·
      refine ⟨25929643594340681898247991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17286429062893787932165327 25929643594340681898247991)
      ·
        refine ⟨38894465391511022847371987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25929643594340681898247991 38894465391511022847371987)
        ·
          refine ⟨58341698087266534271057981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38894465391511022847371987 58341698087266534271057981)
          ·
            refine ⟨21878136782724950351646743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58341698087266534271057981 21878136782724950351646743)
            ·
              refine ⟨32817205174087425527470115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21878136782724950351646743 32817205174087425527470115)
              ·
                refine ⟨49225807761131138291205173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32817205174087425527470115 49225807761131138291205173)
                ·
                  refine ⟨4614919477606044214800485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49225807761131138291205173 4614919477606044214800485)
                  ·
                    refine ⟨865297402051133290275091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4614919477606044214800485 865297402051133290275091)
                    ·
                      rfl

theorem cell22_2527741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_2527741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2527741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2527741 prefixEnd_2527741 := by exact prefixLift 2527741
  have htrace : WordTrace (prefixWord ++ tailWord_2527741) baseStart_2527741 baseEnd_2527741 := by
    simpa [prefixWord, tailWord_2527741, baseEnd_2527741] using wordTrace_append hprefix tailTrace_2527741
  have hstable : (prefixWord ++ tailWord_2527741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527741).length < 2 ^ (prefixWord ++ tailWord_2527741).sum := by decide
  have hdescent : baseEnd_2527741 < baseStart_2527741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527756 : List Nat := [2, 2, 1, 2, 4, 1, 1, 1, 8]
def baseStart_2527756 : Nat := 118140960795 + 2527756 * 2 ^ 59
def prefixEnd_2527756 : Nat := 4983230072969 + 3 ^ 40 * 2527756 * 2
def baseEnd_2527756 : Nat := 288434178952559417050015

theorem tailTrace_2527756 : CollatzResearch.WordTrace tailWord_2527756 prefixEnd_2527756 288434178952559417050015 := by
  unfold tailWord_2527756
  simp only [CollatzResearch.WordTrace]
  refine ⟨46097417715189596600005561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61463223620252795466674081 46097417715189596600005561)
  ·
    refine ⟨34573063286392197450004171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46097417715189596600005561 34573063286392197450004171)
    ·
      refine ⟨51859594929588296175006257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34573063286392197450004171 51859594929588296175006257)
      ·
        refine ⟨38894696197191222131254693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51859594929588296175006257 38894696197191222131254693)
        ·
          refine ⟨7292755536973354149610255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38894696197191222131254693 7292755536973354149610255)
          ·
            refine ⟨10939133305460031224415383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7292755536973354149610255 10939133305460031224415383)
            ·
              refine ⟨16408699958190046836623075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10939133305460031224415383 16408699958190046836623075)
              ·
                refine ⟨24613049937285070254934613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16408699958190046836623075 24613049937285070254934613)
                ·
                  refine ⟨288434178952559417050015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24613049937285070254934613 288434178952559417050015)
                  ·
                    rfl

theorem cell22_2527756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 8].length) (baseStart_2527756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2527756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2527756 prefixEnd_2527756 := by exact prefixLift 2527756
  have htrace : WordTrace (prefixWord ++ tailWord_2527756) baseStart_2527756 baseEnd_2527756 := by
    simpa [prefixWord, tailWord_2527756, baseEnd_2527756] using wordTrace_append hprefix tailTrace_2527756
  have hstable : (prefixWord ++ tailWord_2527756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527756).length < 2 ^ (prefixWord ++ tailWord_2527756).sum := by decide
  have hdescent : baseEnd_2527756 < baseStart_2527756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527758 : List Nat := [4, 1, 1, 2, 3, 1, 2, 1, 3, 4]
def baseStart_2527758 : Nat := 118140960795 + 2527758 * 2 ^ 59
def prefixEnd_2527758 : Nat := 4983230072969 + 3 ^ 40 * 2527758 * 2
def baseEnd_2527758 : Nat := 865303221498550912600039

theorem tailTrace_2527758 : CollatzResearch.WordTrace tailWord_2527758 prefixEnd_2527758 865303221498550912600039 := by
  unfold tailWord_2527758
  simp only [CollatzResearch.WordTrace]
  refine ⟨11524363547046493442697991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61463272250914631694389285 11524363547046493442697991)
  ·
    refine ⟨17286545320569740164046987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11524363547046493442697991 17286545320569740164046987)
    ·
      refine ⟨25929817980854610246070481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17286545320569740164046987 25929817980854610246070481)
      ·
        refine ⟨19447363485640957684552861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25929817980854610246070481 19447363485640957684552861)
        ·
          refine ⟨7292761307115359131707323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19447363485640957684552861 7292761307115359131707323)
          ·
            refine ⟨10939141960673038697560985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7292761307115359131707323 10939141960673038697560985)
            ·
              refine ⟨8204356470504779023170739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10939141960673038697560985 8204356470504779023170739)
              ·
                refine ⟨12306534705757168534756109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8204356470504779023170739 12306534705757168534756109)
                ·
                  refine ⟨4614950514658938200533541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12306534705757168534756109 4614950514658938200533541)
                  ·
                    refine ⟨865303221498550912600039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4614950514658938200533541 865303221498550912600039)
                    ·
                      rfl

theorem cell22_2527758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_2527758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2527758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2527758 prefixEnd_2527758 := by exact prefixLift 2527758
  have htrace : WordTrace (prefixWord ++ tailWord_2527758) baseStart_2527758 baseEnd_2527758 := by
    simpa [prefixWord, tailWord_2527758, baseEnd_2527758] using wordTrace_append hprefix tailTrace_2527758
  have hstable : (prefixWord ++ tailWord_2527758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527758).length < 2 ^ (prefixWord ++ tailWord_2527758).sum := by decide
  have hdescent : baseEnd_2527758 < baseStart_2527758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527790 : List Nat := [4, 1, 3, 1, 3, 1, 2, 1, 6]
def baseStart_2527790 : Nat := 118140960795 + 2527790 * 2 ^ 59
def prefixEnd_2527790 : Nat := 4983230072969 + 3 ^ 40 * 2527790 * 2
def baseEnd_2527790 : Nat := 288438058584171165266647

theorem tailTrace_2527790 : CollatzResearch.WordTrace tailWord_2527790 prefixEnd_2527790 288438058584171165266647 := by
  unfold tailWord_2527790
  simp only [CollatzResearch.WordTrace]
  refine ⟨11524509439032002125843603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61464050341504011337832549 11524509439032002125843603)
  ·
    refine ⟨17286764158548003188765405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11524509439032002125843603 17286764158548003188765405)
    ·
      refine ⟨6482536559455501195787027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17286764158548003188765405 6482536559455501195787027)
      ·
        refine ⟨9723804839183251793680541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6482536559455501195787027 9723804839183251793680541)
        ·
          refine ⟨3646426814693719422630203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9723804839183251793680541 3646426814693719422630203)
          ·
            refine ⟨5469640222040579133945305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3646426814693719422630203 5469640222040579133945305)
            ·
              refine ⟨4102230166530434350458979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5469640222040579133945305 4102230166530434350458979)
              ·
                refine ⟨6153345249795651525688469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4102230166530434350458979 6153345249795651525688469)
                ·
                  refine ⟨288438058584171165266647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6153345249795651525688469 288438058584171165266647)
                  ·
                    rfl

theorem cell22_2527790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_2527790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2527790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2527790 prefixEnd_2527790 := by exact prefixLift 2527790
  have htrace : WordTrace (prefixWord ++ tailWord_2527790) baseStart_2527790 baseEnd_2527790 := by
    simpa [prefixWord, tailWord_2527790, baseEnd_2527790] using wordTrace_append hprefix tailTrace_2527790
  have hstable : (prefixWord ++ tailWord_2527790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527790).length < 2 ^ (prefixWord ++ tailWord_2527790).sum := by decide
  have hdescent : baseEnd_2527790 < baseStart_2527790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527801 : List Nat := [1, 2, 1, 5, 1, 1, 2, 9]
def baseStart_2527801 : Nat := 118140960795 + 2527801 * 2 ^ 59
def prefixEnd_2527801 : Nat := 4983230072969 + 3 ^ 40 * 2527801 * 2
def baseEnd_2527801 : Nat := 96146437919701459308323

theorem tailTrace_2527801 : CollatzResearch.WordTrace tailWord_2527801 prefixEnd_2527801 96146437919701459308323 := by
  unfold tailWord_2527801
  simp only [CollatzResearch.WordTrace]
  refine ⟨92196476715216165885399257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61464317810144110590266171 92196476715216165885399257)
  ·
    refine ⟨69147357536412124414049443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92196476715216165885399257 69147357536412124414049443)
    ·
      refine ⟨103721036304618186621074165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69147357536412124414049443 103721036304618186621074165)
      ·
        refine ⟨9723847153557954995725703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 103721036304618186621074165 9723847153557954995725703)
        ·
          refine ⟨14585770730336932493588555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9723847153557954995725703 14585770730336932493588555)
          ·
            refine ⟨21878656095505398740382833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14585770730336932493588555 21878656095505398740382833)
            ·
              refine ⟨16408992071629049055287125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21878656095505398740382833 16408992071629049055287125)
              ·
                refine ⟨96146437919701459308323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16408992071629049055287125 96146437919701459308323)
                ·
                  rfl

theorem cell22_2527801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 9].length) (baseStart_2527801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2527801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2527801 prefixEnd_2527801 := by exact prefixLift 2527801
  have htrace : WordTrace (prefixWord ++ tailWord_2527801) baseStart_2527801 baseEnd_2527801 := by
    simpa [prefixWord, tailWord_2527801, baseEnd_2527801] using wordTrace_append hprefix tailTrace_2527801
  have hstable : (prefixWord ++ tailWord_2527801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527801).length < 2 ^ (prefixWord ++ tailWord_2527801).sum := by decide
  have hdescent : baseEnd_2527801 < baseStart_2527801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527805 : List Nat := [1, 4, 1, 3, 2, 3, 1, 1, 1, 5]
def baseStart_2527805 : Nat := 118140960795 + 2527805 * 2 ^ 59
def prefixEnd_2527805 : Nat := 4983230072969 + 3 ^ 40 * 2527805 * 2
def baseEnd_2527805 : Nat := 865319310559058456674895

theorem tailTrace_2527805 : CollatzResearch.WordTrace tailWord_2527805 prefixEnd_2527805 865319310559058456674895 := by
  unfold tailWord_2527805
  simp only [CollatzResearch.WordTrace]
  refine ⟨92196622607201674568544869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61464415071467783045696579 92196622607201674568544869)
  ·
    refine ⟨17286866738850313981602163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92196622607201674568544869 17286866738850313981602163)
    ·
      refine ⟨25930300108275470972403245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17286866738850313981602163 25930300108275470972403245)
      ·
        refine ⟨9723862540603301614651217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25930300108275470972403245 9723862540603301614651217)
        ·
          refine ⟨7292896905452476210988413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9723862540603301614651217 7292896905452476210988413)
          ·
            refine ⟨2734836339544678579120655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7292896905452476210988413 2734836339544678579120655)
            ·
              refine ⟨4102254509317017868680983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2734836339544678579120655 4102254509317017868680983)
              ·
                refine ⟨6153381763975526803021475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4102254509317017868680983 6153381763975526803021475)
                ·
                  refine ⟨9230072645963290204532213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6153381763975526803021475 9230072645963290204532213)
                  ·
                    refine ⟨865319310559058456674895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9230072645963290204532213 865319310559058456674895)
                    ·
                      rfl

theorem cell22_2527805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_2527805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2527805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2527805 prefixEnd_2527805 := by exact prefixLift 2527805
  have htrace : WordTrace (prefixWord ++ tailWord_2527805) baseStart_2527805 baseEnd_2527805 := by
    simpa [prefixWord, tailWord_2527805, baseEnd_2527805] using wordTrace_append hprefix tailTrace_2527805
  have hstable : (prefixWord ++ tailWord_2527805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527805).length < 2 ^ (prefixWord ++ tailWord_2527805).sum := by decide
  have hdescent : baseEnd_2527805 < baseStart_2527805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527818 : List Nat := [3, 1, 2, 1, 1, 4, 4, 6]
def baseStart_2527818 : Nat := 118140960795 + 2527818 * 2 ^ 59
def prefixEnd_2527818 : Nat := 4983230072969 + 3 ^ 40 * 2527818 * 2
def baseEnd_2527818 : Nat := 96147084524970084011095

theorem tailTrace_2527818 : CollatzResearch.WordTrace tailWord_2527818 prefixEnd_2527818 96147084524970084011095 := by
  unfold tailWord_2527818
  simp only [CollatzResearch.WordTrace]
  refine ⟨23049274189038644447192027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61464731170769718525845405 23049274189038644447192027)
  ·
    refine ⟨34573911283557966670788041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23049274189038644447192027 34573911283557966670788041)
    ·
      refine ⟨25930433462668475003091031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34573911283557966670788041 25930433462668475003091031)
      ·
        refine ⟨38895650194002712504636547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25930433462668475003091031 38895650194002712504636547)
        ·
          refine ⟨58343475291004068756954821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38895650194002712504636547 58343475291004068756954821)
          ·
            refine ⟨10939401617063262891929029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58343475291004068756954821 10939401617063262891929029)
            ·
              refine ⟨2051137803199361792236693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10939401617063262891929029 2051137803199361792236693)
              ·
                refine ⟨96147084524970084011095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2051137803199361792236693 96147084524970084011095)
                ·
                  rfl

theorem cell22_2527818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 6].length) (baseStart_2527818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2527818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2527818 prefixEnd_2527818 := by exact prefixLift 2527818
  have htrace : WordTrace (prefixWord ++ tailWord_2527818) baseStart_2527818 baseEnd_2527818 := by
    simpa [prefixWord, tailWord_2527818, baseEnd_2527818] using wordTrace_append hprefix tailTrace_2527818
  have hstable : (prefixWord ++ tailWord_2527818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527818).length < 2 ^ (prefixWord ++ tailWord_2527818).sum := by decide
  have hdescent : baseEnd_2527818 < baseStart_2527818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527891 : List Nat := [1, 1, 1, 2, 1, 2, 2, 4, 8]
def baseStart_2527891 : Nat := 118140960795 + 2527891 * 2 ^ 59
def prefixEnd_2527891 : Nat := 4983230072969 + 3 ^ 40 * 2527891 * 2
def baseEnd_2527891 : Nat := 288449583372194299674877

theorem tailTrace_2527891 : CollatzResearch.WordTrace tailWord_2527891 prefixEnd_2527891 288449583372194299674877 := by
  unfold tailWord_2527891
  simp only [CollatzResearch.WordTrace]
  refine ⟨92199759284890111256175527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61466506189926740837450351 92199759284890111256175527)
  ·
    refine ⟨138299638927335166884263291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92199759284890111256175527 138299638927335166884263291)
    ·
      refine ⟨207449458391002750326394937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138299638927335166884263291 207449458391002750326394937)
      ·
        refine ⟨155587093793252062744796203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207449458391002750326394937 155587093793252062744796203)
        ·
          refine ⟨233380640689878094117194305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155587093793252062744796203 233380640689878094117194305)
          ·
            refine ⟨175035480517408570587895729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233380640689878094117194305 175035480517408570587895729)
            ·
              refine ⟨131276610388056427940921797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175035480517408570587895729 131276610388056427940921797)
              ·
                refine ⟨24614364447760580238922837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 131276610388056427940921797 24614364447760580238922837)
                ·
                  refine ⟨288449583372194299674877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24614364447760580238922837 288449583372194299674877)
                  ·
                    rfl

theorem cell22_2527891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 8].length) (baseStart_2527891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2527891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2527891 prefixEnd_2527891 := by exact prefixLift 2527891
  have htrace : WordTrace (prefixWord ++ tailWord_2527891) baseStart_2527891 baseEnd_2527891 := by
    simpa [prefixWord, tailWord_2527891, baseEnd_2527891] using wordTrace_append hprefix tailTrace_2527891
  have hstable : (prefixWord ++ tailWord_2527891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527891).length < 2 ^ (prefixWord ++ tailWord_2527891).sum := by decide
  have hdescent : baseEnd_2527891 < baseStart_2527891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527908 : List Nat := [2, 3, 1, 2, 2, 1, 2, 3, 6]
def baseStart_2527908 : Nat := 118140960795 + 2527908 * 2 ^ 59
def prefixEnd_2527908 : Nat := 4983230072969 + 3 ^ 40 * 2527908 * 2
def baseEnd_2527908 : Nat := 288451523188000173783193

theorem tailTrace_2527908 : CollatzResearch.WordTrace tailWord_2527908 prefixEnd_2527908 288451523188000173783193 := by
  unfold tailWord_2527908
  simp only [CollatzResearch.WordTrace]
  refine ⟨46100189662914261579772189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61466919550552348773029585 46100189662914261579772189)
  ·
    refine ⟨17287571123592848092414571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46100189662914261579772189 17287571123592848092414571)
    ·
      refine ⟨25931356685389272138621857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17287571123592848092414571 25931356685389272138621857)
      ·
        refine ⟨19448517514041954103966393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25931356685389272138621857 19448517514041954103966393)
        ·
          refine ⟨14586388135531465577974795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19448517514041954103966393 14586388135531465577974795)
          ·
            refine ⟨21879582203297198366962193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14586388135531465577974795 21879582203297198366962193)
            ·
              refine ⟨16409686652472898775221645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21879582203297198366962193 16409686652472898775221645)
              ·
                refine ⟨6153632494677337040708117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16409686652472898775221645 6153632494677337040708117)
                ·
                  refine ⟨288451523188000173783193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6153632494677337040708117 288451523188000173783193)
                  ·
                    rfl

theorem cell22_2527908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_2527908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2527908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2527908 prefixEnd_2527908 := by exact prefixLift 2527908
  have htrace : WordTrace (prefixWord ++ tailWord_2527908) baseStart_2527908 baseEnd_2527908 := by
    simpa [prefixWord, tailWord_2527908, baseEnd_2527908] using wordTrace_append hprefix tailTrace_2527908
  have hstable : (prefixWord ++ tailWord_2527908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527908).length < 2 ^ (prefixWord ++ tailWord_2527908).sum := by decide
  have hdescent : baseEnd_2527908 < baseStart_2527908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527923 : List Nat := [1, 1, 1, 2, 3, 4, 1, 3, 1, 5]
def baseStart_2527923 : Nat := 118140960795 + 2527923 * 2 ^ 59
def prefixEnd_2527923 : Nat := 4983230072969 + 3 ^ 40 * 2527923 * 2
def baseEnd_2527923 : Nat := 865359704370545482224533

theorem tailTrace_2527923 : CollatzResearch.WordTrace tailWord_2527923 prefixEnd_2527923 865359704370545482224533 := by
  unfold tailWord_2527923
  simp only [CollatzResearch.WordTrace]
  refine ⟨92200926420774180721340423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61467284280516120480893615 92200926420774180721340423)
  ·
    refine ⟨138301389631161271082010635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92200926420774180721340423 138301389631161271082010635)
    ·
      refine ⟨207452084446741906623015953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138301389631161271082010635 207452084446741906623015953)
      ·
        refine ⟨155589063335056429967261965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207452084446741906623015953 155589063335056429967261965)
        ·
          refine ⟨58345898750646161237723237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155589063335056429967261965 58345898750646161237723237)
          ·
            refine ⟨10939856015746155232073107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58345898750646161237723237 10939856015746155232073107)
            ·
              refine ⟨16409784023619232848109661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10939856015746155232073107 16409784023619232848109661)
              ·
                refine ⟨6153669008857212318041123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16409784023619232848109661 6153669008857212318041123)
                ·
                  refine ⟨9230503513285818477061685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6153669008857212318041123 9230503513285818477061685)
                  ·
                    refine ⟨865359704370545482224533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9230503513285818477061685 865359704370545482224533)
                    ·
                      rfl

theorem cell22_2527923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 5].length) (baseStart_2527923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2527923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2527923 prefixEnd_2527923 := by exact prefixLift 2527923
  have htrace : WordTrace (prefixWord ++ tailWord_2527923) baseStart_2527923 baseEnd_2527923 := by
    simpa [prefixWord, tailWord_2527923, baseEnd_2527923] using wordTrace_append hprefix tailTrace_2527923
  have hstable : (prefixWord ++ tailWord_2527923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527923).length < 2 ^ (prefixWord ++ tailWord_2527923).sum := by decide
  have hdescent : baseEnd_2527923 < baseStart_2527923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527925 : List Nat := [1, 3, 3, 3, 1, 2, 1, 2, 6]
def baseStart_2527925 : Nat := 118140960795 + 2527925 * 2 ^ 59
def prefixEnd_2527925 : Nat := 4983230072969 + 3 ^ 40 * 2527925 * 2
def baseEnd_2527925 : Nat := 288453463003806047891509

theorem tailTrace_2527925 : CollatzResearch.WordTrace tailWord_2527925 prefixEnd_2527925 288453463003806047891509 := by
  unfold tailWord_2527925
  simp only [CollatzResearch.WordTrace]
  refine ⟨92200999366766935062913229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61467332911177956708608819 92200999366766935062913229)
  ·
    refine ⟨34575374762537600648592461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92200999366766935062913229 34575374762537600648592461)
    ·
      refine ⟨12965765535951600243222173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34575374762537600648592461 12965765535951600243222173)
      ·
        refine ⟨4862162075981850091208315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12965765535951600243222173 4862162075981850091208315)
        ·
          refine ⟨7293243113972775136812473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4862162075981850091208315 7293243113972775136812473)
          ·
            refine ⟨5469932335479581352609355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7293243113972775136812473 5469932335479581352609355)
            ·
              refine ⟨8204898503219372028914033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5469932335479581352609355 8204898503219372028914033)
              ·
                refine ⟨6153673877414529021685525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8204898503219372028914033 6153673877414529021685525)
                ·
                  refine ⟨288453463003806047891509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6153673877414529021685525 288453463003806047891509)
                  ·
                    rfl

theorem cell22_2527925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 6].length) (baseStart_2527925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2527925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2527925 prefixEnd_2527925 := by exact prefixLift 2527925
  have htrace : WordTrace (prefixWord ++ tailWord_2527925) baseStart_2527925 baseEnd_2527925 := by
    simpa [prefixWord, tailWord_2527925, baseEnd_2527925] using wordTrace_append hprefix tailTrace_2527925
  have hstable : (prefixWord ++ tailWord_2527925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527925).length < 2 ^ (prefixWord ++ tailWord_2527925).sum := by decide
  have hdescent : baseEnd_2527925 < baseStart_2527925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527940 : List Nat := [2, 3, 3, 1, 1, 2, 2, 2, 1, 5]
def baseStart_2527940 : Nat := 118140960795 + 2527940 * 2 ^ 59
def prefixEnd_2527940 : Nat := 4983230072969 + 3 ^ 40 * 2527940 * 2
def baseEnd_2527940 : Nat := 865365523817963104549481

theorem tailTrace_2527940 : CollatzResearch.WordTrace tailWord_2527940 prefixEnd_2527940 865365523817963104549481 := by
  unfold tailWord_2527940
  simp only [CollatzResearch.WordTrace]
  refine ⟨46100773230856296312354637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61467697641141728416472849 46100773230856296312354637)
  ·
    refine ⟨17287789961571111117132989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46100773230856296312354637 17287789961571111117132989)
    ·
      refine ⟨6482921235589166668924871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17287789961571111117132989 6482921235589166668924871)
      ·
        refine ⟨9724381853383750003387307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6482921235589166668924871 9724381853383750003387307)
        ·
          refine ⟨14586572780075625005080961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9724381853383750003387307 14586572780075625005080961)
          ·
            refine ⟨10939929585056718753810721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14586572780075625005080961 10939929585056718753810721)
            ·
              refine ⟨8204947188792539065358041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10939929585056718753810721 8204947188792539065358041)
              ·
                refine ⟨6153710391594404299018531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8204947188792539065358041 6153710391594404299018531)
                ·
                  refine ⟨9230565587391606448527797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6153710391594404299018531 9230565587391606448527797)
                  ·
                    refine ⟨865365523817963104549481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9230565587391606448527797 865365523817963104549481)
                    ·
                      rfl

theorem cell22_2527940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_2527940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2527940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2527940 prefixEnd_2527940 := by exact prefixLift 2527940
  have htrace : WordTrace (prefixWord ++ tailWord_2527940) baseStart_2527940 baseEnd_2527940 := by
    simpa [prefixWord, tailWord_2527940, baseEnd_2527940] using wordTrace_append hprefix tailTrace_2527940
  have hstable : (prefixWord ++ tailWord_2527940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527940).length < 2 ^ (prefixWord ++ tailWord_2527940).sum := by decide
  have hdescent : baseEnd_2527940 < baseStart_2527940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2527985 : List Nat := [1, 2, 2, 2, 2, 2, 1, 4, 3, 3]
def baseStart_2527985 : Nat := 118140960795 + 2527985 * 2 ^ 59
def prefixEnd_2527985 : Nat := 4983230072969 + 3 ^ 40 * 2527985 * 2
def baseEnd_2527985 : Nat := 865380928237597987174343

theorem tailTrace_2527985 : CollatzResearch.WordTrace tailWord_2527985 prefixEnd_2527985 865380928237597987174343 := by
  unfold tailWord_2527985
  simp only [CollatzResearch.WordTrace]
  refine ⟨92203187746549565310097409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61468791831033043540064939 92203187746549565310097409)
  ·
    refine ⟨69152390809912173982573057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92203187746549565310097409 69152390809912173982573057)
    ·
      refine ⟨51864293107434130486929793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69152390809912173982573057 51864293107434130486929793)
      ·
        refine ⟨38898219830575597865197345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51864293107434130486929793 38898219830575597865197345)
        ·
          refine ⟨29173664872931698398898009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38898219830575597865197345 29173664872931698398898009)
          ·
            refine ⟨21880248654698773799173507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29173664872931698398898009 21880248654698773799173507)
            ·
              refine ⟨32820372982048160698760261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21880248654698773799173507 32820372982048160698760261)
              ·
                refine ⟨6153819934134030131017549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32820372982048160698760261 6153819934134030131017549)
                ·
                  refine ⟨2307682475300261299131581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6153819934134030131017549 2307682475300261299131581)
                  ·
                    refine ⟨865380928237597987174343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2307682475300261299131581 865380928237597987174343)
                    ·
                      rfl

theorem cell22_2527985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 3, 3].length) (baseStart_2527985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2527985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2527985 prefixEnd_2527985 := by exact prefixLift 2527985
  have htrace : WordTrace (prefixWord ++ tailWord_2527985) baseStart_2527985 baseEnd_2527985 := by
    simpa [prefixWord, tailWord_2527985, baseEnd_2527985] using wordTrace_append hprefix tailTrace_2527985
  have hstable : (prefixWord ++ tailWord_2527985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2527985).length < 2 ^ (prefixWord ++ tailWord_2527985).sum := by decide
  have hdescent : baseEnd_2527985 < baseStart_2527985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2527985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528019 : List Nat := [1, 1, 1, 2, 1, 3, 7, 2, 1, 3]
def baseStart_2528019 : Nat := 118140960795 + 2528019 * 2 ^ 59
def prefixEnd_2528019 : Nat := 4983230072969 + 3 ^ 40 * 2528019 * 2
def baseEnd_2528019 : Nat := 865392567132433231824239

theorem tailTrace_2528019 : CollatzResearch.WordTrace tailWord_2528019 prefixEnd_2528019 865392567132433231824239 := by
  unfold tailWord_2528019
  simp only [CollatzResearch.WordTrace]
  refine ⟨92204427828426389116835111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61469618552284259411223407 92204427828426389116835111)
  ·
    refine ⟨138306641742639583675252667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92204427828426389116835111 138306641742639583675252667)
    ·
      refine ⟨207459962613959375512879001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138306641742639583675252667 207459962613959375512879001)
      ·
        refine ⟨155594971960469531634659251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207459962613959375512879001 155594971960469531634659251)
        ·
          refine ⟨233392457940704297451988877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155594971960469531634659251 233392457940704297451988877)
          ·
            refine ⟨87522171727764111544495829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 233392457940704297451988877 87522171727764111544495829)
            ·
              refine ⟨2051300899869471364324121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 87522171727764111544495829 2051300899869471364324121)
              ·
                refine ⟨1538475674902103523243091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2051300899869471364324121 1538475674902103523243091)
                ·
                  refine ⟨2307713512353155284864637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1538475674902103523243091 2307713512353155284864637)
                  ·
                    refine ⟨865392567132433231824239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2307713512353155284864637 865392567132433231824239)
                    ·
                      rfl

theorem cell22_2528019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 2, 1, 3].length) (baseStart_2528019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2528019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2528019 prefixEnd_2528019 := by exact prefixLift 2528019
  have htrace : WordTrace (prefixWord ++ tailWord_2528019) baseStart_2528019 baseEnd_2528019 := by
    simpa [prefixWord, tailWord_2528019, baseEnd_2528019] using wordTrace_append hprefix tailTrace_2528019
  have hstable : (prefixWord ++ tailWord_2528019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528019).length < 2 ^ (prefixWord ++ tailWord_2528019).sum := by decide
  have hdescent : baseEnd_2528019 < baseStart_2528019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528032 : List Nat := [2, 1, 1, 5, 1, 2, 4, 1, 5]
def baseStart_2528032 : Nat := 118140960795 + 2528032 * 2 ^ 59
def prefixEnd_2528032 : Nat := 4983230072969 + 3 ^ 40 * 2528032 * 2
def baseEnd_2528032 : Nat := 288465672432701843749733

theorem tailTrace_2528032 : CollatzResearch.WordTrace tailWord_2528032 prefixEnd_2528032 288465672432701843749733 := by
  unfold tailWord_2528032
  simp only [CollatzResearch.WordTrace]
  refine ⟨46102450988689646168529175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61469934651586194891372233 46102450988689646168529175)
  ·
    refine ⟨69153676483034469252793763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46102450988689646168529175 69153676483034469252793763)
    ·
      refine ⟨103730514724551703879190645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69153676483034469252793763 103730514724551703879190645)
      ·
        refine ⟨9724735755426722238674123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 103730514724551703879190645 9724735755426722238674123)
        ·
          refine ⟨14587103633140083358011185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9724735755426722238674123 14587103633140083358011185)
          ·
            refine ⟨10940327724855062518508389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14587103633140083358011185 10940327724855062518508389)
            ·
              refine ⟨2051311448410324222220323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10940327724855062518508389 2051311448410324222220323)
              ·
                refine ⟨3076967172615486333330485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2051311448410324222220323 3076967172615486333330485)
                ·
                  refine ⟨288465672432701843749733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3076967172615486333330485 288465672432701843749733)
                  ·
                    rfl

theorem cell22_2528032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 5].length) (baseStart_2528032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2528032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2528032 prefixEnd_2528032 := by exact prefixLift 2528032
  have htrace : WordTrace (prefixWord ++ tailWord_2528032) baseStart_2528032 baseEnd_2528032 := by
    simpa [prefixWord, tailWord_2528032, baseEnd_2528032] using wordTrace_append hprefix tailTrace_2528032
  have hstable : (prefixWord ++ tailWord_2528032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528032).length < 2 ^ (prefixWord ++ tailWord_2528032).sum := by decide
  have hdescent : baseEnd_2528032 < baseStart_2528032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528092 : List Nat := [2, 2, 4, 2, 1, 1, 1, 3, 1, 5]
def baseStart_2528092 : Nat := 118140960795 + 2528092 * 2 ^ 59
def prefixEnd_2528092 : Nat := 4983230072969 + 3 ^ 40 * 2528092 * 2
def baseEnd_2528092 : Nat := 865417556524285374749015

theorem tailTrace_2528092 : CollatzResearch.WordTrace tailWord_2528092 prefixEnd_2528092 865417556524285374749015 := by
  unfold tailWord_2528092
  simp only [CollatzResearch.WordTrace]
  refine ⟨46103545178580961292121265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61471393571441281722828353 46103545178580961292121265)
  ·
    refine ⟨34577658883935720969090949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46103545178580961292121265 34577658883935720969090949)
    ·
      refine ⟨6483311040737947681704553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34577658883935720969090949 6483311040737947681704553)
      ·
        refine ⟨4862483280553460761278415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6483311040737947681704553 4862483280553460761278415)
        ·
          refine ⟨7293724920830191141917623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4862483280553460761278415 7293724920830191141917623)
          ·
            refine ⟨10940587381245286712876435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7293724920830191141917623 10940587381245286712876435)
            ·
              refine ⟨16410881071867930069314653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10940587381245286712876435 16410881071867930069314653)
              ·
                refine ⟨6154080401950473775992995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16410881071867930069314653 6154080401950473775992995)
                ·
                  refine ⟨9231120602925710663989493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6154080401950473775992995 9231120602925710663989493)
                  ·
                    refine ⟨865417556524285374749015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9231120602925710663989493 865417556524285374749015)
                    ·
                      rfl

theorem cell22_2528092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_2528092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2528092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2528092 prefixEnd_2528092 := by exact prefixLift 2528092
  have htrace : WordTrace (prefixWord ++ tailWord_2528092) baseStart_2528092 baseEnd_2528092 := by
    simpa [prefixWord, tailWord_2528092, baseEnd_2528092] using wordTrace_append hprefix tailTrace_2528092
  have hstable : (prefixWord ++ tailWord_2528092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528092).length < 2 ^ (prefixWord ++ tailWord_2528092).sum := by decide
  have hdescent : baseEnd_2528092 < baseStart_2528092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528126 : List Nat := [4, 2, 3, 1, 2, 1, 1, 1, 4, 3]
def baseStart_2528126 : Nat := 118140960795 + 2528126 * 2 ^ 59
def prefixEnd_2528126 : Nat := 4983230072969 + 3 ^ 40 * 2528126 * 2
def baseEnd_2528126 : Nat := 865429195419120619398911

theorem tailTrace_2528126 : CollatzResearch.WordTrace tailWord_2528126 prefixEnd_2528126 865429195419120619398911 := by
  unfold tailWord_2528126
  simp only [CollatzResearch.WordTrace]
  refine ⟨11526041304879843298872529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61472220292692497593986821 11526041304879843298872529)
  ·
    refine ⟨8644530978659882474154397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11526041304879843298872529 8644530978659882474154397)
    ·
      refine ⟨3241699116997455927807899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8644530978659882474154397 3241699116997455927807899)
      ·
        refine ⟨4862548675496183891711849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3241699116997455927807899 4862548675496183891711849)
        ·
          refine ⟨3646911506622137918783887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4862548675496183891711849 3646911506622137918783887)
          ·
            refine ⟨5470367259933206878175831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3646911506622137918783887 5470367259933206878175831)
            ·
              refine ⟨8205550889899810317263747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5470367259933206878175831 8205550889899810317263747)
              ·
                refine ⟨12308326334849715475895621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8205550889899810317263747 12308326334849715475895621)
                ·
                  refine ⟨2307811187784321651730429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12308326334849715475895621 2307811187784321651730429)
                  ·
                    refine ⟨865429195419120619398911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2307811187784321651730429 865429195419120619398911)
                    ·
                      rfl

theorem cell22_2528126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_2528126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2528126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2528126 prefixEnd_2528126 := by exact prefixLift 2528126
  have htrace : WordTrace (prefixWord ++ tailWord_2528126) baseStart_2528126 baseEnd_2528126 := by
    simpa [prefixWord, tailWord_2528126, baseEnd_2528126] using wordTrace_append hprefix tailTrace_2528126
  have hstable : (prefixWord ++ tailWord_2528126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528126).length < 2 ^ (prefixWord ++ tailWord_2528126).sum := by decide
  have hdescent : baseEnd_2528126 < baseStart_2528126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528137 : List Nat := [1, 2, 1, 1, 5, 2, 1, 3, 3, 3]
def baseStart_2528137 : Nat := 118140960795 + 2528137 * 2 ^ 59
def prefixEnd_2528137 : Nat := 4983230072969 + 3 ^ 40 * 2528137 * 2
def baseEnd_2528137 : Nat := 865432960943920257373877

theorem tailTrace_2528137 : CollatzResearch.WordTrace tailWord_2528137 prefixEnd_2528137 865432960943920257373877 := by
  unfold tailWord_2528137
  simp only [CollatzResearch.WordTrace]
  refine ⟨92208731641998895269630665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61472487761332596846420443 92208731641998895269630665)
  ·
    refine ⟨69156548731499171452222999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92208731641998895269630665 69156548731499171452222999)
    ·
      refine ⟨103734823097248757178334499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69156548731499171452222999 103734823097248757178334499)
      ·
        refine ⟨155602234645873135767501749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103734823097248757178334499 155602234645873135767501749)
        ·
          refine ⟨14587709498050606478203289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 155602234645873135767501749 14587709498050606478203289)
          ·
            refine ⟨10940782123537954858652467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14587709498050606478203289 10940782123537954858652467)
            ·
              refine ⟨16411173185306932287978701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10940782123537954858652467 16411173185306932287978701)
              ·
                refine ⟨6154189944490099607992013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16411173185306932287978701 6154189944490099607992013)
                ·
                  refine ⟨2307821229183787352997005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6154189944490099607992013 2307821229183787352997005)
                  ·
                    refine ⟨865432960943920257373877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2307821229183787352997005 865432960943920257373877)
                    ·
                      rfl

theorem cell22_2528137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 3, 3].length) (baseStart_2528137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2528137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2528137 prefixEnd_2528137 := by exact prefixLift 2528137
  have htrace : WordTrace (prefixWord ++ tailWord_2528137) baseStart_2528137 baseEnd_2528137 := by
    simpa [prefixWord, tailWord_2528137, baseEnd_2528137] using wordTrace_append hprefix tailTrace_2528137
  have hstable : (prefixWord ++ tailWord_2528137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528137).length < 2 ^ (prefixWord ++ tailWord_2528137).sum := by decide
  have hdescent : baseEnd_2528137 < baseStart_2528137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528156 : List Nat := [2, 2, 3, 3, 3, 1, 2, 6]
def baseStart_2528156 : Nat := 118140960795 + 2528156 * 2 ^ 59
def prefixEnd_2528156 : Nat := 4983230072969 + 3 ^ 40 * 2528156 * 2
def baseEnd_2528156 : Nat := 96159940559134504572091

theorem tailTrace_2528156 : CollatzResearch.WordTrace tailWord_2528156 prefixEnd_2528156 96159940559134504572091 := by
  unfold tailWord_2528156
  simp only [CollatzResearch.WordTrace]
  refine ⟨46104712314465030757286161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61472949752620041009714881 46104712314465030757286161)
  ·
    refine ⟨34578534235848773067964621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46104712314465030757286161 34578534235848773067964621)
    ·
      refine ⟨12966950338443289900486733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34578534235848773067964621 12966950338443289900486733)
      ·
        refine ⟨4862606376916233712682525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12966950338443289900486733 4862606376916233712682525)
        ·
          refine ⟨1823477391343587642255947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4862606376916233712682525 1823477391343587642255947)
          ·
            refine ⟨2735216087015381463383921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1823477391343587642255947 2735216087015381463383921)
            ·
              refine ⟨2051412065261536097537941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2735216087015381463383921 2051412065261536097537941)
              ·
                refine ⟨96159940559134504572091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2051412065261536097537941 96159940559134504572091)
                ·
                  rfl

theorem cell22_2528156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 6].length) (baseStart_2528156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2528156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2528156 prefixEnd_2528156 := by exact prefixLift 2528156
  have htrace : WordTrace (prefixWord ++ tailWord_2528156) baseStart_2528156 baseEnd_2528156 := by
    simpa [prefixWord, tailWord_2528156, baseEnd_2528156] using wordTrace_append hprefix tailTrace_2528156
  have hstable : (prefixWord ++ tailWord_2528156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528156).length < 2 ^ (prefixWord ++ tailWord_2528156).sum := by decide
  have hdescent : baseEnd_2528156 < baseStart_2528156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528227 : List Nat := [1, 1, 1, 6, 1, 1, 3, 2, 1, 5]
def baseStart_2528227 : Nat := 118140960795 + 2528227 * 2 ^ 59
def prefixEnd_2528227 : Nat := 4983230072969 + 3 ^ 40 * 2528227 * 2
def baseEnd_2528227 : Nat := 865463769783190022623601

theorem tailTrace_2528227 : CollatzResearch.WordTrace tailWord_2528227 prefixEnd_2528227 865463769783190022623601 := by
  unfold tailWord_2528227
  simp only [CollatzResearch.WordTrace]
  refine ⟨92212014211672840640406935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61474676141115227093604623 92212014211672840640406935)
  ·
    refine ⟨138318021317509260960610403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92212014211672840640406935 138318021317509260960610403)
    ·
      refine ⟨207477031976263891440915605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138318021317509260960610403 207477031976263891440915605)
      ·
        refine ⟨9725485873887369911292919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 207477031976263891440915605 9725485873887369911292919)
        ·
          refine ⟨14588228810831054866939379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9725485873887369911292919 14588228810831054866939379)
          ·
            refine ⟨21882343216246582300409069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14588228810831054866939379 21882343216246582300409069)
            ·
              refine ⟨8205878706092468362653401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21882343216246582300409069 8205878706092468362653401)
              ·
                refine ⟨6154409029569351271990051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8205878706092468362653401 6154409029569351271990051)
                ·
                  refine ⟨9231613544354026907985077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6154409029569351271990051 9231613544354026907985077)
                  ·
                    refine ⟨865463769783190022623601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9231613544354026907985077 865463769783190022623601)
                    ·
                      rfl

theorem cell22_2528227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 5].length) (baseStart_2528227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2528227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2528227 prefixEnd_2528227 := by exact prefixLift 2528227
  have htrace : WordTrace (prefixWord ++ tailWord_2528227) baseStart_2528227 baseEnd_2528227 := by
    simpa [prefixWord, tailWord_2528227, baseEnd_2528227] using wordTrace_append hprefix tailTrace_2528227
  have hstable : (prefixWord ++ tailWord_2528227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528227).length < 2 ^ (prefixWord ++ tailWord_2528227).sum := by decide
  have hdescent : baseEnd_2528227 < baseStart_2528227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528231 : List Nat := [1, 1, 5, 2, 2, 2, 3, 1, 1, 4]
def baseStart_2528231 : Nat := 118140960795 + 2528231 * 2 ^ 59
def prefixEnd_2528231 : Nat := 4983230072969 + 3 ^ 40 * 2528231 * 2
def baseEnd_2528231 : Nat := 865465139064935345523589

theorem tailTrace_2528231 : CollatzResearch.WordTrace tailWord_2528231 prefixEnd_2528231 865465139064935345523589 := by
  unfold tailWord_2528231
  simp only [CollatzResearch.WordTrace]
  refine ⟨92212160103658349323552547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61474773402438899549035031 92212160103658349323552547)
  ·
    refine ⟨138318240155487523985328821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92212160103658349323552547 138318240155487523985328821)
    ·
      refine ⟨12967335014576955373624577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 138318240155487523985328821 12967335014576955373624577)
      ·
        refine ⟨9725501260932716530218433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12967335014576955373624577 9725501260932716530218433)
        ·
          refine ⟨7294125945699537397663825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9725501260932716530218433 7294125945699537397663825)
          ·
            refine ⟨5470594459274653048247869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7294125945699537397663825 5470594459274653048247869)
            ·
              refine ⟨2051472922227994893092951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5470594459274653048247869 2051472922227994893092951)
              ·
                refine ⟨3077209383341992339639427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2051472922227994893092951 3077209383341992339639427)
                ·
                  refine ⟨4615814075012988509459141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3077209383341992339639427 4615814075012988509459141)
                  ·
                    refine ⟨865465139064935345523589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4615814075012988509459141 865465139064935345523589)
                    ·
                      rfl

theorem cell22_2528231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_2528231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2528231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2528231 prefixEnd_2528231 := by exact prefixLift 2528231
  have htrace : WordTrace (prefixWord ++ tailWord_2528231) baseStart_2528231 baseEnd_2528231 := by
    simpa [prefixWord, tailWord_2528231, baseEnd_2528231] using wordTrace_append hprefix tailTrace_2528231
  have hstable : (prefixWord ++ tailWord_2528231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528231).length < 2 ^ (prefixWord ++ tailWord_2528231).sum := by decide
  have hdescent : baseEnd_2528231 < baseStart_2528231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528246 : List Nat := [5, 1, 1, 1, 3, 2, 1, 4, 4]
def baseStart_2528246 : Nat := 118140960795 + 2528246 * 2 ^ 59
def prefixEnd_2528246 : Nat := 4983230072969 + 3 ^ 40 * 2528246 * 2
def baseEnd_2528246 : Nat := 288490091290493435466181

theorem tailTrace_2528246 : CollatzResearch.WordTrace tailWord_2528246 prefixEnd_2528246 288490091290493435466181 := by
  unfold tailWord_2528246
  simp only [CollatzResearch.WordTrace]
  refine ⟨5763294199912750430334287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61475138132402671256899061 5763294199912750430334287)
  ·
    refine ⟨8644941299869125645501431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5763294199912750430334287 8644941299869125645501431)
    ·
      refine ⟨12967411949803688468252147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8644941299869125645501431 12967411949803688468252147)
      ·
        refine ⟨19451117924705532702378221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12967411949803688468252147 19451117924705532702378221)
        ·
          refine ⟨7294169221764574763391833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19451117924705532702378221 7294169221764574763391833)
          ·
            refine ⟨5470626916323431072543875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7294169221764574763391833 5470626916323431072543875)
            ·
              refine ⟨8205940374485146608815813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5470626916323431072543875 8205940374485146608815813)
              ·
                refine ⟨1538613820215964989152965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8205940374485146608815813 1538613820215964989152965)
                ·
                  refine ⟨288490091290493435466181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1538613820215964989152965 288490091290493435466181)
                  ·
                    rfl

theorem cell22_2528246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_2528246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2528246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2528246 prefixEnd_2528246 := by exact prefixLift 2528246
  have htrace : WordTrace (prefixWord ++ tailWord_2528246) baseStart_2528246 baseEnd_2528246 := by
    simpa [prefixWord, tailWord_2528246, baseEnd_2528246] using wordTrace_append hprefix tailTrace_2528246
  have hstable : (prefixWord ++ tailWord_2528246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528246).length < 2 ^ (prefixWord ++ tailWord_2528246).sum := by decide
  have hdescent : baseEnd_2528246 < baseStart_2528246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528255 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 4, 7]
def baseStart_2528255 : Nat := 118140960795 + 2528255 * 2 ^ 59
def prefixEnd_2528255 : Nat := 4983230072969 + 3 ^ 40 * 2528255 * 2
def baseEnd_2528255 : Nat := 865473354755407282923515

theorem tailTrace_2528255 : CollatzResearch.WordTrace tailWord_2528255 prefixEnd_2528255 865473354755407282923515 := by
  unfold tailWord_2528255
  simp only [CollatzResearch.WordTrace]
  refine ⟨92213035455571401422426219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61475356970380934281617479 92213035455571401422426219)
  ·
    refine ⟨138319553183357102133639329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92213035455571401422426219 138319553183357102133639329)
    ·
      refine ⟨103739664887517826600229497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138319553183357102133639329 103739664887517826600229497)
      ·
        refine ⟨77804748665638369950172123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103739664887517826600229497 77804748665638369950172123)
        ·
          refine ⟨116707122998457554925258185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77804748665638369950172123 116707122998457554925258185)
          ·
            refine ⟨87530342248843166193943639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116707122998457554925258185 87530342248843166193943639)
            ·
              refine ⟨131295513373264749290915459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87530342248843166193943639 131295513373264749290915459)
              ·
                refine ⟨196943270059897123936373189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131295513373264749290915459 196943270059897123936373189)
                ·
                  refine ⟨36926863136230710738069973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 196943270059897123936373189 36926863136230710738069973)
                  ·
                    refine ⟨865473354755407282923515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36926863136230710738069973 865473354755407282923515)
                    ·
                      rfl

theorem cell22_2528255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 7].length) (baseStart_2528255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2528255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2528255 prefixEnd_2528255 := by exact prefixLift 2528255
  have htrace : WordTrace (prefixWord ++ tailWord_2528255) baseStart_2528255 baseEnd_2528255 := by
    simpa [prefixWord, tailWord_2528255, baseEnd_2528255] using wordTrace_append hprefix tailTrace_2528255
  have hstable : (prefixWord ++ tailWord_2528255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528255).length < 2 ^ (prefixWord ++ tailWord_2528255).sum := by decide
  have hdescent : baseEnd_2528255 < baseStart_2528255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528257 : List Nat := [1, 2, 4, 1, 2, 2, 3, 7]
def baseStart_2528257 : Nat := 118140960795 + 2528257 * 2 ^ 59
def prefixEnd_2528257 : Nat := 4983230072969 + 3 ^ 40 * 2528257 * 2
def baseEnd_2528257 : Nat := 96163782155142216041501

theorem tailTrace_2528257 : CollatzResearch.WordTrace tailWord_2528257 prefixEnd_2528257 96163782155142216041501 := by
  unfold tailWord_2528257
  simp only [CollatzResearch.WordTrace]
  refine ⟨92213108401564155763999025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61475405601042770509332683 92213108401564155763999025)
  ·
    refine ⟨69159831301173116822999269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92213108401564155763999025 69159831301173116822999269)
    ·
      refine ⟨12967468368969959404312363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69159831301173116822999269 12967468368969959404312363)
      ·
        refine ⟨19451202553454939106468545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12967468368969959404312363 19451202553454939106468545)
        ·
          refine ⟨14588401915091204329851409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19451202553454939106468545 14588401915091204329851409)
          ·
            refine ⟨10941301436318403247388557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14588401915091204329851409 10941301436318403247388557)
            ·
              refine ⟨4102988038619401217770709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10941301436318403247388557 4102988038619401217770709)
              ·
                refine ⟨96163782155142216041501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4102988038619401217770709 96163782155142216041501)
                ·
                  rfl

theorem cell22_2528257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 7].length) (baseStart_2528257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2528257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2528257 prefixEnd_2528257 := by exact prefixLift 2528257
  have htrace : WordTrace (prefixWord ++ tailWord_2528257) baseStart_2528257 baseEnd_2528257 := by
    simpa [prefixWord, tailWord_2528257, baseEnd_2528257] using wordTrace_append hprefix tailTrace_2528257
  have hstable : (prefixWord ++ tailWord_2528257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528257).length < 2 ^ (prefixWord ++ tailWord_2528257).sum := by decide
  have hdescent : baseEnd_2528257 < baseStart_2528257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528306 : List Nat := [3, 2, 1, 1, 2, 2, 1, 6, 1, 3]
def baseStart_2528306 : Nat := 118140960795 + 2528306 * 2 ^ 59
def prefixEnd_2528306 : Nat := 4983230072969 + 3 ^ 40 * 2528306 * 2
def baseEnd_2528306 : Nat := 865490813097660149898359

theorem tailTrace_2528306 : CollatzResearch.WordTrace tailWord_2528306 prefixEnd_2528306 865490813097660149898359 := by
  unfold tailWord_2528306
  simp only [CollatzResearch.WordTrace]
  refine ⟨23053723894596659283133193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61476597052257758088355181 23053723894596659283133193)
  ·
    refine ⟨17290292920947494462349895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23053723894596659283133193 17290292920947494462349895)
    ·
      refine ⟨25935439381421241693524843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17290292920947494462349895 25935439381421241693524843)
      ·
        refine ⟨38903159072131862540287265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25935439381421241693524843 38903159072131862540287265)
        ·
          refine ⟨29177369304098896905215449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38903159072131862540287265 29177369304098896905215449)
          ·
            refine ⟨21883026978074172678911587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29177369304098896905215449 21883026978074172678911587)
            ·
              refine ⟨32824540467111259018367381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21883026978074172678911587 32824540467111259018367381)
              ·
                refine ⟨1538650334395840266485971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32824540467111259018367381 1538650334395840266485971)
                ·
                  refine ⟨2307975501593760399728957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1538650334395840266485971 2307975501593760399728957)
                  ·
                    refine ⟨865490813097660149898359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2307975501593760399728957 865490813097660149898359)
                    ·
                      rfl

theorem cell22_2528306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 6, 1, 3].length) (baseStart_2528306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2528306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2528306 prefixEnd_2528306 := by exact prefixLift 2528306
  have htrace : WordTrace (prefixWord ++ tailWord_2528306) baseStart_2528306 baseEnd_2528306 := by
    simpa [prefixWord, tailWord_2528306, baseEnd_2528306] using wordTrace_append hprefix tailTrace_2528306
  have hstable : (prefixWord ++ tailWord_2528306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528306).length < 2 ^ (prefixWord ++ tailWord_2528306).sum := by decide
  have hdescent : baseEnd_2528306 < baseStart_2528306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528415 : List Nat := [1, 1, 2, 6, 2, 2, 2, 2, 4]
def baseStart_2528415 : Nat := 118140960795 + 2528415 * 2 ^ 59
def prefixEnd_2528415 : Nat := 4983230072969 + 3 ^ 40 * 2528415 * 2
def baseEnd_2528415 : Nat := 288509375341740066307675

theorem tailTrace_2528415 : CollatzResearch.WordTrace tailWord_2528415 prefixEnd_2528415 288509375341740066307675 := by
  unfold tailWord_2528415
  simp only [CollatzResearch.WordTrace]
  refine ⟨92218871134991748748250699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61479247423327832498833799 92218871134991748748250699)
  ·
    refine ⟨138328306702487623122376049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92218871134991748748250699 138328306702487623122376049)
    ·
      refine ⟨103746230026865717341782037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138328306702487623122376049 103746230026865717341782037)
      ·
        refine ⟨4863104532509330500396033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 103746230026865717341782037 4863104532509330500396033)
        ·
          refine ⟨3647328399381997875297025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4863104532509330500396033 3647328399381997875297025)
          ·
            refine ⟨2735496299536498406472769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3647328399381997875297025 2735496299536498406472769)
            ·
              refine ⟨2051622224652373804854577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2735496299536498406472769 2051622224652373804854577)
              ·
                refine ⟨1538716668489280353640933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2051622224652373804854577 1538716668489280353640933)
                ·
                  refine ⟨288509375341740066307675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1538716668489280353640933 288509375341740066307675)
                  ·
                    rfl

theorem cell22_2528415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 2, 4].length) (baseStart_2528415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2528415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2528415 prefixEnd_2528415 := by exact prefixLift 2528415
  have htrace : WordTrace (prefixWord ++ tailWord_2528415) baseStart_2528415 baseEnd_2528415 := by
    simpa [prefixWord, tailWord_2528415, baseEnd_2528415] using wordTrace_append hprefix tailTrace_2528415
  have hstable : (prefixWord ++ tailWord_2528415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528415).length < 2 ^ (prefixWord ++ tailWord_2528415).sum := by decide
  have hdescent : baseEnd_2528415 < baseStart_2528415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528426 : List Nat := [3, 1, 5, 1, 1, 1, 3, 7]
def baseStart_2528426 : Nat := 118140960795 + 2528426 * 2 ^ 59
def prefixEnd_2528426 : Nat := 4983230072969 + 3 ^ 40 * 2528426 * 2
def baseEnd_2528426 : Nat := 96170210172224426321999

theorem tailTrace_2528426 : CollatzResearch.WordTrace tailWord_2528426 prefixEnd_2528426 96170210172224426321999 := by
  unfold tailWord_2528426
  simp only [CollatzResearch.WordTrace]
  refine ⟨23054818084487974406725283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61479514891967931751267421 23054818084487974406725283)
  ·
    refine ⟨34582227126731961610087925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23054818084487974406725283 34582227126731961610087925)
    ·
      refine ⟨3242083793131121400945743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34582227126731961610087925 3242083793131121400945743)
      ·
        refine ⟨4863125689696682101418615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3242083793131121400945743 4863125689696682101418615)
        ·
          refine ⟨7294688534545023152127923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4863125689696682101418615 7294688534545023152127923)
          ·
            refine ⟨10942032801817534728191885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7294688534545023152127923 10942032801817534728191885)
            ·
              refine ⟨4103262300681575523071957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10942032801817534728191885 4103262300681575523071957)
              ·
                refine ⟨96170210172224426321999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4103262300681575523071957 96170210172224426321999)
                ·
                  rfl

theorem cell22_2528426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 7].length) (baseStart_2528426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2528426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2528426 prefixEnd_2528426 := by exact prefixLift 2528426
  have htrace : WordTrace (prefixWord ++ tailWord_2528426) baseStart_2528426 baseEnd_2528426 := by
    simpa [prefixWord, tailWord_2528426, baseEnd_2528426] using wordTrace_append hprefix tailTrace_2528426
  have hstable : (prefixWord ++ tailWord_2528426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528426).length < 2 ^ (prefixWord ++ tailWord_2528426).sum := by decide
  have hdescent : baseEnd_2528426 < baseStart_2528426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528441 : List Nat := [1, 2, 1, 4, 1, 4, 1, 2, 3, 3]
def baseStart_2528441 : Nat := 118140960795 + 2528441 * 2 ^ 59
def prefixEnd_2528441 : Nat := 4983230072969 + 3 ^ 40 * 2528441 * 2
def baseEnd_2528441 : Nat := 865537026356564797772945

theorem tailTrace_2528441 : CollatzResearch.WordTrace tailWord_2528441 prefixEnd_2528441 865537026356564797772945 := by
  unfold tailWord_2528441
  simp only [CollatzResearch.WordTrace]
  refine ⟨92219819432897555188697177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61479879621931703459131451 92219819432897555188697177)
  ·
    refine ⟨69164864574673166391522883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92219819432897555188697177 69164864574673166391522883)
    ·
      refine ⟨103747296862009749587284325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69164864574673166391522883 103747296862009749587284325)
      ·
        refine ⟨19452618161626828047615811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103747296862009749587284325 19452618161626828047615811)
        ·
          refine ⟨29178927242440242071423717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19452618161626828047615811 29178927242440242071423717)
          ·
            refine ⟨5471048857957545388391947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29178927242440242071423717 5471048857957545388391947)
            ·
              refine ⟨8206573286936318082587921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5471048857957545388391947 8206573286936318082587921)
              ·
                refine ⟨6154929965202238561940941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8206573286936318082587921 6154929965202238561940941)
                ·
                  refine ⟨2308098736950839460727853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6154929965202238561940941 2308098736950839460727853)
                  ·
                    refine ⟨865537026356564797772945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2308098736950839460727853 865537026356564797772945)
                    ·
                      rfl

theorem cell22_2528441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 3, 3].length) (baseStart_2528441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2528441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2528441 prefixEnd_2528441 := by exact prefixLift 2528441
  have htrace : WordTrace (prefixWord ++ tailWord_2528441) baseStart_2528441 baseEnd_2528441 := by
    simpa [prefixWord, tailWord_2528441, baseEnd_2528441] using wordTrace_append hprefix tailTrace_2528441
  have hstable : (prefixWord ++ tailWord_2528441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528441).length < 2 ^ (prefixWord ++ tailWord_2528441).sum := by decide
  have hdescent : baseEnd_2528441 < baseStart_2528441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528458 : List Nat := [3, 1, 2, 1, 3, 2, 1, 5, 1, 3]
def baseStart_2528458 : Nat := 118140960795 + 2528458 * 2 ^ 59
def prefixEnd_2528458 : Nat := 4983230072969 + 3 ^ 40 * 2528458 * 2
def baseEnd_2528458 : Nat := 865542845803982420097893

theorem tailTrace_2528458 : CollatzResearch.WordTrace tailWord_2528458 prefixEnd_2528458 865542845803982420097893 := by
  unfold tailWord_2528458
  simp only [CollatzResearch.WordTrace]
  refine ⟨23055109868458991773016507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61480292982557311394710685 23055109868458991773016507)
  ·
    refine ⟨34582664802688487659524761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23055109868458991773016507 34582664802688487659524761)
    ·
      refine ⟨25936998602016365744643571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34582664802688487659524761 25936998602016365744643571)
      ·
        refine ⟨38905497903024548616965357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25936998602016365744643571 38905497903024548616965357)
        ·
          refine ⟨14589561713634205731362009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38905497903024548616965357 14589561713634205731362009)
          ·
            refine ⟨10942171285225654298521507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14589561713634205731362009 10942171285225654298521507)
            ·
              refine ⟨16413256927838481447782261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10942171285225654298521507 16413256927838481447782261)
              ·
                refine ⟨1538742836984857635729587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16413256927838481447782261 1538742836984857635729587)
                ·
                  refine ⟨2308114255477286453594381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1538742836984857635729587 2308114255477286453594381)
                  ·
                    refine ⟨865542845803982420097893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2308114255477286453594381 865542845803982420097893)
                    ·
                      rfl

theorem cell22_2528458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 5, 1, 3].length) (baseStart_2528458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2528458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2528458 prefixEnd_2528458 := by exact prefixLift 2528458
  have htrace : WordTrace (prefixWord ++ tailWord_2528458) baseStart_2528458 baseEnd_2528458 := by
    simpa [prefixWord, tailWord_2528458, baseEnd_2528458] using wordTrace_append hprefix tailTrace_2528458
  have hstable : (prefixWord ++ tailWord_2528458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528458).length < 2 ^ (prefixWord ++ tailWord_2528458).sum := by decide
  have hdescent : baseEnd_2528458 < baseStart_2528458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528484 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 5, 4]
def baseStart_2528484 : Nat := 118140960795 + 2528484 * 2 ^ 59
def prefixEnd_2528484 : Nat := 4983230072969 + 3 ^ 40 * 2528484 * 2
def baseEnd_2528484 : Nat := 865551746135327018947813

theorem tailTrace_2528484 : CollatzResearch.WordTrace tailWord_2528484 prefixEnd_2528484 865551746135327018947813 := by
  unfold tailWord_2528484
  simp only [CollatzResearch.WordTrace]
  refine ⟨46110693885870886766256253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61480925181161182355008337 46110693885870886766256253)
  ·
    refine ⟨17291510207201582537346095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46110693885870886766256253 17291510207201582537346095)
    ·
      refine ⟨25937265310802373806019143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17291510207201582537346095 25937265310802373806019143)
      ·
        refine ⟨38905897966203560709028715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25937265310802373806019143 38905897966203560709028715)
        ·
          refine ⟨58358846949305341063543073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38905897966203560709028715 58358846949305341063543073)
          ·
            refine ⟨43769135211979005797657305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58358846949305341063543073 43769135211979005797657305)
            ·
              refine ⟨32826851408984254348242979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43769135211979005797657305 32826851408984254348242979)
              ·
                refine ⟨49240277113476381522364469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32826851408984254348242979 49240277113476381522364469)
                ·
                  refine ⟨4616275979388410767721669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49240277113476381522364469 4616275979388410767721669)
                  ·
                    refine ⟨865551746135327018947813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4616275979388410767721669 865551746135327018947813)
                    ·
                      rfl

theorem cell22_2528484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_2528484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2528484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2528484 prefixEnd_2528484 := by exact prefixLift 2528484
  have htrace : WordTrace (prefixWord ++ tailWord_2528484) baseStart_2528484 baseEnd_2528484 := by
    simpa [prefixWord, tailWord_2528484, baseEnd_2528484] using wordTrace_append hprefix tailTrace_2528484
  have hstable : (prefixWord ++ tailWord_2528484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528484).length < 2 ^ (prefixWord ++ tailWord_2528484).sum := by decide
  have hdescent : baseEnd_2528484 < baseStart_2528484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528499 : List Nat := [1, 1, 1, 2, 2, 5, 2, 2, 6]
def baseStart_2528499 : Nat := 118140960795 + 2528499 * 2 ^ 59
def prefixEnd_2528499 : Nat := 4983230072969 + 3 ^ 40 * 2528499 * 2
def baseEnd_2528499 : Nat := 288518960313957326607589

theorem tailTrace_2528499 : CollatzResearch.WordTrace tailWord_2528499 prefixEnd_2528499 288518960313957326607589 := by
  unfold tailWord_2528499
  simp only [CollatzResearch.WordTrace]
  refine ⟨92221934866687431094308551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61481289911124954062872367 92221934866687431094308551)
  ·
    refine ⟨138332902300031146641462827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92221934866687431094308551 138332902300031146641462827)
    ·
      refine ⟨207499353450046719962194241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138332902300031146641462827 207499353450046719962194241)
      ·
        refine ⟨155624515087535039971645681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207499353450046719962194241 155624515087535039971645681)
        ·
          refine ⟨116718386315651279978734261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155624515087535039971645681 116718386315651279978734261)
          ·
            refine ⟨10942348717092307498006337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 116718386315651279978734261 10942348717092307498006337)
            ·
              refine ⟨8206761537819230623504753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10942348717092307498006337 8206761537819230623504753)
              ·
                refine ⟨6155071153364422967628565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8206761537819230623504753 6155071153364422967628565)
                ·
                  refine ⟨288518960313957326607589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6155071153364422967628565 288518960313957326607589)
                  ·
                    rfl

theorem cell22_2528499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 6].length) (baseStart_2528499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2528499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2528499 prefixEnd_2528499 := by exact prefixLift 2528499
  have htrace : WordTrace (prefixWord ++ tailWord_2528499) baseStart_2528499 baseEnd_2528499 := by
    simpa [prefixWord, tailWord_2528499, baseEnd_2528499] using wordTrace_append hprefix tailTrace_2528499
  have hstable : (prefixWord ++ tailWord_2528499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528499).length < 2 ^ (prefixWord ++ tailWord_2528499).sum := by decide
  have hdescent : baseEnd_2528499 < baseStart_2528499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528548 : List Nat := [2, 3, 1, 3, 1, 1, 3, 3, 2, 3]
def baseStart_2528548 : Nat := 118140960795 + 2528548 * 2 ^ 59
def prefixEnd_2528548 : Nat := 4983230072969 + 3 ^ 40 * 2528548 * 2
def baseEnd_2528548 : Nat := 865573654643252185347617

theorem tailTrace_2528548 : CollatzResearch.WordTrace tailWord_2528548 prefixEnd_2528548 865573654643252185347617 := by
  unfold tailWord_2528548
  simp only [CollatzResearch.WordTrace]
  refine ⟨46111861021754956231421149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61482481362339941641894865 46111861021754956231421149)
  ·
    refine ⟨17291947883158108586782931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46111861021754956231421149 17291947883158108586782931)
    ·
      refine ⟨25937921824737162880174397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17291947883158108586782931 25937921824737162880174397)
      ·
        refine ⟨9726720684276436080065399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25937921824737162880174397 9726720684276436080065399)
        ·
          refine ⟨14590081026414654120098099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9726720684276436080065399 14590081026414654120098099)
          ·
            refine ⟨21885121539621981180147149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14590081026414654120098099 21885121539621981180147149)
            ·
              refine ⟨8206920577358242942555181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21885121539621981180147149 8206920577358242942555181)
              ·
                refine ⟨3077595216509341103458193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8206920577358242942555181 3077595216509341103458193)
                ·
                  refine ⟨2308196412382005827593645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3077595216509341103458193 2308196412382005827593645)
                  ·
                    refine ⟨865573654643252185347617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2308196412382005827593645 865573654643252185347617)
                    ·
                      rfl

theorem cell22_2528548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_2528548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2528548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2528548 prefixEnd_2528548 := by exact prefixLift 2528548
  have htrace : WordTrace (prefixWord ++ tailWord_2528548) baseStart_2528548 baseEnd_2528548 := by
    simpa [prefixWord, tailWord_2528548, baseEnd_2528548] using wordTrace_append hprefix tailTrace_2528548
  have hstable : (prefixWord ++ tailWord_2528548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528548).length < 2 ^ (prefixWord ++ tailWord_2528548).sum := by decide
  have hdescent : baseEnd_2528548 < baseStart_2528548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528651 : List Nat := [1, 1, 1, 1, 4, 3, 4, 1, 6]
def baseStart_2528651 : Nat := 118140960795 + 2528651 * 2 ^ 59
def prefixEnd_2528651 : Nat := 4983230072969 + 3 ^ 40 * 2528651 * 2
def baseEnd_2528651 : Nat := 288536304549398083340767

theorem tailTrace_2528651 : CollatzResearch.WordTrace tailWord_2528651 prefixEnd_2528651 288536304549398083340767 := by
  unfold tailWord_2528651
  simp only [CollatzResearch.WordTrace]
  refine ⟨92227478762136761053841807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61484985841424507369227871 92227478762136761053841807)
  ·
    refine ⟨138341218143205141580762711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92227478762136761053841807 138341218143205141580762711)
    ·
      refine ⟨207511827214807712371144067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138341218143205141580762711 207511827214807712371144067)
      ·
        refine ⟨311267740822211568556716101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207511827214807712371144067 311267740822211568556716101)
        ·
          refine ⟨58362701404164669104384269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 311267740822211568556716101 58362701404164669104384269)
          ·
            refine ⟨21886013026561750914144101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58362701404164669104384269 21886013026561750914144101)
            ·
              refine ⟨4103627442480328296402019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21886013026561750914144101 4103627442480328296402019)
              ·
                refine ⟨6155441163720492444603029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4103627442480328296402019 6155441163720492444603029)
                ·
                  refine ⟨288536304549398083340767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6155441163720492444603029 288536304549398083340767)
                  ·
                    rfl

theorem cell22_2528651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 6].length) (baseStart_2528651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2528651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2528651 prefixEnd_2528651 := by exact prefixLift 2528651
  have htrace : WordTrace (prefixWord ++ tailWord_2528651) baseStart_2528651 baseEnd_2528651 := by
    simpa [prefixWord, tailWord_2528651, baseEnd_2528651] using wordTrace_append hprefix tailTrace_2528651
  have hstable : (prefixWord ++ tailWord_2528651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528651).length < 2 ^ (prefixWord ++ tailWord_2528651).sum := by decide
  have hdescent : baseEnd_2528651 < baseStart_2528651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528728 : List Nat := [2, 1, 2, 2, 2, 1, 2, 4, 3, 3]
def baseStart_2528728 : Nat := 118140960795 + 2528728 * 2 ^ 59
def prefixEnd_2528728 : Nat := 4983230072969 + 3 ^ 40 * 2528728 * 2
def baseEnd_2528728 : Nat := 865635272321791715847065

theorem tailTrace_2528728 : CollatzResearch.WordTrace tailWord_2528728 prefixEnd_2528728 865635272321791715847065 := by
  unfold tailWord_2528728
  simp only [CollatzResearch.WordTrace]
  refine ⟨46115143591428901602197419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61486858121905202136263225 46115143591428901602197419)
  ·
    refine ⟨69172715387143352403296129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46115143591428901602197419 69172715387143352403296129)
    ·
      refine ⟨51879536540357514302472097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69172715387143352403296129 51879536540357514302472097)
      ·
        refine ⟨38909652405268135726854073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51879536540357514302472097 38909652405268135726854073)
        ·
          refine ⟨29182239303951101795140555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38909652405268135726854073 29182239303951101795140555)
          ·
            refine ⟨43773358955926652692710833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29182239303951101795140555 43773358955926652692710833)
            ·
              refine ⟨32830019216944989519533125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43773358955926652692710833 32830019216944989519533125)
              ·
                refine ⟨6155628603177185534912461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32830019216944989519533125 6155628603177185534912461)
                ·
                  refine ⟨2308360726191444575592173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6155628603177185534912461 2308360726191444575592173)
                  ·
                    refine ⟨865635272321791715847065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2308360726191444575592173 865635272321791715847065)
                    ·
                      rfl

theorem cell22_2528728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 3, 3].length) (baseStart_2528728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2528728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2528728 prefixEnd_2528728 := by exact prefixLift 2528728
  have htrace : WordTrace (prefixWord ++ tailWord_2528728) baseStart_2528728 baseEnd_2528728 := by
    simpa [prefixWord, tailWord_2528728, baseEnd_2528728] using wordTrace_append hprefix tailTrace_2528728
  have hstable : (prefixWord ++ tailWord_2528728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528728).length < 2 ^ (prefixWord ++ tailWord_2528728).sum := by decide
  have hdescent : baseEnd_2528728 < baseStart_2528728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528833 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 3, 6]
def baseStart_2528833 : Nat := 118140960795 + 2528833 * 2 ^ 59
def prefixEnd_2528833 : Nat := 4983230072969 + 3 ^ 40 * 2528833 * 2
def baseEnd_2528833 : Nat := 865671215967606441971743

theorem tailTrace_2528833 : CollatzResearch.WordTrace tailWord_2528833 prefixEnd_2528833 865671215967606441971743 := by
  unfold tailWord_2528833
  simp only [CollatzResearch.WordTrace]
  refine ⟨92234116847477406136967153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61489411231651604091311435 92234116847477406136967153)
  ·
    refine ⟨69175587635608054602725365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92234116847477406136967153 69175587635608054602725365)
    ·
      refine ⟨6485211340838255119005503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69175587635608054602725365 6485211340838255119005503)
      ·
        refine ⟨9727817011257382678508255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6485211340838255119005503 9727817011257382678508255)
        ·
          refine ⟨14591725516886074017762383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9727817011257382678508255 14591725516886074017762383)
          ·
            refine ⟨21887588275329111026643575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14591725516886074017762383 21887588275329111026643575)
            ·
              refine ⟨32831382412993666539965363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21887588275329111026643575 32831382412993666539965363)
              ·
                refine ⟨49247073619490499809948045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32831382412993666539965363 49247073619490499809948045)
                ·
                  refine ⟨18467652607308937428730517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49247073619490499809948045 18467652607308937428730517)
                  ·
                    refine ⟨865671215967606441971743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18467652607308937428730517 865671215967606441971743)
                    ·
                      rfl

theorem cell22_2528833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_2528833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2528833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2528833 prefixEnd_2528833 := by exact prefixLift 2528833
  have htrace : WordTrace (prefixWord ++ tailWord_2528833) baseStart_2528833 baseEnd_2528833 := by
    simpa [prefixWord, tailWord_2528833, baseEnd_2528833] using wordTrace_append hprefix tailTrace_2528833
  have hstable : (prefixWord ++ tailWord_2528833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528833).length < 2 ^ (prefixWord ++ tailWord_2528833).sum := by decide
  have hdescent : baseEnd_2528833 < baseStart_2528833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528886 : List Nat := [5, 1, 1, 2, 2, 3, 2, 1, 2, 3]
def baseStart_2528886 : Nat := 118140960795 + 2528886 * 2 ^ 59
def prefixEnd_2528886 : Nat := 4983230072969 + 3 ^ 40 * 2528886 * 2
def baseEnd_2528886 : Nat := 865689358950731970396581

theorem tailTrace_2528886 : CollatzResearch.WordTrace tailWord_2528886 prefixEnd_2528886 865689358950731970396581 := by
  unfold tailWord_2528886
  simp only [CollatzResearch.WordTrace]
  refine ⟨5764753119767837261790407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61490699944190264125764341 5764753119767837261790407)
  ·
    refine ⟨8647129679651755892685611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5764753119767837261790407 8647129679651755892685611)
    ·
      refine ⟨12970694519477633839028417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8647129679651755892685611 12970694519477633839028417)
      ·
        refine ⟨9728020889608225379271313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12970694519477633839028417 9728020889608225379271313)
        ·
          refine ⟨7296015667206169034453485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9728020889608225379271313 7296015667206169034453485)
          ·
            refine ⟨2736005875202313387920057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7296015667206169034453485 2736005875202313387920057)
            ·
              refine ⟨2052004406401735040940043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2736005875202313387920057 2052004406401735040940043)
              ·
                refine ⟨3078006609602602561410065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2052004406401735040940043 3078006609602602561410065)
                ·
                  refine ⟨2308504957201951921057549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3078006609602602561410065 2308504957201951921057549)
                  ·
                    refine ⟨865689358950731970396581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2308504957201951921057549 865689358950731970396581)
                    ·
                      rfl

theorem cell22_2528886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_2528886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2528886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2528886 prefixEnd_2528886 := by exact prefixLift 2528886
  have htrace : WordTrace (prefixWord ++ tailWord_2528886) baseStart_2528886 baseEnd_2528886 := by
    simpa [prefixWord, tailWord_2528886, baseEnd_2528886] using wordTrace_append hprefix tailTrace_2528886
  have hstable : (prefixWord ++ tailWord_2528886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528886).length < 2 ^ (prefixWord ++ tailWord_2528886).sum := by decide
  have hdescent : baseEnd_2528886 < baseStart_2528886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528983 : List Nat := [1, 1, 3, 2, 1, 3, 11]
def baseStart_2528983 : Nat := 118140960795 + 2528983 * 2 ^ 59
def prefixEnd_2528983 : Nat := 4983230072969 + 3 ^ 40 * 2528983 * 2
def baseEnd_2528983 : Nat := 32063798667890964841529

theorem tailTrace_2528983 : CollatzResearch.WordTrace tailWord_2528983 prefixEnd_2528983 32063798667890964841529 := by
  unfold tailWord_2528983
  simp only [CollatzResearch.WordTrace]
  refine ⟨92239587796933981754927603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61493058531289321169951735 92239587796933981754927603)
  ·
    refine ⟨138359381695400972632391405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92239587796933981754927603 138359381695400972632391405)
    ·
      refine ⟨51884768135775364737146777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138359381695400972632391405 51884768135775364737146777)
      ·
        refine ⟨38913576101831523552860083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51884768135775364737146777 38913576101831523552860083)
        ·
          refine ⟨58370364152747285329290125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38913576101831523552860083 58370364152747285329290125)
          ·
            refine ⟨21888886557280231998483797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58370364152747285329290125 21888886557280231998483797)
            ·
              refine ⟨32063798667890964841529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 21888886557280231998483797 32063798667890964841529)
              ·
                rfl

theorem cell22_2528983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 11].length) (baseStart_2528983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2528983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2528983 prefixEnd_2528983 := by exact prefixLift 2528983
  have htrace : WordTrace (prefixWord ++ tailWord_2528983) baseStart_2528983 baseEnd_2528983 := by
    simpa [prefixWord, tailWord_2528983, baseEnd_2528983] using wordTrace_append hprefix tailTrace_2528983
  have hstable : (prefixWord ++ tailWord_2528983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528983).length < 2 ^ (prefixWord ++ tailWord_2528983).sum := by decide
  have hdescent : baseEnd_2528983 < baseStart_2528983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2528989 : List Nat := [1, 4, 3, 3, 1, 1, 2, 1, 6]
def baseStart_2528989 : Nat := 118140960795 + 2528989 * 2 ^ 59
def prefixEnd_2528989 : Nat := 4983230072969 + 3 ^ 40 * 2528989 * 2
def baseEnd_2528989 : Nat := 288574872651891345023755

theorem tailTrace_2528989 : CollatzResearch.WordTrace tailWord_2528989 prefixEnd_2528989 288574872651891345023755 := by
  unfold tailWord_2528989
  simp only [CollatzResearch.WordTrace]
  refine ⟨92239806634912244779646021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61493204423274829853097347 92239806634912244779646021)
  ·
    refine ⟨17294963744046045896183629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92239806634912244779646021 17294963744046045896183629)
    ·
      refine ⟨6485611404017267211068861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17294963744046045896183629 6485611404017267211068861)
      ·
        refine ⟨2432104276506475204150823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6485611404017267211068861 2432104276506475204150823)
        ·
          refine ⟨3648156414759712806226235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2432104276506475204150823 3648156414759712806226235)
          ·
            refine ⟨5472234622139569209339353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3648156414759712806226235 5472234622139569209339353)
            ·
              refine ⟨4104175966604676907004515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5472234622139569209339353 4104175966604676907004515)
              ·
                refine ⟨6156263949907015360506773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4104175966604676907004515 6156263949907015360506773)
                ·
                  refine ⟨288574872651891345023755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6156263949907015360506773 288574872651891345023755)
                  ·
                    rfl

theorem cell22_2528989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_2528989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2528989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2528989 prefixEnd_2528989 := by exact prefixLift 2528989
  have htrace : WordTrace (prefixWord ++ tailWord_2528989) baseStart_2528989 baseEnd_2528989 := by
    simpa [prefixWord, tailWord_2528989, baseEnd_2528989] using wordTrace_append hprefix tailTrace_2528989
  have hstable : (prefixWord ++ tailWord_2528989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2528989).length < 2 ^ (prefixWord ++ tailWord_2528989).sum := by decide
  have hdescent : baseEnd_2528989 < baseStart_2528989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2528989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529045 : List Nat := [1, 3, 2, 1, 2, 3, 2, 1, 7]
def baseStart_2529045 : Nat := 118140960795 + 2529045 * 2 ^ 59
def prefixEnd_2529045 : Nat := 4983230072969 + 3 ^ 40 * 2529045 * 2
def baseEnd_2529045 : Nat := 288581262633369518557031

theorem tailTrace_2529045 : CollatzResearch.WordTrace tailWord_2529045 prefixEnd_2529045 288581262633369518557031 := by
  unfold tailWord_2529045
  simp only [CollatzResearch.WordTrace]
  refine ⟨92241849122709366343684589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61494566081806244229123059 92241849122709366343684589)
  ·
    refine ⟨34590693421016012378881721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92241849122709366343684589 34590693421016012378881721)
    ·
      refine ⟨25943020065762009284161291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34590693421016012378881721 25943020065762009284161291)
      ·
        refine ⟨38914530098643013926241937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25943020065762009284161291 38914530098643013926241937)
        ·
          refine ⟨29185897573982260444681453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38914530098643013926241937 29185897573982260444681453)
          ·
            refine ⟨10944711590243347666755545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29185897573982260444681453 10944711590243347666755545)
            ·
              refine ⟨8208533692682510750066659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10944711590243347666755545 8208533692682510750066659)
              ·
                refine ⟨12312800539023766125099989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8208533692682510750066659 12312800539023766125099989)
                ·
                  refine ⟨288581262633369518557031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12312800539023766125099989 288581262633369518557031)
                  ·
                    rfl

theorem cell22_2529045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 7].length) (baseStart_2529045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2529045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2529045 prefixEnd_2529045 := by exact prefixLift 2529045
  have htrace : WordTrace (prefixWord ++ tailWord_2529045) baseStart_2529045 baseEnd_2529045 := by
    simpa [prefixWord, tailWord_2529045, baseEnd_2529045] using wordTrace_append hprefix tailTrace_2529045
  have hstable : (prefixWord ++ tailWord_2529045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529045).length < 2 ^ (prefixWord ++ tailWord_2529045).sum := by decide
  have hdescent : baseEnd_2529045 < baseStart_2529045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529100 : List Nat := [2, 2, 1, 3, 5, 1, 2, 2, 1, 3]
def baseStart_2529100 : Nat := 118140960795 + 2529100 * 2 ^ 59
def prefixEnd_2529100 : Nat := 4983230072969 + 3 ^ 40 * 2529100 * 2
def baseEnd_2529100 : Nat := 865762615524106745545925

theorem tailTrace_2529100 : CollatzResearch.WordTrace tailWord_2529100 prefixEnd_2529100 865762615524106745545925 := by
  unfold tailWord_2529100
  simp only [CollatzResearch.WordTrace]
  refine ⟨46121927568755055368468377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61495903425006740491291169 46121927568755055368468377)
  ·
    refine ⟨34591445676566291526351283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46121927568755055368468377 34591445676566291526351283)
    ·
      refine ⟨51887168514849437289526925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34591445676566291526351283 51887168514849437289526925)
      ·
        refine ⟨19457688193068538983572597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51887168514849437289526925 19457688193068538983572597)
        ·
          refine ⟨1824158268100175529709931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19457688193068538983572597 1824158268100175529709931)
          ·
            refine ⟨2736237402150263294564897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1824158268100175529709931 2736237402150263294564897)
            ·
              refine ⟨2052178051612697470923673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2736237402150263294564897 2052178051612697470923673)
              ·
                refine ⟨1539133538709523103192755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2052178051612697470923673 1539133538709523103192755)
                ·
                  refine ⟨2308700308064284654789133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1539133538709523103192755 2308700308064284654789133)
                  ·
                    refine ⟨865762615524106745545925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2308700308064284654789133 865762615524106745545925)
                    ·
                      rfl

theorem cell22_2529100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 2, 1, 3].length) (baseStart_2529100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2529100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2529100 prefixEnd_2529100 := by exact prefixLift 2529100
  have htrace : WordTrace (prefixWord ++ tailWord_2529100) baseStart_2529100 baseEnd_2529100 := by
    simpa [prefixWord, tailWord_2529100, baseEnd_2529100] using wordTrace_append hprefix tailTrace_2529100
  have hstable : (prefixWord ++ tailWord_2529100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529100).length < 2 ^ (prefixWord ++ tailWord_2529100).sum := by decide
  have hdescent : baseEnd_2529100 < baseStart_2529100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529186 : List Nat := [3, 3, 1, 2, 3, 2, 2, 6]
def baseStart_2529186 : Nat := 118140960795 + 2529186 * 2 ^ 59
def prefixEnd_2529186 : Nat := 4983230072969 + 3 ^ 40 * 2529186 * 2
def baseEnd_2529186 : Nat := 96199117231292354210629

theorem tailTrace_2529186 : CollatzResearch.WordTrace tailWord_2529186 prefixEnd_2529186 96199117231292354210629 := by
  unfold tailWord_2529186
  simp only [CollatzResearch.WordTrace]
  refine ⟨23061747953799636856141853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61497994543465698283044941 23061747953799636856141853)
  ·
    refine ⟨8648155482674863821053195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23061747953799636856141853 8648155482674863821053195)
    ·
      refine ⟨12972233224012295731579793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8648155482674863821053195 12972233224012295731579793)
      ·
        refine ⟨9729174918009221798684845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12972233224012295731579793 9729174918009221798684845)
        ·
          refine ⟨3648440594253458174506817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9729174918009221798684845 3648440594253458174506817)
          ·
            refine ⟨2736330445690093630880113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3648440594253458174506817 2736330445690093630880113)
            ·
              refine ⟨2052247834267570223160085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2736330445690093630880113 2052247834267570223160085)
              ·
                refine ⟨96199117231292354210629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2052247834267570223160085 96199117231292354210629)
                ·
                  rfl

theorem cell22_2529186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 6].length) (baseStart_2529186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2529186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2529186 prefixEnd_2529186 := by exact prefixLift 2529186
  have htrace : WordTrace (prefixWord ++ tailWord_2529186) baseStart_2529186 baseEnd_2529186 := by
    simpa [prefixWord, tailWord_2529186, baseEnd_2529186] using wordTrace_append hprefix tailTrace_2529186
  have hstable : (prefixWord ++ tailWord_2529186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529186).length < 2 ^ (prefixWord ++ tailWord_2529186).sum := by decide
  have hdescent : baseEnd_2529186 < baseStart_2529186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529227 : List Nat := [1, 1, 1, 1, 3, 4, 2, 2, 3, 4]
def baseStart_2529227 : Nat := 118140960795 + 2529227 * 2 ^ 59
def prefixEnd_2529227 : Nat := 4983230072969 + 3 ^ 40 * 2529227 * 2
def baseEnd_2529227 : Nat := 865806090219520747620535

theorem tailTrace_2529227 : CollatzResearch.WordTrace tailWord_2529227 prefixEnd_2529227 865806090219520747620535 := by
  unfold tailWord_2529227
  simp only [CollatzResearch.WordTrace]
  refine ⟨92248487208050011426809935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61498991472033340951206623 92248487208050011426809935)
  ·
    refine ⟨138372730812075017140214903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92248487208050011426809935 138372730812075017140214903)
    ·
      refine ⟨207559096218112525710322355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138372730812075017140214903 207559096218112525710322355)
      ·
        refine ⟨311338644327168788565483533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207559096218112525710322355 311338644327168788565483533)
        ·
          refine ⟨116751991622688295712056325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 311338644327168788565483533 116751991622688295712056325)
          ·
            refine ⟨21890998429254055446010561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116751991622688295712056325 21890998429254055446010561)
            ·
              refine ⟨16418248821940541584507921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21890998429254055446010561 16418248821940541584507921)
              ·
                refine ⟨12313686616455406188380941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16418248821940541584507921 12313686616455406188380941)
                ·
                  refine ⟨4617632481170777320642853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12313686616455406188380941 4617632481170777320642853)
                  ·
                    refine ⟨865806090219520747620535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4617632481170777320642853 865806090219520747620535)
                    ·
                      rfl

theorem cell22_2529227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 4].length) (baseStart_2529227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2529227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2529227 prefixEnd_2529227 := by exact prefixLift 2529227
  have htrace : WordTrace (prefixWord ++ tailWord_2529227) baseStart_2529227 baseEnd_2529227 := by
    simpa [prefixWord, tailWord_2529227, baseEnd_2529227] using wordTrace_append hprefix tailTrace_2529227
  have hstable : (prefixWord ++ tailWord_2529227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529227).length < 2 ^ (prefixWord ++ tailWord_2529227).sum := by decide
  have hdescent : baseEnd_2529227 < baseStart_2529227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529304 : List Nat := [2, 1, 2, 3, 2, 1, 5, 6]
def baseStart_2529304 : Nat := 118140960795 + 2529304 * 2 ^ 59
def prefixEnd_2529304 : Nat := 4983230072969 + 3 ^ 40 * 2529304 * 2
def baseEnd_2529304 : Nat := 96203605432568690382811

theorem tailTrace_2529304 : CollatzResearch.WordTrace tailWord_2529304 prefixEnd_2529304 96203605432568690382811 := by
  unfold tailWord_2529304
  simp only [CollatzResearch.WordTrace]
  refine ⟨46125647814385526788681483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61500863752514035718241977 46125647814385526788681483)
  ·
    refine ⟨69188471721578290183022225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46125647814385526788681483 69188471721578290183022225)
    ·
      refine ⟨51891353791183717637266669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69188471721578290183022225 51891353791183717637266669)
      ·
        refine ⟨19459257671693894113975001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51891353791183717637266669 19459257671693894113975001)
        ·
          refine ⟨14594443253770420585481251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19459257671693894113975001 14594443253770420585481251)
          ·
            refine ⟨21891664880655630878221877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14594443253770420585481251 21891664880655630878221877)
            ·
              refine ⟨2052343582561465394833301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21891664880655630878221877 2052343582561465394833301)
              ·
                refine ⟨96203605432568690382811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2052343582561465394833301 96203605432568690382811)
                ·
                  rfl

theorem cell22_2529304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 6].length) (baseStart_2529304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2529304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2529304 prefixEnd_2529304 := by exact prefixLift 2529304
  have htrace : WordTrace (prefixWord ++ tailWord_2529304) baseStart_2529304 baseEnd_2529304 := by
    simpa [prefixWord, tailWord_2529304, baseEnd_2529304] using wordTrace_append hprefix tailTrace_2529304
  have hstable : (prefixWord ++ tailWord_2529304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529304).length < 2 ^ (prefixWord ++ tailWord_2529304).sum := by decide
  have hdescent : baseEnd_2529304 < baseStart_2529304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529306 : List Nat := [3, 1, 1, 3, 1, 5, 1, 1, 2, 4]
def baseStart_2529306 : Nat := 118140960795 + 2529306 * 2 ^ 59
def prefixEnd_2529306 : Nat := 4983230072969 + 3 ^ 40 * 2529306 * 2
def baseEnd_2529306 : Nat := 865833133533990874895293

theorem tailTrace_2529306 : CollatzResearch.WordTrace tailWord_2529306 prefixEnd_2529306 865833133533990874895293 := by
  unfold tailWord_2529306
  simp only [CollatzResearch.WordTrace]
  refine ⟨23062842143690951979733943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61500912383175871945957181 23062842143690951979733943)
  ·
    refine ⟨34594263215536427969600915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23062842143690951979733943 34594263215536427969600915)
    ·
      refine ⟨51891394823304641954401373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34594263215536427969600915 51891394823304641954401373)
      ·
        refine ⟨19459273058739240732900515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51891394823304641954401373 19459273058739240732900515)
        ·
          refine ⟨29188909588108861099350773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19459273058739240732900515 29188909588108861099350773)
          ·
            refine ⟨2736460273885205728064135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29188909588108861099350773 2736460273885205728064135)
            ·
              refine ⟨4104690410827808592096203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2736460273885205728064135 4104690410827808592096203)
              ·
                refine ⟨6157035616241712888144305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4104690410827808592096203 6157035616241712888144305)
                ·
                  refine ⟨4617776712181284666108229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6157035616241712888144305 4617776712181284666108229)
                  ·
                    refine ⟨865833133533990874895293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4617776712181284666108229 865833133533990874895293)
                    ·
                      rfl

theorem cell22_2529306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 1, 2, 4].length) (baseStart_2529306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2529306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2529306 prefixEnd_2529306 := by exact prefixLift 2529306
  have htrace : WordTrace (prefixWord ++ tailWord_2529306) baseStart_2529306 baseEnd_2529306 := by
    simpa [prefixWord, tailWord_2529306, baseEnd_2529306] using wordTrace_append hprefix tailTrace_2529306
  have hstable : (prefixWord ++ tailWord_2529306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529306).length < 2 ^ (prefixWord ++ tailWord_2529306).sum := by decide
  have hdescent : baseEnd_2529306 < baseStart_2529306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529347 : List Nat := [1, 1, 1, 3, 1, 2, 2, 3, 1, 7]
def baseStart_2529347 : Nat := 118140960795 + 2529347 * 2 ^ 59
def prefixEnd_2529347 : Nat := 4983230072969 + 3 ^ 40 * 2529347 * 2
def baseEnd_2529347 : Nat := 865847168671880434620167

theorem tailTrace_2529347 : CollatzResearch.WordTrace tailWord_2529347 prefixEnd_2529347 865847168671880434620167 := by
  unfold tailWord_2529347
  simp only [CollatzResearch.WordTrace]
  refine ⟨92252863967615271921178295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61501909311743514614118863 92252863967615271921178295)
  ·
    refine ⟨138379295951422907881767443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92252863967615271921178295 138379295951422907881767443)
    ·
      refine ⟨207568943927134361822651165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138379295951422907881767443 207568943927134361822651165)
      ·
        refine ⟨77838353972675385683494187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207568943927134361822651165 77838353972675385683494187)
        ·
          refine ⟨116757530959013078525241281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77838353972675385683494187 116757530959013078525241281)
          ·
            refine ⟨87568148219259808893930961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116757530959013078525241281 87568148219259808893930961)
            ·
              refine ⟨65676111164444856670448221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87568148219259808893930961 65676111164444856670448221)
              ·
                refine ⟨24628541686666821251418083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65676111164444856670448221 24628541686666821251418083)
                ·
                  refine ⟨36942812530000231877127125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24628541686666821251418083 36942812530000231877127125)
                  ·
                    refine ⟨865847168671880434620167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36942812530000231877127125 865847168671880434620167)
                    ·
                      rfl

theorem cell22_2529347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 7].length) (baseStart_2529347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2529347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2529347 prefixEnd_2529347 := by exact prefixLift 2529347
  have htrace : WordTrace (prefixWord ++ tailWord_2529347) baseStart_2529347 baseEnd_2529347 := by
    simpa [prefixWord, tailWord_2529347, baseEnd_2529347] using wordTrace_append hprefix tailTrace_2529347
  have hstable : (prefixWord ++ tailWord_2529347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529347).length < 2 ^ (prefixWord ++ tailWord_2529347).sum := by decide
  have hdescent : baseEnd_2529347 < baseStart_2529347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529413 : List Nat := [1, 3, 1, 1, 5, 3, 1, 2, 1, 4]
def baseStart_2529413 : Nat := 118140960795 + 2529413 * 2 ^ 59
def prefixEnd_2529413 : Nat := 4983230072969 + 3 ^ 40 * 2529413 * 2
def baseEnd_2529413 : Nat := 865869761820678262469965

theorem tailTrace_2529413 : CollatzResearch.WordTrace tailWord_2529413 prefixEnd_2529413 865869761820678262469965 := by
  unfold tailWord_2529413
  simp only [CollatzResearch.WordTrace]
  refine ⟨92255271185376165193080893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61503514123584110128720595 92255271185376165193080893)
  ·
    refine ⟨34595726694516061947405335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92255271185376165193080893 34595726694516061947405335)
    ·
      refine ⟨51893590041774092921108003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34595726694516061947405335 51893590041774092921108003)
      ·
        refine ⟨77840385062661139381662005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51893590041774092921108003 77840385062661139381662005)
        ·
          refine ⟨7297536099624481817030813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77840385062661139381662005 7297536099624481817030813)
          ·
            refine ⟨2736576037359180681386555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7297536099624481817030813 2736576037359180681386555)
            ·
              refine ⟨4104864056038771022079833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2736576037359180681386555 4104864056038771022079833)
              ·
                refine ⟨3078648042029078266559875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4104864056038771022079833 3078648042029078266559875)
                ·
                  refine ⟨4617972063043617399839813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3078648042029078266559875 4617972063043617399839813)
                  ·
                    refine ⟨865869761820678262469965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4617972063043617399839813 865869761820678262469965)
                    ·
                      rfl

theorem cell22_2529413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 4].length) (baseStart_2529413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2529413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2529413 prefixEnd_2529413 := by exact prefixLift 2529413
  have htrace : WordTrace (prefixWord ++ tailWord_2529413) baseStart_2529413 baseEnd_2529413 := by
    simpa [prefixWord, tailWord_2529413, baseEnd_2529413] using wordTrace_append hprefix tailTrace_2529413
  have hstable : (prefixWord ++ tailWord_2529413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529413).length < 2 ^ (prefixWord ++ tailWord_2529413).sum := by decide
  have hdescent : baseEnd_2529413 < baseStart_2529413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529426 : List Nat := [3, 2, 3, 1, 1, 1, 3, 2, 1, 5]
def baseStart_2529426 : Nat := 118140960795 + 2529426 * 2 ^ 59
def prefixEnd_2529426 : Nat := 4983230072969 + 3 ^ 40 * 2529426 * 2
def baseEnd_2529426 : Nat := 865874211986350561894925

theorem tailTrace_2529426 : CollatzResearch.WordTrace tailWord_2529426 prefixEnd_2529426 865874211986350561894925 := by
  unfold tailWord_2529426
  simp only [CollatzResearch.WordTrace]
  refine ⟨23063936333582267103326033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61503830222886045608869421 23063936333582267103326033)
  ·
    refine ⟨17297952250186700327494525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23063936333582267103326033 17297952250186700327494525)
    ·
      refine ⟨6486732093820012622810447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17297952250186700327494525 6486732093820012622810447)
      ·
        refine ⟨9730098140730018934215671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6486732093820012622810447 9730098140730018934215671)
        ·
          refine ⟨14595147211095028401323507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9730098140730018934215671 14595147211095028401323507)
          ·
            refine ⟨21892720816642542601985261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14595147211095028401323507 21892720816642542601985261)
            ·
              refine ⟨8209770306240953475744473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21892720816642542601985261 8209770306240953475744473)
              ·
                refine ⟨6157327729680715106808355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8209770306240953475744473 6157327729680715106808355)
                ·
                  refine ⟨9235991594521072660212533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6157327729680715106808355 9235991594521072660212533)
                  ·
                    refine ⟨865874211986350561894925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9235991594521072660212533 865874211986350561894925)
                    ·
                      rfl

theorem cell22_2529426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_2529426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2529426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2529426 prefixEnd_2529426 := by exact prefixLift 2529426
  have htrace : WordTrace (prefixWord ++ tailWord_2529426) baseStart_2529426 baseEnd_2529426 := by
    simpa [prefixWord, tailWord_2529426, baseEnd_2529426] using wordTrace_append hprefix tailTrace_2529426
  have hstable : (prefixWord ++ tailWord_2529426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529426).length < 2 ^ (prefixWord ++ tailWord_2529426).sum := by decide
  have hdescent : baseEnd_2529426 < baseStart_2529426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529439 : List Nat := [1, 1, 2, 6, 1, 11]
def baseStart_2529439 : Nat := 118140960795 + 2529439 * 2 ^ 59
def prefixEnd_2529439 : Nat := 4983230072969 + 3 ^ 40 * 2529439 * 2
def baseEnd_2529439 : Nat := 10689860026568183473085

theorem tailTrace_2529439 : CollatzResearch.WordTrace tailWord_2529439 prefixEnd_2529439 10689860026568183473085 := by
  unfold tailWord_2529439
  simp only [CollatzResearch.WordTrace]
  refine ⟨92256219483281971633527371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61504146322187981089018247 92256219483281971633527371)
  ·
    refine ⟨138384329224922957450291057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92256219483281971633527371 138384329224922957450291057)
    ·
      refine ⟨103788246918692218087718293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138384329224922957450291057 103788246918692218087718293)
      ·
        refine ⟨4865074074313697722861795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 103788246918692218087718293 4865074074313697722861795)
        ·
          refine ⟨7297611111470546584292693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4865074074313697722861795 7297611111470546584292693)
          ·
            refine ⟨10689860026568183473085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7297611111470546584292693 10689860026568183473085)
            ·
              rfl

theorem cell22_2529439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 11].length) (baseStart_2529439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2529439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2529439 prefixEnd_2529439 := by exact prefixLift 2529439
  have htrace : WordTrace (prefixWord ++ tailWord_2529439) baseStart_2529439 baseEnd_2529439 := by
    simpa [prefixWord, tailWord_2529439, baseEnd_2529439] using wordTrace_append hprefix tailTrace_2529439
  have hstable : (prefixWord ++ tailWord_2529439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529439).length < 2 ^ (prefixWord ++ tailWord_2529439).sum := by decide
  have hdescent : baseEnd_2529439 < baseStart_2529439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529441 : List Nat := [1, 2, 3, 3, 1, 2, 2, 2, 2, 4]
def baseStart_2529441 : Nat := 118140960795 + 2529441 * 2 ^ 59
def prefixEnd_2529441 : Nat := 4983230072969 + 3 ^ 40 * 2529441 * 2
def baseEnd_2529441 : Nat := 865879346792895522769879

theorem tailTrace_2529441 : CollatzResearch.WordTrace tailWord_2529441 prefixEnd_2529441 865879346792895522769879 := by
  unfold tailWord_2529441
  simp only [CollatzResearch.WordTrace]
  refine ⟨92256292429274725975100177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61504194952849817316733451 92256292429274725975100177)
  ·
    refine ⟨69192219321956044481325133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92256292429274725975100177 69192219321956044481325133)
    ·
      refine ⟨25947082245733516680496925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69192219321956044481325133 25947082245733516680496925)
      ·
        refine ⟨9730155842150068755186347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25947082245733516680496925 9730155842150068755186347)
        ·
          refine ⟨14595233763225103132779521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9730155842150068755186347 14595233763225103132779521)
          ·
            refine ⟨10946425322418827349584641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14595233763225103132779521 10946425322418827349584641)
            ·
              refine ⟨8209818991814120512188481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10946425322418827349584641 8209818991814120512188481)
              ·
                refine ⟨6157364243860590384141361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8209818991814120512188481 6157364243860590384141361)
                ·
                  refine ⟨4618023182895442788106021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6157364243860590384141361 4618023182895442788106021)
                  ·
                    refine ⟨865879346792895522769879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4618023182895442788106021 865879346792895522769879)
                    ·
                      rfl

theorem cell22_2529441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_2529441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2529441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2529441 prefixEnd_2529441 := by exact prefixLift 2529441
  have htrace : WordTrace (prefixWord ++ tailWord_2529441) baseStart_2529441 baseEnd_2529441 := by
    simpa [prefixWord, tailWord_2529441, baseEnd_2529441] using wordTrace_append hprefix tailTrace_2529441
  have hstable : (prefixWord ++ tailWord_2529441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529441).length < 2 ^ (prefixWord ++ tailWord_2529441).sum := by decide
  have hdescent : baseEnd_2529441 < baseStart_2529441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529469 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 4, 6]
def baseStart_2529469 : Nat := 118140960795 + 2529469 * 2 ^ 59
def prefixEnd_2529469 : Nat := 4983230072969 + 3 ^ 40 * 2529469 * 2
def baseEnd_2529469 : Nat := 865888931765112783069793

theorem tailTrace_2529469 : CollatzResearch.WordTrace tailWord_2529469 prefixEnd_2529469 865888931765112783069793 := by
  unfold tailWord_2529469
  simp only [CollatzResearch.WordTrace]
  refine ⟨92257313673173286757119461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61504875782115524504746307 92257313673173286757119461)
  ·
    refine ⟨17298246313719991266959899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92257313673173286757119461 17298246313719991266959899)
    ·
      refine ⟨25947369470579986900439849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17298246313719991266959899 25947369470579986900439849)
      ·
        refine ⟨19460527102934990175329887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25947369470579986900439849 19460527102934990175329887)
        ·
          refine ⟨29190790654402485262994831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19460527102934990175329887 29190790654402485262994831)
          ·
            refine ⟨43786185981603727894492247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29190790654402485262994831 43786185981603727894492247)
            ·
              refine ⟨65679278972405591841738371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43786185981603727894492247 65679278972405591841738371)
              ·
                refine ⟨98518918458608387762607557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65679278972405591841738371 98518918458608387762607557)
                ·
                  refine ⟨18472297210989072705488917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98518918458608387762607557 18472297210989072705488917)
                  ·
                    refine ⟨865888931765112783069793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18472297210989072705488917 865888931765112783069793)
                    ·
                      rfl

theorem cell22_2529469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_2529469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2529469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2529469 prefixEnd_2529469 := by exact prefixLift 2529469
  have htrace : WordTrace (prefixWord ++ tailWord_2529469) baseStart_2529469 baseEnd_2529469 := by
    simpa [prefixWord, tailWord_2529469, baseEnd_2529469] using wordTrace_append hprefix tailTrace_2529469
  have hstable : (prefixWord ++ tailWord_2529469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529469).length < 2 ^ (prefixWord ++ tailWord_2529469).sum := by decide
  have hdescent : baseEnd_2529469 < baseStart_2529469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529499 : List Nat := [1, 1, 1, 1, 1, 1, 1, 8, 2, 5]
def baseStart_2529499 : Nat := 118140960795 + 2529499 * 2 ^ 59
def prefixEnd_2529499 : Nat := 4983230072969 + 3 ^ 40 * 2529499 * 2
def baseEnd_2529499 : Nat := 865899201378202704819701

theorem tailTrace_2529499 : CollatzResearch.WordTrace tailWord_2529499 prefixEnd_2529499 865899201378202704819701 := by
  unfold tailWord_2529499
  simp only [CollatzResearch.WordTrace]
  refine ⟨92258407863064601880711551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61505605242043067920474367 92258407863064601880711551)
  ·
    refine ⟨138387611794596902821067327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92258407863064601880711551 138387611794596902821067327)
    ·
      refine ⟨207581417691895354231600991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138387611794596902821067327 207581417691895354231600991)
      ·
        refine ⟨311372126537843031347401487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207581417691895354231600991 311372126537843031347401487)
        ·
          refine ⟨467058189806764547021102231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311372126537843031347401487 467058189806764547021102231)
          ·
            refine ⟨700587284710146820531653347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 467058189806764547021102231 700587284710146820531653347)
            ·
              refine ⟨1050880927065220230797480021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 700587284710146820531653347 1050880927065220230797480021)
              ·
                refine ⟨12315010864045549579657969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1050880927065220230797480021 12315010864045549579657969)
                ·
                  refine ⟨9236258148034162184743477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12315010864045549579657969 9236258148034162184743477)
                  ·
                    refine ⟨865899201378202704819701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9236258148034162184743477 865899201378202704819701)
                    ·
                      rfl

theorem cell22_2529499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 5].length) (baseStart_2529499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2529499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2529499 prefixEnd_2529499 := by exact prefixLift 2529499
  have htrace : WordTrace (prefixWord ++ tailWord_2529499) baseStart_2529499 baseEnd_2529499 := by
    simpa [prefixWord, tailWord_2529499, baseEnd_2529499] using wordTrace_append hprefix tailTrace_2529499
  have hstable : (prefixWord ++ tailWord_2529499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529499).length < 2 ^ (prefixWord ++ tailWord_2529499).sum := by decide
  have hdescent : baseEnd_2529499 < baseStart_2529499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529529 : List Nat := [1, 2, 1, 3, 1, 1, 2, 3, 8]
def baseStart_2529529 : Nat := 118140960795 + 2529529 * 2 ^ 59
def prefixEnd_2529529 : Nat := 4983230072969 + 3 ^ 40 * 2529529 * 2
def baseEnd_2529529 : Nat := 288636490330430875523203

theorem tailTrace_2529529 : CollatzResearch.WordTrace tailWord_2529529 prefixEnd_2529529 288636490330430875523203 := by
  unfold tailWord_2529529
  simp only [CollatzResearch.WordTrace]
  refine ⟨92259502052955917004303641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61506334701970611336202427 92259502052955917004303641)
  ·
    refine ⟨69194626539716937753227731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92259502052955917004303641 69194626539716937753227731)
    ·
      refine ⟨103791939809575406629841597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69194626539716937753227731 103791939809575406629841597)
      ·
        refine ⟨38921977428590777486190599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103791939809575406629841597 38921977428590777486190599)
        ·
          refine ⟨58382966142886166229285899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38921977428590777486190599 58382966142886166229285899)
          ·
            refine ⟨87574449214329249343928849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58382966142886166229285899 87574449214329249343928849)
            ·
              refine ⟨65680836910746937007946637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87574449214329249343928849 65680836910746937007946637)
              ·
                refine ⟨24630313841530101377979989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65680836910746937007946637 24630313841530101377979989)
                ·
                  refine ⟨288636490330430875523203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24630313841530101377979989 288636490330430875523203)
                  ·
                    rfl

theorem cell22_2529529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 8].length) (baseStart_2529529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2529529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2529529 prefixEnd_2529529 := by exact prefixLift 2529529
  have htrace : WordTrace (prefixWord ++ tailWord_2529529) baseStart_2529529 baseEnd_2529529 := by
    simpa [prefixWord, tailWord_2529529, baseEnd_2529529] using wordTrace_append hprefix tailTrace_2529529
  have hstable : (prefixWord ++ tailWord_2529529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529529).length < 2 ^ (prefixWord ++ tailWord_2529529).sum := by decide
  have hdescent : baseEnd_2529529 < baseStart_2529529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529593 : List Nat := [1, 2, 1, 6, 1, 1, 1, 3, 2, 4]
def baseStart_2529593 : Nat := 118140960795 + 2529593 * 2 ^ 59
def prefixEnd_2529593 : Nat := 4983230072969 + 3 ^ 40 * 2529593 * 2
def baseEnd_2529593 : Nat := 865931379499217792969413

theorem tailTrace_2529593 : CollatzResearch.WordTrace tailWord_2529593 prefixEnd_2529593 865931379499217792969413 := by
  unfold tailWord_2529593
  simp only [CollatzResearch.WordTrace]
  refine ⟨92261836324724055934633433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61507890883149370623088955 92261836324724055934633433)
  ·
    refine ⟨69196377243543041950975075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92261836324724055934633433 69196377243543041950975075)
    ·
      refine ⟨103794565865314562926462613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69196377243543041950975075 103794565865314562926462613)
      ·
        refine ⟨4865370274936620137177935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 103794565865314562926462613 4865370274936620137177935)
        ·
          refine ⟨7298055412404930205766903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4865370274936620137177935 7298055412404930205766903)
          ·
            refine ⟨10947083118607395308650355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7298055412404930205766903 10947083118607395308650355)
            ·
              refine ⟨16420624677911092962975533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10947083118607395308650355 16420624677911092962975533)
              ·
                refine ⟨6157734254216659861115825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16420624677911092962975533 6157734254216659861115825)
                ·
                  refine ⟨4618300690662494895836869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6157734254216659861115825 4618300690662494895836869)
                  ·
                    refine ⟨865931379499217792969413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4618300690662494895836869 865931379499217792969413)
                    ·
                      rfl

theorem cell22_2529593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 4].length) (baseStart_2529593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2529593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2529593 prefixEnd_2529593 := by exact prefixLift 2529593
  have htrace : WordTrace (prefixWord ++ tailWord_2529593) baseStart_2529593 baseEnd_2529593 := by
    simpa [prefixWord, tailWord_2529593, baseEnd_2529593] using wordTrace_append hprefix tailTrace_2529593
  have hstable : (prefixWord ++ tailWord_2529593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529593).length < 2 ^ (prefixWord ++ tailWord_2529593).sum := by decide
  have hdescent : baseEnd_2529593 < baseStart_2529593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529623 : List Nat := [1, 1, 3, 2, 3, 1, 2, 3, 3, 3]
def baseStart_2529623 : Nat := 118140960795 + 2529623 * 2 ^ 59
def prefixEnd_2529623 : Nat := 4983230072969 + 3 ^ 40 * 2529623 * 2
def baseEnd_2529623 : Nat := 865941649112307714719321

theorem tailTrace_2529623 : CollatzResearch.WordTrace tailWord_2529623 prefixEnd_2529623 865941649112307714719321 := by
  unfold tailWord_2529623
  simp only [CollatzResearch.WordTrace]
  refine ⟨92262930514615371058225523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61508620343076914038817015 92262930514615371058225523)
  ·
    refine ⟨138394395771923056587338285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92262930514615371058225523 138394395771923056587338285)
    ·
      refine ⟨51897898414471146220251857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138394395771923056587338285 51897898414471146220251857)
      ·
        refine ⟨38923423810853359665188893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51897898414471146220251857 38923423810853359665188893)
        ·
          refine ⟨14596283929070009874445835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38923423810853359665188893 14596283929070009874445835)
          ·
            refine ⟨21894425893605014811668753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14596283929070009874445835 21894425893605014811668753)
            ·
              refine ⟨16420819420203761108751565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21894425893605014811668753 16420819420203761108751565)
              ·
                refine ⟨6157807282576410415781837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16420819420203761108751565 6157807282576410415781837)
                ·
                  refine ⟨2309177730966153905918189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6157807282576410415781837 2309177730966153905918189)
                  ·
                    refine ⟨865941649112307714719321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2309177730966153905918189 865941649112307714719321)
                    ·
                      rfl

theorem cell22_2529623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 3, 3].length) (baseStart_2529623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2529623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2529623 prefixEnd_2529623 := by exact prefixLift 2529623
  have htrace : WordTrace (prefixWord ++ tailWord_2529623) baseStart_2529623 baseEnd_2529623 := by
    simpa [prefixWord, tailWord_2529623, baseEnd_2529623] using wordTrace_append hprefix tailTrace_2529623
  have hstable : (prefixWord ++ tailWord_2529623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529623).length < 2 ^ (prefixWord ++ tailWord_2529623).sum := by decide
  have hdescent : baseEnd_2529623 < baseStart_2529623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529640 : List Nat := [2, 1, 4, 2, 2, 2, 1, 2, 3, 3]
def baseStart_2529640 : Nat := 118140960795 + 2529640 * 2 ^ 59
def prefixEnd_2529640 : Nat := 4983230072969 + 3 ^ 40 * 2529640 * 2
def baseEnd_2529640 : Nat := 865947468559725337044269

theorem tailTrace_2529640 : CollatzResearch.WordTrace tailWord_2529640 prefixEnd_2529640 865947468559725337044269 := by
  unfold tailWord_2529640
  simp only [CollatzResearch.WordTrace]
  refine ⟨46131775277776891480797187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61509033703702521974396249 46131775277776891480797187)
  ·
    refine ⟨69197662916665337221195781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46131775277776891480797187 69197662916665337221195781)
    ·
      refine ⟨12974561796874750728974209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69197662916665337221195781 12974561796874750728974209)
      ·
        refine ⟨9730921347656063046730657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12974561796874750728974209 9730921347656063046730657)
        ·
          refine ⟨7298191010742047285047993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9730921347656063046730657 7298191010742047285047993)
          ·
            refine ⟨5473643258056535463785995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7298191010742047285047993 5473643258056535463785995)
            ·
              refine ⟨8210464887084803195678993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5473643258056535463785995 8210464887084803195678993)
              ·
                refine ⟨6157848665313602396759245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8210464887084803195678993 6157848665313602396759245)
                ·
                  refine ⟨2309193249492600898784717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6157848665313602396759245 2309193249492600898784717)
                  ·
                    refine ⟨865947468559725337044269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2309193249492600898784717 865947468559725337044269)
                    ·
                      rfl

theorem cell22_2529640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_2529640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2529640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2529640 prefixEnd_2529640 := by exact prefixLift 2529640
  have htrace : WordTrace (prefixWord ++ tailWord_2529640) baseStart_2529640 baseEnd_2529640 := by
    simpa [prefixWord, tailWord_2529640, baseEnd_2529640] using wordTrace_append hprefix tailTrace_2529640
  have hstable : (prefixWord ++ tailWord_2529640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529640).length < 2 ^ (prefixWord ++ tailWord_2529640).sum := by decide
  have hdescent : baseEnd_2529640 < baseStart_2529640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529698 : List Nat := [3, 3, 1, 2, 1, 1, 1, 4, 6]
def baseStart_2529698 : Nat := 118140960795 + 2529698 * 2 ^ 59
def prefixEnd_2529698 : Nat := 4983230072969 + 3 ^ 40 * 2529698 * 2
def baseEnd_2529698 : Nat := 288655774381677506364697

theorem tailTrace_2529698 : CollatzResearch.WordTrace tailWord_2529698 prefixEnd_2529698 288655774381677506364697 := by
  unfold tailWord_2529698
  simp only [CollatzResearch.WordTrace]
  refine ⟨23066416497335914716801437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61510443992895772578137165 23066416497335914716801437)
  ·
    refine ⟨8649906186500968018800539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23066416497335914716801437 8649906186500968018800539)
    ·
      refine ⟨12974859279751452028200809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8649906186500968018800539 12974859279751452028200809)
      ·
        refine ⟨9731144459813589021150607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12974859279751452028200809 9731144459813589021150607)
        ·
          refine ⟨14596716689720383531725911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9731144459813589021150607 14596716689720383531725911)
          ·
            refine ⟨21895075034580575297588867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14596716689720383531725911 21895075034580575297588867)
            ·
              refine ⟨32842612551870862946383301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21895075034580575297588867 32842612551870862946383301)
              ·
                refine ⟨6157989853475786802446869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32842612551870862946383301 6157989853475786802446869)
                ·
                  refine ⟨288655774381677506364697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6157989853475786802446869 288655774381677506364697)
                  ·
                    rfl

theorem cell22_2529698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_2529698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2529698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2529698 prefixEnd_2529698 := by exact prefixLift 2529698
  have htrace : WordTrace (prefixWord ++ tailWord_2529698) baseStart_2529698 baseEnd_2529698 := by
    simpa [prefixWord, tailWord_2529698, baseEnd_2529698] using wordTrace_append hprefix tailTrace_2529698
  have hstable : (prefixWord ++ tailWord_2529698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529698).length < 2 ^ (prefixWord ++ tailWord_2529698).sum := by decide
  have hdescent : baseEnd_2529698 < baseStart_2529698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529732 : List Nat := [2, 3, 3, 2, 2, 2, 1, 1, 6]
def baseStart_2529732 : Nat := 118140960795 + 2529732 * 2 ^ 59
def prefixEnd_2529732 : Nat := 4983230072969 + 3 ^ 40 * 2529732 * 2
def baseEnd_2529732 : Nat := 288659654013289254581329

theorem tailTrace_2529732 : CollatzResearch.WordTrace tailWord_2529732 prefixEnd_2529732 288659654013289254581329 := by
  unfold tailWord_2529732
  simp only [CollatzResearch.WordTrace]
  refine ⟨46133453035610241336971725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61511270714146988449295633 46133453035610241336971725)
  ·
    refine ⟨17300044888353840501364397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46133453035610241336971725 17300044888353840501364397)
    ·
      refine ⟨6487516833132690188011649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17300044888353840501364397 6487516833132690188011649)
      ·
        refine ⟨4865637624849517641008737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6487516833132690188011649 4865637624849517641008737)
        ·
          refine ⟨3649228218637138230756553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4865637624849517641008737 3649228218637138230756553)
          ·
            refine ⟨2736921163977853673067415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3649228218637138230756553 2736921163977853673067415)
            ·
              refine ⟨4105381745966780509601123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2736921163977853673067415 4105381745966780509601123)
              ·
                refine ⟨6158072618950170764401685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4105381745966780509601123 6158072618950170764401685)
                ·
                  refine ⟨288659654013289254581329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6158072618950170764401685 288659654013289254581329)
                  ·
                    rfl

theorem cell22_2529732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_2529732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2529732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2529732 prefixEnd_2529732 := by exact prefixLift 2529732
  have htrace : WordTrace (prefixWord ++ tailWord_2529732) baseStart_2529732 baseEnd_2529732 := by
    simpa [prefixWord, tailWord_2529732, baseEnd_2529732] using wordTrace_append hprefix tailTrace_2529732
  have hstable : (prefixWord ++ tailWord_2529732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529732).length < 2 ^ (prefixWord ++ tailWord_2529732).sum := by decide
  have hdescent : baseEnd_2529732 < baseStart_2529732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529794 : List Nat := [3, 4, 1, 2, 3, 1, 1, 7]
def baseStart_2529794 : Nat := 118140960795 + 2529794 * 2 ^ 59
def prefixEnd_2529794 : Nat := 4983230072969 + 3 ^ 40 * 2529794 * 2
def baseEnd_2529794 : Nat := 96222242878546696521533

theorem tailTrace_2529794 : CollatzResearch.WordTrace tailWord_2529794 prefixEnd_2529794 96222242878546696521533 := by
  unfold tailWord_2529794
  simp only [CollatzResearch.WordTrace]
  refine ⟨23067291849248966815675109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61512778264663911508466957 23067291849248966815675109)
  ·
    refine ⟨4325117221734181277939083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23067291849248966815675109 4325117221734181277939083)
    ·
      refine ⟨6487675832601271916908625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4325117221734181277939083 6487675832601271916908625)
      ·
        refine ⟨4865756874450953937681469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6487675832601271916908625 4865756874450953937681469)
        ·
          refine ⟨1824658827919107726630551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4865756874450953937681469 1824658827919107726630551)
          ·
            refine ⟨2736988241878661589945827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1824658827919107726630551 2736988241878661589945827)
            ·
              refine ⟨4105482362817992384918741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2736988241878661589945827 4105482362817992384918741)
              ·
                refine ⟨96222242878546696521533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4105482362817992384918741 96222242878546696521533)
                ·
                  rfl

theorem cell22_2529794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 7].length) (baseStart_2529794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2529794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2529794 prefixEnd_2529794 := by exact prefixLift 2529794
  have htrace : WordTrace (prefixWord ++ tailWord_2529794) baseStart_2529794 baseEnd_2529794 := by
    simpa [prefixWord, tailWord_2529794, baseEnd_2529794] using wordTrace_append hprefix tailTrace_2529794
  have hstable : (prefixWord ++ tailWord_2529794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529794).length < 2 ^ (prefixWord ++ tailWord_2529794).sum := by decide
  have hdescent : baseEnd_2529794 < baseStart_2529794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529803 : List Nat := [1, 1, 1, 1, 7, 1, 1, 1, 1, 7]
def baseStart_2529803 : Nat := 118140960795 + 2529803 * 2 ^ 59
def prefixEnd_2529803 : Nat := 4983230072969 + 3 ^ 40 * 2529803 * 2
def baseEnd_2529803 : Nat := 866003266790847245218769

theorem tailTrace_2529803 : CollatzResearch.WordTrace tailWord_2529803 prefixEnd_2529803 866003266790847245218769 := by
  unfold tailWord_2529803
  simp only [CollatzResearch.WordTrace]
  refine ⟨92269495653963261799778063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61512997102642174533185375 92269495653963261799778063)
  ·
    refine ⟨138404243480944892699667095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92269495653963261799778063 138404243480944892699667095)
    ·
      refine ⟨207606365221417339049500643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138404243480944892699667095 207606365221417339049500643)
      ·
        refine ⟨311409547832126008574250965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207606365221417339049500643 311409547832126008574250965)
        ·
          refine ⟨7298661277315453325959007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 311409547832126008574250965 7298661277315453325959007)
          ·
            refine ⟨10947991915973179988938511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7298661277315453325959007 10947991915973179988938511)
            ·
              refine ⟨16421987873959769983407767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10947991915973179988938511 16421987873959769983407767)
              ·
                refine ⟨24632981810939654975111651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16421987873959769983407767 24632981810939654975111651)
                ·
                  refine ⟨36949472716409482462667477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24632981810939654975111651 36949472716409482462667477)
                  ·
                    refine ⟨866003266790847245218769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36949472716409482462667477 866003266790847245218769)
                    ·
                      rfl

theorem cell22_2529803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 7].length) (baseStart_2529803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2529803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2529803 prefixEnd_2529803 := by exact prefixLift 2529803
  have htrace : WordTrace (prefixWord ++ tailWord_2529803) baseStart_2529803 baseEnd_2529803 := by
    simpa [prefixWord, tailWord_2529803, baseEnd_2529803] using wordTrace_append hprefix tailTrace_2529803
  have hstable : (prefixWord ++ tailWord_2529803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529803).length < 2 ^ (prefixWord ++ tailWord_2529803).sum := by decide
  have hdescent : baseEnd_2529803 < baseStart_2529803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529850 : List Nat := [3, 1, 1, 1, 3, 4, 2, 1, 6]
def baseStart_2529850 : Nat := 118140960795 + 2529850 * 2 ^ 59
def prefixEnd_2529850 : Nat := 4983230072969 + 3 ^ 40 * 2529850 * 2
def baseEnd_2529850 : Nat := 288673118617118263097875

theorem tailTrace_2529850 : CollatzResearch.WordTrace tailWord_2529850 prefixEnd_2529850 288673118617118263097875 := by
  unfold tailWord_2529850
  simp only [CollatzResearch.WordTrace]
  refine ⟨23067802471198247206684751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61514139923195325884492669 23067802471198247206684751)
  ·
    refine ⟨34601703706797370810027127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23067802471198247206684751 34601703706797370810027127)
    ·
      refine ⟨51902555560196056215040691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34601703706797370810027127 51902555560196056215040691)
      ·
        refine ⟨77853833340294084322561037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51902555560196056215040691 77853833340294084322561037)
        ·
          refine ⟨29195187502610281620960389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77853833340294084322561037 29195187502610281620960389)
          ·
            refine ⟨5474097656739427803930073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29195187502610281620960389 5474097656739427803930073)
            ·
              refine ⟨4105573242554570852947555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5474097656739427803930073 4105573242554570852947555)
              ·
                refine ⟨6158359863831856279421333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4105573242554570852947555 6158359863831856279421333)
                ·
                  refine ⟨288673118617118263097875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6158359863831856279421333 288673118617118263097875)
                  ·
                    rfl

theorem cell22_2529850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 6].length) (baseStart_2529850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2529850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2529850 prefixEnd_2529850 := by exact prefixLift 2529850
  have htrace : WordTrace (prefixWord ++ tailWord_2529850) baseStart_2529850 baseEnd_2529850 := by
    simpa [prefixWord, tailWord_2529850, baseEnd_2529850] using wordTrace_append hprefix tailTrace_2529850
  have hstable : (prefixWord ++ tailWord_2529850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529850).length < 2 ^ (prefixWord ++ tailWord_2529850).sum := by decide
  have hdescent : baseEnd_2529850 < baseStart_2529850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529869 : List Nat := [1, 6, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_2529869 : Nat := 118140960795 + 2529869 * 2 ^ 59
def prefixEnd_2529869 : Nat := 4983230072969 + 3 ^ 40 * 2529869 * 2
def baseEnd_2529869 : Nat := 866025859939645073068567

theorem tailTrace_2529869 : CollatzResearch.WordTrace tailWord_2529869 prefixEnd_2529869 866025859939645073068567 := by
  unfold tailWord_2529869
  simp only [CollatzResearch.WordTrace]
  refine ⟨92271902871724155071680661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61514601914482770047787107 92271902871724155071680661)
  ·
    refine ⟨4325245447112069768985031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 92271902871724155071680661 4325245447112069768985031)
    ·
      refine ⟨6487868170668104653477547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4325245447112069768985031 6487868170668104653477547)
      ·
        refine ⟨9731802256002156980216321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6487868170668104653477547 9731802256002156980216321)
        ·
          refine ⟨7298851692001617735162241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9731802256002156980216321 7298851692001617735162241)
          ·
            refine ⟨5474138769001213301371681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7298851692001617735162241 5474138769001213301371681)
            ·
              refine ⟨4105604076750909976028761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5474138769001213301371681 4105604076750909976028761)
              ·
                refine ⟨3079203057563182482021571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4105604076750909976028761 3079203057563182482021571)
                ·
                  refine ⟨4618804586344773723032357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3079203057563182482021571 4618804586344773723032357)
                  ·
                    refine ⟨866025859939645073068567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4618804586344773723032357 866025859939645073068567)
                    ·
                      rfl

theorem cell22_2529869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_2529869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2529869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2529869 prefixEnd_2529869 := by exact prefixLift 2529869
  have htrace : WordTrace (prefixWord ++ tailWord_2529869) baseStart_2529869 baseEnd_2529869 := by
    simpa [prefixWord, tailWord_2529869, baseEnd_2529869] using wordTrace_append hprefix tailTrace_2529869
  have hstable : (prefixWord ++ tailWord_2529869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529869).length < 2 ^ (prefixWord ++ tailWord_2529869).sum := by decide
  have hdescent : baseEnd_2529869 < baseStart_2529869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2529944 : List Nat := [2, 1, 2, 4, 1, 1, 2, 5, 1, 3]
def baseStart_2529944 : Nat := 118140960795 + 2529944 * 2 ^ 59
def prefixEnd_2529944 : Nat := 4983230072969 + 3 ^ 40 * 2529944 * 2
def baseEnd_2529944 : Nat := 866051533972369877443337

theorem tailTrace_2529944 : CollatzResearch.WordTrace tailWord_2529944 prefixEnd_2529944 866051533972369877443337 := by
  unfold tailWord_2529944
  simp only [CollatzResearch.WordTrace]
  refine ⟨46137319173226221440330443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61516425564301628587107257 46137319173226221440330443)
  ·
    refine ⟨69205978759839332160495665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46137319173226221440330443 69205978759839332160495665)
    ·
      refine ⟨51904484069879499120371749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69205978759839332160495665 51904484069879499120371749)
      ·
        refine ⟨9732090763102406085069703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51904484069879499120371749 9732090763102406085069703)
        ·
          refine ⟨14598136144653609127604555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9732090763102406085069703 14598136144653609127604555)
          ·
            refine ⟨21897204216980413691406833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14598136144653609127604555 21897204216980413691406833)
            ·
              refine ⟨16422903162735310268555125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21897204216980413691406833 16422903162735310268555125)
              ·
                refine ⟨1539647171506435337677043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16422903162735310268555125 1539647171506435337677043)
                ·
                  refine ⟨2309470757259653006515565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1539647171506435337677043 2309470757259653006515565)
                  ·
                    refine ⟨866051533972369877443337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2309470757259653006515565 866051533972369877443337)
                    ·
                      rfl

theorem cell22_2529944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 5, 1, 3].length) (baseStart_2529944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2529944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2529944 prefixEnd_2529944 := by exact prefixLift 2529944
  have htrace : WordTrace (prefixWord ++ tailWord_2529944) baseStart_2529944 baseEnd_2529944 := by
    simpa [prefixWord, tailWord_2529944, baseEnd_2529944] using wordTrace_append hprefix tailTrace_2529944
  have hstable : (prefixWord ++ tailWord_2529944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2529944).length < 2 ^ (prefixWord ++ tailWord_2529944).sum := by decide
  have hdescent : baseEnd_2529944 < baseStart_2529944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2529944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530019 : List Nat := [1, 1, 1, 7, 1, 1, 2, 4, 4]
def baseStart_2530019 : Nat := 118140960795 + 2530019 * 2 ^ 59
def prefixEnd_2530019 : Nat := 4983230072969 + 3 ^ 40 * 2530019 * 2
def baseEnd_2530019 : Nat := 288692402668364893939369

theorem tailTrace_2530019 : CollatzResearch.WordTrace tailWord_2530019 prefixEnd_2530019 288692402668364893939369 := by
  unfold tailWord_2530019
  simp only [CollatzResearch.WordTrace]
  refine ⟨92277373821180730689641111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61518249214120487126427407 92277373821180730689641111)
  ·
    refine ⟨138416060731771096034461667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92277373821180730689641111 138416060731771096034461667)
    ·
      refine ⟨207624091097656644051692501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138416060731771096034461667 207624091097656644051692501)
      ·
        refine ⟨4866189635101327594961543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 207624091097656644051692501 4866189635101327594961543)
        ·
          refine ⟨7299284452651991392442315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4866189635101327594961543 7299284452651991392442315)
          ·
            refine ⟨10948926678977987088663473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7299284452651991392442315 10948926678977987088663473)
            ·
              refine ⟨8211695009233490316497605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10948926678977987088663473 8211695009233490316497605)
              ·
                refine ⟨1539692814231279434343301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8211695009233490316497605 1539692814231279434343301)
                ·
                  refine ⟨288692402668364893939369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1539692814231279434343301 288692402668364893939369)
                  ·
                    rfl

theorem cell22_2530019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 4, 4].length) (baseStart_2530019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2530019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2530019 prefixEnd_2530019 := by exact prefixLift 2530019
  have htrace : WordTrace (prefixWord ++ tailWord_2530019) baseStart_2530019 baseEnd_2530019 := by
    simpa [prefixWord, tailWord_2530019, baseEnd_2530019] using wordTrace_append hprefix tailTrace_2530019
  have hstable : (prefixWord ++ tailWord_2530019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530019).length < 2 ^ (prefixWord ++ tailWord_2530019).sum := by decide
  have hdescent : baseEnd_2530019 < baseStart_2530019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530034 : List Nat := [3, 2, 1, 3, 1, 4, 1, 1, 1, 5]
def baseStart_2530034 : Nat := 118140960795 + 2530034 * 2 ^ 59
def prefixEnd_2530034 : Nat := 4983230072969 + 3 ^ 40 * 2530034 * 2
def baseEnd_2530034 : Nat := 866082342811639642693061

theorem tailTrace_2530034 : CollatzResearch.WordTrace tailWord_2530034 prefixEnd_2530034 866082342811639642693061 := by
  unfold tailWord_2530034
  simp only [CollatzResearch.WordTrace]
  refine ⟨23069480229031597062859289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61518613944084258834291437 23069480229031597062859289)
  ·
    refine ⟨17302110171773697797144467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23069480229031597062859289 17302110171773697797144467)
    ·
      refine ⟨25953165257660546695716701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17302110171773697797144467 25953165257660546695716701)
      ·
        refine ⟨9732436971622705010893763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25953165257660546695716701 9732436971622705010893763)
        ·
          refine ⟨14598655457434057516340645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9732436971622705010893763 14598655457434057516340645)
          ·
            refine ⟨2737247898268885784313871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14598655457434057516340645 2737247898268885784313871)
            ·
              refine ⟨4105871847403328676470807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2737247898268885784313871 4105871847403328676470807)
              ·
                refine ⟨6158807771104993014706211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4105871847403328676470807 6158807771104993014706211)
                ·
                  refine ⟨9238211656657489522059317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6158807771104993014706211 9238211656657489522059317)
                  ·
                    refine ⟨866082342811639642693061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9238211656657489522059317 866082342811639642693061)
                    ·
                      rfl

theorem cell22_2530034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_2530034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2530034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2530034 prefixEnd_2530034 := by exact prefixLift 2530034
  have htrace : WordTrace (prefixWord ++ tailWord_2530034) baseStart_2530034 baseEnd_2530034 := by
    simpa [prefixWord, tailWord_2530034, baseEnd_2530034] using wordTrace_append hprefix tailTrace_2530034
  have hstable : (prefixWord ++ tailWord_2530034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530034).length < 2 ^ (prefixWord ++ tailWord_2530034).sum := by decide
  have hdescent : baseEnd_2530034 < baseStart_2530034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530045 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 2, 7]
def baseStart_2530045 : Nat := 118140960795 + 2530045 * 2 ^ 59
def prefixEnd_2530045 : Nat := 4983230072969 + 3 ^ 40 * 2530045 * 2
def baseEnd_2530045 : Nat := 866086108336439280668027

theorem tailTrace_2530045 : CollatzResearch.WordTrace tailWord_2530045 prefixEnd_2530045 866086108336439280668027 := by
  unfold tailWord_2530045
  simp only [CollatzResearch.WordTrace]
  refine ⟨92278322119086537130087589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61518881412724358086725059 92278322119086537130087589)
  ·
    refine ⟨17302185397328725711891423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92278322119086537130087589 17302185397328725711891423)
    ·
      refine ⟨25953278095993088567837135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17302185397328725711891423 25953278095993088567837135)
      ·
        refine ⟨38929917143989632851755703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25953278095993088567837135 38929917143989632851755703)
        ·
          refine ⟨58394875715984449277633555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38929917143989632851755703 58394875715984449277633555)
          ·
            refine ⟨87592313573976673916450333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58394875715984449277633555 87592313573976673916450333)
            ·
              refine ⟨32847117590241252718668875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87592313573976673916450333 32847117590241252718668875)
              ·
                refine ⟨49270676385361879078003313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32847117590241252718668875 49270676385361879078003313)
                ·
                  refine ⟨36953007289021409308502485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49270676385361879078003313 36953007289021409308502485)
                  ·
                    refine ⟨866086108336439280668027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36953007289021409308502485 866086108336439280668027)
                    ·
                      rfl

theorem cell22_2530045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_2530045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2530045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2530045 prefixEnd_2530045 := by exact prefixLift 2530045
  have htrace : WordTrace (prefixWord ++ tailWord_2530045) baseStart_2530045 baseEnd_2530045 := by
    simpa [prefixWord, tailWord_2530045, baseEnd_2530045] using wordTrace_append hprefix tailTrace_2530045
  have hstable : (prefixWord ++ tailWord_2530045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530045).length < 2 ^ (prefixWord ++ tailWord_2530045).sum := by decide
  have hdescent : baseEnd_2530045 < baseStart_2530045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530060 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 1, 8]
def baseStart_2530060 : Nat := 118140960795 + 2530060 * 2 ^ 59
def prefixEnd_2530060 : Nat := 4983230072969 + 3 ^ 40 * 2530060 * 2
def baseEnd_2530060 : Nat := 866091243142984241542981

theorem tailTrace_2530060 : CollatzResearch.WordTrace tailWord_2530060 prefixEnd_2530060 866091243142984241542981 := by
  unfold tailWord_2530060
  simp only [CollatzResearch.WordTrace]
  refine ⟨46139434607016097345941817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61519246142688129794589089 46139434607016097345941817)
  ·
    refine ⟨34604575955262073009456363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46139434607016097345941817 34604575955262073009456363)
    ·
      refine ⟨51906863932893109514184545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34604575955262073009456363 51906863932893109514184545)
      ·
        refine ⟨38930147949669832135638409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51906863932893109514184545 38930147949669832135638409)
        ·
          refine ⟨29197610962252374101728807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38930147949669832135638409 29197610962252374101728807)
          ·
            refine ⟨43796416443378561152593211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29197610962252374101728807 43796416443378561152593211)
            ·
              refine ⟨65694624665067841728889817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43796416443378561152593211 65694624665067841728889817)
              ·
                refine ⟨49270968498800881296667363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65694624665067841728889817 49270968498800881296667363)
                ·
                  refine ⟨73906452748201321945001045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49270968498800881296667363 73906452748201321945001045)
                  ·
                    refine ⟨866091243142984241542981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 73906452748201321945001045 866091243142984241542981)
                    ·
                      rfl

theorem cell22_2530060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_2530060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2530060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2530060 prefixEnd_2530060 := by exact prefixLift 2530060
  have htrace : WordTrace (prefixWord ++ tailWord_2530060) baseStart_2530060 baseEnd_2530060 := by
    simpa [prefixWord, tailWord_2530060, baseEnd_2530060] using wordTrace_append hprefix tailTrace_2530060
  have hstable : (prefixWord ++ tailWord_2530060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530060).length < 2 ^ (prefixWord ++ tailWord_2530060).sum := by decide
  have hdescent : baseEnd_2530060 < baseStart_2530060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530066 : List Nat := [3, 2, 4, 1, 2, 1, 1, 2, 2, 4]
def baseStart_2530066 : Nat := 118140960795 + 2530066 * 2 ^ 59
def prefixEnd_2530066 : Nat := 4983230072969 + 3 ^ 40 * 2530066 * 2
def baseEnd_2530066 : Nat := 866093297065602225892963

theorem tailTrace_2530066 : CollatzResearch.WordTrace tailWord_2530066 prefixEnd_2530066 866093297065602225892963 := by
  unfold tailWord_2530066
  simp only [CollatzResearch.WordTrace]
  refine ⟨23069772013002614429150513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61519392034673638477734701 23069772013002614429150513)
  ·
    refine ⟨17302329009751960821862885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23069772013002614429150513 17302329009751960821862885)
    ·
      refine ⟨3244186689328492654099291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17302329009751960821862885 3244186689328492654099291)
      ·
        refine ⟨4866280033992738981148937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3244186689328492654099291 4866280033992738981148937)
        ·
          refine ⟨3649710025494554235861703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4866280033992738981148937 3649710025494554235861703)
          ·
            refine ⟨5474565038241831353792555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3649710025494554235861703 5474565038241831353792555)
            ·
              refine ⟨8211847557362747030688833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5474565038241831353792555 8211847557362747030688833)
              ·
                refine ⟨6158885668022060273016625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8211847557362747030688833 6158885668022060273016625)
                ·
                  refine ⟨4619164251016545204762469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6158885668022060273016625 4619164251016545204762469)
                  ·
                    refine ⟨866093297065602225892963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4619164251016545204762469 866093297065602225892963)
                    ·
                      rfl

theorem cell22_2530066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_2530066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2530066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2530066 prefixEnd_2530066 := by exact prefixLift 2530066
  have htrace : WordTrace (prefixWord ++ tailWord_2530066) baseStart_2530066 baseEnd_2530066 := by
    simpa [prefixWord, tailWord_2530066, baseEnd_2530066] using wordTrace_append hprefix tailTrace_2530066
  have hstable : (prefixWord ++ tailWord_2530066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530066).length < 2 ^ (prefixWord ++ tailWord_2530066).sum := by decide
  have hdescent : baseEnd_2530066 < baseStart_2530066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530079 : List Nat := [1, 1, 2, 4, 2, 2, 3, 1, 3, 3]
def baseStart_2530079 : Nat := 118140960795 + 2530079 * 2 ^ 59
def prefixEnd_2530079 : Nat := 4983230072969 + 3 ^ 40 * 2530079 * 2
def baseEnd_2530079 : Nat := 866097747231274525317923

theorem tailTrace_2530079 : CollatzResearch.WordTrace tailWord_2530079 prefixEnd_2530079 866097747231274525317923 := by
  unfold tailWord_2530079
  simp only [CollatzResearch.WordTrace]
  refine ⟨92279562200963360936825291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61519708133975573957883527 92279562200963360936825291)
  ·
    refine ⟨138419343301445041405237937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92279562200963360936825291 138419343301445041405237937)
    ·
      refine ⟨103814507476083781053928453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138419343301445041405237937 103814507476083781053928453)
      ·
        refine ⟨19465220151765708947611585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103814507476083781053928453 19465220151765708947611585)
        ·
          refine ⟨14598915113824281710708689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19465220151765708947611585 14598915113824281710708689)
          ·
            refine ⟨10949186335368211283031517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14598915113824281710708689 10949186335368211283031517)
            ·
              refine ⟨4105944875763079231136819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10949186335368211283031517 4105944875763079231136819)
              ·
                refine ⟨6158917313644618846705229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4105944875763079231136819 6158917313644618846705229)
                ·
                  refine ⟨2309593992616732067514461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6158917313644618846705229 2309593992616732067514461)
                  ·
                    refine ⟨866097747231274525317923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2309593992616732067514461 866097747231274525317923)
                    ·
                      rfl

theorem cell22_2530079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 3, 3].length) (baseStart_2530079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2530079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2530079 prefixEnd_2530079 := by exact prefixLift 2530079
  have htrace : WordTrace (prefixWord ++ tailWord_2530079) baseStart_2530079 baseEnd_2530079 := by
    simpa [prefixWord, tailWord_2530079, baseEnd_2530079] using wordTrace_append hprefix tailTrace_2530079
  have hstable : (prefixWord ++ tailWord_2530079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530079).length < 2 ^ (prefixWord ++ tailWord_2530079).sum := by decide
  have hdescent : baseEnd_2530079 < baseStart_2530079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530092 : List Nat := [2, 2, 1, 1, 1, 4, 3, 3, 5]
def baseStart_2530092 : Nat := 118140960795 + 2530092 * 2 ^ 59
def prefixEnd_2530092 : Nat := 4983230072969 + 3 ^ 40 * 2530092 * 2
def baseEnd_2530092 : Nat := 288700732465648941580961

theorem tailTrace_2530092 : CollatzResearch.WordTrace tailWord_2530092 prefixEnd_2530092 288700732465648941580961 := by
  unfold tailWord_2530092
  simp only [CollatzResearch.WordTrace]
  refine ⟨46140018174958132078524265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61520024233277509438032353 46140018174958132078524265)
  ·
    refine ⟨34605013631218599058893199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46140018174958132078524265 34605013631218599058893199)
    ·
      refine ⟨51907520446827898588339799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34605013631218599058893199 51907520446827898588339799)
      ·
        refine ⟨77861280670241847882509699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51907520446827898588339799 77861280670241847882509699)
        ·
          refine ⟨116791921005362771823764549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77861280670241847882509699 116791921005362771823764549)
          ·
            refine ⟨21898485188505519716955853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116791921005362771823764549 21898485188505519716955853)
            ·
              refine ⟨8211931945689569893858445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21898485188505519716955853 8211931945689569893858445)
              ·
                refine ⟨3079474479633588710196917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8211931945689569893858445 3079474479633588710196917)
                ·
                  refine ⟨288700732465648941580961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3079474479633588710196917 288700732465648941580961)
                  ·
                    rfl

theorem cell22_2530092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 5].length) (baseStart_2530092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2530092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2530092 prefixEnd_2530092 := by exact prefixLift 2530092
  have htrace : WordTrace (prefixWord ++ tailWord_2530092) baseStart_2530092 baseEnd_2530092 := by
    simpa [prefixWord, tailWord_2530092, baseEnd_2530092] using wordTrace_append hprefix tailTrace_2530092
  have hstable : (prefixWord ++ tailWord_2530092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530092).length < 2 ^ (prefixWord ++ tailWord_2530092).sum := by decide
  have hdescent : baseEnd_2530092 < baseStart_2530092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530186 : List Nat := [3, 1, 2, 4, 1, 2, 1, 1, 4, 3]
def baseStart_2530186 : Nat := 118140960795 + 2530186 * 2 ^ 59
def prefixEnd_2530186 : Nat := 4983230072969 + 3 ^ 40 * 2530186 * 2
def baseEnd_2530186 : Nat := 866134375517961912892595

theorem tailTrace_2530186 : CollatzResearch.WordTrace tailWord_2530186 prefixEnd_2530186 866134375517961912892595 := by
  unfold tailWord_2530186
  simp only [CollatzResearch.WordTrace]
  refine ⟨23070866202893929552742603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61522309874383812140646941 23070866202893929552742603)
  ·
    refine ⟨34606299304340894329113905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23070866202893929552742603 34606299304340894329113905)
    ·
      refine ⟨25954724478255670746835429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34606299304340894329113905 25954724478255670746835429)
      ·
        refine ⟨4866510839672938265031643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25954724478255670746835429 4866510839672938265031643)
        ·
          refine ⟨7299766259509407397547465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4866510839672938265031643 7299766259509407397547465)
          ·
            refine ⟨5474824694632055548160599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7299766259509407397547465 5474824694632055548160599)
            ·
              refine ⟨8212237041948083322240899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5474824694632055548160599 8212237041948083322240899)
              ·
                refine ⟨12318355562922124983361349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8212237041948083322240899 12318355562922124983361349)
                ·
                  refine ⟨2309691668047898434380253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12318355562922124983361349 2309691668047898434380253)
                  ·
                    refine ⟨866134375517961912892595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2309691668047898434380253 866134375517961912892595)
                    ·
                      rfl

theorem cell22_2530186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_2530186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2530186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2530186 prefixEnd_2530186 := by exact prefixLift 2530186
  have htrace : WordTrace (prefixWord ++ tailWord_2530186) baseStart_2530186 baseEnd_2530186 := by
    simpa [prefixWord, tailWord_2530186, baseEnd_2530186] using wordTrace_append hprefix tailTrace_2530186
  have hstable : (prefixWord ++ tailWord_2530186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530186).length < 2 ^ (prefixWord ++ tailWord_2530186).sum := by decide
  have hdescent : baseEnd_2530186 < baseStart_2530186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530248 : List Nat := [2, 1, 3, 1, 5, 2, 1, 1, 3, 3]
def baseStart_2530248 : Nat := 118140960795 + 2530248 * 2 ^ 59
def prefixEnd_2530248 : Nat := 4983230072969 + 3 ^ 40 * 2530248 * 2
def baseEnd_2530248 : Nat := 866155599385014417842405

theorem tailTrace_2530248 : CollatzResearch.WordTrace tailWord_2530248 prefixEnd_2530248 866155599385014417842405 := by
  unfold tailWord_2530248
  simp only [CollatzResearch.WordTrace]
  refine ⟨46142863068675551399863699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61523817424900735199818265 46142863068675551399863699)
  ·
    refine ⟨69214294603013327099795549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46142863068675551399863699 69214294603013327099795549)
    ·
      refine ⟨25955360476129997662423331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69214294603013327099795549 25955360476129997662423331)
      ·
        refine ⟨38933040714194996493634997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25955360476129997662423331 38933040714194996493634997)
        ·
          refine ⟨3649972566955780921278281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38933040714194996493634997 3649972566955780921278281)
          ·
            refine ⟨2737479425216835690958711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3649972566955780921278281 2737479425216835690958711)
            ·
              refine ⟨4106219137825253536438067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2737479425216835690958711 4106219137825253536438067)
              ·
                refine ⟨6159328706737880304657101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4106219137825253536438067 6159328706737880304657101)
                ·
                  refine ⟨2309748265026705114246413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6159328706737880304657101 2309748265026705114246413)
                  ·
                    refine ⟨866155599385014417842405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2309748265026705114246413 866155599385014417842405)
                    ·
                      rfl

theorem cell22_2530248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_2530248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2530248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2530248 prefixEnd_2530248 := by exact prefixLift 2530248
  have htrace : WordTrace (prefixWord ++ tailWord_2530248) baseStart_2530248 baseEnd_2530248 := by
    simpa [prefixWord, tailWord_2530248, baseEnd_2530248] using wordTrace_append hprefix tailTrace_2530248
  have hstable : (prefixWord ++ tailWord_2530248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530248).length < 2 ^ (prefixWord ++ tailWord_2530248).sum := by decide
  have hdescent : baseEnd_2530248 < baseStart_2530248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530261 : List Nat := [1, 3, 2, 3, 3, 1, 1, 3, 5]
def baseStart_2530261 : Nat := 118140960795 + 2530261 * 2 ^ 59
def prefixEnd_2530261 : Nat := 4983230072969 + 3 ^ 40 * 2530261 * 2
def baseEnd_2530261 : Nat := 288720016516895572422455

theorem tailTrace_2530261 : CollatzResearch.WordTrace tailWord_2530261 prefixEnd_2530261 288720016516895572422455 := by
  unfold tailWord_2530261
  simp only [CollatzResearch.WordTrace]
  refine ⟨92286200286304006019950637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61524133524202670679967091 92286200286304006019950637)
  ·
    refine ⟨34607325107364002257481489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92286200286304006019950637 34607325107364002257481489)
    ·
      refine ⟨25955493830523001693111117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34607325107364002257481489 25955493830523001693111117)
      ·
        refine ⟨9733310186446125634916669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25955493830523001693111117 9733310186446125634916669)
        ·
          refine ⟨3649991319917297113093751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9733310186446125634916669 3649991319917297113093751)
          ·
            refine ⟨5474986979875945669640627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3649991319917297113093751 5474986979875945669640627)
            ·
              refine ⟨8212480469813918504460941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5474986979875945669640627 8212480469813918504460941)
              ·
                refine ⟨3079680176180219439172853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8212480469813918504460941 3079680176180219439172853)
                ·
                  refine ⟨288720016516895572422455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3079680176180219439172853 288720016516895572422455)
                  ·
                    rfl

theorem cell22_2530261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 5].length) (baseStart_2530261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2530261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2530261 prefixEnd_2530261 := by exact prefixLift 2530261
  have htrace : WordTrace (prefixWord ++ tailWord_2530261) baseStart_2530261 baseEnd_2530261 := by
    simpa [prefixWord, tailWord_2530261, baseEnd_2530261] using wordTrace_append hprefix tailTrace_2530261
  have hstable : (prefixWord ++ tailWord_2530261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530261).length < 2 ^ (prefixWord ++ tailWord_2530261).sum := by decide
  have hdescent : baseEnd_2530261 < baseStart_2530261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530304 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 8, 3]
def baseStart_2530304 : Nat := 118140960795 + 2530304 * 2 ^ 59
def prefixEnd_2530304 : Nat := 4983230072969 + 3 ^ 40 * 2530304 * 2
def baseEnd_2530304 : Nat := 866174769329448938442233

theorem tailTrace_2530304 : CollatzResearch.WordTrace tailWord_2530304 prefixEnd_2530304 866174769329448938442233 := by
  unfold tailWord_2530304
  simp only [CollatzResearch.WordTrace]
  refine ⟨46143884312574112181882983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61525179083432149575843977 46143884312574112181882983)
  ·
    refine ⟨69215826468861168272824475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46143884312574112181882983 69215826468861168272824475)
    ·
      refine ⟨103823739703291752409236713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69215826468861168272824475 103823739703291752409236713)
      ·
        refine ⟨77867804777468814306927535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103823739703291752409236713 77867804777468814306927535)
        ·
          refine ⟨116801707166203221460391303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77867804777468814306927535 116801707166203221460391303)
          ·
            refine ⟨175202560749304832190586955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116801707166203221460391303 175202560749304832190586955)
            ·
              refine ⟨262803841123957248285880433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175202560749304832190586955 262803841123957248285880433)
              ·
                refine ⟨197102880842967936214410325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 262803841123957248285880433 197102880842967936214410325)
                ·
                  refine ⟨2309799384878530502512621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 197102880842967936214410325 2309799384878530502512621)
                  ·
                    refine ⟨866174769329448938442233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2309799384878530502512621 866174769329448938442233)
                    ·
                      rfl

theorem cell22_2530304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 8, 3].length) (baseStart_2530304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2530304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2530304 prefixEnd_2530304 := by exact prefixLift 2530304
  have htrace : WordTrace (prefixWord ++ tailWord_2530304) baseStart_2530304 baseEnd_2530304 := by
    simpa [prefixWord, tailWord_2530304, baseEnd_2530304] using wordTrace_append hprefix tailTrace_2530304
  have hstable : (prefixWord ++ tailWord_2530304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530304).length < 2 ^ (prefixWord ++ tailWord_2530304).sum := by decide
  have hdescent : baseEnd_2530304 < baseStart_2530304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530394 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 4, 5]
def baseStart_2530394 : Nat := 118140960795 + 2530394 * 2 ^ 59
def prefixEnd_2530394 : Nat := 4983230072969 + 3 ^ 40 * 2530394 * 2
def baseEnd_2530394 : Nat := 866205578168718703691957

theorem tailTrace_2530394 : CollatzResearch.WordTrace tailWord_2530394 prefixEnd_2530394 866205578168718703691957 := by
  unfold tailWord_2530394
  simp only [CollatzResearch.WordTrace]
  refine ⟨23072762798705542433635559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61527367463214779823028157 23072762798705542433635559)
  ·
    refine ⟨34609144198058313650453339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23072762798705542433635559 34609144198058313650453339)
    ·
      refine ⟨51913716297087470475680009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34609144198058313650453339 51913716297087470475680009)
      ·
        refine ⟨38935287222815602856760007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51913716297087470475680009 38935287222815602856760007)
        ·
          refine ⟨58402930834223404285140011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38935287222815602856760007 58402930834223404285140011)
          ·
            refine ⟨87604396251335106427710017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58402930834223404285140011 87604396251335106427710017)
            ·
              refine ⟨65703297188501329820782513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87604396251335106427710017 65703297188501329820782513)
              ·
                refine ⟨49277472891375997365586885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65703297188501329820782513 49277472891375997365586885)
                ·
                  refine ⟨9239526167132999506047541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49277472891375997365586885 9239526167132999506047541)
                  ·
                    refine ⟨866205578168718703691957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9239526167132999506047541 866205578168718703691957)
                    ·
                      rfl

theorem cell22_2530394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_2530394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2530394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2530394 prefixEnd_2530394 := by exact prefixLift 2530394
  have htrace : WordTrace (prefixWord ++ tailWord_2530394) baseStart_2530394 baseEnd_2530394 := by
    simpa [prefixWord, tailWord_2530394, baseEnd_2530394] using wordTrace_append hprefix tailTrace_2530394
  have hstable : (prefixWord ++ tailWord_2530394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530394).length < 2 ^ (prefixWord ++ tailWord_2530394).sum := by decide
  have hdescent : baseEnd_2530394 < baseStart_2530394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530456 : List Nat := [2, 1, 2, 4, 2, 1, 1, 1, 3, 5]
def baseStart_2530456 : Nat := 118140960795 + 2530456 * 2 ^ 59
def prefixEnd_2530456 : Nat := 4983230072969 + 3 ^ 40 * 2530456 * 2
def baseEnd_2530456 : Nat := 866226802035771208641767

theorem tailTrace_2530456 : CollatzResearch.WordTrace tailWord_2530456 prefixEnd_2530456 866226802035771208641767 := by
  unfold tailWord_2530456
  simp only [CollatzResearch.WordTrace]
  refine ⟨46146656260298777161649611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61528875013731702882199481 46146656260298777161649611)
  ·
    refine ⟨69219984390448165742474417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46146656260298777161649611 69219984390448165742474417)
    ·
      refine ⟨51914988292836124306855813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69219984390448165742474417 51914988292836124306855813)
      ·
        refine ⟨9734060304906773307535465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51914988292836124306855813 9734060304906773307535465)
        ·
          refine ⟨7300545228680079980651599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9734060304906773307535465 7300545228680079980651599)
          ·
            refine ⟨10950817843020119970977399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7300545228680079980651599 10950817843020119970977399)
            ·
              refine ⟨16426226764530179956466099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10950817843020119970977399 16426226764530179956466099)
              ·
                refine ⟨24639340146795269934699149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16426226764530179956466099 24639340146795269934699149)
                ·
                  refine ⟨9239752555048226225512181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24639340146795269934699149 9239752555048226225512181)
                  ·
                    refine ⟨866226802035771208641767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9239752555048226225512181 866226802035771208641767)
                    ·
                      rfl

theorem cell22_2530456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_2530456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2530456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2530456 prefixEnd_2530456 := by exact prefixLift 2530456
  have htrace : WordTrace (prefixWord ++ tailWord_2530456) baseStart_2530456 baseEnd_2530456 := by
    simpa [prefixWord, tailWord_2530456, baseEnd_2530456] using wordTrace_append hprefix tailTrace_2530456
  have hstable : (prefixWord ++ tailWord_2530456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530456).length < 2 ^ (prefixWord ++ tailWord_2530456).sum := by decide
  have hdescent : baseEnd_2530456 < baseStart_2530456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530460 : List Nat := [2, 2, 3, 2, 1, 3, 3, 1, 1, 4]
def baseStart_2530460 : Nat := 118140960795 + 2530460 * 2 ^ 59
def prefixEnd_2530460 : Nat := 4983230072969 + 3 ^ 40 * 2530460 * 2
def baseEnd_2530460 : Nat := 866228171317516531541755

theorem tailTrace_2530460 : CollatzResearch.WordTrace tailWord_2530460 prefixEnd_2530460 866228171317516531541755 := by
  unfold tailWord_2530460
  simp only [CollatzResearch.WordTrace]
  refine ⟨46146729206291531503222417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61528972275055375337629889 46146729206291531503222417)
  ·
    refine ⟨34610046904718648627416813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46146729206291531503222417 34610046904718648627416813)
    ·
      refine ⟨12978767589269493235281305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34610046904718648627416813 12978767589269493235281305)
      ·
        refine ⟨9734075691952119926460979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12978767589269493235281305 9734075691952119926460979)
        ·
          refine ⟨14601113537928179889691469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9734075691952119926460979 14601113537928179889691469)
          ·
            refine ⟨5475417576723067458634301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14601113537928179889691469 5475417576723067458634301)
            ·
              refine ⟨2053281591271150296987863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5475417576723067458634301 2053281591271150296987863)
              ·
                refine ⟨3079922386906725445481795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2053281591271150296987863 3079922386906725445481795)
                ·
                  refine ⟨4619883580360088168222693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3079922386906725445481795 4619883580360088168222693)
                  ·
                    refine ⟨866228171317516531541755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4619883580360088168222693 866228171317516531541755)
                    ·
                      rfl

theorem cell22_2530460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_2530460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2530460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2530460 prefixEnd_2530460 := by exact prefixLift 2530460
  have htrace : WordTrace (prefixWord ++ tailWord_2530460) baseStart_2530460 baseEnd_2530460 := by
    simpa [prefixWord, tailWord_2530460, baseEnd_2530460] using wordTrace_append hprefix tailTrace_2530460
  have hstable : (prefixWord ++ tailWord_2530460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530460).length < 2 ^ (prefixWord ++ tailWord_2530460).sum := by decide
  have hdescent : baseEnd_2530460 < baseStart_2530460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530469 : List Nat := [1, 3, 1, 2, 1, 14]
def baseStart_2530469 : Nat := 118140960795 + 2530469 * 2 ^ 59
def prefixEnd_2530469 : Nat := 4983230072969 + 3 ^ 40 * 2530469 * 2
def baseEnd_2530469 : Nat := 10694212990141277877367

theorem tailTrace_2530469 : CollatzResearch.WordTrace tailWord_2530469 prefixEnd_2530469 10694212990141277877367 := by
  unfold tailWord_2530469
  simp only [CollatzResearch.WordTrace]
  refine ⟨92293786669550457543522461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61529191113033638362348307 92293786669550457543522461)
  ·
    refine ⟨34610170001081421578820923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92293786669550457543522461 34610170001081421578820923)
    ·
      refine ⟨51915255001622132368231385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34610170001081421578820923 51915255001622132368231385)
      ·
        refine ⟨38936441251216599276173539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51915255001622132368231385 38936441251216599276173539)
        ·
          refine ⟨58404661876824898914260309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38936441251216599276173539 58404661876824898914260309)
          ·
            refine ⟨10694212990141277877367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 58404661876824898914260309 10694212990141277877367)
            ·
              rfl

theorem cell22_2530469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 14].length) (baseStart_2530469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2530469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2530469 prefixEnd_2530469 := by exact prefixLift 2530469
  have htrace : WordTrace (prefixWord ++ tailWord_2530469) baseStart_2530469 baseEnd_2530469 := by
    simpa [prefixWord, tailWord_2530469, baseEnd_2530469] using wordTrace_append hprefix tailTrace_2530469
  have hstable : (prefixWord ++ tailWord_2530469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530469).length < 2 ^ (prefixWord ++ tailWord_2530469).sum := by decide
  have hdescent : baseEnd_2530469 < baseStart_2530469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530509 : List Nat := [1, 6, 2, 2, 1, 1, 2, 3, 4]
def baseStart_2530509 : Nat := 118140960795 + 2530509 * 2 ^ 59
def prefixEnd_2530509 : Nat := 4983230072969 + 3 ^ 40 * 2530509 * 2
def baseEnd_2530509 : Nat := 288748315006298912355535

theorem tailTrace_2530509 : CollatzResearch.WordTrace tailWord_2530509 prefixEnd_2530509 288748315006298912355535 := by
  unfold tailWord_2530509
  simp only [CollatzResearch.WordTrace]
  refine ⟨92295245589405544374978581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61530163726270362916652387 92295245589405544374978581)
  ·
    refine ⟨4326339637003384892577121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 92295245589405544374978581 4326339637003384892577121)
    ·
      refine ⟨3244754727752538669432841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4326339637003384892577121 3244754727752538669432841)
      ·
        refine ⟨2433566045814404002074631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3244754727752538669432841 2433566045814404002074631)
        ·
          refine ⟨3650349068721606003111947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2433566045814404002074631 3650349068721606003111947)
          ·
            refine ⟨5475523603082409004667921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3650349068721606003111947 5475523603082409004667921)
            ·
              refine ⟨4106642702311806753500941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5475523603082409004667921 4106642702311806753500941)
              ·
                refine ⟨1539991013366927532562853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4106642702311806753500941 1539991013366927532562853)
                ·
                  refine ⟨288748315006298912355535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1539991013366927532562853 288748315006298912355535)
                  ·
                    rfl

theorem cell22_2530509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_2530509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2530509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2530509 prefixEnd_2530509 := by exact prefixLift 2530509
  have htrace : WordTrace (prefixWord ++ tailWord_2530509) baseStart_2530509 baseEnd_2530509 := by
    simpa [prefixWord, tailWord_2530509, baseEnd_2530509] using wordTrace_append hprefix tailTrace_2530509
  have hstable : (prefixWord ++ tailWord_2530509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530509).length < 2 ^ (prefixWord ++ tailWord_2530509).sum := by decide
  have hdescent : baseEnd_2530509 < baseStart_2530509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530623 : List Nat := [1, 1, 2, 2, 4, 2, 1, 3, 2, 4]
def baseStart_2530623 : Nat := 118140960795 + 2530623 * 2 ^ 59
def prefixEnd_2530623 : Nat := 4983230072969 + 3 ^ 40 * 2530623 * 2
def baseEnd_2530623 : Nat := 866283969548638439716255

theorem tailTrace_2530623 : CollatzResearch.WordTrace tailWord_2530623 prefixEnd_2530623 866283969548638439716255 := by
  unfold tailWord_2530623
  simp only [CollatzResearch.WordTrace]
  refine ⟨92299403510992541844628523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61532935673995027896419015 92299403510992541844628523)
  ·
    refine ⟨138449105266488812766942785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92299403510992541844628523 138449105266488812766942785)
    ·
      refine ⟨103836828949866609575207089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138449105266488812766942785 103836828949866609575207089)
      ·
        refine ⟨77877621712399957181405317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103836828949866609575207089 77877621712399957181405317)
        ·
          refine ⟨14602054071074991971513497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77877621712399957181405317 14602054071074991971513497)
          ·
            refine ⟨10951540553306243978635123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14602054071074991971513497 10951540553306243978635123)
            ·
              refine ⟨16427310829959365967952685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10951540553306243978635123 16427310829959365967952685)
              ·
                refine ⟨6160241561234762237982257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16427310829959365967952685 6160241561234762237982257)
                ·
                  refine ⟨4620181170926071678486693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6160241561234762237982257 4620181170926071678486693)
                  ·
                    refine ⟨866283969548638439716255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4620181170926071678486693 866283969548638439716255)
                    ·
                      rfl

theorem cell22_2530623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 4].length) (baseStart_2530623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2530623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2530623 prefixEnd_2530623 := by exact prefixLift 2530623
  have htrace : WordTrace (prefixWord ++ tailWord_2530623) baseStart_2530623 baseEnd_2530623 := by
    simpa [prefixWord, tailWord_2530623, baseEnd_2530623] using wordTrace_append hprefix tailTrace_2530623
  have hstable : (prefixWord ++ tailWord_2530623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530623).length < 2 ^ (prefixWord ++ tailWord_2530623).sum := by decide
  have hdescent : baseEnd_2530623 < baseStart_2530623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530625 : List Nat := [1, 2, 5, 2, 1, 2, 1, 2, 1, 5]
def baseStart_2530625 : Nat := 118140960795 + 2530625 * 2 ^ 59
def prefixEnd_2530625 : Nat := 4983230072969 + 3 ^ 40 * 2530625 * 2
def baseEnd_2530625 : Nat := 866284654189511101166249

theorem tailTrace_2530625 : CollatzResearch.WordTrace tailWord_2530625 prefixEnd_2530625 866284654189511101166249 := by
  unfold tailWord_2530625
  simp only [CollatzResearch.WordTrace]
  refine ⟨92299476456985296186201329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61532984304656864124134219 92299476456985296186201329)
  ·
    refine ⟨69224607342738972139650997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92299476456985296186201329 69224607342738972139650997)
    ·
      refine ⟨6489806938381778638092281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69224607342738972139650997 6489806938381778638092281)
      ·
        refine ⟨4867355203786333978569211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6489806938381778638092281 4867355203786333978569211)
        ·
          refine ⟨7301032805679500967853817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4867355203786333978569211 7301032805679500967853817)
          ·
            refine ⟨5475774604259625725890363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7301032805679500967853817 5475774604259625725890363)
            ·
              refine ⟨8213661906389438588835545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5475774604259625725890363 8213661906389438588835545)
              ·
                refine ⟨6160246429792078941626659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8213661906389438588835545 6160246429792078941626659)
                ·
                  refine ⟨9240369644688118412439989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6160246429792078941626659 9240369644688118412439989)
                  ·
                    refine ⟨866284654189511101166249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9240369644688118412439989 866284654189511101166249)
                    ·
                      rfl

theorem cell22_2530625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_2530625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2530625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2530625 prefixEnd_2530625 := by exact prefixLift 2530625
  have htrace : WordTrace (prefixWord ++ tailWord_2530625) baseStart_2530625 baseEnd_2530625 := by
    simpa [prefixWord, tailWord_2530625, baseEnd_2530625] using wordTrace_append hprefix tailTrace_2530625
  have hstable : (prefixWord ++ tailWord_2530625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530625).length < 2 ^ (prefixWord ++ tailWord_2530625).sum := by decide
  have hdescent : baseEnd_2530625 < baseStart_2530625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530717 : List Nat := [1, 4, 2, 1, 3, 2, 3, 1, 5]
def baseStart_2530717 : Nat := 118140960795 + 2530717 * 2 ^ 59
def prefixEnd_2530717 : Nat := 4983230072969 + 3 ^ 40 * 2530717 * 2
def baseEnd_2530717 : Nat := 288772049223217842621989

theorem tailTrace_2530717 : CollatzResearch.WordTrace tailWord_2530717 prefixEnd_2530717 288772049223217842621989 := by
  unfold tailWord_2530717
  simp only [CollatzResearch.WordTrace]
  refine ⟨92302831972651995898550405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61535221315101330599033603 92302831972651995898550405)
  ·
    refine ⟨17306780994872249230978201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92302831972651995898550405 17306780994872249230978201)
    ·
      refine ⟨12980085746154186923233651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17306780994872249230978201 12980085746154186923233651)
      ·
        refine ⟨19470128619231280384850477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12980085746154186923233651 19470128619231280384850477)
        ·
          refine ⟨7301298232211730144318929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19470128619231280384850477 7301298232211730144318929)
          ·
            refine ⟨5475973674158797608239197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7301298232211730144318929 5475973674158797608239197)
            ·
              refine ⟨2053490127809549103089699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5475973674158797608239197 2053490127809549103089699)
              ·
                refine ⟨3080235191714323654634549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2053490127809549103089699 3080235191714323654634549)
                ·
                  refine ⟨288772049223217842621989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3080235191714323654634549 288772049223217842621989)
                  ·
                    rfl

theorem cell22_2530717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_2530717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2530717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2530717 prefixEnd_2530717 := by exact prefixLift 2530717
  have htrace : WordTrace (prefixWord ++ tailWord_2530717) baseStart_2530717 baseEnd_2530717 := by
    simpa [prefixWord, tailWord_2530717, baseEnd_2530717] using wordTrace_append hprefix tailTrace_2530717
  have hstable : (prefixWord ++ tailWord_2530717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530717).length < 2 ^ (prefixWord ++ tailWord_2530717).sum := by decide
  have hdescent : baseEnd_2530717 < baseStart_2530717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530743 : List Nat := [1, 1, 3, 1, 3, 2, 2, 1, 3, 5]
def baseStart_2530743 : Nat := 118140960795 + 2530743 * 2 ^ 59
def prefixEnd_2530743 : Nat := 4983230072969 + 3 ^ 40 * 2530743 * 2
def baseEnd_2530743 : Nat := 866325048000998126715887

theorem tailTrace_2530743 : CollatzResearch.WordTrace tailWord_2530743 prefixEnd_2530743 866325048000998126715887 := by
  unfold tailWord_2530743
  simp only [CollatzResearch.WordTrace]
  refine ⟨92303780270557802338996883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61535853513705201559331255 92303780270557802338996883)
  ·
    refine ⟨138455670405836703508495325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92303780270557802338996883 138455670405836703508495325)
    ·
      refine ⟨51920876402188763815685747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138455670405836703508495325 51920876402188763815685747)
      ·
        refine ⟨77881314603283145723528621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51920876402188763815685747 77881314603283145723528621)
        ·
          refine ⟨29205492976231179646323233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77881314603283145723528621 29205492976231179646323233)
          ·
            refine ⟨21904119732173384734742425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29205492976231179646323233 21904119732173384734742425)
            ·
              refine ⟨16428089799130038551056819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21904119732173384734742425 16428089799130038551056819)
              ·
                refine ⟨24642134698695057826585229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16428089799130038551056819 24642134698695057826585229)
                ·
                  refine ⟨9240800512010646684969461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24642134698695057826585229 9240800512010646684969461)
                  ·
                    refine ⟨866325048000998126715887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9240800512010646684969461 866325048000998126715887)
                    ·
                      rfl

theorem cell22_2530743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_2530743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2530743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2530743 prefixEnd_2530743 := by exact prefixLift 2530743
  have htrace : WordTrace (prefixWord ++ tailWord_2530743) baseStart_2530743 baseEnd_2530743 := by
    simpa [prefixWord, tailWord_2530743, baseEnd_2530743] using wordTrace_append hprefix tailTrace_2530743
  have hstable : (prefixWord ++ tailWord_2530743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530743).length < 2 ^ (prefixWord ++ tailWord_2530743).sum := by decide
  have hdescent : baseEnd_2530743 < baseStart_2530743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530760 : List Nat := [2, 1, 3, 1, 3, 1, 1, 3, 4, 3]
def baseStart_2530760 : Nat := 118140960795 + 2530760 * 2 ^ 59
def prefixEnd_2530760 : Nat := 4983230072969 + 3 ^ 40 * 2530760 * 2
def baseEnd_2530760 : Nat := 866330867448415749040835

theorem tailTrace_2530760 : CollatzResearch.WordTrace tailWord_2530760 prefixEnd_2530760 866330867448415749040835 := by
  unfold tailWord_2530760
  simp only [CollatzResearch.WordTrace]
  refine ⟨46152200155748107121182867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61536266874330809494910489 46152200155748107121182867)
  ·
    refine ⟨69228300233622160681774301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46152200155748107121182867 69228300233622160681774301)
    ·
      refine ⟨25960612587608310255665363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69228300233622160681774301 25960612587608310255665363)
      ·
        refine ⟨38940918881412465383498045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25960612587608310255665363 38940918881412465383498045)
        ·
          refine ⟨14602844580529674518811767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38940918881412465383498045 14602844580529674518811767)
          ·
            refine ⟨21904266870794511778217651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14602844580529674518811767 21904266870794511778217651)
            ·
              refine ⟨32856400306191767667326477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21904266870794511778217651 32856400306191767667326477)
              ·
                refine ⟨12321150114821912875247429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32856400306191767667326477 12321150114821912875247429)
                ·
                  refine ⟨2310215646529108664108893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12321150114821912875247429 2310215646529108664108893)
                  ·
                    refine ⟨866330867448415749040835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2310215646529108664108893 866330867448415749040835)
                    ·
                      rfl

theorem cell22_2530760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_2530760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2530760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2530760 prefixEnd_2530760 := by exact prefixLift 2530760
  have htrace : WordTrace (prefixWord ++ tailWord_2530760) baseStart_2530760 baseEnd_2530760 := by
    simpa [prefixWord, tailWord_2530760, baseEnd_2530760] using wordTrace_append hprefix tailTrace_2530760
  have hstable : (prefixWord ++ tailWord_2530760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530760).length < 2 ^ (prefixWord ++ tailWord_2530760).sum := by decide
  have hdescent : baseEnd_2530760 < baseStart_2530760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530777 : List Nat := [1, 2, 1, 2, 4, 3, 1, 3, 2, 3]
def baseStart_2530777 : Nat := 118140960795 + 2530777 * 2 ^ 59
def prefixEnd_2530777 : Nat := 4983230072969 + 3 ^ 40 * 2530777 * 2
def baseEnd_2530777 : Nat := 866336686895833371365783

theorem tailTrace_2530777 : CollatzResearch.WordTrace tailWord_2530777 prefixEnd_2530777 866336686895833371365783 := by
  unfold tailWord_2530777
  simp only [CollatzResearch.WordTrace]
  refine ⟨92305020352434626145734585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61536680234956417430489723 92305020352434626145734585)
  ·
    refine ⟨69228765264325969609300939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92305020352434626145734585 69228765264325969609300939)
    ·
      refine ⟨103843147896488954413951409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69228765264325969609300939 103843147896488954413951409)
      ·
        refine ⟨77882360922366715810463557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103843147896488954413951409 77882360922366715810463557)
        ·
          refine ⟨14602942672943759214461917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77882360922366715810463557 14602942672943759214461917)
          ·
            refine ⟨5476103502353909705423219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14602942672943759214461917 5476103502353909705423219)
            ·
              refine ⟨8214155253530864558134829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5476103502353909705423219 8214155253530864558134829)
              ·
                refine ⟨3080308220074074209300561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8214155253530864558134829 3080308220074074209300561)
                ·
                  refine ⟨2310231165055555656975421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3080308220074074209300561 2310231165055555656975421)
                  ·
                    refine ⟨866336686895833371365783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2310231165055555656975421 866336686895833371365783)
                    ·
                      rfl

theorem cell22_2530777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 3, 2, 3].length) (baseStart_2530777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2530777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2530777 prefixEnd_2530777 := by exact prefixLift 2530777
  have htrace : WordTrace (prefixWord ++ tailWord_2530777) baseStart_2530777 baseEnd_2530777 := by
    simpa [prefixWord, tailWord_2530777, baseEnd_2530777] using wordTrace_append hprefix tailTrace_2530777
  have hstable : (prefixWord ++ tailWord_2530777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530777).length < 2 ^ (prefixWord ++ tailWord_2530777).sum := by decide
  have hdescent : baseEnd_2530777 < baseStart_2530777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530788 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 2, 7]
def baseStart_2530788 : Nat := 118140960795 + 2530788 * 2 ^ 59
def prefixEnd_2530788 : Nat := 4983230072969 + 3 ^ 40 * 2530788 * 2
def baseEnd_2530788 : Nat := 866340452420633009340749

theorem tailTrace_2530788 : CollatzResearch.WordTrace tailWord_2530788 prefixEnd_2530788 866340452420633009340749 := by
  unfold tailWord_2530788
  simp only [CollatzResearch.WordTrace]
  refine ⟨46152710777697387512192509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61536947703596516682923345 46152710777697387512192509)
  ·
    refine ⟨17307266541636520317072191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46152710777697387512192509 17307266541636520317072191)
    ·
      refine ⟨25960899812454780475608287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17307266541636520317072191 25960899812454780475608287)
      ·
        refine ⟨38941349718682170713412431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25960899812454780475608287 38941349718682170713412431)
        ·
          refine ⟨58412024578023256070118647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38941349718682170713412431 58412024578023256070118647)
          ·
            refine ⟨87618036867034884105177971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58412024578023256070118647 87618036867034884105177971)
            ·
              refine ⟨131427055300552326157766957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87618036867034884105177971 131427055300552326157766957)
              ·
                refine ⟨49285145737707122309162609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131427055300552326157766957 49285145737707122309162609)
                ·
                  refine ⟨36963859303280341731871957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49285145737707122309162609 36963859303280341731871957)
                  ·
                    refine ⟨866340452420633009340749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36963859303280341731871957 866340452420633009340749)
                    ·
                      rfl

theorem cell22_2530788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_2530788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2530788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2530788 prefixEnd_2530788 := by exact prefixLift 2530788
  have htrace : WordTrace (prefixWord ++ tailWord_2530788) baseStart_2530788 baseEnd_2530788 := by
    simpa [prefixWord, tailWord_2530788, baseEnd_2530788] using wordTrace_append hprefix tailTrace_2530788
  have hstable : (prefixWord ++ tailWord_2530788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530788).length < 2 ^ (prefixWord ++ tailWord_2530788).sum := by decide
  have hdescent : baseEnd_2530788 < baseStart_2530788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2530835 : List Nat := [1, 1, 1, 2, 1, 6, 2, 3, 5]
def baseStart_2530835 : Nat := 118140960795 + 2530835 * 2 ^ 59
def prefixEnd_2530835 : Nat := 4983230072969 + 3 ^ 40 * 2530835 * 2
def baseEnd_2530835 : Nat := 288785513827046851138535

theorem tailTrace_2530835 : CollatzResearch.WordTrace tailWord_2530835 prefixEnd_2530835 288785513827046851138535 := by
  unfold tailWord_2530835
  simp only [CollatzResearch.WordTrace]
  refine ⟨92307135786224502051345959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61538090524149668034230639 92307135786224502051345959)
  ·
    refine ⟨138460703679336753077018939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92307135786224502051345959 138460703679336753077018939)
    ·
      refine ⟨207691055519005129615528409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138460703679336753077018939 207691055519005129615528409)
      ·
        refine ⟨155768291639253847211646307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207691055519005129615528409 155768291639253847211646307)
        ·
          refine ⟨233652437458880770817469461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155768291639253847211646307 233652437458880770817469461)
          ·
            refine ⟨10952458005885036132068881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 233652437458880770817469461 10952458005885036132068881)
            ·
              refine ⟨8214343504413777099051661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10952458005885036132068881 8214343504413777099051661)
              ·
                refine ⟨3080378814155166412144373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8214343504413777099051661 3080378814155166412144373)
                ·
                  refine ⟨288785513827046851138535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3080378814155166412144373 288785513827046851138535)
                  ·
                    rfl

theorem cell22_2530835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 5].length) (baseStart_2530835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2530835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2530835 prefixEnd_2530835 := by exact prefixLift 2530835
  have htrace : WordTrace (prefixWord ++ tailWord_2530835) baseStart_2530835 baseEnd_2530835 := by
    simpa [prefixWord, tailWord_2530835, baseEnd_2530835] using wordTrace_append hprefix tailTrace_2530835
  have hstable : (prefixWord ++ tailWord_2530835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2530835).length < 2 ^ (prefixWord ++ tailWord_2530835).sum := by decide
  have hdescent : baseEnd_2530835 < baseStart_2530835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2530835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531002 : List Nat := [3, 1, 1, 1, 2, 5, 1, 1, 2, 5]
def baseStart_2531002 : Nat := 118140960795 + 2531002 * 2 ^ 59
def prefixEnd_2531002 : Nat := 4983230072969 + 3 ^ 40 * 2531002 * 2
def baseEnd_2531002 : Nat := 866413708994007784490093

theorem tailTrace_2531002 : CollatzResearch.WordTrace tailWord_2531002 prefixEnd_2531002 866413708994007784490093 := by
  unfold tailWord_2531002
  simp only [CollatzResearch.WordTrace]
  refine ⟨23078306694154872393168815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61542151184412993048450173 23078306694154872393168815)
  ·
    refine ⟨34617460041232308589753223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23078306694154872393168815 34617460041232308589753223)
    ·
      refine ⟨51926190061848462884629835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34617460041232308589753223 51926190061848462884629835)
      ·
        refine ⟨77889285092772694326944753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51926190061848462884629835 77889285092772694326944753)
        ·
          refine ⟨58416963819579520745208565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77889285092772694326944753 58416963819579520745208565)
          ·
            refine ⟨5476590358085580069863303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58416963819579520745208565 5476590358085580069863303)
            ·
              refine ⟨8214885537128370104794955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5476590358085580069863303 8214885537128370104794955)
              ·
                refine ⟨12322328305692555157192433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8214885537128370104794955 12322328305692555157192433)
                ·
                  refine ⟨9241746229269416367894325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12322328305692555157192433 9241746229269416367894325)
                  ·
                    refine ⟨866413708994007784490093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9241746229269416367894325 866413708994007784490093)
                    ·
                      rfl

theorem cell22_2531002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_2531002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2531002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2531002 prefixEnd_2531002 := by exact prefixLift 2531002
  have htrace : WordTrace (prefixWord ++ tailWord_2531002) baseStart_2531002 baseEnd_2531002 := by
    simpa [prefixWord, tailWord_2531002, baseEnd_2531002] using wordTrace_append hprefix tailTrace_2531002
  have hstable : (prefixWord ++ tailWord_2531002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531002).length < 2 ^ (prefixWord ++ tailWord_2531002).sum := by decide
  have hdescent : baseEnd_2531002 < baseStart_2531002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531034 : List Nat := [3, 1, 1, 2, 2, 4, 1, 3, 1, 4]
def baseStart_2531034 : Nat := 118140960795 + 2531034 * 2 ^ 59
def prefixEnd_2531034 : Nat := 4983230072969 + 3 ^ 40 * 2531034 * 2
def baseEnd_2531034 : Nat := 866424663247970367689995

theorem tailTrace_2531034 : CollatzResearch.WordTrace tailWord_2531034 prefixEnd_2531034 866424663247970367689995 := by
  unfold tailWord_2531034
  simp only [CollatzResearch.WordTrace]
  refine ⟨23078598478125889759460039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61542929275002372691893437 23078598478125889759460039)
  ·
    refine ⟨34617897717188834639190059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23078598478125889759460039 34617897717188834639190059)
    ·
      refine ⟨51926846575783251958785089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34617897717188834639190059 51926846575783251958785089)
      ·
        refine ⟨38945134931837438969088817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51926846575783251958785089 38945134931837438969088817)
        ·
          refine ⟨29208851198878079226816613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38945134931837438969088817 29208851198878079226816613)
          ·
            refine ⟨5476659599789639855028115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29208851198878079226816613 5476659599789639855028115)
            ·
              refine ⟨8214989399684459782542173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5476659599789639855028115 8214989399684459782542173)
              ·
                refine ⟨3080621024881672418453315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8214989399684459782542173 3080621024881672418453315)
                ·
                  refine ⟨4620931537322508627679973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3080621024881672418453315 4620931537322508627679973)
                  ·
                    refine ⟨866424663247970367689995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4620931537322508627679973 866424663247970367689995)
                    ·
                      rfl

theorem cell22_2531034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 1, 4].length) (baseStart_2531034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2531034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2531034 prefixEnd_2531034 := by exact prefixLift 2531034
  have htrace : WordTrace (prefixWord ++ tailWord_2531034) baseStart_2531034 baseEnd_2531034 := by
    simpa [prefixWord, tailWord_2531034, baseEnd_2531034] using wordTrace_append hprefix tailTrace_2531034
  have hstable : (prefixWord ++ tailWord_2531034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531034).length < 2 ^ (prefixWord ++ tailWord_2531034).sum := by decide
  have hdescent : baseEnd_2531034 < baseStart_2531034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531156 : List Nat := [2, 4, 1, 1, 3, 2, 2, 2, 5]
def baseStart_2531156 : Nat := 118140960795 + 2531156 * 2 ^ 59
def prefixEnd_2531156 : Nat := 4983230072969 + 3 ^ 40 * 2531156 * 2
def baseEnd_2531156 : Nat := 288822142113734238713207

theorem tailTrace_2531156 : CollatzResearch.WordTrace tailWord_2531156 prefixEnd_2531156 288822142113734238713207 := by
  unfold tailWord_2531156
  simp only [CollatzResearch.WordTrace]
  refine ⟨46159421809030786936890661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61545895745374382582520881 46159421809030786936890661)
  ·
    refine ⟨8654891589193272550666999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46159421809030786936890661 8654891589193272550666999)
    ·
      refine ⟨12982337383789908826000499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8654891589193272550666999 12982337383789908826000499)
      ·
        refine ⟨19473506075684863239000749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12982337383789908826000499 19473506075684863239000749)
        ·
          refine ⟨7302564778381823714625281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19473506075684863239000749 7302564778381823714625281)
          ·
            refine ⟨5476923583786367785968961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7302564778381823714625281 5476923583786367785968961)
            ·
              refine ⟨4107692687839775839476721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5476923583786367785968961 4107692687839775839476721)
              ·
                refine ⟨3080769515879831879607541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4107692687839775839476721 3080769515879831879607541)
                ·
                  refine ⟨288822142113734238713207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3080769515879831879607541 288822142113734238713207)
                  ·
                    rfl

theorem cell22_2531156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_2531156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2531156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2531156 prefixEnd_2531156 := by exact prefixLift 2531156
  have htrace : WordTrace (prefixWord ++ tailWord_2531156) baseStart_2531156 baseEnd_2531156 := by
    simpa [prefixWord, tailWord_2531156, baseEnd_2531156] using wordTrace_append hprefix tailTrace_2531156
  have hstable : (prefixWord ++ tailWord_2531156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531156).length < 2 ^ (prefixWord ++ tailWord_2531156).sum := by decide
  have hdescent : baseEnd_2531156 < baseStart_2531156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531199 : List Nat := [1, 1, 2, 2, 1, 1, 3, 4, 4, 3]
def baseStart_2531199 : Nat := 118140960795 + 2531199 * 2 ^ 59
def prefixEnd_2531199 : Nat := 4983230072969 + 3 ^ 40 * 2531199 * 2
def baseEnd_2531199 : Nat := 866481146119964937314489

theorem tailTrace_2531199 : CollatzResearch.WordTrace tailWord_2531199 prefixEnd_2531199 866481146119964937314489 := by
  unfold tailWord_2531199
  simp only [CollatzResearch.WordTrace]
  refine ⟨92320411956905792217596651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61546941304603861478397767 92320411956905792217596651)
  ·
    refine ⟨138480617935358688326394977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92320411956905792217596651 138480617935358688326394977)
    ·
      refine ⟨103860463451519016244796233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138480617935358688326394977 103860463451519016244796233)
      ·
        refine ⟨77895347588639262183597175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103860463451519016244796233 77895347588639262183597175)
        ·
          refine ⟨116843021382958893275395763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77895347588639262183597175 116843021382958893275395763)
          ·
            refine ⟨175264532074438339913093645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116843021382958893275395763 175264532074438339913093645)
            ·
              refine ⟨65724199527914377467410117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175264532074438339913093645 65724199527914377467410117)
              ·
                refine ⟨12323287411483945775139397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65724199527914377467410117 12323287411483945775139397)
                ·
                  refine ⟨2310616389653239832838637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12323287411483945775139397 2310616389653239832838637)
                  ·
                    refine ⟨866481146119964937314489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2310616389653239832838637 866481146119964937314489)
                    ·
                      rfl

theorem cell22_2531199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 4, 3].length) (baseStart_2531199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2531199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2531199 prefixEnd_2531199 := by exact prefixLift 2531199
  have htrace : WordTrace (prefixWord ++ tailWord_2531199) baseStart_2531199 baseEnd_2531199 := by
    simpa [prefixWord, tailWord_2531199, baseEnd_2531199] using wordTrace_append hprefix tailTrace_2531199
  have hstable : (prefixWord ++ tailWord_2531199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531199).length < 2 ^ (prefixWord ++ tailWord_2531199).sum := by decide
  have hdescent : baseEnd_2531199 < baseStart_2531199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531203 : List Nat := [1, 1, 1, 3, 4, 4, 2, 1, 1, 4]
def baseStart_2531203 : Nat := 118140960795 + 2531203 * 2 ^ 59
def prefixEnd_2531203 : Nat := 4983230072969 + 3 ^ 40 * 2531203 * 2
def baseEnd_2531203 : Nat := 866482515401710260214477

theorem tailTrace_2531203 : CollatzResearch.WordTrace tailWord_2531203 prefixEnd_2531203 866482515401710260214477 := by
  unfold tailWord_2531203
  simp only [CollatzResearch.WordTrace]
  refine ⟨92320557848891300900742263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61547038565927533933828175 92320557848891300900742263)
  ·
    refine ⟨138480836773336951351113395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92320557848891300900742263 138480836773336951351113395)
    ·
      refine ⟨207721255160005427026670093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138480836773336951351113395 207721255160005427026670093)
      ·
        refine ⟨77895470685002035135001285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207721255160005427026670093 77895470685002035135001285)
        ·
          refine ⟨14605400753437881587812741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77895470685002035135001285 14605400753437881587812741)
          ·
            refine ⟨2738512641269602797714889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14605400753437881587812741 2738512641269602797714889)
            ·
              refine ⟨2053884480952202098286167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2738512641269602797714889 2053884480952202098286167)
              ·
                refine ⟨3080826721428303147429251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2053884480952202098286167 3080826721428303147429251)
                ·
                  refine ⟨4621240082142454721143877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3080826721428303147429251 4621240082142454721143877)
                  ·
                    refine ⟨866482515401710260214477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4621240082142454721143877 866482515401710260214477)
                    ·
                      rfl

theorem cell22_2531203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 1, 4].length) (baseStart_2531203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2531203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2531203 prefixEnd_2531203 := by exact prefixLift 2531203
  have htrace : WordTrace (prefixWord ++ tailWord_2531203) baseStart_2531203 baseEnd_2531203 := by
    simpa [prefixWord, tailWord_2531203, baseEnd_2531203] using wordTrace_append hprefix tailTrace_2531203
  have hstable : (prefixWord ++ tailWord_2531203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531203).length < 2 ^ (prefixWord ++ tailWord_2531203).sum := by decide
  have hdescent : baseEnd_2531203 < baseStart_2531203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531218 : List Nat := [3, 2, 3, 2, 1, 1, 2, 4, 4]
def baseStart_2531218 : Nat := 118140960795 + 2531218 * 2 ^ 59
def prefixEnd_2531218 : Nat := 4983230072969 + 3 ^ 40 * 2531218 * 2
def baseEnd_2531218 : Nat := 288829216736085073696477

theorem tailTrace_2531218 : CollatzResearch.WordTrace tailWord_2531218 prefixEnd_2531218 288829216736085073696477 := by
  unfold tailWord_2531218
  simp only [CollatzResearch.WordTrace]
  refine ⟨23080276235959239615634577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61547403295891305641692205 23080276235959239615634577)
  ·
    refine ⟨17310207176969429711725933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23080276235959239615634577 17310207176969429711725933)
    ·
      refine ⟨6491327691363536141897225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17310207176969429711725933 6491327691363536141897225)
      ·
        refine ⟨4868495768522652106422919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6491327691363536141897225 4868495768522652106422919)
        ·
          refine ⟨7302743652783978159634379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4868495768522652106422919 7302743652783978159634379)
          ·
            refine ⟨10954115479175967239451569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7302743652783978159634379 10954115479175967239451569)
            ·
              refine ⟨8215586609381975429588677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10954115479175967239451569 8215586609381975429588677)
              ·
                refine ⟨1540422489259120393047877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8215586609381975429588677 1540422489259120393047877)
                ·
                  refine ⟨288829216736085073696477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1540422489259120393047877 288829216736085073696477)
                  ·
                    rfl

theorem cell22_2531218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_2531218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2531218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2531218 prefixEnd_2531218 := by exact prefixLift 2531218
  have htrace : WordTrace (prefixWord ++ tailWord_2531218) baseStart_2531218 baseEnd_2531218 := by
    simpa [prefixWord, tailWord_2531218, baseEnd_2531218] using wordTrace_append hprefix tailTrace_2531218
  have hstable : (prefixWord ++ tailWord_2531218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531218).length < 2 ^ (prefixWord ++ tailWord_2531218).sum := by decide
  have hdescent : baseEnd_2531218 < baseStart_2531218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531233 : List Nat := [1, 2, 3, 4, 2, 2, 1, 1, 1, 5]
def baseStart_2531233 : Nat := 118140960795 + 2531233 * 2 ^ 59
def prefixEnd_2531233 : Nat := 4983230072969 + 3 ^ 40 * 2531233 * 2
def baseEnd_2531233 : Nat := 866492785014800181964385

theorem tailTrace_2531233 : CollatzResearch.WordTrace tailWord_2531233 prefixEnd_2531233 866492785014800181964385 := by
  unfold tailWord_2531233
  simp only [CollatzResearch.WordTrace]
  refine ⟨92321652038782616024334353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61547768025855077349556235 92321652038782616024334353)
  ·
    refine ⟨69241239029086962018250765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92321652038782616024334353 69241239029086962018250765)
    ·
      refine ⟨25965464635907610756844037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69241239029086962018250765 25965464635907610756844037)
      ·
        refine ⟨4868524619232677016908257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25965464635907610756844037 4868524619232677016908257)
        ·
          refine ⟨3651393464424507762681193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4868524619232677016908257 3651393464424507762681193)
          ·
            refine ⟨2738545098318380822010895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3651393464424507762681193 2738545098318380822010895)
            ·
              refine ⟨4107817647477571233016343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2738545098318380822010895 4107817647477571233016343)
              ·
                refine ⟨6161726471216356849524515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4107817647477571233016343 6161726471216356849524515)
                ·
                  refine ⟨9242589706824535274286773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6161726471216356849524515 9242589706824535274286773)
                  ·
                    refine ⟨866492785014800181964385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9242589706824535274286773 866492785014800181964385)
                    ·
                      rfl

theorem cell22_2531233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_2531233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2531233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2531233 prefixEnd_2531233 := by exact prefixLift 2531233
  have htrace : WordTrace (prefixWord ++ tailWord_2531233) baseStart_2531233 baseEnd_2531233 := by
    simpa [prefixWord, tailWord_2531233, baseEnd_2531233] using wordTrace_append hprefix tailTrace_2531233
  have hstable : (prefixWord ++ tailWord_2531233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531233).length < 2 ^ (prefixWord ++ tailWord_2531233).sum := by decide
  have hdescent : baseEnd_2531233 < baseStart_2531233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531252 : List Nat := [2, 5, 2, 1, 2, 2, 1, 3, 4]
def baseStart_2531252 : Nat := 118140960795 + 2531252 * 2 ^ 59
def prefixEnd_2531252 : Nat := 4983230072969 + 3 ^ 40 * 2531252 * 2
def baseEnd_2531252 : Nat := 288833096367696821913109

theorem tailTrace_2531252 : CollatzResearch.WordTrace tailWord_2531252 prefixEnd_2531252 288833096367696821913109 := by
  unfold tailWord_2531252
  simp only [CollatzResearch.WordTrace]
  refine ⟨46161172512856891134638005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61548230017142521512850673 46161172512856891134638005)
  ·
    refine ⟨4327609923080333543872313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46161172512856891134638005 4327609923080333543872313)
    ·
      refine ⟨3245707442310250157904235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4327609923080333543872313 3245707442310250157904235)
      ·
        refine ⟨4868561163465375236856353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3245707442310250157904235 4868561163465375236856353)
        ·
          refine ⟨3651420872599031427642265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4868561163465375236856353 3651420872599031427642265)
          ·
            refine ⟨2738565654449273570731699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3651420872599031427642265 2738565654449273570731699)
            ·
              refine ⟨4107848481673910356097549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2738565654449273570731699 4107848481673910356097549)
              ·
                refine ⟨1540443180627716383536581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4107848481673910356097549 1540443180627716383536581)
                ·
                  refine ⟨288833096367696821913109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1540443180627716383536581 288833096367696821913109)
                  ·
                    rfl

theorem cell22_2531252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_2531252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2531252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2531252 prefixEnd_2531252 := by exact prefixLift 2531252
  have htrace : WordTrace (prefixWord ++ tailWord_2531252) baseStart_2531252 baseEnd_2531252 := by
    simpa [prefixWord, tailWord_2531252, baseEnd_2531252] using wordTrace_append hprefix tailTrace_2531252
  have hstable : (prefixWord ++ tailWord_2531252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531252).length < 2 ^ (prefixWord ++ tailWord_2531252).sum := by decide
  have hdescent : baseEnd_2531252 < baseStart_2531252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531274 : List Nat := [3, 1, 2, 1, 2, 1, 4, 1, 7]
def baseStart_2531274 : Nat := 118140960795 + 2531274 * 2 ^ 59
def prefixEnd_2531274 : Nat := 4983230072969 + 3 ^ 40 * 2531274 * 2
def baseEnd_2531274 : Nat := 288835606717563247229753

theorem tailTrace_2531274 : CollatzResearch.WordTrace tailWord_2531274 prefixEnd_2531274 288835606717563247229753 := by
  unfold tailWord_2531274
  simp only [CollatzResearch.WordTrace]
  refine ⟨23080786857908520006644219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61548764954422720017717917 23080786857908520006644219)
  ·
    refine ⟨34621180286862780009966329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23080786857908520006644219 34621180286862780009966329)
    ·
      refine ⟨25965885215147085007474747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34621180286862780009966329 25965885215147085007474747)
      ·
        refine ⟨38948827822720627511212121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25965885215147085007474747 38948827822720627511212121)
        ·
          refine ⟨29211620867040470633409091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38948827822720627511212121 29211620867040470633409091)
          ·
            refine ⟨43817431300560705950113637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29211620867040470633409091 43817431300560705950113637)
            ·
              refine ⟨8215768368855132365646307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43817431300560705950113637 8215768368855132365646307)
              ·
                refine ⟨12323652553282698548469461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8215768368855132365646307 12323652553282698548469461)
                ·
                  refine ⟨288835606717563247229753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12323652553282698548469461 288835606717563247229753)
                  ·
                    rfl

theorem cell22_2531274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 7].length) (baseStart_2531274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2531274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2531274 prefixEnd_2531274 := by exact prefixLift 2531274
  have htrace : WordTrace (prefixWord ++ tailWord_2531274) baseStart_2531274 baseEnd_2531274 := by
    simpa [prefixWord, tailWord_2531274, baseEnd_2531274] using wordTrace_append hprefix tailTrace_2531274
  have hstable : (prefixWord ++ tailWord_2531274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531274).length < 2 ^ (prefixWord ++ tailWord_2531274).sum := by decide
  have hdescent : baseEnd_2531274 < baseStart_2531274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531370 : List Nat := [3, 1, 4, 1, 2, 2, 2, 3, 4]
def baseStart_2531370 : Nat := 118140960795 + 2531370 * 2 ^ 59
def prefixEnd_2531370 : Nat := 4983230072969 + 3 ^ 40 * 2531370 * 2
def baseEnd_2531370 : Nat := 288846560971525830429655

theorem tailTrace_2531370 : CollatzResearch.WordTrace tailWord_2531370 prefixEnd_2531370 288846560971525830429655 := by
  unfold tailWord_2531370
  simp only [CollatzResearch.WordTrace]
  refine ⟨23081662209821572105517891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61551099226190858948047709 23081662209821572105517891)
  ·
    refine ⟨34622493314732358158276837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23081662209821572105517891 34622493314732358158276837)
    ·
      refine ⟨6491717496512317154676907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34622493314732358158276837 6491717496512317154676907)
      ·
        refine ⟨9737576244768475732015361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6491717496512317154676907 9737576244768475732015361)
        ·
          refine ⟨7303182183576356799011521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9737576244768475732015361 7303182183576356799011521)
          ·
            refine ⟨5477386637682267599258641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7303182183576356799011521 5477386637682267599258641)
            ·
              refine ⟨4108039978261700699443981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5477386637682267599258641 4108039978261700699443981)
              ·
                refine ⟨1540514991848137762291493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4108039978261700699443981 1540514991848137762291493)
                ·
                  refine ⟨288846560971525830429655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1540514991848137762291493 288846560971525830429655)
                  ·
                    rfl

theorem cell22_2531370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 3, 4].length) (baseStart_2531370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2531370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2531370 prefixEnd_2531370 := by exact prefixLift 2531370
  have htrace : WordTrace (prefixWord ++ tailWord_2531370) baseStart_2531370 baseEnd_2531370 := by
    simpa [prefixWord, tailWord_2531370, baseEnd_2531370] using wordTrace_append hprefix tailTrace_2531370
  have hstable : (prefixWord ++ tailWord_2531370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531370).length < 2 ^ (prefixWord ++ tailWord_2531370).sum := by decide
  have hdescent : baseEnd_2531370 < baseStart_2531370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531398 : List Nat := [6, 1, 1, 1, 1, 1, 2, 9]
def baseStart_2531398 : Nat := 118140960795 + 2531398 * 2 ^ 59
def prefixEnd_2531398 : Nat := 4983230072969 + 3 ^ 40 * 2531398 * 2
def baseEnd_2531398 : Nat := 96283251987421639065431

theorem tailTrace_2531398 : CollatzResearch.WordTrace tailWord_2531398 prefixEnd_2531398 96283251987421639065431 := by
  unfold tailWord_2531398
  simp only [CollatzResearch.WordTrace]
  refine ⟨2885239690099526537627839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 61551780055456566136060565 2885239690099526537627839)
  ·
    refine ⟨4327859535149289806441759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2885239690099526537627839 4327859535149289806441759)
    ·
      refine ⟨6491789302723934709662639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4327859535149289806441759 6491789302723934709662639)
      ·
        refine ⟨9737683954085902064493959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6491789302723934709662639 9737683954085902064493959)
        ·
          refine ⟨14606525931128853096740939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9737683954085902064493959 14606525931128853096740939)
          ·
            refine ⟨21909788896693279645111409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14606525931128853096740939 21909788896693279645111409)
            ·
              refine ⟨16432341672519959733833557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21909788896693279645111409 16432341672519959733833557)
              ·
                refine ⟨96283251987421639065431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16432341672519959733833557 96283251987421639065431)
                ·
                  rfl

theorem cell22_2531398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_2531398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2531398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2531398 prefixEnd_2531398 := by exact prefixLift 2531398
  have htrace : WordTrace (prefixWord ++ tailWord_2531398) baseStart_2531398 baseEnd_2531398 := by
    simpa [prefixWord, tailWord_2531398, baseEnd_2531398] using wordTrace_append hprefix tailTrace_2531398
  have hstable : (prefixWord ++ tailWord_2531398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531398).length < 2 ^ (prefixWord ++ tailWord_2531398).sum := by decide
  have hdescent : baseEnd_2531398 < baseStart_2531398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531413 : List Nat := [1, 3, 2, 2, 1, 3, 2, 2, 3, 3]
def baseStart_2531413 : Nat := 118140960795 + 2531413 * 2 ^ 59
def prefixEnd_2531413 : Nat := 4983230072969 + 3 ^ 40 * 2531413 * 2
def baseEnd_2531413 : Nat := 866554402693339712463833

theorem tailTrace_2531413 : CollatzResearch.WordTrace tailWord_2531413 prefixEnd_2531413 866554402693339712463833 := by
  unfold tailWord_2531413
  simp only [CollatzResearch.WordTrace]
  refine ⟨92328217178130506765886893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61552144785420337843924595 92328217178130506765886893)
  ·
    refine ⟨34623081441798940037207585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92328217178130506765886893 34623081441798940037207585)
    ·
      refine ⟨25967311081349205027905689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34623081441798940037207585 25967311081349205027905689)
      ·
        refine ⟨19475483311011903770929267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25967311081349205027905689 19475483311011903770929267)
        ·
          refine ⟨29213224966517855656393901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19475483311011903770929267 29213224966517855656393901)
          ·
            refine ⟨10954959362444195871147713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29213224966517855656393901 10954959362444195871147713)
            ·
              refine ⟨8216219521833146903360785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10954959362444195871147713 8216219521833146903360785)
              ·
                refine ⟨6162164641374860177520589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8216219521833146903360785 6162164641374860177520589)
                ·
                  refine ⟨2310811740515572566570221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6162164641374860177520589 2310811740515572566570221)
                  ·
                    refine ⟨866554402693339712463833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2310811740515572566570221 866554402693339712463833)
                    ·
                      rfl

theorem cell22_2531413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_2531413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2531413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2531413 prefixEnd_2531413 := by exact prefixLift 2531413
  have htrace : WordTrace (prefixWord ++ tailWord_2531413) baseStart_2531413 baseEnd_2531413 := by
    simpa [prefixWord, tailWord_2531413, baseEnd_2531413] using wordTrace_append hprefix tailTrace_2531413
  have hstable : (prefixWord ++ tailWord_2531413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531413).length < 2 ^ (prefixWord ++ tailWord_2531413).sum := by decide
  have hdescent : baseEnd_2531413 < baseStart_2531413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531447 : List Nat := [1, 1, 3, 1, 1, 6, 3, 2, 1, 3]
def baseStart_2531447 : Nat := 118140960795 + 2531447 * 2 ^ 59
def prefixEnd_2531447 : Nat := 4983230072969 + 3 ^ 40 * 2531447 * 2
def baseEnd_2531447 : Nat := 866566041588174957113729

theorem tailTrace_2531447 : CollatzResearch.WordTrace tailWord_2531447 prefixEnd_2531447 866566041588174957113729 := by
  unfold tailWord_2531447
  simp only [CollatzResearch.WordTrace]
  refine ⟨92329457260007330572624595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61552971506671553715083063 92329457260007330572624595)
  ·
    refine ⟨138494185890010995858936893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92329457260007330572624595 138494185890010995858936893)
    ·
      refine ⟨51935319708754123447101335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138494185890010995858936893 51935319708754123447101335)
      ·
        refine ⟨77902979563131185170652003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51935319708754123447101335 77902979563131185170652003)
        ·
          refine ⟨116854469344696777755978005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77902979563131185170652003 116854469344696777755978005)
          ·
            refine ⟨5477553250532661457311469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 116854469344696777755978005 5477553250532661457311469)
            ·
              refine ⟨2054082468949748046491801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5477553250532661457311469 2054082468949748046491801)
              ·
                refine ⟨1540561851712311034868851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2054082468949748046491801 1540561851712311034868851)
                ·
                  refine ⟨2310842777568466552303277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1540561851712311034868851 2310842777568466552303277)
                  ·
                    refine ⟨866566041588174957113729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2310842777568466552303277 866566041588174957113729)
                    ·
                      rfl

theorem cell22_2531447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 2, 1, 3].length) (baseStart_2531447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2531447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2531447 prefixEnd_2531447 := by exact prefixLift 2531447
  have htrace : WordTrace (prefixWord ++ tailWord_2531447) baseStart_2531447 baseEnd_2531447 := by
    simpa [prefixWord, tailWord_2531447, baseEnd_2531447] using wordTrace_append hprefix tailTrace_2531447
  have hstable : (prefixWord ++ tailWord_2531447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531447).length < 2 ^ (prefixWord ++ tailWord_2531447).sum := by decide
  have hdescent : baseEnd_2531447 < baseStart_2531447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531456 : List Nat := [2, 1, 1, 2, 1, 3, 1, 4, 3, 4]
def baseStart_2531456 : Nat := 118140960795 + 2531456 * 2 ^ 59
def prefixEnd_2531456 : Nat := 4983230072969 + 3 ^ 40 * 2531456 * 2
def baseEnd_2531456 : Nat := 866569122472101933638701

theorem tailTrace_2531456 : CollatzResearch.WordTrace tailWord_2531456 prefixEnd_2531456 866569122472101933638701 := by
  unfold tailWord_2531456
  simp only [CollatzResearch.WordTrace]
  refine ⟨46164892758487362554851111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61553190344649816739801481 46164892758487362554851111)
  ·
    refine ⟨69247339137731043832276667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46164892758487362554851111 69247339137731043832276667)
    ·
      refine ⟨103871008706596565748415001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69247339137731043832276667 103871008706596565748415001)
      ·
        refine ⟨77903256529947424311311251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103871008706596565748415001 77903256529947424311311251)
        ·
          refine ⟨116854884794921136466966877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77903256529947424311311251 116854884794921136466966877)
          ·
            refine ⟨43820581798095426175112579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116854884794921136466966877 43820581798095426175112579)
            ·
              refine ⟨65730872697143139262668869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43820581798095426175112579 65730872697143139262668869)
              ·
                refine ⟨12324538630714338611750413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65730872697143139262668869 12324538630714338611750413)
                ·
                  refine ⟨4621701986517876979406405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12324538630714338611750413 4621701986517876979406405)
                  ·
                    refine ⟨866569122472101933638701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4621701986517876979406405 866569122472101933638701)
                    ·
                      rfl

theorem cell22_2531456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 3, 4].length) (baseStart_2531456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2531456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2531456 prefixEnd_2531456 := by exact prefixLift 2531456
  have htrace : WordTrace (prefixWord ++ tailWord_2531456) baseStart_2531456 baseEnd_2531456 := by
    simpa [prefixWord, tailWord_2531456, baseEnd_2531456] using wordTrace_append hprefix tailTrace_2531456
  have hstable : (prefixWord ++ tailWord_2531456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531456).length < 2 ^ (prefixWord ++ tailWord_2531456).sum := by decide
  have hdescent : baseEnd_2531456 < baseStart_2531456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531498 : List Nat := [3, 1, 5, 1, 3, 1, 2, 2, 1, 3]
def baseStart_2531498 : Nat := 118140960795 + 2531498 * 2 ^ 59
def prefixEnd_2531498 : Nat := 4983230072969 + 3 ^ 40 * 2531498 * 2
def baseEnd_2531498 : Nat := 866583499930427824088573

theorem tailTrace_2531498 : CollatzResearch.WordTrace tailWord_2531498 prefixEnd_2531498 866583499930427824088573 := by
  unfold tailWord_2531498
  simp only [CollatzResearch.WordTrace]
  refine ⟨23082829345705641570682787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61554211588548377521820765 23082829345705641570682787)
  ·
    refine ⟨34624244018558462356024181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23082829345705641570682787 34624244018558462356024181)
    ·
      refine ⟨3246022876739855845877267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34624244018558462356024181 3246022876739855845877267)
      ·
        refine ⟨4869034315109783768815901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3246022876739855845877267 4869034315109783768815901)
        ·
          refine ⟨1825887868166168913305963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4869034315109783768815901 1825887868166168913305963)
          ·
            refine ⟨2738831802249253369958945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1825887868166168913305963 2738831802249253369958945)
            ·
              refine ⟨2054123851686940027469209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2738831802249253369958945 2054123851686940027469209)
              ·
                refine ⟨1540592888765205020601907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2054123851686940027469209 1540592888765205020601907)
                ·
                  refine ⟨2310889333147807530902861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1540592888765205020601907 2310889333147807530902861)
                  ·
                    refine ⟨866583499930427824088573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2310889333147807530902861 866583499930427824088573)
                    ·
                      rfl

theorem cell22_2531498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_2531498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2531498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2531498 prefixEnd_2531498 := by exact prefixLift 2531498
  have htrace : WordTrace (prefixWord ++ tailWord_2531498) baseStart_2531498 baseEnd_2531498 := by
    simpa [prefixWord, tailWord_2531498, baseEnd_2531498] using wordTrace_append hprefix tailTrace_2531498
  have hstable : (prefixWord ++ tailWord_2531498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531498).length < 2 ^ (prefixWord ++ tailWord_2531498).sum := by decide
  have hdescent : baseEnd_2531498 < baseStart_2531498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531520 : List Nat := [2, 1, 1, 2, 5, 1, 2, 3, 2, 3]
def baseStart_2531520 : Nat := 118140960795 + 2531520 * 2 ^ 59
def prefixEnd_2531520 : Nat := 4983230072969 + 3 ^ 40 * 2531520 * 2
def baseEnd_2531520 : Nat := 866591030980027100038505

theorem tailTrace_2531520 : CollatzResearch.WordTrace tailWord_2531520 prefixEnd_2531520 866591030980027100038505 := by
  unfold tailWord_2531520
  simp only [CollatzResearch.WordTrace]
  refine ⟨46166059894371432020016007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61554746525828576026688009 46166059894371432020016007)
  ·
    refine ⟨69249089841557148030024011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46166059894371432020016007 69249089841557148030024011)
    ·
      refine ⟨103873634762335722045036017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69249089841557148030024011 103873634762335722045036017)
      ·
        refine ⟨77905226071751791533777013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103873634762335722045036017 77905226071751791533777013)
        ·
          refine ⟨7303614944226730456291595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77905226071751791533777013 7303614944226730456291595)
          ·
            refine ⟨10955422416340095684437393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7303614944226730456291595 10955422416340095684437393)
            ·
              refine ⟨8216566812255071763328045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10955422416340095684437393 8216566812255071763328045)
              ·
                refine ⟨3081212554595651911248017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8216566812255071763328045 3081212554595651911248017)
                ·
                  refine ⟨2310909415946738933436013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3081212554595651911248017 2310909415946738933436013)
                  ·
                    refine ⟨866591030980027100038505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2310909415946738933436013 866591030980027100038505)
                    ·
                      rfl

theorem cell22_2531520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 2, 3].length) (baseStart_2531520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2531520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2531520 prefixEnd_2531520 := by exact prefixLift 2531520
  have htrace : WordTrace (prefixWord ++ tailWord_2531520) baseStart_2531520 baseEnd_2531520 := by
    simpa [prefixWord, tailWord_2531520, baseEnd_2531520] using wordTrace_append hprefix tailTrace_2531520
  have hstable : (prefixWord ++ tailWord_2531520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531520).length < 2 ^ (prefixWord ++ tailWord_2531520).sum := by decide
  have hdescent : baseEnd_2531520 < baseStart_2531520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531522 : List Nat := [3, 5, 1, 1, 1, 2, 1, 2, 6]
def baseStart_2531522 : Nat := 118140960795 + 2531522 * 2 ^ 59
def prefixEnd_2531522 : Nat := 4983230072969 + 3 ^ 40 * 2531522 * 2
def baseEnd_2531522 : Nat := 288863905206966587162833

theorem tailTrace_2531522 : CollatzResearch.WordTrace tailWord_2531522 prefixEnd_2531522 288863905206966587162833 := by
  unfold tailWord_2531522
  simp only [CollatzResearch.WordTrace]
  refine ⟨23083048183683904595401205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61554795156490412254403213 23083048183683904595401205)
  ·
    refine ⟨2164035767220366055818863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23083048183683904595401205 2164035767220366055818863)
    ·
      refine ⟨3246053650830549083728295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2164035767220366055818863 3246053650830549083728295)
      ·
        refine ⟨4869080476245823625592443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3246053650830549083728295 4869080476245823625592443)
        ·
          refine ⟨7303620714368735438388665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4869080476245823625592443 7303620714368735438388665)
          ·
            refine ⟨5477715535776551578791499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7303620714368735438388665 5477715535776551578791499)
            ·
              refine ⟨8216573303664827368187249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5477715535776551578791499 8216573303664827368187249)
              ·
                refine ⟨6162429977748620526140437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8216573303664827368187249 6162429977748620526140437)
                ·
                  refine ⟨288863905206966587162833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6162429977748620526140437 288863905206966587162833)
                  ·
                    rfl

theorem cell22_2531522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_2531522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2531522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2531522 prefixEnd_2531522 := by exact prefixLift 2531522
  have htrace : WordTrace (prefixWord ++ tailWord_2531522) baseStart_2531522 baseEnd_2531522 := by
    simpa [prefixWord, tailWord_2531522, baseEnd_2531522] using wordTrace_append hprefix tailTrace_2531522
  have hstable : (prefixWord ++ tailWord_2531522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531522).length < 2 ^ (prefixWord ++ tailWord_2531522).sum := by decide
  have hdescent : baseEnd_2531522 < baseStart_2531522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531561 : List Nat := [1, 2, 1, 1, 1, 2, 2, 5, 7]
def baseStart_2531561 : Nat := 118140960795 + 2531561 * 2 ^ 59
def prefixEnd_2531561 : Nat := 4983230072969 + 3 ^ 40 * 2531561 * 2
def baseEnd_2531561 : Nat := 288868355372638886587793

theorem tailTrace_2531561 : CollatzResearch.WordTrace tailWord_2531561 prefixEnd_2531561 288868355372638886587793 := by
  unfold tailWord_2531561
  simp only [CollatzResearch.WordTrace]
  refine ⟨92333615181594328042274537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61555743454396218694849691 92333615181594328042274537)
  ·
    refine ⟨69250211386195746031705903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92333615181594328042274537 69250211386195746031705903)
    ·
      refine ⟨103875317079293619047558855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69250211386195746031705903 103875317079293619047558855)
      ·
        refine ⟨155812975618940428571338283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103875317079293619047558855 155812975618940428571338283)
        ·
          refine ⟨233719463428410642857007425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155812975618940428571338283 233719463428410642857007425)
          ·
            refine ⟨175289597571307982142755569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233719463428410642857007425 175289597571307982142755569)
            ·
              refine ⟨131467198178480986607066677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175289597571307982142755569 131467198178480986607066677)
              ·
                refine ⟨12325049829232592494412501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 131467198178480986607066677 12325049829232592494412501)
                ·
                  refine ⟨288868355372638886587793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12325049829232592494412501 288868355372638886587793)
                  ·
                    rfl

theorem cell22_2531561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 7].length) (baseStart_2531561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2531561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2531561 prefixEnd_2531561 := by exact prefixLift 2531561
  have htrace : WordTrace (prefixWord ++ tailWord_2531561) baseStart_2531561 baseEnd_2531561 := by
    simpa [prefixWord, tailWord_2531561, baseEnd_2531561] using wordTrace_append hprefix tailTrace_2531561
  have hstable : (prefixWord ++ tailWord_2531561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531561).length < 2 ^ (prefixWord ++ tailWord_2531561).sum := by decide
  have hdescent : baseEnd_2531561 < baseStart_2531561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531642 : List Nat := [3, 1, 1, 1, 4, 4, 1, 2, 1, 4]
def baseStart_2531642 : Nat := 118140960795 + 2531642 * 2 ^ 59
def prefixEnd_2531642 : Nat := 4983230072969 + 3 ^ 40 * 2531642 * 2
def baseEnd_2531642 : Nat := 866632794073259448488131

theorem tailTrace_2531642 : CollatzResearch.WordTrace tailWord_2531642 prefixEnd_2531642 866632794073259448488131 := by
  unfold tailWord_2531642
  simp only [CollatzResearch.WordTrace]
  refine ⟨23084142373575219718993295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61557712996200585917315453 23084142373575219718993295)
  ·
    refine ⟨34626213560362829578489943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23084142373575219718993295 34626213560362829578489943)
    ·
      refine ⟨51939320340544244367734915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34626213560362829578489943 51939320340544244367734915)
      ·
        refine ⟨77908980510816366551602373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51939320340544244367734915 77908980510816366551602373)
        ·
          refine ⟨14607933845778068728425445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77908980510816366551602373 14607933845778068728425445)
          ·
            refine ⟨2738987596083387886579771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14607933845778068728425445 2738987596083387886579771)
            ·
              refine ⟨4108481394125081829869657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2738987596083387886579771 4108481394125081829869657)
              ·
                refine ⟨3081361045593811372402243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4108481394125081829869657 3081361045593811372402243)
                ·
                  refine ⟨4622041568390717058603365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3081361045593811372402243 4622041568390717058603365)
                  ·
                    refine ⟨866632794073259448488131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4622041568390717058603365 866632794073259448488131)
                    ·
                      rfl

theorem cell22_2531642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 1, 4].length) (baseStart_2531642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2531642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2531642 prefixEnd_2531642 := by exact prefixLift 2531642
  have htrace : WordTrace (prefixWord ++ tailWord_2531642) baseStart_2531642 baseEnd_2531642 := by
    simpa [prefixWord, tailWord_2531642, baseEnd_2531642] using wordTrace_append hprefix tailTrace_2531642
  have hstable : (prefixWord ++ tailWord_2531642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531642).length < 2 ^ (prefixWord ++ tailWord_2531642).sum := by decide
  have hdescent : baseEnd_2531642 < baseStart_2531642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531668 : List Nat := [2, 4, 1, 1, 2, 12]
def baseStart_2531668 : Nat := 118140960795 + 2531668 * 2 ^ 59
def prefixEnd_2531668 : Nat := 4983230072969 + 3 ^ 40 * 2531668 * 2
def baseEnd_2531668 : Nat := 10699280177834617868371

theorem tailTrace_2531668 : CollatzResearch.WordTrace tailWord_2531668 prefixEnd_2531668 10699280177834617868371 := by
  unfold tailWord_2531668
  simp only [CollatzResearch.WordTrace]
  refine ⟨46168758896103342658209829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61558345194804456877613105 46168758896103342658209829)
  ·
    refine ⟨8656642293019376748414343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46168758896103342658209829 8656642293019376748414343)
    ·
      refine ⟨12984963439529065122621515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8656642293019376748414343 12984963439529065122621515)
      ·
        refine ⟨19477445159293597683932273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12984963439529065122621515 19477445159293597683932273)
        ·
          refine ⟨14608083869470198262949205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19477445159293597683932273 14608083869470198262949205)
          ·
            refine ⟨10699280177834617868371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 14608083869470198262949205 10699280177834617868371)
            ·
              rfl

theorem cell22_2531668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 12].length) (baseStart_2531668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2531668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2531668 prefixEnd_2531668 := by exact prefixLift 2531668
  have htrace : WordTrace (prefixWord ++ tailWord_2531668) baseStart_2531668 baseEnd_2531668 := by
    simpa [prefixWord, tailWord_2531668, baseEnd_2531668] using wordTrace_append hprefix tailTrace_2531668
  have hstable : (prefixWord ++ tailWord_2531668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531668).length < 2 ^ (prefixWord ++ tailWord_2531668).sum := by decide
  have hdescent : baseEnd_2531668 < baseStart_2531668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531685 : List Nat := [1, 3, 1, 3, 1, 5, 1, 7]
def baseStart_2531685 : Nat := 118140960795 + 2531685 * 2 ^ 59
def prefixEnd_2531685 : Nat := 4983230072969 + 3 ^ 40 * 2531685 * 2
def baseEnd_2531685 : Nat := 96294168205780185518111

theorem tailTrace_2531685 : CollatzResearch.WordTrace tailWord_2531685 prefixEnd_2531685 96294168205780185518111 := by
  unfold tailWord_2531685
  simp only [CollatzResearch.WordTrace]
  refine ⟨92338137833145097219788509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61558758555430064813192339 92338137833145097219788509)
  ·
    refine ⟨34626801687429411457420691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92338137833145097219788509 34626801687429411457420691)
    ·
      refine ⟨51940202531144117186131037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34626801687429411457420691 51940202531144117186131037)
      ·
        refine ⟨19477575949179043944799139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51940202531144117186131037 19477575949179043944799139)
        ·
          refine ⟨29216363923768565917198709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19477575949179043944799139 29216363923768565917198709)
          ·
            refine ⟨2739034117853303054737379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29216363923768565917198709 2739034117853303054737379)
            ·
              refine ⟨4108551176779954582106069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2739034117853303054737379 4108551176779954582106069)
              ·
                refine ⟨96294168205780185518111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4108551176779954582106069 96294168205780185518111)
                ·
                  rfl

theorem cell22_2531685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 7].length) (baseStart_2531685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2531685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2531685 prefixEnd_2531685 := by exact prefixLift 2531685
  have htrace : WordTrace (prefixWord ++ tailWord_2531685) baseStart_2531685 baseEnd_2531685 := by
    simpa [prefixWord, tailWord_2531685, baseEnd_2531685] using wordTrace_append hprefix tailTrace_2531685
  have hstable : (prefixWord ++ tailWord_2531685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531685).length < 2 ^ (prefixWord ++ tailWord_2531685).sum := by decide
  have hdescent : baseEnd_2531685 < baseStart_2531685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531747 : List Nat := [1, 1, 1, 4, 1, 5, 3, 1, 5]
def baseStart_2531747 : Nat := 118140960795 + 2531747 * 2 ^ 59
def prefixEnd_2531747 : Nat := 4983230072969 + 3 ^ 40 * 2531747 * 2
def baseEnd_2531747 : Nat := 288889579239691391537603

theorem tailTrace_2531747 : CollatzResearch.WordTrace tailWord_2531747 prefixEnd_2531747 288889579239691391537603 := by
  unfold tailWord_2531747
  simp only [CollatzResearch.WordTrace]
  refine ⟨92340399158920481808545495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61560266105946987872363663 92340399158920481808545495)
  ·
    refine ⟨138510598738380722712818243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92340399158920481808545495 138510598738380722712818243)
    ·
      refine ⟨207765898107571084069227365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138510598738380722712818243 207765898107571084069227365)
      ·
        refine ⟨38956105895169578262980131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 207765898107571084069227365 38956105895169578262980131)
        ·
          refine ⟨58434158842754367394470197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38956105895169578262980131 58434158842754367394470197)
          ·
            refine ⟨5478202391508221943231581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58434158842754367394470197 5478202391508221943231581)
            ·
              refine ⟨2054325896815583228711843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5478202391508221943231581 2054325896815583228711843)
              ·
                refine ⟨3081488845223374843067765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2054325896815583228711843 3081488845223374843067765)
                ·
                  refine ⟨288889579239691391537603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3081488845223374843067765 288889579239691391537603)
                  ·
                    rfl

theorem cell22_2531747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 5].length) (baseStart_2531747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2531747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2531747 prefixEnd_2531747 := by exact prefixLift 2531747
  have htrace : WordTrace (prefixWord ++ tailWord_2531747) baseStart_2531747 baseEnd_2531747 := by
    simpa [prefixWord, tailWord_2531747, baseEnd_2531747] using wordTrace_append hprefix tailTrace_2531747
  have hstable : (prefixWord ++ tailWord_2531747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531747).length < 2 ^ (prefixWord ++ tailWord_2531747).sum := by decide
  have hdescent : baseEnd_2531747 < baseStart_2531747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531811 : List Nat := [1, 1, 1, 6, 4, 1, 1, 2, 1, 4]
def baseStart_2531811 : Nat := 118140960795 + 2531811 * 2 ^ 59
def prefixEnd_2531811 : Nat := 4983230072969 + 3 ^ 40 * 2531811 * 2
def baseEnd_2531811 : Nat := 866690646226999341012613

theorem tailTrace_2531811 : CollatzResearch.WordTrace tailWord_2531811 prefixEnd_2531811 866690646226999341012613 := by
  unfold tailWord_2531811
  simp only [CollatzResearch.WordTrace]
  refine ⟨92342733430688620738875287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61561822287125747159250191 92342733430688620738875287)
  ·
    refine ⟨138514100146032931108312931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92342733430688620738875287 138514100146032931108312931)
    ·
      refine ⟨207771150219049396662469397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138514100146032931108312931 207771150219049396662469397)
      ·
        refine ⟨9739272666517940468553253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 207771150219049396662469397 9739272666517940468553253)
        ·
          refine ⟨1826113624972113837853735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9739272666517940468553253 1826113624972113837853735)
          ·
            refine ⟨2739170437458170756780603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1826113624972113837853735 2739170437458170756780603)
            ·
              refine ⟨4108755656187256135170905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2739170437458170756780603 4108755656187256135170905)
              ·
                refine ⟨3081566742140442101378179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4108755656187256135170905 3081566742140442101378179)
                ·
                  refine ⟨4622350113210663152067269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3081566742140442101378179 4622350113210663152067269)
                  ·
                    refine ⟨866690646226999341012613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4622350113210663152067269 866690646226999341012613)
                    ·
                      rfl

theorem cell22_2531811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 1, 4].length) (baseStart_2531811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2531811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2531811 prefixEnd_2531811 := by exact prefixLift 2531811
  have htrace : WordTrace (prefixWord ++ tailWord_2531811) baseStart_2531811 baseEnd_2531811 := by
    simpa [prefixWord, tailWord_2531811, baseEnd_2531811] using wordTrace_append hprefix tailTrace_2531811
  have hstable : (prefixWord ++ tailWord_2531811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531811).length < 2 ^ (prefixWord ++ tailWord_2531811).sum := by decide
  have hdescent : baseEnd_2531811 < baseStart_2531811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531822 : List Nat := [4, 1, 2, 1, 2, 2, 1, 3, 2, 4]
def baseStart_2531822 : Nat := 118140960795 + 2531822 * 2 ^ 59
def prefixEnd_2531822 : Nat := 4983230072969 + 3 ^ 40 * 2531822 * 2
def baseEnd_2531822 : Nat := 866694411751798978987579

theorem tailTrace_2531822 : CollatzResearch.WordTrace tailWord_2531822 prefixEnd_2531822 866694411751798978987579 := by
  unfold tailWord_2531822
  simp only [CollatzResearch.WordTrace]
  refine ⟨11542891829206096202190715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61562089755765846411683813 11542891829206096202190715)
  ·
    refine ⟨17314337743809144303286073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11542891829206096202190715 17314337743809144303286073)
    ·
      refine ⟨12985753307856858227464555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17314337743809144303286073 12985753307856858227464555)
      ·
        refine ⟨19478629961785287341196833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12985753307856858227464555 19478629961785287341196833)
        ·
          refine ⟨14608972471338965505897625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19478629961785287341196833 14608972471338965505897625)
          ·
            refine ⟨10956729353504224129423219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14608972471338965505897625 10956729353504224129423219)
            ·
              refine ⟨16435094030256336194134829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10956729353504224129423219 16435094030256336194134829)
              ·
                refine ⟨6163160261346126072800561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16435094030256336194134829 6163160261346126072800561)
                ·
                  refine ⟨4622370196009594554600421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6163160261346126072800561 4622370196009594554600421)
                  ·
                    refine ⟨866694411751798978987579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4622370196009594554600421 866694411751798978987579)
                    ·
                      rfl

theorem cell22_2531822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_2531822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2531822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2531822 prefixEnd_2531822 := by exact prefixLift 2531822
  have htrace : WordTrace (prefixWord ++ tailWord_2531822) baseStart_2531822 baseEnd_2531822 := by
    simpa [prefixWord, tailWord_2531822, baseEnd_2531822] using wordTrace_append hprefix tailTrace_2531822
  have hstable : (prefixWord ++ tailWord_2531822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531822).length < 2 ^ (prefixWord ++ tailWord_2531822).sum := by decide
  have hdescent : baseEnd_2531822 < baseStart_2531822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531850 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 1, 8]
def baseStart_2531850 : Nat := 118140960795 + 2531850 * 2 ^ 59
def prefixEnd_2531850 : Nat := 4983230072969 + 3 ^ 40 * 2531850 * 2
def baseEnd_2531850 : Nat := 866703996724016239287493

theorem tailTrace_2531850 : CollatzResearch.WordTrace tailWord_2531850 prefixEnd_2531850 866703996724016239287493 := by
  unfold tailWord_2531850
  simp only [CollatzResearch.WordTrace]
  refine ⟨23086038969386832599886251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61562770585031553599696669 23086038969386832599886251)
  ·
    refine ⟨34629058454080248899829377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23086038969386832599886251 34629058454080248899829377)
    ·
      refine ⟨25971793840560186674872033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34629058454080248899829377 25971793840560186674872033)
      ·
        refine ⟨19478845380420140006154025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25971793840560186674872033 19478845380420140006154025)
        ·
          refine ⟨14609134035315105004615519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19478845380420140006154025 14609134035315105004615519)
          ·
            refine ⟨21913701052972657506923279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14609134035315105004615519 21913701052972657506923279)
            ·
              refine ⟨32870551579458986260384919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21913701052972657506923279 32870551579458986260384919)
              ·
                refine ⟨49305827369188479390577379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32870551579458986260384919 49305827369188479390577379)
                ·
                  refine ⟨73958741053782719085866069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49305827369188479390577379 73958741053782719085866069)
                  ·
                    refine ⟨866703996724016239287493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 73958741053782719085866069 866703996724016239287493)
                    ·
                      rfl

theorem cell22_2531850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_2531850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2531850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2531850 prefixEnd_2531850 := by exact prefixLift 2531850
  have htrace : WordTrace (prefixWord ++ tailWord_2531850) baseStart_2531850 baseEnd_2531850 := by
    simpa [prefixWord, tailWord_2531850, baseEnd_2531850] using wordTrace_append hprefix tailTrace_2531850
  have hstable : (prefixWord ++ tailWord_2531850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531850).length < 2 ^ (prefixWord ++ tailWord_2531850).sum := by decide
  have hdescent : baseEnd_2531850 < baseStart_2531850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531869 : List Nat := [1, 4, 2, 2, 1, 3, 1, 2, 3, 3]
def baseStart_2531869 : Nat := 118140960795 + 2531869 * 2 ^ 59
def prefixEnd_2531869 : Nat := 4983230072969 + 3 ^ 40 * 2531869 * 2
def baseEnd_2531869 : Nat := 866710500812306523062435

theorem tailTrace_2531869 : CollatzResearch.WordTrace tailWord_2531869 prefixEnd_2531869 866710500812306523062435 := by
  unfold tailWord_2531869
  simp only [CollatzResearch.WordTrace]
  refine ⟨92344848864478496644486661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61563232576318997762991107 92344848864478496644486661)
  ·
    refine ⟨17314659162089718120841249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92344848864478496644486661 17314659162089718120841249)
    ·
      refine ⟨12985994371567288590630937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17314659162089718120841249 12985994371567288590630937)
      ·
        refine ⟨9739495778675466442973203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12985994371567288590630937 9739495778675466442973203)
        ·
          refine ⟨14609243668013199664459805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9739495778675466442973203 14609243668013199664459805)
          ·
            refine ⟨5478466375504949874172427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14609243668013199664459805 5478466375504949874172427)
            ·
              refine ⟨8217699563257424811258641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5478466375504949874172427 8217699563257424811258641)
              ·
                refine ⟨6163274672443068608443981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8217699563257424811258641 6163274672443068608443981)
                ·
                  refine ⟨2311228002166150728166493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6163274672443068608443981 2311228002166150728166493)
                  ·
                    refine ⟨866710500812306523062435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2311228002166150728166493 866710500812306523062435)
                    ·
                      rfl

theorem cell22_2531869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_2531869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2531869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2531869 prefixEnd_2531869 := by exact prefixLift 2531869
  have htrace : WordTrace (prefixWord ++ tailWord_2531869) baseStart_2531869 baseEnd_2531869 := by
    simpa [prefixWord, tailWord_2531869, baseEnd_2531869] using wordTrace_append hprefix tailTrace_2531869
  have hstable : (prefixWord ++ tailWord_2531869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531869).length < 2 ^ (prefixWord ++ tailWord_2531869).sum := by decide
  have hdescent : baseEnd_2531869 < baseStart_2531869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531961 : List Nat := [1, 2, 1, 3, 3, 3, 3, 2, 4]
def baseStart_2531961 : Nat := 118140960795 + 2531961 * 2 ^ 59
def prefixEnd_2531961 : Nat := 4983230072969 + 3 ^ 40 * 2531961 * 2
def baseEnd_2531961 : Nat := 288913998097482983254051

theorem tailTrace_2531961 : CollatzResearch.WordTrace tailWord_2531961 prefixEnd_2531961 288913998097482983254051 := by
  unfold tailWord_2531961
  simp only [CollatzResearch.WordTrace]
  refine ⟨92348204380145196356835737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61565469586763464237890491 92348204380145196356835737)
  ·
    refine ⟨69261153285108897267626803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92348204380145196356835737 69261153285108897267626803)
    ·
      refine ⟨103891729927663345901440205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69261153285108897267626803 103891729927663345901440205)
      ·
        refine ⟨38959398722873754713040077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103891729927663345901440205 38959398722873754713040077)
        ·
          refine ⟨14609774521077658017390029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38959398722873754713040077 14609774521077658017390029)
          ·
            refine ⟨5478665445404121756521261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14609774521077658017390029 5478665445404121756521261)
            ·
              refine ⟨2054499542026545658695473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5478665445404121756521261 2054499542026545658695473)
              ·
                refine ⟨1540874656519909244021605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2054499542026545658695473 1540874656519909244021605)
                ·
                  refine ⟨288913998097482983254051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1540874656519909244021605 288913998097482983254051)
                  ·
                    rfl

theorem cell22_2531961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 2, 4].length) (baseStart_2531961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2531961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2531961 prefixEnd_2531961 := by exact prefixLift 2531961
  have htrace : WordTrace (prefixWord ++ tailWord_2531961) baseStart_2531961 baseEnd_2531961 := by
    simpa [prefixWord, tailWord_2531961, baseEnd_2531961] using wordTrace_append hprefix tailTrace_2531961
  have hstable : (prefixWord ++ tailWord_2531961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531961).length < 2 ^ (prefixWord ++ tailWord_2531961).sum := by decide
  have hdescent : baseEnd_2531961 < baseStart_2531961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2531972 : List Nat := [2, 3, 2, 1, 3, 1, 1, 9]
def baseStart_2531972 : Nat := 118140960795 + 2531972 * 2 ^ 59
def prefixEnd_2531972 : Nat := 4983230072969 + 3 ^ 40 * 2531972 * 2
def baseEnd_2531972 : Nat := 96305084424138731970791

theorem tailTrace_2531972 : CollatzResearch.WordTrace tailWord_2531972 prefixEnd_2531972 96305084424138731970791 := by
  unfold tailWord_2531972
  simp only [CollatzResearch.WordTrace]
  refine ⟨46174302791552672617743085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61565737055403563490324113 46174302791552672617743085)
  ·
    refine ⟨17315363546832252231653657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46174302791552672617743085 17315363546832252231653657)
    ·
      refine ⟨12986522660124189173740243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17315363546832252231653657 12986522660124189173740243)
      ·
        refine ⟨19479783990186283760610365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12986522660124189173740243 19479783990186283760610365)
        ·
          refine ⟨7304918996319856410228887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19479783990186283760610365 7304918996319856410228887)
          ·
            refine ⟨10957378494479784615343331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7304918996319856410228887 10957378494479784615343331)
            ·
              refine ⟨16436067741719676923014997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10957378494479784615343331 16436067741719676923014997)
              ·
                refine ⟨96305084424138731970791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16436067741719676923014997 96305084424138731970791)
                ·
                  rfl

theorem cell22_2531972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 9].length) (baseStart_2531972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2531972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2531972 prefixEnd_2531972 := by exact prefixLift 2531972
  have htrace : WordTrace (prefixWord ++ tailWord_2531972) baseStart_2531972 baseEnd_2531972 := by
    simpa [prefixWord, tailWord_2531972, baseEnd_2531972] using wordTrace_append hprefix tailTrace_2531972
  have hstable : (prefixWord ++ tailWord_2531972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2531972).length < 2 ^ (prefixWord ++ tailWord_2531972).sum := by decide
  have hdescent : baseEnd_2531972 < baseStart_2531972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2531972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532010 : List Nat := [3, 1, 5, 2, 1, 1, 2, 2, 2, 3]
def baseStart_2532010 : Nat := 118140960795 + 2532010 * 2 ^ 59
def prefixEnd_2532010 : Nat := 4983230072969 + 3 ^ 40 * 2532010 * 2
def baseEnd_2532010 : Nat := 866758767993829155287003

theorem tailTrace_2532010 : CollatzResearch.WordTrace tailWord_2532010 prefixEnd_2532010 866758767993829155287003 := by
  unfold tailWord_2532010
  simp only [CollatzResearch.WordTrace]
  refine ⟨23087497889241919431342371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61566661037978451816912989 23087497889241919431342371)
  ·
    refine ⟨34631246833862879147013557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23087497889241919431342371 34631246833862879147013557)
    ·
      refine ⟨3246679390674644920032521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34631246833862879147013557 3246679390674644920032521)
      ·
        refine ⟨2435009543005983690024391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3246679390674644920032521 2435009543005983690024391)
        ·
          refine ⟨3652514314508975535036587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2435009543005983690024391 3652514314508975535036587)
          ·
            refine ⟨5478771471763463302554881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3652514314508975535036587 5478771471763463302554881)
            ·
              refine ⟨4109078603822597476916161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5478771471763463302554881 4109078603822597476916161)
              ·
                refine ⟨3081808952866948107687121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4109078603822597476916161 3081808952866948107687121)
                ·
                  refine ⟨2311356714650211080765341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3081808952866948107687121 2311356714650211080765341)
                  ·
                    refine ⟨866758767993829155287003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2311356714650211080765341 866758767993829155287003)
                    ·
                      rfl

theorem cell22_2532010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_2532010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2532010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2532010 prefixEnd_2532010 := by exact prefixLift 2532010
  have htrace : WordTrace (prefixWord ++ tailWord_2532010) baseStart_2532010 baseEnd_2532010 := by
    simpa [prefixWord, tailWord_2532010, baseEnd_2532010] using wordTrace_append hprefix tailTrace_2532010
  have hstable : (prefixWord ++ tailWord_2532010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532010).length < 2 ^ (prefixWord ++ tailWord_2532010).sum := by decide
  have hdescent : baseEnd_2532010 < baseStart_2532010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532032 : List Nat := [2, 1, 1, 2, 4, 2, 1, 1, 1, 7]
def baseStart_2532032 : Nat := 118140960795 + 2532032 * 2 ^ 59
def prefixEnd_2532032 : Nat := 4983230072969 + 3 ^ 40 * 2532032 * 2
def baseEnd_2532032 : Nat := 866766299043428431236935

theorem tailTrace_2532032 : CollatzResearch.WordTrace tailWord_2532032 prefixEnd_2532032 866766299043428431236935 := by
  unfold tailWord_2532032
  simp only [CollatzResearch.WordTrace]
  refine ⟨46175396981443987741335175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61567195975258650321780233 46175396981443987741335175)
  ·
    refine ⟨69263095472165981612002763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46175396981443987741335175 69263095472165981612002763)
    ·
      refine ⟨103894643208248972418004145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69263095472165981612002763 103894643208248972418004145)
      ·
        refine ⟨77920982406186729313503109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103894643208248972418004145 77920982406186729313503109)
        ·
          refine ⟨14610184201160011746281833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77920982406186729313503109 14610184201160011746281833)
          ·
            refine ⟨10957638150870008809711375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14610184201160011746281833 10957638150870008809711375)
            ·
              refine ⟨16436457226305013214567063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10957638150870008809711375 16436457226305013214567063)
              ·
                refine ⟨24654685839457519821850595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16436457226305013214567063 24654685839457519821850595)
                ·
                  refine ⟨36982028759186279732775893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24654685839457519821850595 36982028759186279732775893)
                  ·
                    refine ⟨866766299043428431236935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36982028759186279732775893 866766299043428431236935)
                    ·
                      rfl

theorem cell22_2532032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 1, 7].length) (baseStart_2532032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2532032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2532032 prefixEnd_2532032 := by exact prefixLift 2532032
  have htrace : WordTrace (prefixWord ++ tailWord_2532032) baseStart_2532032 baseEnd_2532032 := by
    simpa [prefixWord, tailWord_2532032, baseEnd_2532032] using wordTrace_append hprefix tailTrace_2532032
  have hstable : (prefixWord ++ tailWord_2532032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532032).length < 2 ^ (prefixWord ++ tailWord_2532032).sum := by decide
  have hdescent : baseEnd_2532032 < baseStart_2532032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532079 : List Nat := [1, 1, 2, 1, 5, 3, 2, 1, 6]
def baseStart_2532079 : Nat := 118140960795 + 2532079 * 2 ^ 59
def prefixEnd_2532079 : Nat := 4983230072969 + 3 ^ 40 * 2532079 * 2
def baseEnd_2532079 : Nat := 288927462701311991770597

theorem tailTrace_2532079 : CollatzResearch.WordTrace tailWord_2532079 prefixEnd_2532079 288927462701311991770597 := by
  unfold tailWord_2532079
  simp only [CollatzResearch.WordTrace]
  refine ⟨92352508193717702509631291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61568338795811801673087527 92352508193717702509631291)
  ·
    refine ⟨138528762290576553764446937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92352508193717702509631291 138528762290576553764446937)
    ·
      refine ⟨103896571717932415323335203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138528762290576553764446937 103896571717932415323335203)
      ·
        refine ⟨155844857576898622985002805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103896571717932415323335203 155844857576898622985002805)
        ·
          refine ⟨14610455397834245904844013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 155844857576898622985002805 14610455397834245904844013)
          ·
            refine ⟨5478920774187842214316505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14610455397834245904844013 5478920774187842214316505)
            ·
              refine ⟨4109190580640881660737379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5478920774187842214316505 4109190580640881660737379)
              ·
                refine ⟨6163785870961322491106069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4109190580640881660737379 6163785870961322491106069)
                ·
                  refine ⟨288927462701311991770597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6163785870961322491106069 288927462701311991770597)
                  ·
                    rfl

theorem cell22_2532079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 6].length) (baseStart_2532079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2532079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2532079 prefixEnd_2532079 := by exact prefixLift 2532079
  have htrace : WordTrace (prefixWord ++ tailWord_2532079) baseStart_2532079 baseEnd_2532079 := by
    simpa [prefixWord, tailWord_2532079, baseEnd_2532079] using wordTrace_append hprefix tailTrace_2532079
  have hstable : (prefixWord ++ tailWord_2532079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532079).length < 2 ^ (prefixWord ++ tailWord_2532079).sum := by decide
  have hdescent : baseEnd_2532079 < baseStart_2532079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532098 : List Nat := [3, 4, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_2532098 : Nat := 118140960795 + 2532098 * 2 ^ 59
def prefixEnd_2532098 : Nat := 4983230072969 + 3 ^ 40 * 2532098 * 2
def baseEnd_2532098 : Nat := 866788892192226259086733

theorem tailTrace_2532098 : CollatzResearch.WordTrace tailWord_2532098 prefixEnd_2532098 866788892192226259086733 := by
  unfold tailWord_2532098
  simp only [CollatzResearch.WordTrace]
  refine ⟨23088300295162217188643237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61568800787099245836381965 23088300295162217188643237)
  ·
    refine ⟨4329056305342915722870607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23088300295162217188643237 4329056305342915722870607)
    ·
      refine ⟨6493584458014373584305911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4329056305342915722870607 6493584458014373584305911)
      ·
        refine ⟨9740376687021560376458867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6493584458014373584305911 9740376687021560376458867)
        ·
          refine ⟨14610565030532340564688301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9740376687021560376458867 14610565030532340564688301)
          ·
            refine ⟨5478961886449627711758113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14610565030532340564688301 5478961886449627711758113)
            ·
              refine ⟨4109221414837220783818585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5478961886449627711758113 4109221414837220783818585)
              ·
                refine ⟨3081916061127915587863939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4109221414837220783818585 3081916061127915587863939)
                ·
                  refine ⟨4622874091691873381795909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3081916061127915587863939 4622874091691873381795909)
                  ·
                    refine ⟨866788892192226259086733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4622874091691873381795909 866788892192226259086733)
                    ·
                      rfl

theorem cell22_2532098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_2532098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2532098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2532098 prefixEnd_2532098 := by exact prefixLift 2532098
  have htrace : WordTrace (prefixWord ++ tailWord_2532098) baseStart_2532098 baseEnd_2532098 := by
    simpa [prefixWord, tailWord_2532098, baseEnd_2532098] using wordTrace_append hprefix tailTrace_2532098
  have hstable : (prefixWord ++ tailWord_2532098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532098).length < 2 ^ (prefixWord ++ tailWord_2532098).sum := by decide
  have hdescent : baseEnd_2532098 < baseStart_2532098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532124 : List Nat := [2, 2, 3, 1, 1, 5, 8]
def baseStart_2532124 : Nat := 118140960795 + 2532124 * 2 ^ 59
def prefixEnd_2532124 : Nat := 4983230072969 + 3 ^ 40 * 2532124 * 2
def baseEnd_2532124 : Nat := 32103621945317439182839

theorem tailTrace_2532124 : CollatzResearch.WordTrace tailWord_2532124 prefixEnd_2532124 32103621945317439182839 := by
  unfold tailWord_2532124
  simp only [CollatzResearch.WordTrace]
  refine ⟨46177074739277337597509713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61569432985703116796679617 46177074739277337597509713)
  ·
    refine ⟨34632806054458003198132285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46177074739277337597509713 34632806054458003198132285)
    ·
      refine ⟨12987302270421751199299607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34632806054458003198132285 12987302270421751199299607)
      ·
        refine ⟨19480953405632626798949411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12987302270421751199299607 19480953405632626798949411)
        ·
          refine ⟨29221430108448940198424117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19480953405632626798949411 29221430108448940198424117)
          ·
            refine ⟨2739509072667088143602261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29221430108448940198424117 2739509072667088143602261)
            ·
              refine ⟨32103621945317439182839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2739509072667088143602261 32103621945317439182839)
              ·
                rfl

theorem cell22_2532124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 8].length) (baseStart_2532124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2532124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2532124 prefixEnd_2532124 := by exact prefixLift 2532124
  have htrace : WordTrace (prefixWord ++ tailWord_2532124) baseStart_2532124 baseEnd_2532124 := by
    simpa [prefixWord, tailWord_2532124, baseEnd_2532124] using wordTrace_append hprefix tailTrace_2532124
  have hstable : (prefixWord ++ tailWord_2532124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532124).length < 2 ^ (prefixWord ++ tailWord_2532124).sum := by decide
  have hdescent : baseEnd_2532124 < baseStart_2532124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532137 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 1, 8]
def baseStart_2532137 : Nat := 118140960795 + 2532137 * 2 ^ 59
def prefixEnd_2532137 : Nat := 4983230072969 + 3 ^ 40 * 2532137 * 2
def baseEnd_2532137 : Nat := 866802242689243157361613

theorem tailTrace_2532137 : CollatzResearch.WordTrace tailWord_2532137 prefixEnd_2532137 866802242689243157361613 := by
  unfold tailWord_2532137
  simp only [CollatzResearch.WordTrace]
  refine ⟨92354623627507578415242665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61569749085005052276828443 92354623627507578415242665)
  ·
    refine ⟨69265967720630683811431999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92354623627507578415242665 69265967720630683811431999)
    ·
      refine ⟨103898951580946025717147999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69265967720630683811431999 103898951580946025717147999)
      ·
        refine ⟨155848427371419038575721999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103898951580946025717147999 155848427371419038575721999)
        ·
          refine ⟨233772641057128557863582999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155848427371419038575721999 233772641057128557863582999)
          ·
            refine ⟨350658961585692836795374499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233772641057128557863582999 350658961585692836795374499)
            ·
              refine ⟨525988442378539255193061749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 350658961585692836795374499 525988442378539255193061749)
              ·
                refine ⟨49311416472988055174349539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 525988442378539255193061749 49311416472988055174349539)
                ·
                  refine ⟨73967124709482082761524309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49311416472988055174349539 73967124709482082761524309)
                  ·
                    refine ⟨866802242689243157361613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 73967124709482082761524309 866802242689243157361613)
                    ·
                      rfl

theorem cell22_2532137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 8].length) (baseStart_2532137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2532137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2532137 prefixEnd_2532137 := by exact prefixLift 2532137
  have htrace : WordTrace (prefixWord ++ tailWord_2532137) baseStart_2532137 baseEnd_2532137 := by
    simpa [prefixWord, tailWord_2532137, baseEnd_2532137] using wordTrace_append hprefix tailTrace_2532137
  have hstable : (prefixWord ++ tailWord_2532137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532137).length < 2 ^ (prefixWord ++ tailWord_2532137).sum := by decide
  have hdescent : baseEnd_2532137 < baseStart_2532137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532186 : List Nat := [3, 1, 1, 2, 1, 5, 2, 2, 5]
def baseStart_2532186 : Nat := 118140960795 + 2532186 * 2 ^ 59
def prefixEnd_2532186 : Nat := 4983230072969 + 3 ^ 40 * 2532186 * 2
def baseEnd_2532186 : Nat := 288939672130207787628821

theorem tailTrace_2532186 : CollatzResearch.WordTrace tailWord_2532186 prefixEnd_2532186 288939672130207787628821 := by
  unfold tailWord_2532186
  simp only [CollatzResearch.WordTrace]
  refine ⟨23089102701082514945944103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61570940536220039855850941 23089102701082514945944103)
  ·
    refine ⟨34633654051623772418916155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23089102701082514945944103 34633654051623772418916155)
    ·
      refine ⟨51950481077435658628374233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34633654051623772418916155 51950481077435658628374233)
      ·
        refine ⟨38962860808076743971280675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51950481077435658628374233 38962860808076743971280675)
        ·
          refine ⟨58444291212115115956921013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38962860808076743971280675 58444291212115115956921013)
          ·
            refine ⟨5479152301135792120961345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58444291212115115956921013 5479152301135792120961345)
            ·
              refine ⟨4109364225851844090721009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5479152301135792120961345 4109364225851844090721009)
              ·
                refine ⟨3082023169388883068040757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4109364225851844090721009 3082023169388883068040757)
                ·
                  refine ⟨288939672130207787628821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3082023169388883068040757 288939672130207787628821)
                  ·
                    rfl

theorem cell22_2532186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 5].length) (baseStart_2532186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2532186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2532186 prefixEnd_2532186 := by exact prefixLift 2532186
  have htrace : WordTrace (prefixWord ++ tailWord_2532186) baseStart_2532186 baseEnd_2532186 := by
    simpa [prefixWord, tailWord_2532186, baseEnd_2532186] using wordTrace_append hprefix tailTrace_2532186
  have hstable : (prefixWord ++ tailWord_2532186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532186).length < 2 ^ (prefixWord ++ tailWord_2532186).sum := by decide
  have hdescent : baseEnd_2532186 < baseStart_2532186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532233 : List Nat := [1, 2, 1, 1, 5, 2, 4, 1, 1, 4]
def baseStart_2532233 : Nat := 118140960795 + 2532233 * 2 ^ 59
def prefixEnd_2532233 : Nat := 4983230072969 + 3 ^ 40 * 2532233 * 2
def baseEnd_2532233 : Nat := 866835105451130906961319

theorem tailTrace_2532233 : CollatzResearch.WordTrace tailWord_2532233 prefixEnd_2532233 866835105451130906961319 := by
  unfold tailWord_2532233
  simp only [CollatzResearch.WordTrace]
  refine ⟨92358125035159786810737353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61572083356773191207158235 92358125035159786810737353)
  ·
    refine ⟨69268593776369840108053015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92358125035159786810737353 69268593776369840108053015)
    ·
      refine ⟨103902890664554760162079523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69268593776369840108053015 103902890664554760162079523)
      ·
        refine ⟨155854335996832140243119285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103902890664554760162079523 155854335996832140243119285)
        ·
          refine ⟨14611343999703013147792433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 155854335996832140243119285 14611343999703013147792433)
          ·
            refine ⟨10958507999777259860844325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14611343999703013147792433 10958507999777259860844325)
            ·
              refine ⟨2054720249958236223908311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10958507999777259860844325 2054720249958236223908311)
              ·
                refine ⟨3082080374937354335862467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2054720249958236223908311 3082080374937354335862467)
                ·
                  refine ⟨4623120562406031503793701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3082080374937354335862467 4623120562406031503793701)
                  ·
                    refine ⟨866835105451130906961319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4623120562406031503793701 866835105451130906961319)
                    ·
                      rfl

theorem cell22_2532233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 1, 4].length) (baseStart_2532233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2532233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2532233 prefixEnd_2532233 := by exact prefixLift 2532233
  have htrace : WordTrace (prefixWord ++ tailWord_2532233) baseStart_2532233 baseEnd_2532233 := by
    simpa [prefixWord, tailWord_2532233, baseEnd_2532233] using wordTrace_append hprefix tailTrace_2532233
  have hstable : (prefixWord ++ tailWord_2532233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532233).length < 2 ^ (prefixWord ++ tailWord_2532233).sum := by decide
  have hdescent : baseEnd_2532233 < baseStart_2532233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532396 : List Nat := [2, 2, 1, 1, 1, 2, 5, 1, 1, 6]
def baseStart_2532396 : Nat := 118140960795 + 2532396 * 2 ^ 59
def prefixEnd_2532396 : Nat := 4983230072969 + 3 ^ 40 * 2532396 * 2
def baseEnd_2532396 : Nat := 866890903682252815135819

theorem tailTrace_2532396 : CollatzResearch.WordTrace tailWord_2532396 prefixEnd_2532396 866890903682252815135819 := by
  unfold tailWord_2532396
  simp only [CollatzResearch.WordTrace]
  refine ⟨46182035066784632824460521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61576046755712843765947361 46182035066784632824460521)
  ·
    refine ⟨34636526300088474618345391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46182035066784632824460521 34636526300088474618345391)
    ·
      refine ⟨51954789450132711927518087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34636526300088474618345391 51954789450132711927518087)
      ·
        refine ⟨77932184175199067891277131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51954789450132711927518087 77932184175199067891277131)
        ·
          refine ⟨116898276262798601836915697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77932184175199067891277131 116898276262798601836915697)
          ·
            refine ⟨87673707197098951377686773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116898276262798601836915697 87673707197098951377686773)
            ·
              refine ⟨8219410049728026691658135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87673707197098951377686773 8219410049728026691658135)
              ·
                refine ⟨12329115074592040037487203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8219410049728026691658135 12329115074592040037487203)
                ·
                  refine ⟨18493672611888060056230805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12329115074592040037487203 18493672611888060056230805)
                  ·
                    refine ⟨866890903682252815135819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18493672611888060056230805 866890903682252815135819)
                    ·
                      rfl

theorem cell22_2532396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_2532396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2532396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2532396 prefixEnd_2532396 := by exact prefixLift 2532396
  have htrace : WordTrace (prefixWord ++ tailWord_2532396) baseStart_2532396 baseEnd_2532396 := by
    simpa [prefixWord, tailWord_2532396, baseEnd_2532396] using wordTrace_append hprefix tailTrace_2532396
  have hstable : (prefixWord ++ tailWord_2532396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532396).length < 2 ^ (prefixWord ++ tailWord_2532396).sum := by decide
  have hdescent : baseEnd_2532396 < baseStart_2532396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532398 : List Nat := [4, 1, 3, 1, 1, 1, 1, 4, 1, 5]
def baseStart_2532398 : Nat := 118140960795 + 2532398 * 2 ^ 59
def prefixEnd_2532398 : Nat := 4983230072969 + 3 ^ 40 * 2532398 * 2
def baseEnd_2532398 : Nat := 866891588323125476585813

theorem tailTrace_2532398 : CollatzResearch.WordTrace tailWord_2532398 prefixEnd_2532398 866891588323125476585813 := by
  unfold tailWord_2532398
  simp only [CollatzResearch.WordTrace]
  refine ⟨11545517884945252498811731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61576095386374679993662565 11545517884945252498811731)
  ·
    refine ⟨17318276827417878748217597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11545517884945252498811731 17318276827417878748217597)
    ·
      refine ⟨6494353810281704530581599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17318276827417878748217597 6494353810281704530581599)
      ·
        refine ⟨9741530715422556795872399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6494353810281704530581599 9741530715422556795872399)
        ·
          refine ⟨14612296073133835193808599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9741530715422556795872399 14612296073133835193808599)
          ·
            refine ⟨21918444109700752790712899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14612296073133835193808599 21918444109700752790712899)
            ·
              refine ⟨32877666164551129186069349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21918444109700752790712899 32877666164551129186069349)
              ·
                refine ⟨6164562405853336722388003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32877666164551129186069349 6164562405853336722388003)
                ·
                  refine ⟨9246843608780005083582005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6164562405853336722388003 9246843608780005083582005)
                  ·
                    refine ⟨866891588323125476585813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9246843608780005083582005 866891588323125476585813)
                    ·
                      rfl

theorem cell22_2532398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_2532398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2532398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2532398 prefixEnd_2532398 := by exact prefixLift 2532398
  have htrace : WordTrace (prefixWord ++ tailWord_2532398) baseStart_2532398 baseEnd_2532398 := by
    simpa [prefixWord, tailWord_2532398, baseEnd_2532398] using wordTrace_append hprefix tailTrace_2532398
  have hstable : (prefixWord ++ tailWord_2532398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532398).length < 2 ^ (prefixWord ++ tailWord_2532398).sum := by decide
  have hdescent : baseEnd_2532398 < baseStart_2532398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532445 : List Nat := [1, 4, 4, 1, 2, 1, 1, 8]
def baseStart_2532445 : Nat := 118140960795 + 2532445 * 2 ^ 59
def prefixEnd_2532445 : Nat := 4983230072969 + 3 ^ 40 * 2532445 * 2
def baseEnd_2532445 : Nat := 96323075264848113406741

theorem tailTrace_2532445 : CollatzResearch.WordTrace tailWord_2532445 prefixEnd_2532445 96323075264848113406741 := by
  unfold tailWord_2532445
  simp only [CollatzResearch.WordTrace]
  refine ⟨92365857310391747017454789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61577238206927831344969859 92365857310391747017454789)
  ·
    refine ⟨17318598245698452565772773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92365857310391747017454789 17318598245698452565772773)
    ·
      refine ⟨3247237171068459856082395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17318598245698452565772773 3247237171068459856082395)
      ·
        refine ⟨4870855756602689784123593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3247237171068459856082395 4870855756602689784123593)
        ·
          refine ⟨3653141817452017338092695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4870855756602689784123593 3653141817452017338092695)
          ·
            refine ⟨5479712726178026007139043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3653141817452017338092695 5479712726178026007139043)
            ·
              refine ⟨8219569089267039010708565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5479712726178026007139043 8219569089267039010708565)
              ·
                refine ⟨96323075264848113406741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8219569089267039010708565 96323075264848113406741)
                ·
                  rfl

theorem cell22_2532445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 8].length) (baseStart_2532445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2532445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2532445 prefixEnd_2532445 := by exact prefixLift 2532445
  have htrace : WordTrace (prefixWord ++ tailWord_2532445) baseStart_2532445 baseEnd_2532445 := by
    simpa [prefixWord, tailWord_2532445, baseEnd_2532445] using wordTrace_append hprefix tailTrace_2532445
  have hstable : (prefixWord ++ tailWord_2532445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532445).length < 2 ^ (prefixWord ++ tailWord_2532445).sum := by decide
  have hdescent : baseEnd_2532445 < baseStart_2532445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532535 : List Nat := [1, 1, 3, 1, 4, 1, 3, 4, 4]
def baseStart_2532535 : Nat := 118140960795 + 2532535 * 2 ^ 59
def prefixEnd_2532535 : Nat := 4983230072969 + 3 ^ 40 * 2532535 * 2
def baseEnd_2532535 : Nat := 288979495407634261970131

theorem tailTrace_2532535 : CollatzResearch.WordTrace tailWord_2532535 prefixEnd_2532535 288979495407634261970131 := by
  unfold tailWord_2532535
  simp only [CollatzResearch.WordTrace]
  refine ⟨92369139880065692388231059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61579426586710461592154039 92369139880065692388231059)
  ·
    refine ⟨138553709820098538582346589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92369139880065692388231059 138553709820098538582346589)
    ·
      refine ⟨51957641182536951968379971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138553709820098538582346589 51957641182536951968379971)
      ·
        refine ⟨77936461773805427952569957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51957641182536951968379971 77936461773805427952569957)
        ·
          refine ⟨14613086582588517741106867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77936461773805427952569957 14613086582588517741106867)
          ·
            refine ⟨21919629873882776611660301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14613086582588517741106867 21919629873882776611660301)
            ·
              refine ⟨8219861202706041229372613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21919629873882776611660301 8219861202706041229372613)
              ·
                refine ⟨1541223975507382730507365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8219861202706041229372613 1541223975507382730507365)
                ·
                  refine ⟨288979495407634261970131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1541223975507382730507365 288979495407634261970131)
                  ·
                    rfl

theorem cell22_2532535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 4, 4].length) (baseStart_2532535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2532535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2532535 prefixEnd_2532535 := by exact prefixLift 2532535
  have htrace : WordTrace (prefixWord ++ tailWord_2532535) baseStart_2532535 baseEnd_2532535 := by
    simpa [prefixWord, tailWord_2532535, baseEnd_2532535] using wordTrace_append hprefix tailTrace_2532535
  have hstable : (prefixWord ++ tailWord_2532535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532535).length < 2 ^ (prefixWord ++ tailWord_2532535).sum := by decide
  have hdescent : baseEnd_2532535 < baseStart_2532535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532565 : List Nat := [1, 3, 2, 4, 1, 2, 1, 1, 1, 6]
def baseStart_2532565 : Nat := 118140960795 + 2532565 * 2 ^ 59
def prefixEnd_2532565 : Nat := 4983230072969 + 3 ^ 40 * 2532565 * 2
def baseEnd_2532565 : Nat := 866948755835992707660301

theorem tailTrace_2532565 : CollatzResearch.WordTrace tailWord_2532565 prefixEnd_2532565 866948755835992707660301 := by
  unfold tailWord_2532565
  simp only [CollatzResearch.WordTrace]
  refine ⟨92370234069957007511823149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61580156046638005007882099 92370234069957007511823149)
  ·
    refine ⟨34638837776233877816933681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92370234069957007511823149 34638837776233877816933681)
    ·
      refine ⟨25979128332175408362700261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34638837776233877816933681 25979128332175408362700261)
      ·
        refine ⟨4871086562282889068006299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25979128332175408362700261 4871086562282889068006299)
        ·
          refine ⟨7306629843424333602009449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4871086562282889068006299 7306629843424333602009449)
          ·
            refine ⟨5479972382568250201507087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7306629843424333602009449 5479972382568250201507087)
            ·
              refine ⟨8219958573852375302260631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5479972382568250201507087 8219958573852375302260631)
              ·
                refine ⟨12329937860778562953390947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8219958573852375302260631 12329937860778562953390947)
                ·
                  refine ⟨18494906791167844430086421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12329937860778562953390947 18494906791167844430086421)
                  ·
                    refine ⟨866948755835992707660301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18494906791167844430086421 866948755835992707660301)
                    ·
                      rfl

theorem cell22_2532565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_2532565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2532565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2532565 prefixEnd_2532565 := by exact prefixLift 2532565
  have htrace : WordTrace (prefixWord ++ tailWord_2532565) baseStart_2532565 baseEnd_2532565 := by
    simpa [prefixWord, tailWord_2532565, baseEnd_2532565] using wordTrace_append hprefix tailTrace_2532565
  have hstable : (prefixWord ++ tailWord_2532565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532565).length < 2 ^ (prefixWord ++ tailWord_2532565).sum := by decide
  have hdescent : baseEnd_2532565 < baseStart_2532565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532595 : List Nat := [1, 1, 1, 2, 2, 5, 1, 3, 3, 3]
def baseStart_2532595 : Nat := 118140960795 + 2532595 * 2 ^ 59
def prefixEnd_2532595 : Nat := 4983230072969 + 3 ^ 40 * 2532595 * 2
def baseEnd_2532595 : Nat := 866959025449082629410209

theorem tailTrace_2532595 : CollatzResearch.WordTrace tailWord_2532595 prefixEnd_2532595 866959025449082629410209 := by
  unfold tailWord_2532595
  simp only [CollatzResearch.WordTrace]
  refine ⟨92371328259848322635415239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61580885506565548423610159 92371328259848322635415239)
  ·
    refine ⟨138556992389772483953122859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92371328259848322635415239 138556992389772483953122859)
    ·
      refine ⟨207835488584658725929684289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138556992389772483953122859 207835488584658725929684289)
      ·
        refine ⟨155876616438494044447263217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207835488584658725929684289 155876616438494044447263217)
        ·
          refine ⟨116907462328870533335447413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155876616438494044447263217 116907462328870533335447413)
          ·
            refine ⟨10960074593331612500198195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 116907462328870533335447413 10960074593331612500198195)
            ·
              refine ⟨16440111889997418750297293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10960074593331612500198195 16440111889997418750297293)
              ·
                refine ⟨6165041958749032031361485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16440111889997418750297293 6165041958749032031361485)
                ·
                  refine ⟨2311890734530887011760557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6165041958749032031361485 2311890734530887011760557)
                  ·
                    refine ⟨866959025449082629410209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2311890734530887011760557 866959025449082629410209)
                    ·
                      rfl

theorem cell22_2532595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 3, 3].length) (baseStart_2532595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2532595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2532595 prefixEnd_2532595 := by exact prefixLift 2532595
  have htrace : WordTrace (prefixWord ++ tailWord_2532595) baseStart_2532595 baseEnd_2532595 := by
    simpa [prefixWord, tailWord_2532595, baseEnd_2532595] using wordTrace_append hprefix tailTrace_2532595
  have hstable : (prefixWord ++ tailWord_2532595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532595).length < 2 ^ (prefixWord ++ tailWord_2532595).sum := by decide
  have hdescent : baseEnd_2532595 < baseStart_2532595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532612 : List Nat := [2, 3, 2, 2, 2, 1, 2, 2, 3, 3]
def baseStart_2532612 : Nat := 118140960795 + 2532612 * 2 ^ 59
def prefixEnd_2532612 : Nat := 4983230072969 + 3 ^ 40 * 2532612 * 2
def baseEnd_2532612 : Nat := 866964844896500251735157

theorem tailTrace_2532612 : CollatzResearch.WordTrace tailWord_2532612 prefixEnd_2532612 866964844896500251735157 := by
  unfold tailWord_2532612
  simp only [CollatzResearch.WordTrace]
  refine ⟨46185974150393367269392045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61581298867191156359189393 46185974150393367269392045)
  ·
    refine ⟨17319740306397512726022017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46185974150393367269392045 17319740306397512726022017)
    ·
      refine ⟨12989805229798134544516513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17319740306397512726022017 12989805229798134544516513)
      ·
        refine ⟨9742353922348600908387385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12989805229798134544516513 9742353922348600908387385)
        ·
          refine ⟨7306765441761450681290539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9742353922348600908387385 7306765441761450681290539)
          ·
            refine ⟨10960148162642176021935809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7306765441761450681290539 10960148162642176021935809)
            ·
              refine ⟨8220111121981632016451857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10960148162642176021935809 8220111121981632016451857)
              ·
                refine ⟨6165083341486224012338893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8220111121981632016451857 6165083341486224012338893)
                ·
                  refine ⟨2311906253057334004627085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6165083341486224012338893 2311906253057334004627085)
                  ·
                    refine ⟨866964844896500251735157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2311906253057334004627085 866964844896500251735157)
                    ·
                      rfl

theorem cell22_2532612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_2532612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2532612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2532612 prefixEnd_2532612 := by exact prefixLift 2532612
  have htrace : WordTrace (prefixWord ++ tailWord_2532612) baseStart_2532612 baseEnd_2532612 := by
    simpa [prefixWord, tailWord_2532612, baseEnd_2532612] using wordTrace_append hprefix tailTrace_2532612
  have hstable : (prefixWord ++ tailWord_2532612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532612).length < 2 ^ (prefixWord ++ tailWord_2532612).sum := by decide
  have hdescent : baseEnd_2532612 < baseStart_2532612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532670 : List Nat := [4, 2, 1, 2, 1, 1, 2, 1, 8]
def baseStart_2532670 : Nat := 118140960795 + 2532670 * 2 ^ 59
def prefixEnd_2532670 : Nat := 4983230072969 + 3 ^ 40 * 2532670 * 2
def baseEnd_2532670 : Nat := 288994899827269144594993

theorem tailTrace_2532670 : CollatzResearch.WordTrace tailWord_2532670 prefixEnd_2532670 288994899827269144594993 := by
  unfold tailWord_2532670
  simp only [CollatzResearch.WordTrace]
  refine ⟨11546757966822076305549433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61582709156384406962930309 11546757966822076305549433)
  ·
    refine ⟨8660068475116557229162075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11546757966822076305549433 8660068475116557229162075)
    ·
      refine ⟨12990102712674835843743113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8660068475116557229162075 12990102712674835843743113)
      ·
        refine ⟨9742577034506126882807335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12990102712674835843743113 9742577034506126882807335)
        ·
          refine ⟨14613865551759190324211003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9742577034506126882807335 14613865551759190324211003)
          ·
            refine ⟨21920798327638785486316505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14613865551759190324211003 21920798327638785486316505)
            ·
              refine ⟨16440598745729089114737379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21920798327638785486316505 16440598745729089114737379)
              ·
                refine ⟨24660898118593633672106069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16440598745729089114737379 24660898118593633672106069)
                ·
                  refine ⟨288994899827269144594993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24660898118593633672106069 288994899827269144594993)
                  ·
                    rfl

theorem cell22_2532670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_2532670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2532670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2532670 prefixEnd_2532670 := by exact prefixLift 2532670
  have htrace : WordTrace (prefixWord ++ tailWord_2532670) baseStart_2532670 baseEnd_2532670 := by
    simpa [prefixWord, tailWord_2532670, baseEnd_2532670] using wordTrace_append hprefix tailTrace_2532670
  have hstable : (prefixWord ++ tailWord_2532670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532670).length < 2 ^ (prefixWord ++ tailWord_2532670).sum := by decide
  have hdescent : baseEnd_2532670 < baseStart_2532670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532683 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 5, 6]
def baseStart_2532683 : Nat := 118140960795 + 2532683 * 2 ^ 59
def prefixEnd_2532683 : Nat := 4983230072969 + 3 ^ 40 * 2532683 * 2
def baseEnd_2532683 : Nat := 866989149647479733209939

theorem tailTrace_2532683 : CollatzResearch.WordTrace tailWord_2532683 prefixEnd_2532683 866989149647479733209939 := by
  unfold tailWord_2532683
  simp only [CollatzResearch.WordTrace]
  refine ⟨92374537883529513664618703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61583025255686342443079135 92374537883529513664618703)
  ·
    refine ⟨138561806825294270496928055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92374537883529513664618703 138561806825294270496928055)
    ·
      refine ⟨207842710237941405745392083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138561806825294270496928055 207842710237941405745392083)
      ·
        refine ⟨311764065356912108618088125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207842710237941405745392083 311764065356912108618088125)
        ·
          refine ⟨116911524508842040731783047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 311764065356912108618088125 116911524508842040731783047)
          ·
            refine ⟨175367286763263061097674571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116911524508842040731783047 175367286763263061097674571)
            ·
              refine ⟨263050930144894591646511857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175367286763263061097674571 263050930144894591646511857)
              ·
                refine ⟨197288197608670943734883893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 263050930144894591646511857 197288197608670943734883893)
                ·
                  refine ⟨18495768525812900975145365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 197288197608670943734883893 18495768525812900975145365)
                  ·
                    refine ⟨866989149647479733209939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18495768525812900975145365 866989149647479733209939)
                    ·
                      rfl

theorem cell22_2532683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 6].length) (baseStart_2532683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2532683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2532683 prefixEnd_2532683 := by exact prefixLift 2532683
  have htrace : WordTrace (prefixWord ++ tailWord_2532683) baseStart_2532683 baseEnd_2532683 := by
    simpa [prefixWord, tailWord_2532683, baseEnd_2532683] using wordTrace_append hprefix tailTrace_2532683
  have hstable : (prefixWord ++ tailWord_2532683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532683).length < 2 ^ (prefixWord ++ tailWord_2532683).sum := by decide
  have hdescent : baseEnd_2532683 < baseStart_2532683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532704 : List Nat := [2, 1, 1, 3, 4, 1, 4, 2, 4]
def baseStart_2532704 : Nat := 118140960795 + 2532704 * 2 ^ 59
def prefixEnd_2532704 : Nat := 4983230072969 + 3 ^ 40 * 2532704 * 2
def baseEnd_2532704 : Nat := 288998779458880892811625

theorem tailTrace_2532704 : CollatzResearch.WordTrace tailWord_2532704 prefixEnd_2532704 288998779458880892811625 := by
  unfold tailWord_2532704
  simp only [CollatzResearch.WordTrace]
  refine ⟨46187651908226717125566583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61583535877635622834088777 46187651908226717125566583)
  ·
    refine ⟨69281477862340075688349875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46187651908226717125566583 69281477862340075688349875)
    ·
      refine ⟨103922216793510113532524813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69281477862340075688349875 103922216793510113532524813)
      ·
        refine ⟨38970831297566292574696805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103922216793510113532524813 38970831297566292574696805)
        ·
          refine ⟨7307030868293679857755651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38970831297566292574696805 7307030868293679857755651)
          ·
            refine ⟨10960546302440519786633477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7307030868293679857755651 10960546302440519786633477)
            ·
              refine ⟨2055102431707597459993777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10960546302440519786633477 2055102431707597459993777)
              ·
                refine ⟨1541326823780698094995333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2055102431707597459993777 1541326823780698094995333)
                ·
                  refine ⟨288998779458880892811625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1541326823780698094995333 288998779458880892811625)
                  ·
                    rfl

theorem cell22_2532704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 2, 4].length) (baseStart_2532704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2532704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2532704 prefixEnd_2532704 := by exact prefixLift 2532704
  have htrace : WordTrace (prefixWord ++ tailWord_2532704) baseStart_2532704 baseEnd_2532704 := by
    simpa [prefixWord, tailWord_2532704, baseEnd_2532704] using wordTrace_append hprefix tailTrace_2532704
  have hstable : (prefixWord ++ tailWord_2532704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532704).length < 2 ^ (prefixWord ++ tailWord_2532704).sum := by decide
  have hdescent : baseEnd_2532704 < baseStart_2532704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532807 : List Nat := [1, 1, 4, 1, 1, 3, 1, 5, 1, 4]
def baseStart_2532807 : Nat := 118140960795 + 2532807 * 2 ^ 59
def prefixEnd_2532807 : Nat := 4983230072969 + 3 ^ 40 * 2532807 * 2
def baseEnd_2532807 : Nat := 867031597381584743109559

theorem tailTrace_2532807 : CollatzResearch.WordTrace tailWord_2532807 prefixEnd_2532807 867031597381584743109559 := by
  unfold tailWord_2532807
  simp only [CollatzResearch.WordTrace]
  refine ⟨92379060535080282842132675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61586040356720188561421783 92379060535080282842132675)
  ·
    refine ⟨138568590802620424263199013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92379060535080282842132675 138568590802620424263199013)
    ·
      refine ⟨25981610775491329549349815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138568590802620424263199013 25981610775491329549349815)
      ·
        refine ⟨38972416163236994324024723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25981610775491329549349815 38972416163236994324024723)
        ·
          refine ⟨58458624244855491486037085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38972416163236994324024723 58458624244855491486037085)
          ·
            refine ⟨21921984091820809307263907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58458624244855491486037085 21921984091820809307263907)
            ·
              refine ⟨32882976137731213960895861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21921984091820809307263907 32882976137731213960895861)
              ·
                refine ⟨3082779012912301308833987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32882976137731213960895861 3082779012912301308833987)
                ·
                  refine ⟨4624168519368451963250981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3082779012912301308833987 4624168519368451963250981)
                  ·
                    refine ⟨867031597381584743109559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4624168519368451963250981 867031597381584743109559)
                    ·
                      rfl

theorem cell22_2532807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_2532807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2532807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2532807 prefixEnd_2532807 := by exact prefixLift 2532807
  have htrace : WordTrace (prefixWord ++ tailWord_2532807) baseStart_2532807 baseEnd_2532807 := by
    simpa [prefixWord, tailWord_2532807, baseEnd_2532807] using wordTrace_append hprefix tailTrace_2532807
  have hstable : (prefixWord ++ tailWord_2532807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532807).length < 2 ^ (prefixWord ++ tailWord_2532807).sum := by decide
  have hdescent : baseEnd_2532807 < baseStart_2532807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532854 : List Nat := [5, 1, 1, 1, 2, 3, 1, 2, 1, 5]
def baseStart_2532854 : Nat := 118140960795 + 2532854 * 2 ^ 59
def prefixEnd_2532854 : Nat := 4983230072969 + 3 ^ 40 * 2532854 * 2
def baseEnd_2532854 : Nat := 867047686442092287184415

theorem tailTrace_2532854 : CollatzResearch.WordTrace tailWord_2532854 prefixEnd_2532854 867047686442092287184415 := by
  unfold tailWord_2532854
  simp only [CollatzResearch.WordTrace]
  refine ⟨5773798422869375616818351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61587183177273339912729077 5773798422869375616818351)
  ·
    refine ⟨8660697634304063425227527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5773798422869375616818351 8660697634304063425227527)
    ·
      refine ⟨12991046451456095137841291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8660697634304063425227527 12991046451456095137841291)
      ·
        refine ⟨19486569677184142706761937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12991046451456095137841291 19486569677184142706761937)
        ·
          refine ⟨14614927257888107030071453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19486569677184142706761937 14614927257888107030071453)
          ·
            refine ⟨5480597721708040136276795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14614927257888107030071453 5480597721708040136276795)
            ·
              refine ⟨8220896582562060204415193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5480597721708040136276795 8220896582562060204415193)
              ·
                refine ⟨6165672436921545153311395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8220896582562060204415193 6165672436921545153311395)
                ·
                  refine ⟨9248508655382317729967093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6165672436921545153311395 9248508655382317729967093)
                  ·
                    refine ⟨867047686442092287184415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9248508655382317729967093 867047686442092287184415)
                    ·
                      rfl

theorem cell22_2532854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_2532854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2532854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2532854 prefixEnd_2532854 := by exact prefixLift 2532854
  have htrace : WordTrace (prefixWord ++ tailWord_2532854) baseStart_2532854 baseEnd_2532854 := by
    simpa [prefixWord, tailWord_2532854, baseEnd_2532854] using wordTrace_append hprefix tailTrace_2532854
  have hstable : (prefixWord ++ tailWord_2532854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532854).length < 2 ^ (prefixWord ++ tailWord_2532854).sum := by decide
  have hdescent : baseEnd_2532854 < baseStart_2532854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532871 : List Nat := [1, 1, 4, 3, 2, 2, 2, 2, 2, 3]
def baseStart_2532871 : Nat := 118140960795 + 2532871 * 2 ^ 59
def prefixEnd_2532871 : Nat := 4983230072969 + 3 ^ 40 * 2532871 * 2
def baseEnd_2532871 : Nat := 867053505889509909509363

theorem tailTrace_2532871 : CollatzResearch.WordTrace tailWord_2532871 prefixEnd_2532871 867053505889509909509363 := by
  unfold tailWord_2532871
  simp only [CollatzResearch.WordTrace]
  refine ⟨92381394806848421772462467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61587596537898947848308311 92381394806848421772462467)
  ·
    refine ⟨138572092210272632658693701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92381394806848421772462467 138572092210272632658693701)
    ·
      refine ⟨25982267289426118623505069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138572092210272632658693701 25982267289426118623505069)
      ·
        refine ⟨9743350233534794483814401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25982267289426118623505069 9743350233534794483814401)
        ·
          refine ⟨7307512675151095862860801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9743350233534794483814401 7307512675151095862860801)
          ·
            refine ⟨5480634506363321897145601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7307512675151095862860801 5480634506363321897145601)
            ·
              refine ⟨4110475879772491422859201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5480634506363321897145601 4110475879772491422859201)
              ·
                refine ⟨3082856909829368567144401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4110475879772491422859201 3082856909829368567144401)
                ·
                  refine ⟨2312142682372026425358301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3082856909829368567144401 2312142682372026425358301)
                  ·
                    refine ⟨867053505889509909509363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2312142682372026425358301 867053505889509909509363)
                    ·
                      rfl

theorem cell22_2532871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_2532871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2532871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2532871 prefixEnd_2532871 := by exact prefixLift 2532871
  have htrace : WordTrace (prefixWord ++ tailWord_2532871) baseStart_2532871 baseEnd_2532871 := by
    simpa [prefixWord, tailWord_2532871, baseEnd_2532871] using wordTrace_append hprefix tailTrace_2532871
  have hstable : (prefixWord ++ tailWord_2532871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532871).length < 2 ^ (prefixWord ++ tailWord_2532871).sum := by decide
  have hdescent : baseEnd_2532871 < baseStart_2532871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532927 : List Nat := [1, 1, 2, 2, 3, 3, 1, 2, 2, 5]
def baseStart_2532927 : Nat := 118140960795 + 2532927 * 2 ^ 59
def prefixEnd_2532927 : Nat := 4983230072969 + 3 ^ 40 * 2532927 * 2
def baseEnd_2532927 : Nat := 867072675833944430109191

theorem tailTrace_2532927 : CollatzResearch.WordTrace tailWord_2532927 prefixEnd_2532927 867072675833944430109191 := by
  unfold tailWord_2532927
  simp only [CollatzResearch.WordTrace]
  refine ⟨92383437294645543336501035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61588958196430362224334023 92383437294645543336501035)
  ·
    refine ⟨138575155941968315004751553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92383437294645543336501035 138575155941968315004751553)
    ·
      refine ⟨103931366956476236253563665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138575155941968315004751553 103931366956476236253563665)
      ·
        refine ⟨77948525217357177190172749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103931366956476236253563665 77948525217357177190172749)
        ·
          refine ⟨29230696956508941446314781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77948525217357177190172749 29230696956508941446314781)
          ·
            refine ⟨10961511358690853042368043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29230696956508941446314781 10961511358690853042368043)
            ·
              refine ⟨16442267038036279563552065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10961511358690853042368043 16442267038036279563552065)
              ·
                refine ⟨12331700278527209672664049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16442267038036279563552065 12331700278527209672664049)
                ·
                  refine ⟨9248775208895407254498037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12331700278527209672664049 9248775208895407254498037)
                  ·
                    refine ⟨867072675833944430109191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9248775208895407254498037 867072675833944430109191)
                    ·
                      rfl

theorem cell22_2532927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 5].length) (baseStart_2532927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2532927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2532927 prefixEnd_2532927 := by exact prefixLift 2532927
  have htrace : WordTrace (prefixWord ++ tailWord_2532927) baseStart_2532927 baseEnd_2532927 := by
    simpa [prefixWord, tailWord_2532927, baseEnd_2532927] using wordTrace_append hprefix tailTrace_2532927
  have hstable : (prefixWord ++ tailWord_2532927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532927).length < 2 ^ (prefixWord ++ tailWord_2532927).sum := by decide
  have hdescent : baseEnd_2532927 < baseStart_2532927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532946 : List Nat := [3, 2, 2, 1, 2, 3, 3, 1, 5]
def baseStart_2532946 : Nat := 118140960795 + 2532946 * 2 ^ 59
def prefixEnd_2532946 : Nat := 4983230072969 + 3 ^ 40 * 2532946 * 2
def baseEnd_2532946 : Nat := 289026393307411571294711

theorem tailTrace_2532946 : CollatzResearch.WordTrace tailWord_2532946 prefixEnd_2532946 289026393307411571294711 := by
  unfold tailWord_2532946
  simp only [CollatzResearch.WordTrace]
  refine ⟨23096032570394177395360673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61589420187717806387628461 23096032570394177395360673)
  ·
    refine ⟨17322024427795633046520505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23096032570394177395360673 17322024427795633046520505)
    ·
      refine ⟨12991518320846724784890379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17322024427795633046520505 12991518320846724784890379)
      ·
        refine ⟨19487277481270087177335569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12991518320846724784890379 19487277481270087177335569)
        ·
          refine ⟨14615458110952565383001677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19487277481270087177335569 14615458110952565383001677)
          ·
            refine ⟨5480796791607212018625629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14615458110952565383001677 5480796791607212018625629)
            ·
              refine ⟨2055298796852704506984611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5480796791607212018625629 2055298796852704506984611)
              ·
                refine ⟨3082948195279056760476917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2055298796852704506984611 3082948195279056760476917)
                ·
                  refine ⟨289026393307411571294711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3082948195279056760476917 289026393307411571294711)
                  ·
                    rfl

theorem cell22_2532946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_2532946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2532946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2532946 prefixEnd_2532946 := by exact prefixLift 2532946
  have htrace : WordTrace (prefixWord ++ tailWord_2532946) baseStart_2532946 baseEnd_2532946 := by
    simpa [prefixWord, tailWord_2532946, baseEnd_2532946] using wordTrace_append hprefix tailTrace_2532946
  have hstable : (prefixWord ++ tailWord_2532946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532946).length < 2 ^ (prefixWord ++ tailWord_2532946).sum := by decide
  have hdescent : baseEnd_2532946 < baseStart_2532946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2532972 : List Nat := [2, 2, 1, 1, 3, 1, 1, 3, 3, 5]
def baseStart_2532972 : Nat := 118140960795 + 2532972 * 2 ^ 59
def prefixEnd_2532972 : Nat := 4983230072969 + 3 ^ 40 * 2532972 * 2
def baseEnd_2532972 : Nat := 867088080253579312734053

theorem tailTrace_2532972 : CollatzResearch.WordTrace tailWord_2532972 prefixEnd_2532972 867088080253579312734053 := by
  unfold tailWord_2532972
  simp only [CollatzResearch.WordTrace]
  refine ⟨46192539289741258010944585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61590052386321677347926113 46192539289741258010944585)
  ·
    refine ⟨34644404467305943508208439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46192539289741258010944585 34644404467305943508208439)
    ·
      refine ⟨51966606700958915262312659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34644404467305943508208439 51966606700958915262312659)
      ·
        refine ⟨77949910051438372893468989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51966606700958915262312659 77949910051438372893468989)
        ·
          refine ⟨29231216269289389835050871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77949910051438372893468989 29231216269289389835050871)
          ·
            refine ⟨43846824403934084752576307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29231216269289389835050871 43846824403934084752576307)
            ·
              refine ⟨65770236605901127128864461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43846824403934084752576307 65770236605901127128864461)
              ·
                refine ⟨24663838727212922673324173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65770236605901127128864461 24663838727212922673324173)
                ·
                  refine ⟨9248939522704846002496565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24663838727212922673324173 9248939522704846002496565)
                  ·
                    refine ⟨867088080253579312734053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9248939522704846002496565 867088080253579312734053)
                    ·
                      rfl

theorem cell22_2532972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_2532972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2532972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2532972 prefixEnd_2532972 := by exact prefixLift 2532972
  have htrace : WordTrace (prefixWord ++ tailWord_2532972) baseStart_2532972 baseEnd_2532972 := by
    simpa [prefixWord, tailWord_2532972, baseEnd_2532972] using wordTrace_append hprefix tailTrace_2532972
  have hstable : (prefixWord ++ tailWord_2532972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2532972).length < 2 ^ (prefixWord ++ tailWord_2532972).sum := by decide
  have hdescent : baseEnd_2532972 < baseStart_2532972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2532972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533010 : List Nat := [3, 2, 3, 1, 4, 1, 1, 2, 1, 4]
def baseStart_2533010 : Nat := 118140960795 + 2533010 * 2 ^ 59
def prefixEnd_2533010 : Nat := 4983230072969 + 3 ^ 40 * 2533010 * 2
def baseEnd_2533010 : Nat := 867101088430159880283937

theorem tailTrace_2533010 : CollatzResearch.WordTrace tailWord_2533010 prefixEnd_2533010 867101088430159880283937 := by
  unfold tailWord_2533010
  simp only [CollatzResearch.WordTrace]
  refine ⟨23096616138336212127943121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61590976368896565674514989 23096616138336212127943121)
  ·
    refine ⟨17322462103752159095957341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23096616138336212127943121 17322462103752159095957341)
    ·
      refine ⟨6495923288907059660984003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17322462103752159095957341 6495923288907059660984003)
      ·
        refine ⟨9743884933360589491476005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6495923288907059660984003 9743884933360589491476005)
        ·
          refine ⟨1826978425005110529651751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9743884933360589491476005 1826978425005110529651751)
          ·
            refine ⟨2740467637507665794477627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1826978425005110529651751 2740467637507665794477627)
            ·
              refine ⟨4110701456261498691716441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2740467637507665794477627 4110701456261498691716441)
              ·
                refine ⟨3083026092196124018787331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4110701456261498691716441 3083026092196124018787331)
                ·
                  refine ⟨4624539138294186028180997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3083026092196124018787331 4624539138294186028180997)
                  ·
                    refine ⟨867101088430159880283937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4624539138294186028180997 867101088430159880283937)
                    ·
                      rfl

theorem cell22_2533010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_2533010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2533010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2533010 prefixEnd_2533010 := by exact prefixLift 2533010
  have htrace : WordTrace (prefixWord ++ tailWord_2533010) baseStart_2533010 baseEnd_2533010 := by
    simpa [prefixWord, tailWord_2533010, baseEnd_2533010] using wordTrace_append hprefix tailTrace_2533010
  have hstable : (prefixWord ++ tailWord_2533010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533010).length < 2 ^ (prefixWord ++ tailWord_2533010).sum := by decide
  have hdescent : baseEnd_2533010 < baseStart_2533010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533064 : List Nat := [2, 1, 3, 1, 2, 2, 1, 5, 5]
def baseStart_2533064 : Nat := 118140960795 + 2533064 * 2 ^ 59
def prefixEnd_2533064 : Nat := 4983230072969 + 3 ^ 40 * 2533064 * 2
def baseEnd_2533064 : Nat := 289039857911240579811257

theorem tailTrace_2533064 : CollatzResearch.WordTrace tailWord_2533064 prefixEnd_2533064 289039857911240579811257 := by
  unfold tailWord_2533064
  simp only [CollatzResearch.WordTrace]
  refine ⟨46194217047574607867119123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61592289396766143822825497 46194217047574607867119123)
  ·
    refine ⟨69291325571361911800678685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46194217047574607867119123 69291325571361911800678685)
    ·
      refine ⟨25984247089260716925254507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69291325571361911800678685 25984247089260716925254507)
      ·
        refine ⟨38976370633891075387881761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25984247089260716925254507 38976370633891075387881761)
        ·
          refine ⟨29232277975418306540911321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38976370633891075387881761 29232277975418306540911321)
          ·
            refine ⟨21924208481563729905683491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29232277975418306540911321 21924208481563729905683491)
            ·
              refine ⟨32886312722345594858525237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21924208481563729905683491 32886312722345594858525237)
              ·
                refine ⟨3083091817719899517986741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32886312722345594858525237 3083091817719899517986741)
                ·
                  refine ⟨289039857911240579811257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3083091817719899517986741 289039857911240579811257)
                  ·
                    rfl

theorem cell22_2533064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 5].length) (baseStart_2533064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2533064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2533064 prefixEnd_2533064 := by exact prefixLift 2533064
  have htrace : WordTrace (prefixWord ++ tailWord_2533064) baseStart_2533064 baseEnd_2533064 := by
    simpa [prefixWord, tailWord_2533064, baseEnd_2533064] using wordTrace_append hprefix tailTrace_2533064
  have hstable : (prefixWord ++ tailWord_2533064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533064).length < 2 ^ (prefixWord ++ tailWord_2533064).sum := by decide
  have hdescent : baseEnd_2533064 < baseStart_2533064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533068 : List Nat := [2, 2, 1, 5, 2, 1, 1, 2, 3, 3]
def baseStart_2533068 : Nat := 118140960795 + 2533068 * 2 ^ 59
def prefixEnd_2533068 : Nat := 4983230072969 + 3 ^ 40 * 2533068 * 2
def baseEnd_2533068 : Nat := 867120943015467062333759

theorem tailTrace_2533068 : CollatzResearch.WordTrace tailWord_2533068 prefixEnd_2533068 867120943015467062333759 := by
  unfold tailWord_2533068
  simp only [CollatzResearch.WordTrace]
  refine ⟨46194289993567362208691929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61592386658089816278255905 46194289993567362208691929)
  ·
    refine ⟨34645717495175521656518947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46194289993567362208691929 34645717495175521656518947)
    ·
      refine ⟨51968576242763282484778421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34645717495175521656518947 51968576242763282484778421)
      ·
        refine ⟨4872054022759057732947977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51968576242763282484778421 4872054022759057732947977)
        ·
          refine ⟨3654040517069293299710983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4872054022759057732947977 3654040517069293299710983)
          ·
            refine ⟨5481060775603939949566475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3654040517069293299710983 5481060775603939949566475)
            ·
              refine ⟨8221591163405909924349713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5481060775603939949566475 8221591163405909924349713)
              ·
                refine ⟨6166193372554432443262285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8221591163405909924349713 6166193372554432443262285)
                ·
                  refine ⟨2312322514707912166223357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6166193372554432443262285 2312322514707912166223357)
                  ·
                    refine ⟨867120943015467062333759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2312322514707912166223357 867120943015467062333759)
                    ·
                      rfl

theorem cell22_2533068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 3, 3].length) (baseStart_2533068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2533068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2533068 prefixEnd_2533068 := by exact prefixLift 2533068
  have htrace : WordTrace (prefixWord ++ tailWord_2533068) baseStart_2533068 baseEnd_2533068 := by
    simpa [prefixWord, tailWord_2533068, baseEnd_2533068] using wordTrace_append hprefix tailTrace_2533068
  have hstable : (prefixWord ++ tailWord_2533068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533068).length < 2 ^ (prefixWord ++ tailWord_2533068).sum := by decide
  have hdescent : baseEnd_2533068 < baseStart_2533068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533141 : List Nat := [1, 3, 2, 1, 2, 3, 1, 2, 4, 3]
def baseStart_2533141 : Nat := 118140960795 + 2533141 * 2 ^ 59
def prefixEnd_2533141 : Nat := 4983230072969 + 3 ^ 40 * 2533141 * 2
def baseEnd_2533141 : Nat := 867145932407319205258535

theorem tailTrace_2533141 : CollatzResearch.WordTrace tailWord_2533141 prefixEnd_2533141 867145932407319205258535 := by
  unfold tailWord_2533141
  simp only [CollatzResearch.WordTrace]
  refine ⟨92391242515870257884791277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61594161677246838589860851 92391242515870257884791277)
  ·
    refine ⟨34646715943451346706796729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92391242515870257884791277 34646715943451346706796729)
    ·
      refine ⟨25985036957588510030097547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34646715943451346706796729 25985036957588510030097547)
      ·
        refine ⟨38977555436382765045146321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25985036957588510030097547 38977555436382765045146321)
        ·
          refine ⟨29233166577287073783859741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38977555436382765045146321 29233166577287073783859741)
          ·
            refine ⟨10962437466482652668947403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29233166577287073783859741 10962437466482652668947403)
            ·
              refine ⟨16443656199723979003421105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10962437466482652668947403 16443656199723979003421105)
              ·
                refine ⟨12332742149792984252565829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16443656199723979003421105 12332742149792984252565829)
                ·
                  refine ⟨2312389153086184547356093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12332742149792984252565829 2312389153086184547356093)
                  ·
                    refine ⟨867145932407319205258535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2312389153086184547356093 867145932407319205258535)
                    ·
                      rfl

theorem cell22_2533141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_2533141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2533141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2533141 prefixEnd_2533141 := by exact prefixLift 2533141
  have htrace : WordTrace (prefixWord ++ tailWord_2533141) baseStart_2533141 baseEnd_2533141 := by
    simpa [prefixWord, tailWord_2533141, baseEnd_2533141] using wordTrace_append hprefix tailTrace_2533141
  have hstable : (prefixWord ++ tailWord_2533141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533141).length < 2 ^ (prefixWord ++ tailWord_2533141).sum := by decide
  have hdescent : baseEnd_2533141 < baseStart_2533141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533143 : List Nat := [1, 1, 3, 4, 2, 1, 3, 3, 4]
def baseStart_2533143 : Nat := 118140960795 + 2533143 * 2 ^ 59
def prefixEnd_2533143 : Nat := 4983230072969 + 3 ^ 40 * 2533143 * 2
def baseEnd_2533143 : Nat := 289048872349397288902843

theorem tailTrace_2533143 : CollatzResearch.WordTrace tailWord_2533143 prefixEnd_2533143 289048872349397288902843 := by
  unfold tailWord_2533143
  simp only [CollatzResearch.WordTrace]
  refine ⟨92391315461863012226364083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61594210307908674817576055 92391315461863012226364083)
  ·
    refine ⟨138586973192794518339546125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92391315461863012226364083 138586973192794518339546125)
    ·
      refine ⟨51970114947297944377329797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138586973192794518339546125 51970114947297944377329797)
      ·
        refine ⟨9744396552618364570749337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51970114947297944377329797 9744396552618364570749337)
        ·
          refine ⟨7308297414463773428062003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9744396552618364570749337 7308297414463773428062003)
          ·
            refine ⟨10962446121695660142093005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7308297414463773428062003 10962446121695660142093005)
            ·
              refine ⟨4110917295635872553284877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10962446121695660142093005 4110917295635872553284877)
              ·
                refine ⟨1541593985863452207481829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4110917295635872553284877 1541593985863452207481829)
                ·
                  refine ⟨289048872349397288902843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1541593985863452207481829 289048872349397288902843)
                  ·
                    rfl

theorem cell22_2533143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 3, 4].length) (baseStart_2533143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2533143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2533143 prefixEnd_2533143 := by exact prefixLift 2533143
  have htrace : WordTrace (prefixWord ++ tailWord_2533143) baseStart_2533143 baseEnd_2533143 := by
    simpa [prefixWord, tailWord_2533143, baseEnd_2533143] using wordTrace_append hprefix tailTrace_2533143
  have hstable : (prefixWord ++ tailWord_2533143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533143).length < 2 ^ (prefixWord ++ tailWord_2533143).sum := by decide
  have hdescent : baseEnd_2533143 < baseStart_2533143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533156 : List Nat := [2, 3, 1, 3, 2, 1, 1, 1, 4, 4]
def baseStart_2533156 : Nat := 118140960795 + 2533156 * 2 ^ 59
def prefixEnd_2533156 : Nat := 4983230072969 + 3 ^ 40 * 2533156 * 2
def baseEnd_2533156 : Nat := 867151067213864166133489

theorem tailTrace_2533156 : CollatzResearch.WordTrace tailWord_2533156 prefixEnd_2533156 867151067213864166133489 := by
  unfold tailWord_2533156
  simp only [CollatzResearch.WordTrace]
  refine ⟨46195894805407957723293661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61594526407210610297724881 46195894805407957723293661)
  ·
    refine ⟨17323460552027984146235123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46195894805407957723293661 17323460552027984146235123)
    ·
      refine ⟨25985190828041976219352685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17323460552027984146235123 25985190828041976219352685)
      ·
        refine ⟨9744446560515741082257257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25985190828041976219352685 9744446560515741082257257)
        ·
          refine ⟨7308334920386805811692943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9744446560515741082257257 7308334920386805811692943)
          ·
            refine ⟨10962502380580208717539415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7308334920386805811692943 10962502380580208717539415)
            ·
              refine ⟨16443753570870313076309123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10962502380580208717539415 16443753570870313076309123)
              ·
                refine ⟨24665630356305469614463685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16443753570870313076309123 24665630356305469614463685)
                ·
                  refine ⟨4624805691807275552711941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24665630356305469614463685 4624805691807275552711941)
                  ·
                    refine ⟨867151067213864166133489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4624805691807275552711941 867151067213864166133489)
                    ·
                      rfl

theorem cell22_2533156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_2533156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2533156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2533156 prefixEnd_2533156 := by exact prefixLift 2533156
  have htrace : WordTrace (prefixWord ++ tailWord_2533156) baseStart_2533156 baseEnd_2533156 := by
    simpa [prefixWord, tailWord_2533156, baseEnd_2533156] using wordTrace_append hprefix tailTrace_2533156
  have hstable : (prefixWord ++ tailWord_2533156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533156).length < 2 ^ (prefixWord ++ tailWord_2533156).sum := by decide
  have hdescent : baseEnd_2533156 < baseStart_2533156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533160 : List Nat := [2, 1, 5, 1, 1, 3, 3, 2, 4]
def baseStart_2533160 : Nat := 118140960795 + 2533160 * 2 ^ 59
def prefixEnd_2533160 : Nat := 4983230072969 + 3 ^ 40 * 2533160 * 2
def baseEnd_2533160 : Nat := 289050812165203163011159

theorem tailTrace_2533160 : CollatzResearch.WordTrace tailWord_2533160 prefixEnd_2533160 289050812165203163011159 := by
  unfold tailWord_2533160
  simp only [CollatzResearch.WordTrace]
  refine ⟨46195967751400712064866467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61594623668534282753155289 46195967751400712064866467)
  ·
    refine ⟨69293951627101068097299701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46195967751400712064866467 69293951627101068097299701)
    ·
      refine ⟨6496307965040725134121847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69293951627101068097299701 6496307965040725134121847)
      ·
        refine ⟨9744461947561087701182771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6496307965040725134121847 9744461947561087701182771)
        ·
          refine ⟨14616692921341631551774157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9744461947561087701182771 14616692921341631551774157)
          ·
            refine ⟨5481259845503111831915309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14616692921341631551774157 5481259845503111831915309)
            ·
              refine ⟨2055472442063666936968241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5481259845503111831915309 2055472442063666936968241)
              ·
                refine ⟨1541604331547750202726181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2055472442063666936968241 1541604331547750202726181)
                ·
                  refine ⟨289050812165203163011159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1541604331547750202726181 289050812165203163011159)
                  ·
                    rfl

theorem cell22_2533160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 2, 4].length) (baseStart_2533160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2533160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2533160 prefixEnd_2533160 := by exact prefixLift 2533160
  have htrace : WordTrace (prefixWord ++ tailWord_2533160) baseStart_2533160 baseEnd_2533160 := by
    simpa [prefixWord, tailWord_2533160, baseEnd_2533160] using wordTrace_append hprefix tailTrace_2533160
  have hstable : (prefixWord ++ tailWord_2533160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533160).length < 2 ^ (prefixWord ++ tailWord_2533160).sum := by decide
  have hdescent : baseEnd_2533160 < baseStart_2533160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533171 : List Nat := [1, 1, 1, 2, 7, 1, 2, 7]
def baseStart_2533171 : Nat := 118140960795 + 2533171 * 2 ^ 59
def prefixEnd_2533171 : Nat := 4983230072969 + 3 ^ 40 * 2533171 * 2
def baseEnd_2533171 : Nat := 96350689113378791889827

theorem tailTrace_2533171 : CollatzResearch.WordTrace tailWord_2533171 prefixEnd_2533171 96350689113378791889827 := by
  unfold tailWord_2533171
  simp only [CollatzResearch.WordTrace]
  refine ⟨92392336705761573008383367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61594891137174382005588911 92392336705761573008383367)
  ·
    refine ⟨138588505058642359512575051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92392336705761573008383367 138588505058642359512575051)
    ·
      refine ⟨207882757587963539268862577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138588505058642359512575051 207882757587963539268862577)
      ·
        refine ⟨155912068190972654451646933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207882757587963539268862577 155912068190972654451646933)
        ·
          refine ⟨3654189098225921588710475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 155912068190972654451646933 3654189098225921588710475)
          ·
            refine ⟨5481283647338882383065713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3654189098225921588710475 5481283647338882383065713)
            ·
              refine ⟨4110962735504161787299285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5481283647338882383065713 4110962735504161787299285)
              ·
                refine ⟨96350689113378791889827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4110962735504161787299285 96350689113378791889827)
                ·
                  rfl

theorem cell22_2533171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 7].length) (baseStart_2533171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2533171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2533171 prefixEnd_2533171 := by exact prefixLift 2533171
  have htrace : WordTrace (prefixWord ++ tailWord_2533171) baseStart_2533171 baseEnd_2533171 := by
    simpa [prefixWord, tailWord_2533171, baseEnd_2533171] using wordTrace_append hprefix tailTrace_2533171
  have hstable : (prefixWord ++ tailWord_2533171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533171).length < 2 ^ (prefixWord ++ tailWord_2533171).sum := by decide
  have hdescent : baseEnd_2533171 < baseStart_2533171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533190 : List Nat := [6, 1, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_2533190 : Nat := 118140960795 + 2533190 * 2 ^ 59
def prefixEnd_2533190 : Nat := 4983230072969 + 3 ^ 40 * 2533190 * 2
def baseEnd_2533190 : Nat := 867162706108699410783385

theorem tailTrace_2533190 : CollatzResearch.WordTrace tailWord_2533190 prefixEnd_2533190 867162706108699410783385 := by
  unfold tailWord_2533190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2887282177896648101666407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 61595353128461826168883349 2887282177896648101666407)
  ·
    refine ⟨4330923266844972152499611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2887282177896648101666407 4330923266844972152499611)
    ·
      refine ⟨6496384900267458228749417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4330923266844972152499611 6496384900267458228749417)
      ·
        refine ⟨4872288675200593671562063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6496384900267458228749417 4872288675200593671562063)
        ·
          refine ⟨7308433012800890507343095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4872288675200593671562063 7308433012800890507343095)
          ·
            refine ⟨10962649519201335761014643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7308433012800890507343095 10962649519201335761014643)
            ·
              refine ⟨16443974278802003641521965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10962649519201335761014643 16443974278802003641521965)
              ·
                refine ⟨6166490354550751365570737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16443974278802003641521965 6166490354550751365570737)
                ·
                  refine ⟨4624867765913063524178053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6166490354550751365570737 4624867765913063524178053)
                  ·
                    refine ⟨867162706108699410783385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4624867765913063524178053 867162706108699410783385)
                    ·
                      rfl

theorem cell22_2533190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_2533190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2533190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2533190 prefixEnd_2533190 := by exact prefixLift 2533190
  have htrace : WordTrace (prefixWord ++ tailWord_2533190) baseStart_2533190 baseEnd_2533190 := by
    simpa [prefixWord, tailWord_2533190, baseEnd_2533190] using wordTrace_append hprefix tailTrace_2533190
  have hstable : (prefixWord ++ tailWord_2533190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533190).length < 2 ^ (prefixWord ++ tailWord_2533190).sum := by decide
  have hdescent : baseEnd_2533190 < baseStart_2533190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533216 : List Nat := [2, 1, 1, 3, 3, 2, 1, 4, 5]
def baseStart_2533216 : Nat := 118140960795 + 2533216 * 2 ^ 59
def prefixEnd_2533216 : Nat := 4983230072969 + 3 ^ 40 * 2533216 * 2
def baseEnd_2533216 : Nat := 289057202146681336544435

theorem tailTrace_2533216 : CollatzResearch.WordTrace tailWord_2533216 prefixEnd_2533216 289057202146681336544435 := by
  unfold tailWord_2533216
  simp only [CollatzResearch.WordTrace]
  refine ⟨46196988995299272846885751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61595985327065697129181001 46196988995299272846885751)
  ·
    refine ⟨69295483492948909270328627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46196988995299272846885751 69295483492948909270328627)
    ·
      refine ⟨103943225239423363905492941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69295483492948909270328627 103943225239423363905492941)
      ·
        refine ⟨38978709464783761464559853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103943225239423363905492941 38978709464783761464559853)
        ·
          refine ⟨14617016049293910549209945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38978709464783761464559853 14617016049293910549209945)
          ·
            refine ⟨10962762036970432911907459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14617016049293910549209945 10962762036970432911907459)
            ·
              refine ⟨16444143055455649367861189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10962762036970432911907459 16444143055455649367861189)
              ·
                refine ⟨3083276822897934256473973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16444143055455649367861189 3083276822897934256473973)
                ·
                  refine ⟨289057202146681336544435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3083276822897934256473973 289057202146681336544435)
                  ·
                    rfl

theorem cell22_2533216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 5].length) (baseStart_2533216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2533216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2533216 prefixEnd_2533216 := by exact prefixLift 2533216
  have htrace : WordTrace (prefixWord ++ tailWord_2533216) baseStart_2533216 baseEnd_2533216 := by
    simpa [prefixWord, tailWord_2533216, baseEnd_2533216] using wordTrace_append hprefix tailTrace_2533216
  have hstable : (prefixWord ++ tailWord_2533216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533216).length < 2 ^ (prefixWord ++ tailWord_2533216).sum := by decide
  have hdescent : baseEnd_2533216 < baseStart_2533216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533336 : List Nat := [2, 1, 2, 2, 2, 2, 2, 1, 2, 6]
def baseStart_2533336 : Nat := 118140960795 + 2533336 * 2 ^ 59
def prefixEnd_2533336 : Nat := 4983230072969 + 3 ^ 40 * 2533336 * 2
def baseEnd_2533336 : Nat := 867212684892403696632937

theorem tailTrace_2533336 : CollatzResearch.WordTrace tailWord_2533336 prefixEnd_2533336 867212684892403696632937 := by
  unfold tailWord_2533336
  simp only [CollatzResearch.WordTrace]
  refine ⟨46199177375081903094069931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61598903166775870792093241 46199177375081903094069931)
  ·
    refine ⟨69298766062622854641104897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46199177375081903094069931 69298766062622854641104897)
    ·
      refine ⟨51974074546967140980828673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69298766062622854641104897 51974074546967140980828673)
      ·
        refine ⟨38980555910225355735621505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51974074546967140980828673 38980555910225355735621505)
        ·
          refine ⟨29235416932669016801716129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38980555910225355735621505 29235416932669016801716129)
          ·
            refine ⟨21926562699501762601287097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29235416932669016801716129 21926562699501762601287097)
            ·
              refine ⟨16444922024626321950965323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21926562699501762601287097 16444922024626321950965323)
              ·
                refine ⟨24667383036939482926447985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16444922024626321950965323 24667383036939482926447985)
                ·
                  refine ⟨18500537277704612194835989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24667383036939482926447985 18500537277704612194835989)
                  ·
                    refine ⟨867212684892403696632937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18500537277704612194835989 867212684892403696632937)
                    ·
                      rfl

theorem cell22_2533336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_2533336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2533336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2533336 prefixEnd_2533336 := by exact prefixLift 2533336
  have htrace : WordTrace (prefixWord ++ tailWord_2533336) baseStart_2533336 baseEnd_2533336 := by
    simpa [prefixWord, tailWord_2533336, baseEnd_2533336] using wordTrace_append hprefix tailTrace_2533336
  have hstable : (prefixWord ++ tailWord_2533336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533336).length < 2 ^ (prefixWord ++ tailWord_2533336).sum := by decide
  have hdescent : baseEnd_2533336 < baseStart_2533336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533413 : List Nat := [1, 3, 1, 2, 2, 4, 1, 2, 6]
def baseStart_2533413 : Nat := 118140960795 + 2533413 * 2 ^ 59
def prefixEnd_2533413 : Nat := 4983230072969 + 3 ^ 40 * 2533413 * 2
def baseEnd_2533413 : Nat := 289079681188667054152567

theorem tailTrace_2533413 : CollatzResearch.WordTrace tailWord_2533413 prefixEnd_2533413 289079681188667054152567 := by
  unfold tailWord_2533413
  simp only [CollatzResearch.WordTrace]
  refine ⟨92401163170884848338692893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61600775447256565559128595 92401163170884848338692893)
  ·
    refine ⟨34650436189081818127009835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92401163170884848338692893 34650436189081818127009835)
    ·
      refine ⟨51975654283622727190514753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34650436189081818127009835 51975654283622727190514753)
      ·
        refine ⟨38981740712717045392886065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51975654283622727190514753 38981740712717045392886065)
        ·
          refine ⟨29236305534537784044664549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38981740712717045392886065 29236305534537784044664549)
          ·
            refine ⟨5481807287725834508374603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29236305534537784044664549 5481807287725834508374603)
            ·
              refine ⟨8222710931588751762561905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5481807287725834508374603 8222710931588751762561905)
              ·
                refine ⟨6167033198691563821921429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8222710931588751762561905 6167033198691563821921429)
                ·
                  refine ⟨289079681188667054152567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6167033198691563821921429 289079681188667054152567)
                  ·
                    rfl

theorem cell22_2533413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 6].length) (baseStart_2533413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2533413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2533413 prefixEnd_2533413 := by exact prefixLift 2533413
  have htrace : WordTrace (prefixWord ++ tailWord_2533413) baseStart_2533413 baseEnd_2533413 := by
    simpa [prefixWord, tailWord_2533413, baseEnd_2533413] using wordTrace_append hprefix tailTrace_2533413
  have hstable : (prefixWord ++ tailWord_2533413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533413).length < 2 ^ (prefixWord ++ tailWord_2533413).sum := by decide
  have hdescent : baseEnd_2533413 < baseStart_2533413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533507 : List Nat := [1, 1, 1, 3, 3, 5, 1, 1, 3, 3]
def baseStart_2533507 : Nat := 118140960795 + 2533507 * 2 ^ 59
def prefixEnd_2533507 : Nat := 4983230072969 + 3 ^ 40 * 2533507 * 2
def baseEnd_2533507 : Nat := 867271221687016250607413

theorem tailTrace_2533507 : CollatzResearch.WordTrace tailWord_2533507 prefixEnd_2533507 867271221687016250607413 := by
  unfold tailWord_2533507
  simp only [CollatzResearch.WordTrace]
  refine ⟨92404591632544302392614775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61603061088362868261743183 92404591632544302392614775)
  ·
    refine ⟨138606887448816453588922163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92404591632544302392614775 138606887448816453588922163)
    ·
      refine ⟨207910331173224680383383245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138606887448816453588922163 207910331173224680383383245)
      ·
        refine ⟨77966374189959255143768717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 207910331173224680383383245 77966374189959255143768717)
        ·
          refine ⟨29237390321234720678913269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77966374189959255143768717 29237390321234720678913269)
          ·
            refine ⟨2741005342615755063648119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29237390321234720678913269 2741005342615755063648119)
            ·
              refine ⟨4111508013923632595472179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2741005342615755063648119 4111508013923632595472179)
              ·
                refine ⟨6167262020885448893208269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4111508013923632595472179 6167262020885448893208269)
                ·
                  refine ⟨2312723257832043334953101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6167262020885448893208269 2312723257832043334953101)
                  ·
                    refine ⟨867271221687016250607413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2312723257832043334953101 867271221687016250607413)
                    ·
                      rfl

theorem cell22_2533507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 3, 3].length) (baseStart_2533507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2533507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2533507 prefixEnd_2533507 := by exact prefixLift 2533507
  have htrace : WordTrace (prefixWord ++ tailWord_2533507) baseStart_2533507 baseEnd_2533507 := by
    simpa [prefixWord, tailWord_2533507, baseEnd_2533507] using wordTrace_append hprefix tailTrace_2533507
  have hstable : (prefixWord ++ tailWord_2533507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533507).length < 2 ^ (prefixWord ++ tailWord_2533507).sum := by decide
  have hdescent : baseEnd_2533507 < baseStart_2533507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533563 : List Nat := [1, 1, 1, 1, 1, 2, 5, 2, 3, 5]
def baseStart_2533563 : Nat := 118140960795 + 2533563 * 2 ^ 59
def prefixEnd_2533563 : Nat := 4983230072969 + 3 ^ 40 * 2533563 * 2
def baseEnd_2533563 : Nat := 867290391631450771207241

theorem tailTrace_2533563 : CollatzResearch.WordTrace tailWord_2533563 prefixEnd_2533563 867290391631450771207241 := by
  unfold tailWord_2533563
  simp only [CollatzResearch.WordTrace]
  refine ⟨92406634120341423956653343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61604422746894282637768895 92406634120341423956653343)
  ·
    refine ⟨138609951180512135934980015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92406634120341423956653343 138609951180512135934980015)
    ·
      refine ⟨207914926770768203902470023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138609951180512135934980015 207914926770768203902470023)
      ·
        refine ⟨311872390156152305853705035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207914926770768203902470023 311872390156152305853705035)
        ·
          refine ⟨467808585234228458780557553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311872390156152305853705035 467808585234228458780557553)
          ·
            refine ⟨350856438925671344085418165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 467808585234228458780557553 350856438925671344085418165)
            ·
              refine ⟨32892791149281688508007953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 350856438925671344085418165 32892791149281688508007953)
              ·
                refine ⟨24669593361961266381005965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32892791149281688508007953 24669593361961266381005965)
                ·
                  refine ⟨9251097510735474892877237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24669593361961266381005965 9251097510735474892877237)
                  ·
                    refine ⟨867290391631450771207241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9251097510735474892877237 867290391631450771207241)
                    ·
                      rfl

theorem cell22_2533563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 5].length) (baseStart_2533563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2533563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2533563 prefixEnd_2533563 := by exact prefixLift 2533563
  have htrace : WordTrace (prefixWord ++ tailWord_2533563) baseStart_2533563 baseEnd_2533563 := by
    simpa [prefixWord, tailWord_2533563, baseEnd_2533563] using wordTrace_append hprefix tailTrace_2533563
  have hstable : (prefixWord ++ tailWord_2533563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533563).length < 2 ^ (prefixWord ++ tailWord_2533563).sum := by decide
  have hdescent : baseEnd_2533563 < baseStart_2533563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533593 : List Nat := [1, 2, 1, 2, 3, 1, 2, 10]
def baseStart_2533593 : Nat := 118140960795 + 2533593 * 2 ^ 59
def prefixEnd_2533593 : Nat := 4983230072969 + 3 ^ 40 * 2533593 * 2
def baseEnd_2533593 : Nat := 96366740138282299217461

theorem tailTrace_2533593 : CollatzResearch.WordTrace tailWord_2533593 prefixEnd_2533593 96366740138282299217461 := by
  unfold tailWord_2533593
  simp only [CollatzResearch.WordTrace]
  refine ⟨92407728310232739080245433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61605152206821826053496955 92407728310232739080245433)
  ·
    refine ⟨69305796232674554310184075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92407728310232739080245433 69305796232674554310184075)
    ·
      refine ⟨103958694349011831465276113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69305796232674554310184075 103958694349011831465276113)
      ·
        refine ⟨77969020761758873598957085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103958694349011831465276113 77969020761758873598957085)
        ·
          refine ⟨29238382785659577599608907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77969020761758873598957085 29238382785659577599608907)
          ·
            refine ⟨43857574178489366399413361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29238382785659577599608907 43857574178489366399413361)
            ·
              refine ⟨32893180633867024799560021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43857574178489366399413361 32893180633867024799560021)
              ·
                refine ⟨96366740138282299217461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32893180633867024799560021 96366740138282299217461)
                ·
                  rfl

theorem cell22_2533593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 10].length) (baseStart_2533593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2533593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2533593 prefixEnd_2533593 := by exact prefixLift 2533593
  have htrace : WordTrace (prefixWord ++ tailWord_2533593) baseStart_2533593 baseEnd_2533593 := by
    simpa [prefixWord, tailWord_2533593, baseEnd_2533593] using wordTrace_append hprefix tailTrace_2533593
  have hstable : (prefixWord ++ tailWord_2533593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533593).length < 2 ^ (prefixWord ++ tailWord_2533593).sum := by decide
  have hdescent : baseEnd_2533593 < baseStart_2533593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533597 : List Nat := [1, 4, 3, 2, 1, 1, 2, 2, 1, 5]
def baseStart_2533597 : Nat := 118140960795 + 2533597 * 2 ^ 59
def prefixEnd_2533597 : Nat := 4983230072969 + 3 ^ 40 * 2533597 * 2
def baseEnd_2533597 : Nat := 867302030526286015857137

theorem tailTrace_2533597 : CollatzResearch.WordTrace tailWord_2533597 prefixEnd_2533597 867302030526286015857137 := by
  unfold tailWord_2533597
  simp only [CollatzResearch.WordTrace]
  refine ⟨92407874202218247763391045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61605249468145498508927363 92407874202218247763391045)
  ·
    refine ⟨17326476412915921455635821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92407874202218247763391045 17326476412915921455635821)
    ·
      refine ⟨6497428654843470545863433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17326476412915921455635821 6497428654843470545863433)
      ·
        refine ⟨4873071491132602909397575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6497428654843470545863433 4873071491132602909397575)
        ·
          refine ⟨7309607236698904364096363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4873071491132602909397575 7309607236698904364096363)
          ·
            refine ⟨10964410855048356546144545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7309607236698904364096363 10964410855048356546144545)
            ·
              refine ⟨8223308141286267409608409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10964410855048356546144545 8223308141286267409608409)
              ·
                refine ⟨6167481105964700557206307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8223308141286267409608409 6167481105964700557206307)
                ·
                  refine ⟨9251221658947050835809461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6167481105964700557206307 9251221658947050835809461)
                  ·
                    refine ⟨867302030526286015857137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9251221658947050835809461 867302030526286015857137)
                    ·
                      rfl

theorem cell22_2533597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_2533597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2533597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2533597 prefixEnd_2533597 := by exact prefixLift 2533597
  have htrace : WordTrace (prefixWord ++ tailWord_2533597) baseStart_2533597 baseEnd_2533597 := by
    simpa [prefixWord, tailWord_2533597, baseEnd_2533597] using wordTrace_append hprefix tailTrace_2533597
  have hstable : (prefixWord ++ tailWord_2533597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533597).length < 2 ^ (prefixWord ++ tailWord_2533597).sum := by decide
  have hdescent : baseEnd_2533597 < baseStart_2533597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533642 : List Nat := [3, 1, 2, 2, 1, 1, 4, 2, 3, 3]
def baseStart_2533642 : Nat := 118140960795 + 2533642 * 2 ^ 59
def prefixEnd_2533642 : Nat := 4983230072969 + 3 ^ 40 * 2533642 * 2
def baseEnd_2533642 : Nat := 867317434945920898481999

theorem tailTrace_2533642 : CollatzResearch.WordTrace tailWord_2533642 prefixEnd_2533642 867317434945920898481999 := by
  unfold tailWord_2533642
  simp only [CollatzResearch.WordTrace]
  refine ⟨23102378871763805112194795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61606343658036813632519453 23102378871763805112194795)
  ·
    refine ⟨34653568307645707668292193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23102378871763805112194795 34653568307645707668292193)
    ·
      refine ⟨25990176230734280751219145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34653568307645707668292193 25990176230734280751219145)
      ·
        refine ⟨19492632173050710563414359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25990176230734280751219145 19492632173050710563414359)
        ·
          refine ⟨29238948259576065845121539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19492632173050710563414359 29238948259576065845121539)
          ·
            refine ⟨43858422389364098767682309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29238948259576065845121539 43858422389364098767682309)
            ·
              refine ⟨8223454198005768518940433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43858422389364098767682309 8223454198005768518940433)
              ·
                refine ⟨6167590648504326389205325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8223454198005768518940433 6167590648504326389205325)
                ·
                  refine ⟨2312846493189122395951997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6167590648504326389205325 2312846493189122395951997)
                  ·
                    refine ⟨867317434945920898481999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2312846493189122395951997 867317434945920898481999)
                    ·
                      rfl

theorem cell22_2533642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_2533642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2533642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2533642 prefixEnd_2533642 := by exact prefixLift 2533642
  have htrace : WordTrace (prefixWord ++ tailWord_2533642) baseStart_2533642 baseEnd_2533642 := by
    simpa [prefixWord, tailWord_2533642, baseEnd_2533642] using wordTrace_append hprefix tailTrace_2533642
  have hstable : (prefixWord ++ tailWord_2533642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533642).length < 2 ^ (prefixWord ++ tailWord_2533642).sum := by decide
  have hdescent : baseEnd_2533642 < baseStart_2533642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533655 : List Nat := [1, 1, 3, 4, 1, 2, 1, 2, 7]
def baseStart_2533655 : Nat := 118140960795 + 2533655 * 2 ^ 59
def prefixEnd_2533655 : Nat := 4983230072969 + 3 ^ 40 * 2533655 * 2
def baseEnd_2533655 : Nat := 289107295037197732635653

theorem tailTrace_2533655 : CollatzResearch.WordTrace tailWord_2533655 prefixEnd_2533655 289107295037197732635653 := by
  unfold tailWord_2533655
  simp only [CollatzResearch.WordTrace]
  refine ⟨92409989636008123669002419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61606659757338749112668279 92409989636008123669002419)
  ·
    refine ⟨138614984454012185503503629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92409989636008123669002419 138614984454012185503503629)
    ·
      refine ⟨51980619170254569563813861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138614984454012185503503629 51980619170254569563813861)
      ·
        refine ⟨9746366094422731793215099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51980619170254569563813861 9746366094422731793215099)
        ·
          refine ⟨14619549141634097689822649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9746366094422731793215099 14619549141634097689822649)
          ·
            refine ⟨10964661856225573267366987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14619549141634097689822649 10964661856225573267366987)
            ·
              refine ⟨16446992784338359901050481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10964661856225573267366987 16446992784338359901050481)
              ·
                refine ⟨12335244588253769925787861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16446992784338359901050481 12335244588253769925787861)
                ·
                  refine ⟨289107295037197732635653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12335244588253769925787861 289107295037197732635653)
                  ·
                    rfl

theorem cell22_2533655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 7].length) (baseStart_2533655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2533655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2533655 prefixEnd_2533655 := by exact prefixLift 2533655
  have htrace : WordTrace (prefixWord ++ tailWord_2533655) baseStart_2533655 baseEnd_2533655 := by
    simpa [prefixWord, tailWord_2533655, baseEnd_2533655] using wordTrace_append hprefix tailTrace_2533655
  have hstable : (prefixWord ++ tailWord_2533655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533655).length < 2 ^ (prefixWord ++ tailWord_2533655).sum := by decide
  have hdescent : baseEnd_2533655 < baseStart_2533655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533659 : List Nat := [1, 1, 1, 1, 1, 1, 9, 3, 1, 3]
def baseStart_2533659 : Nat := 118140960795 + 2533659 * 2 ^ 59
def prefixEnd_2533659 : Nat := 4983230072969 + 3 ^ 40 * 2533659 * 2
def baseEnd_2533659 : Nat := 867323254393338520806947

theorem tailTrace_2533659 : CollatzResearch.WordTrace tailWord_2533659 prefixEnd_2533659 867323254393338520806947 := by
  unfold tailWord_2533659
  simp only [CollatzResearch.WordTrace]
  refine ⟨92410135527993632352148031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61606757018662421568098687 92410135527993632352148031)
  ·
    refine ⟨138615203291990448528222047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92410135527993632352148031 138615203291990448528222047)
    ·
      refine ⟨207922804937985672792333071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138615203291990448528222047 207922804937985672792333071)
      ·
        refine ⟨311884207406978509188499607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207922804937985672792333071 311884207406978509188499607)
        ·
          refine ⟨467826311110467763782749411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311884207406978509188499607 467826311110467763782749411)
          ·
            refine ⟨701739466665701645674124117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 467826311110467763782749411 701739466665701645674124117)
            ·
              refine ⟨4111754687494345580121821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 701739466665701645674124117 4111754687494345580121821)
              ·
                refine ⟨1541908007810379592545683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4111754687494345580121821 1541908007810379592545683)
                ·
                  refine ⟨2312862011715569388818525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1541908007810379592545683 2312862011715569388818525)
                  ·
                    refine ⟨867323254393338520806947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2312862011715569388818525 867323254393338520806947)
                    ·
                      rfl

theorem cell22_2533659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 3, 1, 3].length) (baseStart_2533659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2533659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2533659 prefixEnd_2533659 := by exact prefixLift 2533659
  have htrace : WordTrace (prefixWord ++ tailWord_2533659) baseStart_2533659 baseEnd_2533659 := by
    simpa [prefixWord, tailWord_2533659, baseEnd_2533659] using wordTrace_append hprefix tailTrace_2533659
  have hstable : (prefixWord ++ tailWord_2533659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533659).length < 2 ^ (prefixWord ++ tailWord_2533659).sum := by decide
  have hdescent : baseEnd_2533659 < baseStart_2533659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533689 : List Nat := [1, 2, 1, 6, 1, 1, 4, 1, 5]
def baseStart_2533689 : Nat := 118140960795 + 2533689 * 2 ^ 59
def prefixEnd_2533689 : Nat := 4983230072969 + 3 ^ 40 * 2533689 * 2
def baseEnd_2533689 : Nat := 289111174668809480852285

theorem tailTrace_2533689 : CollatzResearch.WordTrace tailWord_2533689 prefixEnd_2533689 289111174668809480852285 := by
  unfold tailWord_2533689
  simp only [CollatzResearch.WordTrace]
  refine ⟨92411229717884947475740121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61607486478589964983826747 92411229717884947475740121)
  ·
    refine ⟨69308422288413710606805091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92411229717884947475740121 69308422288413710606805091)
    ·
      refine ⟨103962633432620565910207637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69308422288413710606805091 103962633432620565910207637)
      ·
        refine ⟨4873248442154089027040983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 103962633432620565910207637 4873248442154089027040983)
        ·
          refine ⟨7309872663231133540561475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4873248442154089027040983 7309872663231133540561475)
          ·
            refine ⟨10964808994846700310842213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7309872663231133540561475 10964808994846700310842213)
            ·
              refine ⟨2055901686533756308282915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10964808994846700310842213 2055901686533756308282915)
              ·
                refine ⟨3083852529800634462424373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2055901686533756308282915 3083852529800634462424373)
                ·
                  refine ⟨289111174668809480852285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3083852529800634462424373 289111174668809480852285)
                  ·
                    rfl

theorem cell22_2533689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 5].length) (baseStart_2533689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2533689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2533689 prefixEnd_2533689 := by exact prefixLift 2533689
  have htrace : WordTrace (prefixWord ++ tailWord_2533689) baseStart_2533689 baseEnd_2533689 := by
    simpa [prefixWord, tailWord_2533689, baseEnd_2533689] using wordTrace_append hprefix tailTrace_2533689
  have hstable : (prefixWord ++ tailWord_2533689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533689).length < 2 ^ (prefixWord ++ tailWord_2533689).sum := by decide
  have hdescent : baseEnd_2533689 < baseStart_2533689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533719 : List Nat := [1, 1, 3, 2, 3, 1, 5, 1, 1, 4]
def baseStart_2533719 : Nat := 118140960795 + 2533719 * 2 ^ 59
def prefixEnd_2533719 : Nat := 4983230072969 + 3 ^ 40 * 2533719 * 2
def baseEnd_2533719 : Nat := 867343793619518364306763

theorem tailTrace_2533719 : CollatzResearch.WordTrace tailWord_2533719 prefixEnd_2533719 867343793619518364306763 := by
  unfold tailWord_2533719
  simp only [CollatzResearch.WordTrace]
  refine ⟨92412323907776262599332211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61608215938517508399554807 92412323907776262599332211)
  ·
    refine ⟨138618485861664393898998317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92412323907776262599332211 138618485861664393898998317)
    ·
      refine ⟨51981932198124147712124369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138618485861664393898998317 51981932198124147712124369)
      ·
        refine ⟨38986449148593110784093277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51981932198124147712124369 38986449148593110784093277)
        ·
          refine ⟨14619918430722416544034979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38986449148593110784093277 14619918430722416544034979)
          ·
            refine ⟨21929877646083624816052469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14619918430722416544034979 21929877646083624816052469)
            ·
              refine ⟨2055926029320339826504919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21929877646083624816052469 2055926029320339826504919)
              ·
                refine ⟨3083889043980509739757379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2055926029320339826504919 3083889043980509739757379)
                ·
                  refine ⟨4625833565970764609636069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3083889043980509739757379 4625833565970764609636069)
                  ·
                    refine ⟨867343793619518364306763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4625833565970764609636069 867343793619518364306763)
                    ·
                      rfl

theorem cell22_2533719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 1, 4].length) (baseStart_2533719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2533719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2533719 prefixEnd_2533719 := by exact prefixLift 2533719
  have htrace : WordTrace (prefixWord ++ tailWord_2533719) baseStart_2533719 baseEnd_2533719 := by
    simpa [prefixWord, tailWord_2533719, baseEnd_2533719] using wordTrace_append hprefix tailTrace_2533719
  have hstable : (prefixWord ++ tailWord_2533719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533719).length < 2 ^ (prefixWord ++ tailWord_2533719).sum := by decide
  have hdescent : baseEnd_2533719 < baseStart_2533719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533749 : List Nat := [1, 3, 4, 1, 2, 2, 2, 1, 1, 5]
def baseStart_2533749 : Nat := 118140960795 + 2533749 * 2 ^ 59
def prefixEnd_2533749 : Nat := 4983230072969 + 3 ^ 40 * 2533749 * 2
def baseEnd_2533749 : Nat := 867354063232608286056671

theorem tailTrace_2533749 : CollatzResearch.WordTrace tailWord_2533749 prefixEnd_2533749 867354063232608286056671 := by
  unfold tailWord_2533749
  simp only [CollatzResearch.WordTrace]
  refine ⟨92413418097667577722924301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61608945398445051815282867 92413418097667577722924301)
  ·
    refine ⟨34655031786625341646096613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92413418097667577722924301 34655031786625341646096613)
    ·
      refine ⟨6497818459992251558643115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34655031786625341646096613 6497818459992251558643115)
      ·
        refine ⟨9746727689988377337964673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6497818459992251558643115 9746727689988377337964673)
        ·
          refine ⟨7310045767491283003473505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9746727689988377337964673 7310045767491283003473505)
          ·
            refine ⟨5482534325618462252605129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7310045767491283003473505 5482534325618462252605129)
            ·
              refine ⟨4111900744213846689453847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5482534325618462252605129 4111900744213846689453847)
              ·
                refine ⟨6167851116320770034180771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4111900744213846689453847 6167851116320770034180771)
                ·
                  refine ⟨9251776674481155051271157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6167851116320770034180771 9251776674481155051271157)
                  ·
                    refine ⟨867354063232608286056671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9251776674481155051271157 867354063232608286056671)
                    ·
                      rfl

theorem cell22_2533749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_2533749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2533749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2533749 prefixEnd_2533749 := by exact prefixLift 2533749
  have htrace : WordTrace (prefixWord ++ tailWord_2533749) baseStart_2533749 baseEnd_2533749 := by
    simpa [prefixWord, tailWord_2533749, baseEnd_2533749] using wordTrace_append hprefix tailTrace_2533749
  have hstable : (prefixWord ++ tailWord_2533749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533749).length < 2 ^ (prefixWord ++ tailWord_2533749).sum := by decide
  have hdescent : baseEnd_2533749 < baseStart_2533749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533770 : List Nat := [3, 1, 2, 5, 2, 1, 2, 1, 1, 4]
def baseStart_2533770 : Nat := 118140960795 + 2533770 * 2 ^ 59
def prefixEnd_2533770 : Nat := 4983230072969 + 3 ^ 40 * 2533770 * 2
def baseEnd_2533770 : Nat := 867361251961771231281607

theorem tailTrace_2533770 : CollatzResearch.WordTrace tailWord_2533770 prefixEnd_2533770 867361251961771231281607 := by
  unfold tailWord_2533770
  simp only [CollatzResearch.WordTrace]
  refine ⟨23103546007647874577359691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61609456020394332206292509 23103546007647874577359691)
  ·
    refine ⟨34655319011471811866039537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23103546007647874577359691 34655319011471811866039537)
    ·
      refine ⟨25991489258603858899529653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34655319011471811866039537 25991489258603858899529653)
      ·
        refine ⟨2436702117994111771830905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25991489258603858899529653 2436702117994111771830905)
        ·
          refine ⟨1827526588495583828873179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2436702117994111771830905 1827526588495583828873179)
          ·
            refine ⟨2741289882743375743309769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1827526588495583828873179 2741289882743375743309769)
            ·
              refine ⟨2055967412057531807482327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2741289882743375743309769 2055967412057531807482327)
              ·
                refine ⟨3083951118086297711223491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2055967412057531807482327 3083951118086297711223491)
                ·
                  refine ⟨4625926677129446566835237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3083951118086297711223491 4625926677129446566835237)
                  ·
                    refine ⟨867361251961771231281607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4625926677129446566835237 867361251961771231281607)
                    ·
                      rfl

theorem cell22_2533770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 1, 4].length) (baseStart_2533770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2533770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2533770 prefixEnd_2533770 := by exact prefixLift 2533770
  have htrace : WordTrace (prefixWord ++ tailWord_2533770) baseStart_2533770 baseEnd_2533770 := by
    simpa [prefixWord, tailWord_2533770, baseEnd_2533770] using wordTrace_append hprefix tailTrace_2533770
  have hstable : (prefixWord ++ tailWord_2533770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533770).length < 2 ^ (prefixWord ++ tailWord_2533770).sum := by decide
  have hdescent : baseEnd_2533770 < baseStart_2533770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533822 : List Nat := [4, 2, 1, 1, 1, 1, 2, 2, 1, 7]
def baseStart_2533822 : Nat := 118140960795 + 2533822 * 2 ^ 59
def prefixEnd_2533822 : Nat := 4983230072969 + 3 ^ 40 * 2533822 * 2
def baseEnd_2533822 : Nat := 867379052624460428981447

theorem tailTrace_2533822 : CollatzResearch.WordTrace tailWord_2533822 prefixEnd_2533822 867379052624460428981447 := by
  unfold tailWord_2533822
  simp only [CollatzResearch.WordTrace]
  refine ⟨11552010078300388898791465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61610720417602074126887813 11552010078300388898791465)
  ·
    refine ⟨8664007558725291674093599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11552010078300388898791465 8664007558725291674093599)
    ·
      refine ⟨12996011338087937511140399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8664007558725291674093599 12996011338087937511140399)
      ·
        refine ⟨19494017007131906266710599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12996011338087937511140399 19494017007131906266710599)
        ·
          refine ⟨29241025510697859400065899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19494017007131906266710599 29241025510697859400065899)
          ·
            refine ⟨43861538266046789100098849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29241025510697859400065899 43861538266046789100098849)
            ·
              refine ⟨32896153699535091825074137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43861538266046789100098849 32896153699535091825074137)
              ·
                refine ⟨24672115274651318868805603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32896153699535091825074137 24672115274651318868805603)
                ·
                  refine ⟨37008172911976978303208405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24672115274651318868805603 37008172911976978303208405)
                  ·
                    refine ⟨867379052624460428981447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37008172911976978303208405 867379052624460428981447)
                    ·
                      rfl

theorem cell22_2533822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_2533822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2533822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2533822 prefixEnd_2533822 := by exact prefixLift 2533822
  have htrace : WordTrace (prefixWord ++ tailWord_2533822) baseStart_2533822 baseEnd_2533822 := by
    simpa [prefixWord, tailWord_2533822, baseEnd_2533822] using wordTrace_append hprefix tailTrace_2533822
  have hstable : (prefixWord ++ tailWord_2533822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533822).length < 2 ^ (prefixWord ++ tailWord_2533822).sum := by decide
  have hdescent : baseEnd_2533822 < baseStart_2533822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533858 : List Nat := [3, 3, 3, 2, 1, 1, 1, 3, 5]
def baseStart_2533858 : Nat := 118140960795 + 2533858 * 2 ^ 59
def prefixEnd_2533858 : Nat := 4983230072969 + 3 ^ 40 * 2533858 * 2
def baseEnd_2533858 : Nat := 289130458720056111693779

theorem tailTrace_2533858 : CollatzResearch.WordTrace tailWord_2533858 prefixEnd_2533858 289130458720056111693779 := by
  unfold tailWord_2533858
  simp only [CollatzResearch.WordTrace]
  refine ⟨23104348413568172334660557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61611595769515126225761485 23104348413568172334660557)
  ·
    refine ⟨8664130655088064625497709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23104348413568172334660557 8664130655088064625497709)
    ·
      refine ⟨3249048995658024234561641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8664130655088064625497709 3249048995658024234561641)
      ·
        refine ⟨2436786746743518175921231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3249048995658024234561641 2436786746743518175921231)
        ·
          refine ⟨3655180120115277263881847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2436786746743518175921231 3655180120115277263881847)
          ·
            refine ⟨5482770180172915895822771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3655180120115277263881847 5482770180172915895822771)
            ·
              refine ⟨8224155270259373843734157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5482770180172915895822771 8224155270259373843734157)
              ·
                refine ⟨3084058226347265191400309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8224155270259373843734157 3084058226347265191400309)
                ·
                  refine ⟨289130458720056111693779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3084058226347265191400309 289130458720056111693779)
                  ·
                    rfl

theorem cell22_2533858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_2533858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2533858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2533858 prefixEnd_2533858 := by exact prefixLift 2533858
  have htrace : WordTrace (prefixWord ++ tailWord_2533858) baseStart_2533858 baseEnd_2533858 := by
    simpa [prefixWord, tailWord_2533858, baseEnd_2533858] using wordTrace_append hprefix tailTrace_2533858
  have hstable : (prefixWord ++ tailWord_2533858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533858).length < 2 ^ (prefixWord ++ tailWord_2533858).sum := by decide
  have hdescent : baseEnd_2533858 < baseStart_2533858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533867 : List Nat := [1, 1, 1, 1, 2, 3, 4, 3, 1, 5]
def baseStart_2533867 : Nat := 118140960795 + 2533867 * 2 ^ 59
def prefixEnd_2533867 : Nat := 4983230072969 + 3 ^ 40 * 2533867 * 2
def baseEnd_2533867 : Nat := 867394457044095311606309

theorem tailTrace_2533867 : CollatzResearch.WordTrace tailWord_2533867 prefixEnd_2533867 867394457044095311606309 := by
  unfold tailWord_2533867
  simp only [CollatzResearch.WordTrace]
  refine ⟨92417721911240083875719855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61611814607493389250479903 92417721911240083875719855)
  ·
    refine ⟨138626582866860125813579783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92417721911240083875719855 138626582866860125813579783)
    ·
      refine ⟨207939874300290188720369675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138626582866860125813579783 207939874300290188720369675)
      ·
        refine ⟨311909811450435283080554513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207939874300290188720369675 311909811450435283080554513)
        ·
          refine ⟨233932358587826462310415885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 311909811450435283080554513 233932358587826462310415885)
          ·
            refine ⟨87724634470434923366405957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 233932358587826462310415885 87724634470434923366405957)
            ·
              refine ⟨16448368963206548131201117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87724634470434923366405957 16448368963206548131201117)
              ·
                refine ⟨6168138361202455549200419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16448368963206548131201117 6168138361202455549200419)
                ·
                  refine ⟨9252207541803683323800629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6168138361202455549200419 9252207541803683323800629)
                  ·
                    refine ⟨867394457044095311606309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9252207541803683323800629 867394457044095311606309)
                    ·
                      rfl

theorem cell22_2533867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 5].length) (baseStart_2533867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2533867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2533867 prefixEnd_2533867 := by exact prefixLift 2533867
  have htrace : WordTrace (prefixWord ++ tailWord_2533867) baseStart_2533867 baseEnd_2533867 := by
    simpa [prefixWord, tailWord_2533867, baseEnd_2533867] using wordTrace_append hprefix tailTrace_2533867
  have hstable : (prefixWord ++ tailWord_2533867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533867).length < 2 ^ (prefixWord ++ tailWord_2533867).sum := by decide
  have hdescent : baseEnd_2533867 < baseStart_2533867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533899 : List Nat := [1, 1, 1, 1, 7, 1, 2, 2, 2, 4]
def baseStart_2533899 : Nat := 118140960795 + 2533899 * 2 ^ 59
def prefixEnd_2533899 : Nat := 4983230072969 + 3 ^ 40 * 2533899 * 2
def baseEnd_2533899 : Nat := 867405411298057894806211

theorem tailTrace_2533899 : CollatzResearch.WordTrace tailWord_2533899 prefixEnd_2533899 867405411298057894806211 := by
  unfold tailWord_2533899
  simp only [CollatzResearch.WordTrace]
  refine ⟨92418889047124153340884751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61612592698082768893923167 92418889047124153340884751)
  ·
    refine ⟨138628333570686230011327127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92418889047124153340884751 138628333570686230011327127)
    ·
      refine ⟨207942500356029345016990691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138628333570686230011327127 207942500356029345016990691)
      ·
        refine ⟨311913750534044017525486037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207942500356029345016990691 311913750534044017525486037)
        ·
          refine ⟨7310478528141656660753579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 311913750534044017525486037 7310478528141656660753579)
          ·
            refine ⟨10965717792212484991130369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7310478528141656660753579 10965717792212484991130369)
            ·
              refine ⟨8224288344159363743347777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10965717792212484991130369 8224288344159363743347777)
              ·
                refine ⟨6168216258119522807510833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8224288344159363743347777 6168216258119522807510833)
                ·
                  refine ⟨4626162193589642105633125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6168216258119522807510833 4626162193589642105633125)
                  ·
                    refine ⟨867405411298057894806211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4626162193589642105633125 867405411298057894806211)
                    ·
                      rfl

theorem cell22_2533899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 4].length) (baseStart_2533899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2533899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2533899 prefixEnd_2533899 := by exact prefixLift 2533899
  have htrace : WordTrace (prefixWord ++ tailWord_2533899) baseStart_2533899 baseEnd_2533899 := by
    simpa [prefixWord, tailWord_2533899, baseEnd_2533899] using wordTrace_append hprefix tailTrace_2533899
  have hstable : (prefixWord ++ tailWord_2533899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533899).length < 2 ^ (prefixWord ++ tailWord_2533899).sum := by decide
  have hdescent : baseEnd_2533899 < baseStart_2533899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533959 : List Nat := [1, 1, 4, 1, 4, 2, 1, 1, 7]
def baseStart_2533959 : Nat := 118140960795 + 2533959 * 2 ^ 59
def prefixEnd_2533959 : Nat := 4983230072969 + 3 ^ 40 * 2533959 * 2
def baseEnd_2533959 : Nat := 289141983508079246102009

theorem tailTrace_2533959 : CollatzResearch.WordTrace tailWord_2533959 prefixEnd_2533959 289141983508079246102009 := by
  unfold tailWord_2533959
  simp only [CollatzResearch.WordTrace]
  refine ⟨92421077426906783588068931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61614051617937855725379287 92421077426906783588068931)
  ·
    refine ⟨138631616140360175382103397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92421077426906783588068931 138631616140360175382103397)
    ·
      refine ⟨25993428026317532884144387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138631616140360175382103397 25993428026317532884144387)
      ·
        refine ⟨38990142039476299326216581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25993428026317532884144387 38990142039476299326216581)
        ·
          refine ⟨7310651632401806123665609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38990142039476299326216581 7310651632401806123665609)
          ·
            refine ⟨5482988724301354592749207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7310651632401806123665609 5482988724301354592749207)
            ·
              refine ⟨8224483086452031889123811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5482988724301354592749207 8224483086452031889123811)
              ·
                refine ⟨12336724629678047833685717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8224483086452031889123811 12336724629678047833685717)
                ·
                  refine ⟨289141983508079246102009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12336724629678047833685717 289141983508079246102009)
                  ·
                    rfl

theorem cell22_2533959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 7].length) (baseStart_2533959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2533959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2533959 prefixEnd_2533959 := by exact prefixLift 2533959
  have htrace : WordTrace (prefixWord ++ tailWord_2533959) baseStart_2533959 baseEnd_2533959 := by
    simpa [prefixWord, tailWord_2533959, baseEnd_2533959] using wordTrace_append hprefix tailTrace_2533959
  have hstable : (prefixWord ++ tailWord_2533959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533959).length < 2 ^ (prefixWord ++ tailWord_2533959).sum := by decide
  have hdescent : baseEnd_2533959 < baseStart_2533959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2533982 : List Nat := [4, 4, 1, 2, 1, 2, 2, 6]
def baseStart_2533982 : Nat := 118140960795 + 2533982 * 2 ^ 59
def prefixEnd_2533982 : Nat := 4983230072969 + 3 ^ 40 * 2533982 * 2
def baseEnd_2533982 : Nat := 96381535988252593886773

theorem tailTrace_2533982 : CollatzResearch.WordTrace tailWord_2533982 prefixEnd_2533982 96381535988252593886773 := by
  unfold tailWord_2533982
  simp only [CollatzResearch.WordTrace]
  refine ⟨11552739538227932314519525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61614610870548972344104133 11552739538227932314519525)
  ·
    refine ⟨2166138663417737308972411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11552739538227932314519525 2166138663417737308972411)
    ·
      refine ⟨3249207995126605963458617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2166138663417737308972411 3249207995126605963458617)
      ·
        refine ⟨2436905996344954472593963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3249207995126605963458617 2436905996344954472593963)
        ·
          refine ⟨3655358994517431708890945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2436905996344954472593963 3655358994517431708890945)
          ·
            refine ⟨2741519245888073781668209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3655358994517431708890945 2741519245888073781668209)
            ·
              refine ⟨2056139434416055336251157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2741519245888073781668209 2056139434416055336251157)
              ·
                refine ⟨96381535988252593886773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2056139434416055336251157 96381535988252593886773)
                ·
                  rfl

theorem cell22_2533982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 6].length) (baseStart_2533982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2533982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2533982 prefixEnd_2533982 := by exact prefixLift 2533982
  have htrace : WordTrace (prefixWord ++ tailWord_2533982) baseStart_2533982 baseEnd_2533982 := by
    simpa [prefixWord, tailWord_2533982, baseEnd_2533982] using wordTrace_append hprefix tailTrace_2533982
  have hstable : (prefixWord ++ tailWord_2533982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2533982).length < 2 ^ (prefixWord ++ tailWord_2533982).sum := by decide
  have hdescent : baseEnd_2533982 < baseStart_2533982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2533982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534021 : List Nat := [1, 3, 1, 1, 4, 4, 1, 1, 6]
def baseStart_2534021 : Nat := 118140960795 + 2534021 * 2 ^ 59
def prefixEnd_2534021 : Nat := 4983230072969 + 3 ^ 40 * 2534021 * 2
def baseEnd_2534021 : Nat := 289149058130430081085279

theorem tailTrace_2534021 : CollatzResearch.WordTrace tailWord_2534021 prefixEnd_2534021 289149058130430081085279 := by
  unfold tailWord_2534021
  simp only [CollatzResearch.WordTrace]
  refine ⟨92423338752682168176825917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61615559168454778784550611 92423338752682168176825917)
  ·
    refine ⟨34658752032255813066309719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92423338752682168176825917 34658752032255813066309719)
    ·
      refine ⟨51988128048383719599464579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34658752032255813066309719 51988128048383719599464579)
      ·
        refine ⟨77982192072575579399196869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51988128048383719599464579 77982192072575579399196869)
        ·
          refine ⟨14621661013607921137349413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77982192072575579399196869 14621661013607921137349413)
          ·
            refine ⟨2741561440051485213253015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14621661013607921137349413 2741561440051485213253015)
            ·
              refine ⟨4112342160077227819879523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2741561440051485213253015 4112342160077227819879523)
              ·
                refine ⟨6168513240115841729819285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4112342160077227819879523 6168513240115841729819285)
                ·
                  refine ⟨289149058130430081085279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6168513240115841729819285 289149058130430081085279)
                  ·
                    rfl

theorem cell22_2534021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 6].length) (baseStart_2534021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2534021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2534021 prefixEnd_2534021 := by exact prefixLift 2534021
  have htrace : WordTrace (prefixWord ++ tailWord_2534021) baseStart_2534021 baseEnd_2534021 := by
    simpa [prefixWord, tailWord_2534021, baseEnd_2534021] using wordTrace_append hprefix tailTrace_2534021
  have hstable : (prefixWord ++ tailWord_2534021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534021).length < 2 ^ (prefixWord ++ tailWord_2534021).sum := by decide
  have hdescent : baseEnd_2534021 < baseStart_2534021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534079 : List Nat := [1, 1, 2, 2, 2, 4, 1, 1, 2, 6]
def baseStart_2534079 : Nat := 118140960795 + 2534079 * 2 ^ 59
def prefixEnd_2534079 : Nat := 4983230072969 + 3 ^ 40 * 2534079 * 2
def baseEnd_2534079 : Nat := 867467028976597425305659

theorem tailTrace_2534079 : CollatzResearch.WordTrace tailWord_2534079 prefixEnd_2534079 867467028976597425305659 := by
  unfold tailWord_2534079
  simp only [CollatzResearch.WordTrace]
  refine ⟨92425454186472044082437291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61616969457648029388291527 92425454186472044082437291)
  ·
    refine ⟨138638181279708066123655937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92425454186472044082437291 138638181279708066123655937)
    ·
      refine ⟨103978635959781049592741953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138638181279708066123655937 103978635959781049592741953)
      ·
        refine ⟨77983976969835787194556465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103978635959781049592741953 77983976969835787194556465)
        ·
          refine ⟨58487982727376840395917349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77983976969835787194556465 58487982727376840395917349)
          ·
            refine ⟨10966496761383157574234503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58487982727376840395917349 10966496761383157574234503)
            ·
              refine ⟨16449745142074736361351755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10966496761383157574234503 16449745142074736361351755)
              ·
                refine ⟨24674617713112104542027633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16449745142074736361351755 24674617713112104542027633)
                ·
                  refine ⟨18505963284834078406520725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24674617713112104542027633 18505963284834078406520725)
                  ·
                    refine ⟨867467028976597425305659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18505963284834078406520725 867467028976597425305659)
                    ·
                      rfl

theorem cell22_2534079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 6].length) (baseStart_2534079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2534079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2534079 prefixEnd_2534079 := by exact prefixLift 2534079
  have htrace : WordTrace (prefixWord ++ tailWord_2534079) baseStart_2534079 baseEnd_2534079 := by
    simpa [prefixWord, tailWord_2534079, baseEnd_2534079] using wordTrace_append hprefix tailTrace_2534079
  have hstable : (prefixWord ++ tailWord_2534079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534079).length < 2 ^ (prefixWord ++ tailWord_2534079).sum := by decide
  have hdescent : baseEnd_2534079 < baseStart_2534079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534115 : List Nat := [1, 1, 1, 7, 1, 1, 1, 5, 1, 3]
def baseStart_2534115 : Nat := 118140960795 + 2534115 * 2 ^ 59
def prefixEnd_2534115 : Nat := 4983230072969 + 3 ^ 40 * 2534115 * 2
def baseEnd_2534115 : Nat := 867479352512305331405549

theorem tailTrace_2534115 : CollatzResearch.WordTrace tailWord_2534115 prefixEnd_2534115 867479352512305331405549 := by
  unfold tailWord_2534115
  simp only [CollatzResearch.WordTrace]
  refine ⟨92426767214341622230747799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61617844809561081487165199 92426767214341622230747799)
  ·
    refine ⟨138640150821512433346121699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92426767214341622230747799 138640150821512433346121699)
    ·
      refine ⟨207960226232268650019182549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138640150821512433346121699 207960226232268650019182549)
      ·
        refine ⟨4874067802318796484824591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 207960226232268650019182549 4874067802318796484824591)
        ·
          refine ⟨7311101703478194727236887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4874067802318796484824591 7311101703478194727236887)
          ·
            refine ⟨10966652555217292090855331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7311101703478194727236887 10966652555217292090855331)
            ·
              refine ⟨16449978832825938136282997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10966652555217292090855331 16449978832825938136282997)
              ·
                refine ⟨1542185515577431700276531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16449978832825938136282997 1542185515577431700276531)
                ·
                  refine ⟨2313278273366147550414797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1542185515577431700276531 2313278273366147550414797)
                  ·
                    refine ⟨867479352512305331405549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2313278273366147550414797 867479352512305331405549)
                    ·
                      rfl

theorem cell22_2534115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 5, 1, 3].length) (baseStart_2534115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2534115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2534115 prefixEnd_2534115 := by exact prefixLift 2534115
  have htrace : WordTrace (prefixWord ++ tailWord_2534115) baseStart_2534115 baseEnd_2534115 := by
    simpa [prefixWord, tailWord_2534115, baseEnd_2534115] using wordTrace_append hprefix tailTrace_2534115
  have hstable : (prefixWord ++ tailWord_2534115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534115).length < 2 ^ (prefixWord ++ tailWord_2534115).sum := by decide
  have hdescent : baseEnd_2534115 < baseStart_2534115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534126 : List Nat := [4, 1, 2, 1, 1, 3, 1, 2, 2, 5]
def baseStart_2534126 : Nat := 118140960795 + 2534126 * 2 ^ 59
def prefixEnd_2534126 : Nat := 4983230072969 + 3 ^ 40 * 2534126 * 2
def baseEnd_2534126 : Nat := 867483118037104969380515

theorem tailTrace_2534126 : CollatzResearch.WordTrace tailWord_2534126 prefixEnd_2534126 867483118037104969380515 := by
  unfold tailWord_2534126
  simp only [CollatzResearch.WordTrace]
  refine ⟨11553396052162721388674779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61618112278201180739598821 11553396052162721388674779)
  ·
    refine ⟨17330094078244082083012169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11553396052162721388674779 17330094078244082083012169)
    ·
      refine ⟨12997570558683061562259127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17330094078244082083012169 12997570558683061562259127)
      ·
        refine ⟨19496355838024592343388691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12997570558683061562259127 19496355838024592343388691)
        ·
          refine ⟨29244533757036888515083037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19496355838024592343388691 29244533757036888515083037)
          ·
            refine ⟨10966700158888833193156139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29244533757036888515083037 10966700158888833193156139)
            ·
              refine ⟨16450050238333249789734209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10966700158888833193156139 16450050238333249789734209)
              ·
                refine ⟨12337537678749937342300657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16450050238333249789734209 12337537678749937342300657)
                ·
                  refine ⟨9253153259062453006725493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12337537678749937342300657 9253153259062453006725493)
                  ·
                    refine ⟨867483118037104969380515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9253153259062453006725493 867483118037104969380515)
                    ·
                      rfl

theorem cell22_2534126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_2534126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2534126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2534126 prefixEnd_2534126 := by exact prefixLift 2534126
  have htrace : WordTrace (prefixWord ++ tailWord_2534126) baseStart_2534126 baseEnd_2534126 := by
    simpa [prefixWord, tailWord_2534126, baseEnd_2534126] using wordTrace_append hprefix tailTrace_2534126
  have hstable : (prefixWord ++ tailWord_2534126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534126).length < 2 ^ (prefixWord ++ tailWord_2534126).sum := by decide
  have hdescent : baseEnd_2534126 < baseStart_2534126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534188 : List Nat := [2, 2, 1, 1, 1, 4, 2, 4, 2, 3]
def baseStart_2534188 : Nat := 118140960795 + 2534188 * 2 ^ 59
def prefixEnd_2534188 : Nat := 4983230072969 + 3 ^ 40 * 2534188 * 2
def baseEnd_2534188 : Nat := 867504341904157474330325

theorem tailTrace_2534188 : CollatzResearch.WordTrace tailWord_2534188 prefixEnd_2534188 867504341904157474330325 := by
  unfold tailWord_2534188
  simp only [CollatzResearch.WordTrace]
  refine ⟨46214714871538577849077609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61619619828718103798770145 46214714871538577849077609)
  ·
    refine ⟨34661036153653933386808207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46214714871538577849077609 34661036153653933386808207)
    ·
      refine ⟨51991554230480900080212311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34661036153653933386808207 51991554230480900080212311)
      ·
        refine ⟨77987331345721350120318467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51991554230480900080212311 77987331345721350120318467)
        ·
          refine ⟨116980997018582025180477701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77987331345721350120318467 116980997018582025180477701)
          ·
            refine ⟨21933936940984129721339569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116980997018582025180477701 21933936940984129721339569)
            ·
              refine ⟨16450452705738097291004677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21933936940984129721339569 16450452705738097291004677)
              ·
                refine ⟨3084459882325893242063377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16450452705738097291004677 3084459882325893242063377)
                ·
                  refine ⟨2313344911744419931547533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3084459882325893242063377 2313344911744419931547533)
                  ·
                    refine ⟨867504341904157474330325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2313344911744419931547533 867504341904157474330325)
                    ·
                      rfl

theorem cell22_2534188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 3].length) (baseStart_2534188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2534188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2534188 prefixEnd_2534188 := by exact prefixLift 2534188
  have htrace : WordTrace (prefixWord ++ tailWord_2534188) baseStart_2534188 baseEnd_2534188 := by
    simpa [prefixWord, tailWord_2534188, baseEnd_2534188] using wordTrace_append hprefix tailTrace_2534188
  have hstable : (prefixWord ++ tailWord_2534188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534188).length < 2 ^ (prefixWord ++ tailWord_2534188).sum := by decide
  have hdescent : baseEnd_2534188 < baseStart_2534188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534190 : List Nat := [4, 1, 3, 2, 1, 3, 1, 1, 6]
def baseStart_2534190 : Nat := 118140960795 + 2534190 * 2 ^ 59
def prefixEnd_2534190 : Nat := 4983230072969 + 3 ^ 40 * 2534190 * 2
def baseEnd_2534190 : Nat := 289168342181676711926773

theorem tailTrace_2534190 : CollatzResearch.WordTrace tailWord_2534190 prefixEnd_2534190 289168342181676711926773 := by
  unfold tailWord_2534190
  simp only [CollatzResearch.WordTrace]
  refine ⟨11553687836133738754966003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61619668459379940026485349 11553687836133738754966003)
  ·
    refine ⟨17330531754200608132449005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11553687836133738754966003 17330531754200608132449005)
    ·
      refine ⟨6498949407825228049668377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17330531754200608132449005 6498949407825228049668377)
      ·
        refine ⟨4874212055868921037251283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6498949407825228049668377 4874212055868921037251283)
        ·
          refine ⟨7311318083803381555876925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4874212055868921037251283 7311318083803381555876925)
          ·
            refine ⟨2741744281426268083453847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7311318083803381555876925 2741744281426268083453847)
            ·
              refine ⟨4112616422139402125180771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2741744281426268083453847 4112616422139402125180771)
              ·
                refine ⟨6168924633209103187771157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4112616422139402125180771 6168924633209103187771157)
                ·
                  refine ⟨289168342181676711926773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6168924633209103187771157 289168342181676711926773)
                  ·
                    rfl

theorem cell22_2534190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_2534190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2534190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2534190 prefixEnd_2534190 := by exact prefixLift 2534190
  have htrace : WordTrace (prefixWord ++ tailWord_2534190) baseStart_2534190 baseEnd_2534190 := by
    simpa [prefixWord, tailWord_2534190, baseEnd_2534190] using wordTrace_append hprefix tailTrace_2534190
  have hstable : (prefixWord ++ tailWord_2534190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534190).length < 2 ^ (prefixWord ++ tailWord_2534190).sum := by decide
  have hdescent : baseEnd_2534190 < baseStart_2534190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534209 : List Nat := [1, 2, 5, 3, 2, 1, 1, 2, 1, 4]
def baseStart_2534209 : Nat := 118140960795 + 2534209 * 2 ^ 59
def prefixEnd_2534209 : Nat := 4983230072969 + 3 ^ 40 * 2534209 * 2
def baseEnd_2534209 : Nat := 867511530633320419555261

theorem tailTrace_2534209 : CollatzResearch.WordTrace tailWord_2534209 prefixEnd_2534209 867511530633320419555261 := by
  unfold tailWord_2534209
  simp only [CollatzResearch.WordTrace]
  refine ⟨92430195676001076284669681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61620130450667384189779787 92430195676001076284669681)
  ·
    refine ⟨69322646757000807213502261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92430195676001076284669681 69322646757000807213502261)
    ·
      refine ⟨6498998133468825676265837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69322646757000807213502261 6498998133468825676265837)
      ·
        refine ⟨2437124300050809628599689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6498998133468825676265837 2437124300050809628599689)
        ·
          refine ⟨1827843225038107221449767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2437124300050809628599689 1827843225038107221449767)
          ·
            refine ⟨2741764837557160832174651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1827843225038107221449767 2741764837557160832174651)
            ·
              refine ⟨4112647256335741248261977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2741764837557160832174651 4112647256335741248261977)
              ·
                refine ⟨3084485442251805936196483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4112647256335741248261977 3084485442251805936196483)
                ·
                  refine ⟨4626728163377708904294725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3084485442251805936196483 4626728163377708904294725)
                  ·
                    refine ⟨867511530633320419555261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4626728163377708904294725 867511530633320419555261)
                    ·
                      rfl

theorem cell22_2534209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_2534209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2534209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2534209 prefixEnd_2534209 := by exact prefixLift 2534209
  have htrace : WordTrace (prefixWord ++ tailWord_2534209) baseStart_2534209 baseEnd_2534209 := by
    simpa [prefixWord, tailWord_2534209, baseEnd_2534209] using wordTrace_append hprefix tailTrace_2534209
  have hstable : (prefixWord ++ tailWord_2534209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534209).length < 2 ^ (prefixWord ++ tailWord_2534209).sum := by decide
  have hdescent : baseEnd_2534209 < baseStart_2534209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534308 : List Nat := [2, 3, 1, 2, 1, 2, 4, 1, 6]
def baseStart_2534308 : Nat := 118140960795 + 2534308 * 2 ^ 59
def prefixEnd_2534308 : Nat := 4983230072969 + 3 ^ 40 * 2534308 * 2
def baseEnd_2534308 : Nat := 289181806785505720443319

theorem tailTrace_2534308 : CollatzResearch.WordTrace tailWord_2534308 prefixEnd_2534308 289181806785505720443319 := by
  unfold tailWord_2534308
  simp only [CollatzResearch.WordTrace]
  refine ⟨46216903251321208096261789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61622537668428277461682385 46216903251321208096261789)
  ·
    refine ⟨17331338719245453036098171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46216903251321208096261789 17331338719245453036098171)
    ·
      refine ⟨25997008078868179554147257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17331338719245453036098171 25997008078868179554147257)
      ·
        refine ⟨19497756059151134665610443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25997008078868179554147257 19497756059151134665610443)
        ·
          refine ⟨29246634088726701998415665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19497756059151134665610443 29246634088726701998415665)
          ·
            refine ⟨21934975566545026498811749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29246634088726701998415665 21934975566545026498811749)
            ·
              refine ⟨4112807918727192468527203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21934975566545026498811749 4112807918727192468527203)
              ·
                refine ⟨6169211878090788702790805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4112807918727192468527203 6169211878090788702790805)
                ·
                  refine ⟨289181806785505720443319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6169211878090788702790805 289181806785505720443319)
                  ·
                    rfl

theorem cell22_2534308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_2534308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2534308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2534308 prefixEnd_2534308 := by exact prefixLift 2534308
  have htrace : WordTrace (prefixWord ++ tailWord_2534308) baseStart_2534308 baseEnd_2534308 := by
    simpa [prefixWord, tailWord_2534308, baseEnd_2534308] using wordTrace_append hprefix tailTrace_2534308
  have hstable : (prefixWord ++ tailWord_2534308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534308).length < 2 ^ (prefixWord ++ tailWord_2534308).sum := by decide
  have hdescent : baseEnd_2534308 < baseStart_2534308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534370 : List Nat := [3, 3, 3, 1, 1, 1, 1, 9]
def baseStart_2534370 : Nat := 118140960795 + 2534370 * 2 ^ 59
def prefixEnd_2534370 : Nat := 4983230072969 + 3 ^ 40 * 2534370 * 2
def baseEnd_2534370 : Nat := 96396293802618851808863

theorem tailTrace_2534370 : CollatzResearch.WordTrace tailWord_2534370 prefixEnd_2534370 96396293802618851808863 := by
  unfold tailWord_2534370
  simp only [CollatzResearch.WordTrace]
  refine ⟨23109016957104450195320141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61624045218945200520853709 23109016957104450195320141)
  ·
    refine ⟨8665881358914168823245053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23109016957104450195320141 8665881358914168823245053)
    ·
      refine ⟨3249705509592813308716895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8665881358914168823245053 3249705509592813308716895)
      ·
        refine ⟨4874558264389219963075343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3249705509592813308716895 4874558264389219963075343)
        ·
          refine ⟨7311837396583829944613015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4874558264389219963075343 7311837396583829944613015)
          ·
            refine ⟨10967756094875744916919523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7311837396583829944613015 10967756094875744916919523)
            ·
              refine ⟨16451634142313617375379285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10967756094875744916919523 16451634142313617375379285)
              ·
                refine ⟨96396293802618851808863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16451634142313617375379285 96396293802618851808863)
                ·
                  rfl

theorem cell22_2534370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 9].length) (baseStart_2534370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2534370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2534370 prefixEnd_2534370 := by exact prefixLift 2534370
  have htrace : WordTrace (prefixWord ++ tailWord_2534370) baseStart_2534370 baseEnd_2534370 := by
    simpa [prefixWord, tailWord_2534370, baseEnd_2534370] using wordTrace_append hprefix tailTrace_2534370
  have hstable : (prefixWord ++ tailWord_2534370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534370).length < 2 ^ (prefixWord ++ tailWord_2534370).sum := by decide
  have hdescent : baseEnd_2534370 < baseStart_2534370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534389 : List Nat := [1, 3, 5, 2, 1, 1, 2, 1, 2, 4]
def baseStart_2534389 : Nat := 118140960795 + 2534389 * 2 ^ 59
def prefixEnd_2534389 : Nat := 4983230072969 + 3 ^ 40 * 2534389 * 2
def baseEnd_2534389 : Nat := 867573148311859950054709

theorem tailTrace_2534389 : CollatzResearch.WordTrace tailWord_2534389 prefixEnd_2534389 867573148311859950054709 := by
  unfold tailWord_2534389
  simp only [CollatzResearch.WordTrace]
  refine ⟨92436760815348967026222221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61624507210232644684148147 92436760815348967026222221)
  ·
    refine ⟨34663785305755862634833333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92436760815348967026222221 34663785305755862634833333)
    ·
      refine ⟨3249729872414612122015625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34663785305755862634833333 3249729872414612122015625)
      ·
        refine ⟨2437297404310959091511719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3249729872414612122015625 2437297404310959091511719)
        ·
          refine ⟨3655946106466438637267579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2437297404310959091511719 3655946106466438637267579)
          ·
            refine ⟨5483919159699657955901369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3655946106466438637267579 5483919159699657955901369)
            ·
              refine ⟨4112939369774743466926027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5483919159699657955901369 4112939369774743466926027)
              ·
                refine ⟨6169409054662115200389041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4112939369774743466926027 6169409054662115200389041)
                ·
                  refine ⟨4627056790996586400291781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6169409054662115200389041 4627056790996586400291781)
                  ·
                    refine ⟨867573148311859950054709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4627056790996586400291781 867573148311859950054709)
                    ·
                      rfl

theorem cell22_2534389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_2534389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2534389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2534389 prefixEnd_2534389 := by exact prefixLift 2534389
  have htrace : WordTrace (prefixWord ++ tailWord_2534389) baseStart_2534389 baseEnd_2534389 := by
    simpa [prefixWord, tailWord_2534389, baseEnd_2534389] using wordTrace_append hprefix tailTrace_2534389
  have hstable : (prefixWord ++ tailWord_2534389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534389).length < 2 ^ (prefixWord ++ tailWord_2534389).sum := by decide
  have hdescent : baseEnd_2534389 < baseStart_2534389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534443 : List Nat := [1, 1, 1, 1, 2, 1, 7, 2, 6]
def baseStart_2534443 : Nat := 118140960795 + 2534443 * 2 ^ 59
def prefixEnd_2534443 : Nat := 4983230072969 + 3 ^ 40 * 2534443 * 2
def baseEnd_2534443 : Nat := 289197211205140603068181

theorem tailTrace_2534443 : CollatzResearch.WordTrace tailWord_2534443 prefixEnd_2534443 289197211205140603068181 := by
  unfold tailWord_2534443
  simp only [CollatzResearch.WordTrace]
  refine ⟨92438730357153334248687983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61625820238102222832458655 92438730357153334248687983)
  ·
    refine ⟨138658095535730001373031975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92438730357153334248687983 138658095535730001373031975)
    ·
      refine ⟨207987143303595002059547963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138658095535730001373031975 207987143303595002059547963)
      ·
        refine ⟨311980714955392503089321945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207987143303595002059547963 311980714955392503089321945)
        ·
          refine ⟨233985536216544377316991459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 311980714955392503089321945 233985536216544377316991459)
          ·
            refine ⟨350978304324816565975487189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233985536216544377316991459 350978304324816565975487189)
            ·
              refine ⟨8226054007612888265050481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 350978304324816565975487189 8226054007612888265050481)
              ·
                refine ⟨6169540505709666198787861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8226054007612888265050481 6169540505709666198787861)
                ·
                  refine ⟨289197211205140603068181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6169540505709666198787861 289197211205140603068181)
                  ·
                    rfl

theorem cell22_2534443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 6].length) (baseStart_2534443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2534443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2534443 prefixEnd_2534443 := by exact prefixLift 2534443
  have htrace : WordTrace (prefixWord ++ tailWord_2534443) baseStart_2534443 baseEnd_2534443 := by
    simpa [prefixWord, tailWord_2534443, baseEnd_2534443] using wordTrace_append hprefix tailTrace_2534443
  have hstable : (prefixWord ++ tailWord_2534443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534443).length < 2 ^ (prefixWord ++ tailWord_2534443).sum := by decide
  have hdescent : baseEnd_2534443 < baseStart_2534443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534477 : List Nat := [1, 6, 1, 1, 1, 3, 2, 1, 6]
def baseStart_2534477 : Nat := 118140960795 + 2534477 * 2 ^ 59
def prefixEnd_2534477 : Nat := 4983230072969 + 3 ^ 40 * 2534477 * 2
def baseEnd_2534477 : Nat := 289201090836752351284813

theorem tailTrace_2534477 : CollatzResearch.WordTrace tailWord_2534477 prefixEnd_2534477 289201090836752351284813 := by
  unfold tailWord_2534477
  simp only [CollatzResearch.WordTrace]
  refine ⟨92439970439030158055425685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61626646959353438703617123 92439970439030158055425685)
  ·
    refine ⟨4333123614329538658848079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 92439970439030158055425685 4333123614329538658848079)
    ·
      refine ⟨6499685421494307988272119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4333123614329538658848079 6499685421494307988272119)
      ·
        refine ⟨9749528132241461982408179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6499685421494307988272119 9749528132241461982408179)
        ·
          refine ⟨14624292198362192973612269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9749528132241461982408179 14624292198362192973612269)
          ·
            refine ⟨5484109574385822365104601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14624292198362192973612269 5484109574385822365104601)
            ·
              refine ⟨4113082180789366773828451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5484109574385822365104601 4113082180789366773828451)
              ·
                refine ⟨6169623271184050160742677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4113082180789366773828451 6169623271184050160742677)
                ·
                  refine ⟨289201090836752351284813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6169623271184050160742677 289201090836752351284813)
                  ·
                    rfl

theorem cell22_2534477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_2534477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2534477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2534477 prefixEnd_2534477 := by exact prefixLift 2534477
  have htrace : WordTrace (prefixWord ++ tailWord_2534477) baseStart_2534477 baseEnd_2534477 := by
    simpa [prefixWord, tailWord_2534477, baseEnd_2534477] using wordTrace_append hprefix tailTrace_2534477
  have hstable : (prefixWord ++ tailWord_2534477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534477).length < 2 ^ (prefixWord ++ tailWord_2534477).sum := by decide
  have hdescent : baseEnd_2534477 < baseStart_2534477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534488 : List Nat := [2, 1, 2, 2, 1, 3, 2, 9]
def baseStart_2534488 : Nat := 118140960795 + 2534488 * 2 ^ 59
def prefixEnd_2534488 : Nat := 4983230072969 + 3 ^ 40 * 2534488 * 2
def baseEnd_2534488 : Nat := 96400782003895187981045

theorem tailTrace_2534488 : CollatzResearch.WordTrace tailWord_2534488 prefixEnd_2534488 96400782003895187981045 := by
  unfold tailWord_2534488
  simp only [CollatzResearch.WordTrace]
  refine ⟨46220185820995153467038059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61626914427993537956050745 46220185820995153467038059)
  ·
    refine ⟨69330278731492730200557089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46220185820995153467038059 69330278731492730200557089)
    ·
      refine ⟨51997709048619547650417817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69330278731492730200557089 51997709048619547650417817)
      ·
        refine ⟨38998281786464660737813363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51997709048619547650417817 38998281786464660737813363)
        ·
          refine ⟨58497422679696991106720045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38998281786464660737813363 58497422679696991106720045)
          ·
            refine ⟨21936533504886371665020017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58497422679696991106720045 21936533504886371665020017)
            ·
              refine ⟨16452400128664778748765013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21936533504886371665020017 16452400128664778748765013)
              ·
                refine ⟨96400782003895187981045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16452400128664778748765013 96400782003895187981045)
                ·
                  rfl

theorem cell22_2534488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 9].length) (baseStart_2534488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2534488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2534488 prefixEnd_2534488 := by exact prefixLift 2534488
  have htrace : WordTrace (prefixWord ++ tailWord_2534488) baseStart_2534488 baseEnd_2534488 := by
    simpa [prefixWord, tailWord_2534488, baseEnd_2534488] using wordTrace_append hprefix tailTrace_2534488
  have hstable : (prefixWord ++ tailWord_2534488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534488).length < 2 ^ (prefixWord ++ tailWord_2534488).sum := by decide
  have hdescent : baseEnd_2534488 < baseStart_2534488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2534494 : List Nat := [4, 4, 1, 1, 1, 1, 2, 2, 6]
def baseStart_2534494 : Nat := 118140960795 + 2534494 * 2 ^ 59
def prefixEnd_2534494 : Nat := 4983230072969 + 3 ^ 40 * 2534494 * 2
def baseEnd_2534494 : Nat := 289203030652558225393129

theorem tailTrace_2534494 : CollatzResearch.WordTrace tailWord_2534494 prefixEnd_2534494 289203030652558225393129 := by
  unfold tailWord_2534494
  simp only [CollatzResearch.WordTrace]
  refine ⟨11555073809996071244849317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61627060319979046639196357 11555073809996071244849317)
  ·
    refine ⟨2166576339374263358409247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11555073809996071244849317 2166576339374263358409247)
    ·
      refine ⟨3249864509061395037613871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2166576339374263358409247 3249864509061395037613871)
      ·
        refine ⟨4874796763592092556420807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3249864509061395037613871 4874796763592092556420807)
        ·
          refine ⟨7312195145388138834631211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4874796763592092556420807 7312195145388138834631211)
          ·
            refine ⟨10968292718082208251946817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7312195145388138834631211 10968292718082208251946817)
            ·
              refine ⟨8226219538561656188960113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10968292718082208251946817 8226219538561656188960113)
              ·
                refine ⟨6169664653921242141720085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8226219538561656188960113 6169664653921242141720085)
                ·
                  refine ⟨289203030652558225393129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6169664653921242141720085 289203030652558225393129)
                  ·
                    rfl

theorem cell22_2534494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_2534494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2534494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2534494 prefixEnd_2534494 := by exact prefixLift 2534494
  have htrace : WordTrace (prefixWord ++ tailWord_2534494) baseStart_2534494 baseEnd_2534494 := by
    simpa [prefixWord, tailWord_2534494, baseEnd_2534494] using wordTrace_append hprefix tailTrace_2534494
  have hstable : (prefixWord ++ tailWord_2534494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2534494).length < 2 ^ (prefixWord ++ tailWord_2534494).sum := by decide
  have hdescent : baseEnd_2534494 < baseStart_2534494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2534494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
