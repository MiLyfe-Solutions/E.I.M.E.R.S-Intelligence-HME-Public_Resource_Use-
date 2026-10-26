import V185TrunkScan23Chunk0044

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_267034 : List Nat := [3, 1, 1, 3, 2, 1, 2, 2, 1, 5, 2]
def baseStart_267034 : Nat := 118140960795 + 267034 * 2 ^ 59
def prefixEnd_267034 : Nat := 4983230072969 + 3 ^ 40 * 267034 * 2
def baseEnd_267034 : Nat := 137116793092813461946939

theorem tailTrace_267034 : CollatzResearch.WordTrace tailWord_267034 prefixEnd_267034 137116793092813461946939 := by
  unfold tailWord_267034
  simp only [CollatzResearch.WordTrace]
  refine ⟨2434882528647224655362039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6493020076392599080965437 2434882528647224655362039)
  ·
    refine ⟨3652323792970836983043059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2434882528647224655362039 3652323792970836983043059)
    ·
      refine ⟨5478485689456255474564589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3652323792970836983043059 5478485689456255474564589)
      ·
        refine ⟨2054432133546095802961721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5478485689456255474564589 2054432133546095802961721)
        ·
          refine ⟨1540824100159571852221291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2054432133546095802961721 1540824100159571852221291)
          ·
            refine ⟨2311236150239357778331937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1540824100159571852221291 2311236150239357778331937)
            ·
              refine ⟨1733427112679518333748953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2311236150239357778331937 1733427112679518333748953)
              ·
                refine ⟨1300070334509638750311715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1733427112679518333748953 1300070334509638750311715)
                ·
                  refine ⟨1950105501764458125467573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1300070334509638750311715 1950105501764458125467573)
                  ·
                    refine ⟨182822390790417949262585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1950105501764458125467573 182822390790417949262585)
                    ·
                      refine ⟨137116793092813461946939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 182822390790417949262585 137116793092813461946939)
                      ·
                        rfl

theorem cell23_267034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_267034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267034 prefixEnd_267034 := by exact prefixLift 267034
  have htrace : WordTrace (prefixWord ++ tailWord_267034) baseStart_267034 baseEnd_267034 := by
    simpa [prefixWord, tailWord_267034, baseEnd_267034] using wordTrace_append hprefix tailTrace_267034
  have hstable : (prefixWord ++ tailWord_267034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267034).length < 2 ^ (prefixWord ++ tailWord_267034).sum := by decide
  have hdescent : baseEnd_267034 < baseStart_267034 := by decide
  rcases family_descends (prefixWord ++ tailWord_267034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267057 : List Nat := [1, 2, 2, 3, 2, 1, 1, 4, 1, 6]
def baseStart_267057 : Nat := 118140960795 + 267057 * 2 ^ 59
def prefixEnd_267057 : Nat := 4983230072969 + 3 ^ 40 * 267057 * 2
def baseEnd_267057 : Nat := 45709534382622290653111

theorem tailTrace_267057 : CollatzResearch.WordTrace tailWord_267057 prefixEnd_267057 45709534382622290653111 := by
  unfold tailWord_267057
  simp only [CollatzResearch.WordTrace]
  refine ⟨9740368993505573549535425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6493579329003715699690283 9740368993505573549535425)
  ·
    refine ⟨7305276745129180162151569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9740368993505573549535425 7305276745129180162151569)
    ·
      refine ⟨5478957558846885121613677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7305276745129180162151569 5478957558846885121613677)
      ·
        refine ⟨2054609084567581920605129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5478957558846885121613677 2054609084567581920605129)
        ·
          refine ⟨1540956813425686440453847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2054609084567581920605129 1540956813425686440453847)
          ·
            refine ⟨2311435220138529660680771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1540956813425686440453847 2311435220138529660680771)
            ·
              refine ⟨3467152830207794491021157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2311435220138529660680771 3467152830207794491021157)
              ·
                refine ⟨650091155663961467066467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3467152830207794491021157 650091155663961467066467)
                ·
                  refine ⟨975136733495942200599701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 650091155663961467066467 975136733495942200599701)
                  ·
                    refine ⟨45709534382622290653111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 975136733495942200599701 45709534382622290653111)
                    ·
                      rfl

theorem cell23_267057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 6].length) (baseStart_267057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267057 prefixEnd_267057 := by exact prefixLift 267057
  have htrace : WordTrace (prefixWord ++ tailWord_267057) baseStart_267057 baseEnd_267057 := by
    simpa [prefixWord, tailWord_267057, baseEnd_267057] using wordTrace_append hprefix tailTrace_267057
  have hstable : (prefixWord ++ tailWord_267057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267057).length < 2 ^ (prefixWord ++ tailWord_267057).sum := by decide
  have hdescent : baseEnd_267057 < baseStart_267057 := by decide
  rcases family_descends (prefixWord ++ tailWord_267057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267058 : List Nat := [3, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3]
def baseStart_267058 : Nat := 118140960795 + 267058 * 2 ^ 59
def prefixEnd_267058 : Nat := 4983230072969 + 3 ^ 40 * 267058 * 2
def baseEnd_267058 : Nat := 137129116628521368046829

theorem tailTrace_267058 : CollatzResearch.WordTrace tailWord_267058 prefixEnd_267058 137129116628521368046829 := by
  unfold tailWord_267058
  simp only [CollatzResearch.WordTrace]
  refine ⟨2435101366625487680080457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6493603644334633813547885 2435101366625487680080457)
  ·
    refine ⟨1826326024969115760060343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2435101366625487680080457 1826326024969115760060343)
    ·
      refine ⟨2739489037453673640090515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1826326024969115760060343 2739489037453673640090515)
      ·
        refine ⟨4109233556180510460135773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2739489037453673640090515 4109233556180510460135773)
        ·
          refine ⟨1540962583567691422550915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4109233556180510460135773 1540962583567691422550915)
          ·
            refine ⟨2311443875351537133826373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1540962583567691422550915 2311443875351537133826373)
            ·
              refine ⟨433395726628413212592445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2311443875351537133826373 433395726628413212592445)
              ·
                refine ⟨162523397485654954722167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 433395726628413212592445 162523397485654954722167)
                ·
                  refine ⟨243785096228482432083251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162523397485654954722167 243785096228482432083251)
                  ·
                    refine ⟨365677644342723648124877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 243785096228482432083251 365677644342723648124877)
                    ·
                      refine ⟨137129116628521368046829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 365677644342723648124877 137129116628521368046829)
                      ·
                        rfl

theorem cell23_267058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3].length) (baseStart_267058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267058 prefixEnd_267058 := by exact prefixLift 267058
  have htrace : WordTrace (prefixWord ++ tailWord_267058) baseStart_267058 baseEnd_267058 := by
    simpa [prefixWord, tailWord_267058, baseEnd_267058] using wordTrace_append hprefix tailTrace_267058
  have hstable : (prefixWord ++ tailWord_267058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267058).length < 2 ^ (prefixWord ++ tailWord_267058).sum := by decide
  have hdescent : baseEnd_267058 < baseStart_267058 := by decide
  rcases family_descends (prefixWord ++ tailWord_267058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267061 : List Nat := [1, 3, 3, 1, 3, 1, 4, 1, 1, 5]
def baseStart_267061 : Nat := 118140960795 + 267061 * 2 ^ 59
def prefixEnd_267061 : Nat := 4983230072969 + 3 ^ 40 * 267061 * 2
def baseEnd_267061 : Nat := 45710219023494952103105

theorem tailTrace_267061 : CollatzResearch.WordTrace tailWord_267061 prefixEnd_267061 45710219023494952103105 := by
  unfold tailWord_267061
  simp only [CollatzResearch.WordTrace]
  refine ⟨9740514885491082232681037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6493676590327388155120691 9740514885491082232681037)
  ·
    refine ⟨3652693082059155837255389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9740514885491082232681037 3652693082059155837255389)
    ·
      refine ⟨1369759905772183438970771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3652693082059155837255389 1369759905772183438970771)
      ·
        refine ⟨2054639858658275158456157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1369759905772183438970771 2054639858658275158456157)
        ·
          refine ⟨770489946996853184421059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2054639858658275158456157 770489946996853184421059)
          ·
            refine ⟨1155734920495279776631589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770489946996853184421059 1155734920495279776631589)
            ·
              refine ⟨216700297592864958118423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1155734920495279776631589 216700297592864958118423)
              ·
                refine ⟨325050446389297437177635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216700297592864958118423 325050446389297437177635)
                ·
                  refine ⟨487575669583946155766453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 325050446389297437177635 487575669583946155766453)
                  ·
                    refine ⟨45710219023494952103105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 487575669583946155766453 45710219023494952103105)
                    ·
                      rfl

theorem cell23_267061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_267061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267061 prefixEnd_267061 := by exact prefixLift 267061
  have htrace : WordTrace (prefixWord ++ tailWord_267061) baseStart_267061 baseEnd_267061 := by
    simpa [prefixWord, tailWord_267061, baseEnd_267061] using wordTrace_append hprefix tailTrace_267061
  have hstable : (prefixWord ++ tailWord_267061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267061).length < 2 ^ (prefixWord ++ tailWord_267061).sum := by decide
  have hdescent : baseEnd_267061 < baseStart_267061 := by decide
  rcases family_descends (prefixWord ++ tailWord_267061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267064 : List Nat := [2, 1, 2, 1, 3, 2, 3, 3, 1, 1, 4]
def baseStart_267064 : Nat := 118140960795 + 267064 * 2 ^ 59
def prefixEnd_267064 : Nat := 4983230072969 + 3 ^ 40 * 267064 * 2
def baseEnd_267064 : Nat := 137132197512448344571801

theorem tailTrace_267064 : CollatzResearch.WordTrace tailWord_267064 prefixEnd_267064 137132197512448344571801 := by
  unfold tailWord_267064
  simp only [CollatzResearch.WordTrace]
  refine ⟨4870312152240106872520123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6493749536320142496693497 4870312152240106872520123)
  ·
    refine ⟨7305468228360160308780185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4870312152240106872520123 7305468228360160308780185)
    ·
      refine ⟨5479101171270120231585139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7305468228360160308780185 5479101171270120231585139)
      ·
        refine ⟨8218651756905180347377709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5479101171270120231585139 8218651756905180347377709)
        ·
          refine ⟨3081994408839442630266641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8218651756905180347377709 3081994408839442630266641)
          ·
            refine ⟨2311495806629581972699981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3081994408839442630266641 2311495806629581972699981)
            ·
              refine ⟨866810927486093239762493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2311495806629581972699981 866810927486093239762493)
              ·
                refine ⟨325054097807284964910935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 866810927486093239762493 325054097807284964910935)
                ·
                  refine ⟨487581146710927447366403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 325054097807284964910935 487581146710927447366403)
                  ·
                    refine ⟨731371720066391171049605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 487581146710927447366403 731371720066391171049605)
                    ·
                      refine ⟨137132197512448344571801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 731371720066391171049605 137132197512448344571801)
                      ·
                        rfl

theorem cell23_267064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 1, 1, 4].length) (baseStart_267064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267064 prefixEnd_267064 := by exact prefixLift 267064
  have htrace : WordTrace (prefixWord ++ tailWord_267064) baseStart_267064 baseEnd_267064 := by
    simpa [prefixWord, tailWord_267064, baseEnd_267064] using wordTrace_append hprefix tailTrace_267064
  have hstable : (prefixWord ++ tailWord_267064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267064).length < 2 ^ (prefixWord ++ tailWord_267064).sum := by decide
  have hdescent : baseEnd_267064 < baseStart_267064 := by decide
  rcases family_descends (prefixWord ++ tailWord_267064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267081 : List Nat := [1, 2, 1, 1, 2, 5, 1, 3, 3, 2, 2]
def baseStart_267081 : Nat := 118140960795 + 267081 * 2 ^ 59
def prefixEnd_267081 : Nat := 4983230072969 + 3 ^ 40 * 267081 * 2
def baseEnd_267081 : Nat := 137140926683574778059223

theorem tailTrace_267081 : CollatzResearch.WordTrace tailWord_267081 prefixEnd_267081 137140926683574778059223 := by
  unfold tailWord_267081
  simp only [CollatzResearch.WordTrace]
  refine ⟨9741244345418625648409097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6494162896945750432272731 9741244345418625648409097)
  ·
    refine ⟨7305933259063969236306823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9741244345418625648409097 7305933259063969236306823)
    ·
      refine ⟨10958899888595953854460235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7305933259063969236306823 10958899888595953854460235)
      ·
        refine ⟨16438349832893930781690353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10958899888595953854460235 16438349832893930781690353)
        ·
          refine ⟨12328762374670448086267765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16438349832893930781690353 12328762374670448086267765)
          ·
            refine ⟨1155821472625354508087603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12328762374670448086267765 1155821472625354508087603)
            ·
              refine ⟨1733732208938031762131405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1155821472625354508087603 1733732208938031762131405)
              ·
                refine ⟨650149578351761910799277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1733732208938031762131405 650149578351761910799277)
                ·
                  refine ⟨243806091881910716549729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 650149578351761910799277 243806091881910716549729)
                  ·
                    refine ⟨182854568911433037412297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 243806091881910716549729 182854568911433037412297)
                    ·
                      refine ⟨137140926683574778059223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 182854568911433037412297 137140926683574778059223)
                      ·
                        rfl

theorem cell23_267081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 3, 2, 2].length) (baseStart_267081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267081 prefixEnd_267081 := by exact prefixLift 267081
  have htrace : WordTrace (prefixWord ++ tailWord_267081) baseStart_267081 baseEnd_267081 := by
    simpa [prefixWord, tailWord_267081, baseEnd_267081] using wordTrace_append hprefix tailTrace_267081
  have hstable : (prefixWord ++ tailWord_267081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267081).length < 2 ^ (prefixWord ++ tailWord_267081).sum := by decide
  have hdescent : baseEnd_267081 < baseStart_267081 := by decide
  rcases family_descends (prefixWord ++ tailWord_267081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267084 : List Nat := [2, 2, 1, 3, 3, 2, 1, 2, 1, 1, 5]
def baseStart_267084 : Nat := 118140960795 + 267084 * 2 ^ 59
def prefixEnd_267084 : Nat := 4983230072969 + 3 ^ 40 * 267084 * 2
def baseEnd_267084 : Nat := 137142467125538266321709

theorem tailTrace_267084 : CollatzResearch.WordTrace tailWord_267084 prefixEnd_267084 137142467125538266321709 := by
  unfold tailWord_267084
  simp only [CollatzResearch.WordTrace]
  refine ⟨4870676882203878580384153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6494235842938504773845537 4870676882203878580384153)
  ·
    refine ⟨3653007661652908935288115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4870676882203878580384153 3653007661652908935288115)
    ·
      refine ⟨5479511492479363402932173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3653007661652908935288115 5479511492479363402932173)
      ·
        refine ⟨2054816809679761276099565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5479511492479363402932173 2054816809679761276099565)
        ·
          refine ⟨770556303629910478537337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2054816809679761276099565 770556303629910478537337)
          ·
            refine ⟨577917227722432858903003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 770556303629910478537337 577917227722432858903003)
            ·
              refine ⟨866875841583649288354505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577917227722432858903003 866875841583649288354505)
              ·
                refine ⟨650156881187736966265879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 866875841583649288354505 650156881187736966265879)
                ·
                  refine ⟨975235321781605449398819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 650156881187736966265879 975235321781605449398819)
                  ·
                    refine ⟨1462852982672408174098229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 975235321781605449398819 1462852982672408174098229)
                    ·
                      refine ⟨137142467125538266321709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1462852982672408174098229 137142467125538266321709)
                      ·
                        rfl

theorem cell23_267084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_267084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267084 prefixEnd_267084 := by exact prefixLift 267084
  have htrace : WordTrace (prefixWord ++ tailWord_267084) baseStart_267084 baseEnd_267084 := by
    simpa [prefixWord, tailWord_267084, baseEnd_267084] using wordTrace_append hprefix tailTrace_267084
  have hstable : (prefixWord ++ tailWord_267084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267084).length < 2 ^ (prefixWord ++ tailWord_267084).sum := by decide
  have hdescent : baseEnd_267084 < baseStart_267084 := by decide
  rcases family_descends (prefixWord ++ tailWord_267084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267117 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 1, 9]
def baseStart_267117 : Nat := 118140960795 + 267117 * 2 ^ 59
def prefixEnd_267117 : Nat := 4983230072969 + 3 ^ 40 * 267117 * 2
def baseEnd_267117 : Nat := 45719803995712212403019

theorem tailTrace_267117 : CollatzResearch.WordTrace tailWord_267117 prefixEnd_267117 45719803995712212403019 := by
  unfold tailWord_267117
  simp only [CollatzResearch.WordTrace]
  refine ⟨9742557373288203796719605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6495038248858802531146403 9742557373288203796719605)
  ·
    refine ⟨913364753745769105942463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9742557373288203796719605 913364753745769105942463)
    ·
      refine ⟨1370047130618653658913695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 913364753745769105942463 1370047130618653658913695)
      ·
        refine ⟨2055070695927980488370543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1370047130618653658913695 2055070695927980488370543)
        ·
          refine ⟨3082606043891970732555815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2055070695927980488370543 3082606043891970732555815)
          ·
            refine ⟨4623909065837956098833723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3082606043891970732555815 4623909065837956098833723)
            ·
              refine ⟨6935863598756934148250585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4623909065837956098833723 6935863598756934148250585)
              ·
                refine ⟨5201897699067700611187939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6935863598756934148250585 5201897699067700611187939)
                ·
                  refine ⟨7802846548601550916781909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5201897699067700611187939 7802846548601550916781909)
                  ·
                    refine ⟨45719803995712212403019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 7802846548601550916781909 45719803995712212403019)
                    ·
                      rfl

theorem cell23_267117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_267117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267117 prefixEnd_267117 := by exact prefixLift 267117
  have htrace : WordTrace (prefixWord ++ tailWord_267117) baseStart_267117 baseEnd_267117 := by
    simpa [prefixWord, tailWord_267117, baseEnd_267117] using wordTrace_append hprefix tailTrace_267117
  have hstable : (prefixWord ++ tailWord_267117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267117).length < 2 ^ (prefixWord ++ tailWord_267117).sum := by decide
  have hdescent : baseEnd_267117 < baseStart_267117 := by decide
  rcases family_descends (prefixWord ++ tailWord_267117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267138 : List Nat := [3, 4, 2, 2, 1, 1, 2, 8]
def baseStart_267138 : Nat := 118140960795 + 267138 * 2 ^ 59
def prefixEnd_267138 : Nat := 4983230072969 + 3 ^ 40 * 267138 * 2
def baseEnd_267138 : Nat := 5080377595588187223943

theorem tailTrace_267138 : CollatzResearch.WordTrace tailWord_267138 prefixEnd_267138 5080377595588187223943 := by
  unfold tailWord_267138
  simp only [CollatzResearch.WordTrace]
  refine ⟨2435830826553031095808517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6495548870808082922156045 2435830826553031095808517)
  ·
    refine ⟨456718279978693330464097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2435830826553031095808517 456718279978693330464097)
    ·
      refine ⟨342538709984019997848073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456718279978693330464097 342538709984019997848073)
      ·
        refine ⟨256904032488014998386055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342538709984019997848073 256904032488014998386055)
        ·
          refine ⟨385356048732022497579083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256904032488014998386055 385356048732022497579083)
          ·
            refine ⟨578034073098033746368625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385356048732022497579083 578034073098033746368625)
            ·
              refine ⟨433525554823525309776469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 578034073098033746368625 433525554823525309776469)
              ·
                refine ⟨5080377595588187223943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 433525554823525309776469 5080377595588187223943)
                ·
                  rfl

theorem cell23_267138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 8].length) (baseStart_267138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267138 prefixEnd_267138 := by exact prefixLift 267138
  have htrace : WordTrace (prefixWord ++ tailWord_267138) baseStart_267138 baseEnd_267138 := by
    simpa [prefixWord, tailWord_267138, baseEnd_267138] using wordTrace_append hprefix tailTrace_267138
  have hstable : (prefixWord ++ tailWord_267138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267138).length < 2 ^ (prefixWord ++ tailWord_267138).sum := by decide
  have hdescent : baseEnd_267138 < baseStart_267138 := by decide
  rcases family_descends (prefixWord ++ tailWord_267138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267147 : List Nat := [1, 1, 1, 1, 4, 2, 2, 3, 2, 6]
def baseStart_267147 : Nat := 118140960795 + 267147 * 2 ^ 59
def prefixEnd_267147 : Nat := 4983230072969 + 3 ^ 40 * 267147 * 2
def baseEnd_267147 : Nat := 45724938802257173277973

theorem tailTrace_267147 : CollatzResearch.WordTrace tailWord_267147 prefixEnd_267147 45724938802257173277973 := by
  unfold tailWord_267147
  simp only [CollatzResearch.WordTrace]
  refine ⟨9743651563179518920311695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6495767708786345946874463 9743651563179518920311695)
  ·
    refine ⟨14615477344769278380467543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9743651563179518920311695 14615477344769278380467543)
    ·
      refine ⟨21923216017153917570701315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14615477344769278380467543 21923216017153917570701315)
      ·
        refine ⟨32884824025730876356051973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21923216017153917570701315 32884824025730876356051973)
        ·
          refine ⟨6165904504824539316759745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32884824025730876356051973 6165904504824539316759745)
          ·
            refine ⟨4624428378618404487569809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6165904504824539316759745 4624428378618404487569809)
            ·
              refine ⟨3468321283963803365677357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4624428378618404487569809 3468321283963803365677357)
              ·
                refine ⟨1300620481486426262129009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3468321283963803365677357 1300620481486426262129009)
                ·
                  refine ⟨975465361114819696596757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1300620481486426262129009 975465361114819696596757)
                  ·
                    refine ⟨45724938802257173277973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 975465361114819696596757 45724938802257173277973)
                    ·
                      rfl

theorem cell23_267147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 6].length) (baseStart_267147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267147 prefixEnd_267147 := by exact prefixLift 267147
  have htrace : WordTrace (prefixWord ++ tailWord_267147) baseStart_267147 baseEnd_267147 := by
    simpa [prefixWord, tailWord_267147, baseEnd_267147] using wordTrace_append hprefix tailTrace_267147
  have hstable : (prefixWord ++ tailWord_267147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267147).length < 2 ^ (prefixWord ++ tailWord_267147).sum := by decide
  have hdescent : baseEnd_267147 < baseStart_267147 := by decide
  rcases family_descends (prefixWord ++ tailWord_267147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267148 : List Nat := [2, 2, 1, 2, 1, 2, 6, 1, 2, 1, 3]
def baseStart_267148 : Nat := 118140960795 + 267148 * 2 ^ 59
def prefixEnd_267148 : Nat := 4983230072969 + 3 ^ 40 * 267148 * 2
def baseEnd_267148 : Nat := 137175329887426015921415

theorem tailTrace_267148 : CollatzResearch.WordTrace tailWord_267148 prefixEnd_267148 137175329887426015921415 := by
  unfold tailWord_267148
  simp only [CollatzResearch.WordTrace]
  refine ⟨4871844018087948045549049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6495792024117264060732065 4871844018087948045549049)
  ·
    refine ⟨3653883013565961034161787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4871844018087948045549049 3653883013565961034161787)
    ·
      refine ⟨5480824520348941551242681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3653883013565961034161787 5480824520348941551242681)
      ·
        refine ⟨4110618390261706163432011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5480824520348941551242681 4110618390261706163432011)
        ·
          refine ⟨6165927585392559245148017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4110618390261706163432011 6165927585392559245148017)
          ·
            refine ⟨4624445689044419433861013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6165927585392559245148017 4624445689044419433861013)
            ·
              refine ⟨216770891673957160962235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4624445689044419433861013 216770891673957160962235)
              ·
                refine ⟨325156337510935741443353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216770891673957160962235 325156337510935741443353)
                ·
                  refine ⟨243867253133201806082515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 325156337510935741443353 243867253133201806082515)
                  ·
                    refine ⟨365800879699802709123773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 243867253133201806082515 365800879699802709123773)
                    ·
                      refine ⟨137175329887426015921415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 365800879699802709123773 137175329887426015921415)
                      ·
                        rfl

theorem cell23_267148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 2, 1, 3].length) (baseStart_267148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267148 prefixEnd_267148 := by exact prefixLift 267148
  have htrace : WordTrace (prefixWord ++ tailWord_267148) baseStart_267148 baseEnd_267148 := by
    simpa [prefixWord, tailWord_267148, baseEnd_267148] using wordTrace_append hprefix tailTrace_267148
  have hstable : (prefixWord ++ tailWord_267148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267148).length < 2 ^ (prefixWord ++ tailWord_267148).sum := by decide
  have hdescent : baseEnd_267148 < baseStart_267148 := by decide
  rcases family_descends (prefixWord ++ tailWord_267148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267171 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 6, 2, 2]
def baseStart_267171 : Nat := 118140960795 + 267171 * 2 ^ 59
def prefixEnd_267171 : Nat := 4983230072969 + 3 ^ 40 * 267171 * 2
def baseEnd_267171 : Nat := 137187139942479425933809

theorem tailTrace_267171 : CollatzResearch.WordTrace tailWord_267171 prefixEnd_267171 137187139942479425933809 := by
  unfold tailWord_267171
  simp only [CollatzResearch.WordTrace]
  refine ⟨9744526915092571019185367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6496351276728380679456911 9744526915092571019185367)
  ·
    refine ⟨14616790372638856528778051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9744526915092571019185367 14616790372638856528778051)
    ·
      refine ⟨21925185558958284793167077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14616790372638856528778051 21925185558958284793167077)
      ·
        refine ⟨4110972292304678398718827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21925185558958284793167077 4110972292304678398718827)
        ·
          refine ⟨6166458438457017598078241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4110972292304678398718827 6166458438457017598078241)
          ·
            refine ⟨4624843828842763198558681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6166458438457017598078241 4624843828842763198558681)
            ·
              refine ⟨3468632871632072398919011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4624843828842763198558681 3468632871632072398919011)
              ·
                refine ⟨5202949307448108598378517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3468632871632072398919011 5202949307448108598378517)
                ·
                  refine ⟨243888248786630090548993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5202949307448108598378517 243888248786630090548993)
                  ·
                    refine ⟨182916186589972567911745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 243888248786630090548993 182916186589972567911745)
                    ·
                      refine ⟨137187139942479425933809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 182916186589972567911745 137187139942479425933809)
                      ·
                        rfl

theorem cell23_267171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 6, 2, 2].length) (baseStart_267171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267171 prefixEnd_267171 := by exact prefixLift 267171
  have htrace : WordTrace (prefixWord ++ tailWord_267171) baseStart_267171 baseEnd_267171 := by
    simpa [prefixWord, tailWord_267171, baseEnd_267171] using wordTrace_append hprefix tailTrace_267171
  have hstable : (prefixWord ++ tailWord_267171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267171).length < 2 ^ (prefixWord ++ tailWord_267171).sum := by decide
  have hdescent : baseEnd_267171 < baseStart_267171 := by decide
  rcases family_descends (prefixWord ++ tailWord_267171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267224 : List Nat := [2, 1, 2, 2, 2, 4, 1, 1, 1, 7]
def baseStart_267224 : Nat := 118140960795 + 267224 * 2 ^ 59
def prefixEnd_267224 : Nat := 4983230072969 + 3 ^ 40 * 267224 * 2
def baseEnd_267224 : Nat := 45738118139055906190355

theorem tailTrace_267224 : CollatzResearch.WordTrace tailWord_267224 prefixEnd_267224 45738118139055906190355 := by
  unfold tailWord_267224
  simp only [CollatzResearch.WordTrace]
  refine ⟨4873229991950280535432363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6497639989267040713909817 4873229991950280535432363)
  ·
    refine ⟨7309844987925420803148545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4873229991950280535432363 7309844987925420803148545)
    ·
      refine ⟨5482383740944065602361409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7309844987925420803148545 5482383740944065602361409)
      ·
        refine ⟨4111787805708049201771057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5482383740944065602361409 4111787805708049201771057)
        ·
          refine ⟨3083840854281036901328293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4111787805708049201771057 3083840854281036901328293)
          ·
            refine ⟨578220160177694418999055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3083840854281036901328293 578220160177694418999055)
            ·
              refine ⟨867330240266541628498583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578220160177694418999055 867330240266541628498583)
              ·
                refine ⟨1300995360399812442747875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 867330240266541628498583 1300995360399812442747875)
                ·
                  refine ⟨1951493040599718664121813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1300995360399812442747875 1951493040599718664121813)
                  ·
                    refine ⟨45738118139055906190355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1951493040599718664121813 45738118139055906190355)
                    ·
                      rfl

theorem cell23_267224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 1, 7].length) (baseStart_267224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267224 prefixEnd_267224 := by exact prefixLift 267224
  have htrace : WordTrace (prefixWord ++ tailWord_267224) baseStart_267224 baseEnd_267224 := by
    simpa [prefixWord, tailWord_267224, baseEnd_267224] using wordTrace_append hprefix tailTrace_267224
  have hstable : (prefixWord ++ tailWord_267224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267224).length < 2 ^ (prefixWord ++ tailWord_267224).sum := by decide
  have hdescent : baseEnd_267224 < baseStart_267224 := by decide
  rcases family_descends (prefixWord ++ tailWord_267224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267271 : List Nat := [1, 1, 4, 3, 1, 1, 1, 4, 3, 4]
def baseStart_267271 : Nat := 118140960795 + 267271 * 2 ^ 59
def prefixEnd_267271 : Nat := 4983230072969 + 3 ^ 40 * 267271 * 2
def baseEnd_267271 : Nat := 45746162669309678227783

theorem tailTrace_267271 : CollatzResearch.WordTrace tailWord_267271 prefixEnd_267271 45746162669309678227783 := by
  unfold tailWord_267271
  simp only [CollatzResearch.WordTrace]
  refine ⟨9748174214730288097825667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6498782809820192065217111 9748174214730288097825667)
  ·
    refine ⟨14622261322095432146738501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9748174214730288097825667 14622261322095432146738501)
    ·
      refine ⟨2741673997892893527513469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14622261322095432146738501 2741673997892893527513469)
      ·
        refine ⟨1028127749209835072817551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2741673997892893527513469 1028127749209835072817551)
        ·
          refine ⟨1542191623814752609226327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1028127749209835072817551 1542191623814752609226327)
          ·
            refine ⟨2313287435722128913839491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1542191623814752609226327 2313287435722128913839491)
            ·
              refine ⟨3469931153583193370759237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2313287435722128913839491 3469931153583193370759237)
              ·
                refine ⟨650612091296848757017357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3469931153583193370759237 650612091296848757017357)
                ·
                  refine ⟨243979534236318283881509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 650612091296848757017357 243979534236318283881509)
                  ·
                    refine ⟨45746162669309678227783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 243979534236318283881509 45746162669309678227783)
                    ·
                      rfl

theorem cell23_267271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_267271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267271 prefixEnd_267271 := by exact prefixLift 267271
  have htrace : WordTrace (prefixWord ++ tailWord_267271) baseStart_267271 baseEnd_267271 := by
    simpa [prefixWord, tailWord_267271, baseEnd_267271] using wordTrace_append hprefix tailTrace_267271
  have hstable : (prefixWord ++ tailWord_267271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267271).length < 2 ^ (prefixWord ++ tailWord_267271).sum := by decide
  have hdescent : baseEnd_267271 < baseStart_267271 := by decide
  rcases family_descends (prefixWord ++ tailWord_267271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267298 : List Nat := [3, 3, 1, 1, 1, 4, 1, 2, 2, 2, 3]
def baseStart_267298 : Nat := 118140960795 + 267298 * 2 ^ 59
def prefixEnd_267298 : Nat := 4983230072969 + 3 ^ 40 * 267298 * 2
def baseEnd_267298 : Nat := 137252351985600429045725

theorem tailTrace_267298 : CollatzResearch.WordTrace tailWord_267298 prefixEnd_267298 137252351985600429045725 := by
  unfold tailWord_267298
  simp only [CollatzResearch.WordTrace]
  refine ⟨2437289746408117927264637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6499439323754981139372365 2437289746408117927264637)
  ·
    refine ⟨913983654903044222724239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2437289746408117927264637 913983654903044222724239)
    ·
      refine ⟨1370975482354566334086359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 913983654903044222724239 1370975482354566334086359)
      ·
        refine ⟨2056463223531849501129539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1370975482354566334086359 2056463223531849501129539)
        ·
          refine ⟨3084694835297774251694309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2056463223531849501129539 3084694835297774251694309)
          ·
            refine ⟨578380281618332672192683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3084694835297774251694309 578380281618332672192683)
            ·
              refine ⟨867570422427499008289025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578380281618332672192683 867570422427499008289025)
              ·
                refine ⟨650677816820624256216769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 867570422427499008289025 650677816820624256216769)
                ·
                  refine ⟨488008362615468192162577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 650677816820624256216769 488008362615468192162577)
                  ·
                    refine ⟨366006271961601144121933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 488008362615468192162577 366006271961601144121933)
                    ·
                      refine ⟨137252351985600429045725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 366006271961601144121933 137252351985600429045725)
                      ·
                        rfl

theorem cell23_267298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_267298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267298 prefixEnd_267298 := by exact prefixLift 267298
  have htrace : WordTrace (prefixWord ++ tailWord_267298) baseStart_267298 baseEnd_267298 := by
    simpa [prefixWord, tailWord_267298, baseEnd_267298] using wordTrace_append hprefix tailTrace_267298
  have hstable : (prefixWord ++ tailWord_267298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267298).length < 2 ^ (prefixWord ++ tailWord_267298).sum := by decide
  have hdescent : baseEnd_267298 < baseStart_267298 := by decide
  rcases family_descends (prefixWord ++ tailWord_267298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267318 : List Nat := [5, 1, 2, 1, 1, 3, 1, 3, 6]
def baseStart_267318 : Nat := 118140960795 + 267318 * 2 ^ 59
def prefixEnd_267318 : Nat := 4983230072969 + 3 ^ 40 * 267318 * 2
def baseEnd_267318 : Nat := 15251402399854483421737

theorem tailTrace_267318 : CollatzResearch.WordTrace tailWord_267318 prefixEnd_267318 15251402399854483421737 := by
  unfold tailWord_267318
  simp only [CollatzResearch.WordTrace]
  refine ⟨609368027847500945299163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6499925630373343416524405 609368027847500945299163)
  ·
    refine ⟨914052041771251417948745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 609368027847500945299163 914052041771251417948745)
    ·
      refine ⟨685539031328438563461559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 914052041771251417948745 685539031328438563461559)
      ·
        refine ⟨1028308546992657845192339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685539031328438563461559 1028308546992657845192339)
        ·
          refine ⟨1542462820488986767788509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1028308546992657845192339 1542462820488986767788509)
          ·
            refine ⟨578423557683370037920691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1542462820488986767788509 578423557683370037920691)
            ·
              refine ⟨867635336525055056881037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578423557683370037920691 867635336525055056881037)
              ·
                refine ⟨325363251196895646330389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 867635336525055056881037 325363251196895646330389)
                ·
                  refine ⟨15251402399854483421737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 325363251196895646330389 15251402399854483421737)
                  ·
                    rfl

theorem cell23_267318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_267318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267318 prefixEnd_267318 := by exact prefixLift 267318
  have htrace : WordTrace (prefixWord ++ tailWord_267318) baseStart_267318 baseEnd_267318 := by
    simpa [prefixWord, tailWord_267318, baseEnd_267318] using wordTrace_append hprefix tailTrace_267318
  have hstable : (prefixWord ++ tailWord_267318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267318).length < 2 ^ (prefixWord ++ tailWord_267318).sum := by decide
  have hdescent : baseEnd_267318 < baseStart_267318 := by decide
  rcases family_descends (prefixWord ++ tailWord_267318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267338 : List Nat := [3, 1, 2, 1, 1, 2, 3, 3, 2, 3, 2]
def baseStart_267338 : Nat := 118140960795 + 267338 * 2 ^ 59
def prefixEnd_267338 : Nat := 4983230072969 + 3 ^ 40 * 267338 * 2
def baseEnd_267338 : Nat := 137272891211780272545541

theorem tailTrace_267338 : CollatzResearch.WordTrace tailWord_267338 prefixEnd_267338 137272891211780272545541 := by
  unfold tailWord_267338
  simp only [CollatzResearch.WordTrace]
  refine ⟨2437654476371889635128667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6500411936991705693676445 2437654476371889635128667)
  ·
    refine ⟨3656481714557834452693001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2437654476371889635128667 3656481714557834452693001)
    ·
      refine ⟨2742361285918375839519751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3656481714557834452693001 2742361285918375839519751)
      ·
        refine ⟨4113541928877563759279627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2742361285918375839519751 4113541928877563759279627)
        ·
          refine ⟨6170312893316345638919441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4113541928877563759279627 6170312893316345638919441)
          ·
            refine ⟨4627734669987259229189581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6170312893316345638919441 4627734669987259229189581)
            ·
              refine ⟨1735400501245222210946093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4627734669987259229189581 1735400501245222210946093)
              ·
                refine ⟨650775187966958329104785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1735400501245222210946093 650775187966958329104785)
                ·
                  refine ⟨488081390975218746828589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 650775187966958329104785 488081390975218746828589)
                  ·
                    refine ⟨183030521615707030060721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 488081390975218746828589 183030521615707030060721)
                    ·
                      refine ⟨137272891211780272545541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 183030521615707030060721 137272891211780272545541)
                      ·
                        rfl

theorem cell23_267338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 2, 3, 2].length) (baseStart_267338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267338 prefixEnd_267338 := by exact prefixLift 267338
  have htrace : WordTrace (prefixWord ++ tailWord_267338) baseStart_267338 baseEnd_267338 := by
    simpa [prefixWord, tailWord_267338, baseEnd_267338] using wordTrace_append hprefix tailTrace_267338
  have hstable : (prefixWord ++ tailWord_267338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267338).length < 2 ^ (prefixWord ++ tailWord_267338).sum := by decide
  have hdescent : baseEnd_267338 < baseStart_267338 := by decide
  rcases family_descends (prefixWord ++ tailWord_267338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267361 : List Nat := [1, 2, 3, 1, 1, 2, 2, 3, 4, 4]
def baseStart_267361 : Nat := 118140960795 + 267361 * 2 ^ 59
def prefixEnd_267361 : Nat := 4983230072969 + 3 ^ 40 * 267361 * 2
def baseEnd_267361 : Nat := 45761567088944560852645

theorem tailTrace_267361 : CollatzResearch.WordTrace tailWord_267361 prefixEnd_267361 45761567088944560852645 := by
  unfold tailWord_267361
  simp only [CollatzResearch.WordTrace]
  refine ⟨9751456784404233468601937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6500971189602822312401291 9751456784404233468601937)
  ·
    refine ⟨7313592588303175101451453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9751456784404233468601937 7313592588303175101451453)
    ·
      refine ⟨2742597220613690663044295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7313592588303175101451453 2742597220613690663044295)
      ·
        refine ⟨4113895830920535994566443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2742597220613690663044295 4113895830920535994566443)
        ·
          refine ⟨6170843746380803991849665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4113895830920535994566443 6170843746380803991849665)
          ·
            refine ⟨4628132809785602993887249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6170843746380803991849665 4628132809785602993887249)
            ·
              refine ⟨3471099607339202245415437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4628132809785602993887249 3471099607339202245415437)
              ·
                refine ⟨1301662352752200842030789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3471099607339202245415437 1301662352752200842030789)
                ·
                  refine ⟨244061691141037657880773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1301662352752200842030789 244061691141037657880773)
                  ·
                    refine ⟨45761567088944560852645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 244061691141037657880773 45761567088944560852645)
                    ·
                      rfl

theorem cell23_267361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_267361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267361 prefixEnd_267361 := by exact prefixLift 267361
  have htrace : WordTrace (prefixWord ++ tailWord_267361) baseStart_267361 baseEnd_267361 := by
    simpa [prefixWord, tailWord_267361, baseEnd_267361] using wordTrace_append hprefix tailTrace_267361
  have hstable : (prefixWord ++ tailWord_267361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267361).length < 2 ^ (prefixWord ++ tailWord_267361).sum := by decide
  have hdescent : baseEnd_267361 < baseStart_267361 := by decide
  rcases family_descends (prefixWord ++ tailWord_267361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267378 : List Nat := [3, 2, 1, 2, 2, 1, 1, 5, 2, 4]
def baseStart_267378 : Nat := 118140960795 + 267378 * 2 ^ 59
def prefixEnd_267378 : Nat := 4983230072969 + 3 ^ 40 * 267378 * 2
def baseEnd_267378 : Nat := 45764476812653372015119

theorem tailTrace_267378 : CollatzResearch.WordTrace tailWord_267378 prefixEnd_267378 45764476812653372015119 := by
  unfold tailWord_267378
  simp only [CollatzResearch.WordTrace]
  refine ⟨2438019206335661342992697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6501384550228430247980525 2438019206335661342992697)
  ·
    refine ⟨1828514404751746007244523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2438019206335661342992697 1828514404751746007244523)
    ·
      refine ⟨2742771607127619010866785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1828514404751746007244523 2742771607127619010866785)
      ·
        refine ⟨2057078705345714258150089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2742771607127619010866785 2057078705345714258150089)
        ·
          refine ⟨1542809029009285693612567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2057078705345714258150089 1542809029009285693612567)
          ·
            refine ⟨2314213543513928540418851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1542809029009285693612567 2314213543513928540418851)
            ·
              refine ⟨3471320315270892810628277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2314213543513928540418851 3471320315270892810628277)
              ·
                refine ⟨325436279556646200996401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3471320315270892810628277 325436279556646200996401)
                ·
                  refine ⟨244077209667484650747301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 325436279556646200996401 244077209667484650747301)
                  ·
                    refine ⟨45764476812653372015119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 244077209667484650747301 45764476812653372015119)
                    ·
                      rfl

theorem cell23_267378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_267378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267378 prefixEnd_267378 := by exact prefixLift 267378
  have htrace : WordTrace (prefixWord ++ tailWord_267378) baseStart_267378 baseEnd_267378 := by
    simpa [prefixWord, tailWord_267378, baseEnd_267378] using wordTrace_append hprefix tailTrace_267378
  have hstable : (prefixWord ++ tailWord_267378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267378).length < 2 ^ (prefixWord ++ tailWord_267378).sum := by decide
  have hdescent : baseEnd_267378 < baseStart_267378 := by decide
  rcases family_descends (prefixWord ++ tailWord_267378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267388 : List Nat := [2, 2, 2, 1, 1, 3, 2, 4, 1, 2, 3]
def baseStart_267388 : Nat := 118140960795 + 267388 * 2 ^ 59
def prefixEnd_267388 : Nat := 4983230072969 + 3 ^ 40 * 267388 * 2
def baseEnd_267388 : Nat := 137298565244505076920311

theorem tailTrace_267388 : CollatzResearch.WordTrace tailWord_267388 prefixEnd_267388 137298565244505076920311 := by
  unfold tailWord_267388
  simp only [CollatzResearch.WordTrace]
  refine ⟨4876220777653208539917409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6501627703537611386556545 4876220777653208539917409)
  ·
    refine ⟨3657165583239906404938057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4876220777653208539917409 3657165583239906404938057)
    ·
      refine ⟨2742874187429929803703543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3657165583239906404938057 2742874187429929803703543)
      ·
        refine ⟨4114311281144894705555315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2742874187429929803703543 4114311281144894705555315)
        ·
          refine ⟨6171466921717342058332973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4114311281144894705555315 6171466921717342058332973)
          ·
            refine ⟨2314300095644003271874865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6171466921717342058332973 2314300095644003271874865)
            ·
              refine ⟨1735725071733002453906149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2314300095644003271874865 1735725071733002453906149)
              ·
                refine ⟨325448450949937960107403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1735725071733002453906149 325448450949937960107403)
                ·
                  refine ⟨488172676424906940161105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 325448450949937960107403 488172676424906940161105)
                  ·
                    refine ⟨366129507318680205120829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 488172676424906940161105 366129507318680205120829)
                    ·
                      refine ⟨137298565244505076920311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 366129507318680205120829 137298565244505076920311)
                      ·
                        rfl

theorem cell23_267388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 1, 2, 3].length) (baseStart_267388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267388 prefixEnd_267388 := by exact prefixLift 267388
  have htrace : WordTrace (prefixWord ++ tailWord_267388) baseStart_267388 baseEnd_267388 := by
    simpa [prefixWord, tailWord_267388, baseEnd_267388] using wordTrace_append hprefix tailTrace_267388
  have hstable : (prefixWord ++ tailWord_267388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267388).length < 2 ^ (prefixWord ++ tailWord_267388).sum := by decide
  have hdescent : baseEnd_267388 < baseStart_267388 := by decide
  rcases family_descends (prefixWord ++ tailWord_267388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267461 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 1, 6, 3]
def baseStart_267461 : Nat := 118140960795 + 267461 * 2 ^ 59
def prefixEnd_267461 : Nat := 4983230072969 + 3 ^ 40 * 267461 * 2
def baseEnd_267461 : Nat := 137336049332283291307475

theorem tailTrace_267461 : CollatzResearch.WordTrace tailWord_267461 prefixEnd_267461 137336049332283291307475 := by
  unfold tailWord_267461
  simp only [CollatzResearch.WordTrace]
  refine ⟨9755104084041950547242237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6503402722694633698161491 9755104084041950547242237)
  ·
    refine ⟨3658164031515731455215839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9755104084041950547242237 3658164031515731455215839)
    ·
      refine ⟨5487246047273597182823759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3658164031515731455215839 5487246047273597182823759)
      ·
        refine ⟨8230869070910395774235639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5487246047273597182823759 8230869070910395774235639)
        ·
          refine ⟨12346303606365593661353459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8230869070910395774235639 12346303606365593661353459)
          ·
            refine ⟨18519455409548390492030189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12346303606365593661353459 18519455409548390492030189)
            ·
              refine ⟨6944795778580646434511321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18519455409548390492030189 6944795778580646434511321)
              ·
                refine ⟨5208596833935484825883491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6944795778580646434511321 5208596833935484825883491)
                ·
                  refine ⟨7812895250903227238825237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5208596833935484825883491 7812895250903227238825237)
                  ·
                    refine ⟨366229464886088776819933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7812895250903227238825237 366229464886088776819933)
                    ·
                      refine ⟨137336049332283291307475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 366229464886088776819933 137336049332283291307475)
                      ·
                        rfl

theorem cell23_267461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 6, 3].length) (baseStart_267461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267461 prefixEnd_267461 := by exact prefixLift 267461
  have htrace : WordTrace (prefixWord ++ tailWord_267461) baseStart_267461 baseEnd_267461 := by
    simpa [prefixWord, tailWord_267461, baseEnd_267461] using wordTrace_append hprefix tailTrace_267461
  have hstable : (prefixWord ++ tailWord_267461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267461).length < 2 ^ (prefixWord ++ tailWord_267461).sum := by decide
  have hdescent : baseEnd_267461 < baseStart_267461 := by decide
  rcases family_descends (prefixWord ++ tailWord_267461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267471 : List Nat := [1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 4]
def baseStart_267471 : Nat := 118140960795 + 267471 * 2 ^ 59
def prefixEnd_267471 : Nat := 4983230072969 + 3 ^ 40 * 267471 * 2
def baseEnd_267471 : Nat := 137341184138828252182429

theorem tailTrace_267471 : CollatzResearch.WordTrace tailWord_267471 prefixEnd_267471 137341184138828252182429 := by
  unfold tailWord_267471
  simp only [CollatzResearch.WordTrace]
  refine ⟨9755468814005722255106267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6503645876003814836737511 9755468814005722255106267)
  ·
    refine ⟨14633203221008583382659401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9755468814005722255106267 14633203221008583382659401)
    ·
      refine ⟨10974902415756437536994551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14633203221008583382659401 10974902415756437536994551)
      ·
        refine ⟨16462353623634656305491827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10974902415756437536994551 16462353623634656305491827)
        ·
          refine ⟨24693530435451984458237741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16462353623634656305491827 24693530435451984458237741)
          ·
            refine ⟨9260073913294494171839153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24693530435451984458237741 9260073913294494171839153)
            ·
              refine ⟨6945055434970870628879365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9260073913294494171839153 6945055434970870628879365)
              ·
                refine ⟨1302197894057038242914881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6945055434970870628879365 1302197894057038242914881)
                ·
                  refine ⟨976648420542778682186161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1302197894057038242914881 976648420542778682186161)
                  ·
                    refine ⟨732486315407084011639621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 976648420542778682186161 732486315407084011639621)
                    ·
                      refine ⟨137341184138828252182429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 732486315407084011639621 137341184138828252182429)
                      ·
                        rfl

theorem cell23_267471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 4].length) (baseStart_267471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267471 prefixEnd_267471 := by exact prefixLift 267471
  have htrace : WordTrace (prefixWord ++ tailWord_267471) baseStart_267471 baseEnd_267471 := by
    simpa [prefixWord, tailWord_267471, baseEnd_267471] using wordTrace_append hprefix tailTrace_267471
  have hstable : (prefixWord ++ tailWord_267471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267471).length < 2 ^ (prefixWord ++ tailWord_267471).sum := by decide
  have hdescent : baseEnd_267471 < baseStart_267471 := by decide
  rcases family_descends (prefixWord ++ tailWord_267471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267511 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 6, 5]
def baseStart_267511 : Nat := 118140960795 + 267511 * 2 ^ 59
def prefixEnd_267511 : Nat := 4983230072969 + 3 ^ 40 * 267511 * 2
def baseEnd_267511 : Nat := 45787241121669365227415

theorem tailTrace_267511 : CollatzResearch.WordTrace tailWord_267511 prefixEnd_267511 45787241121669365227415 := by
  unfold tailWord_267511
  simp only [CollatzResearch.WordTrace]
  refine ⟨9756927733860809086562387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6504618489240539391041591 9756927733860809086562387)
  ·
    refine ⟨14635391600791213629843581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9756927733860809086562387 14635391600791213629843581)
    ·
      refine ⟨5488271850296705111191343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14635391600791213629843581 5488271850296705111191343)
      ·
        refine ⟨8232407775445057666787015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5488271850296705111191343 8232407775445057666787015)
        ·
          refine ⟨12348611663167586500180523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8232407775445057666787015 12348611663167586500180523)
          ·
            refine ⟨18522917494751379750270785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12348611663167586500180523 18522917494751379750270785)
            ·
              refine ⟨13892188121063534812703089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18522917494751379750270785 13892188121063534812703089)
              ·
                refine ⟨10419141090797651109527317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13892188121063534812703089 10419141090797651109527317)
                ·
                  refine ⟨488397238631139895759093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10419141090797651109527317 488397238631139895759093)
                  ·
                    refine ⟨45787241121669365227415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 488397238631139895759093 45787241121669365227415)
                    ·
                      rfl

theorem cell23_267511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 5].length) (baseStart_267511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267511 prefixEnd_267511 := by exact prefixLift 267511
  have htrace : WordTrace (prefixWord ++ tailWord_267511) baseStart_267511 baseEnd_267511 := by
    simpa [prefixWord, tailWord_267511, baseEnd_267511] using wordTrace_append hprefix tailTrace_267511
  have hstable : (prefixWord ++ tailWord_267511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267511).length < 2 ^ (prefixWord ++ tailWord_267511).sum := by decide
  have hdescent : baseEnd_267511 < baseStart_267511 := by decide
  rcases family_descends (prefixWord ++ tailWord_267511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267532 : List Nat := [2, 2, 1, 2, 2, 5, 2, 2, 5]
def baseStart_267532 : Nat := 118140960795 + 267532 * 2 ^ 59
def prefixEnd_267532 : Nat := 4983230072969 + 3 ^ 40 * 267532 * 2
def baseEnd_267532 : Nat := 15263611828750279279961

theorem tailTrace_267532 : CollatzResearch.WordTrace tailWord_267532 prefixEnd_267532 15263611828750279279961 := by
  unfold tailWord_267532
  simp only [CollatzResearch.WordTrace]
  refine ⟨4878846833392364836538425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6505129111189819782051233 4878846833392364836538425)
  ·
    refine ⟨3659135125044273627403819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4878846833392364836538425 3659135125044273627403819)
    ·
      refine ⟨5488702687566410441105729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3659135125044273627403819 5488702687566410441105729)
      ·
        refine ⟨4116527015674807830829297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5488702687566410441105729 4116527015674807830829297)
        ·
          refine ⟨3087395261756105873121973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4116527015674807830829297 3087395261756105873121973)
          ·
            refine ⟨289443305789634925605185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3087395261756105873121973 289443305789634925605185)
            ·
              refine ⟨217082479342226194203889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289443305789634925605185 217082479342226194203889)
              ·
                refine ⟨162811859506669645652917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217082479342226194203889 162811859506669645652917)
                ·
                  refine ⟨15263611828750279279961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 162811859506669645652917 15263611828750279279961)
                  ·
                    rfl

theorem cell23_267532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 2, 5].length) (baseStart_267532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267532 prefixEnd_267532 := by exact prefixLift 267532
  have htrace : WordTrace (prefixWord ++ tailWord_267532) baseStart_267532 baseEnd_267532 := by
    simpa [prefixWord, tailWord_267532, baseEnd_267532] using wordTrace_append hprefix tailTrace_267532
  have hstable : (prefixWord ++ tailWord_267532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267532).length < 2 ^ (prefixWord ++ tailWord_267532).sum := by decide
  have hdescent : baseEnd_267532 < baseStart_267532 := by decide
  rcases family_descends (prefixWord ++ tailWord_267532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267541 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 2, 8]
def baseStart_267541 : Nat := 118140960795 + 267541 * 2 ^ 59
def prefixEnd_267541 : Nat := 4983230072969 + 3 ^ 40 * 267541 * 2
def baseEnd_267541 : Nat := 45792375928214326102369

theorem tailTrace_267541 : CollatzResearch.WordTrace tailWord_267541 prefixEnd_267541 45792375928214326102369 := by
  unfold tailWord_267541
  simp only [CollatzResearch.WordTrace]
  refine ⟨9758021923752124210154477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6505347949168082806769651 9758021923752124210154477)
  ·
    refine ⟨3659258221407046578807929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9758021923752124210154477 3659258221407046578807929)
    ·
      refine ⟨2744443666055284934105947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3659258221407046578807929 2744443666055284934105947)
      ·
        refine ⟨4116665499082927401158921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2744443666055284934105947 4116665499082927401158921)
        ·
          refine ⟨3087499124312195550869191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4116665499082927401158921 3087499124312195550869191)
          ·
            refine ⟨4631248686468293326303787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3087499124312195550869191 4631248686468293326303787)
            ·
              refine ⟨6946873029702439989455681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4631248686468293326303787 6946873029702439989455681)
              ·
                refine ⟨5210154772276829992091761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6946873029702439989455681 5210154772276829992091761)
                ·
                  refine ⟨3907616079207622494068821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5210154772276829992091761 3907616079207622494068821)
                  ·
                    refine ⟨45792375928214326102369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3907616079207622494068821 45792375928214326102369)
                    ·
                      rfl

theorem cell23_267541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_267541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267541 prefixEnd_267541 := by exact prefixLift 267541
  have htrace : WordTrace (prefixWord ++ tailWord_267541) baseStart_267541 baseEnd_267541 := by
    simpa [prefixWord, tailWord_267541, baseEnd_267541] using wordTrace_append hprefix tailTrace_267541
  have hstable : (prefixWord ++ tailWord_267541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267541).length < 2 ^ (prefixWord ++ tailWord_267541).sum := by decide
  have hdescent : baseEnd_267541 < baseStart_267541 := by decide
  rcases family_descends (prefixWord ++ tailWord_267541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267548 : List Nat := [2, 2, 3, 1, 1, 1, 2, 2, 4, 1, 4]
def baseStart_267548 : Nat := 118140960795 + 267548 * 2 ^ 59
def prefixEnd_267548 : Nat := 4983230072969 + 3 ^ 40 * 267548 * 2
def baseEnd_267548 : Nat := 137380722149224450919575

theorem tailTrace_267548 : CollatzResearch.WordTrace tailWord_267548 prefixEnd_267548 137380722149224450919575 := by
  unfold tailWord_267548
  simp only [CollatzResearch.WordTrace]
  refine ⟨4879138617363382202829649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6505518156484509603772865 4879138617363382202829649)
  ·
    refine ⟨3659353963022536652122237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4879138617363382202829649 3659353963022536652122237)
    ·
      refine ⟨1372257736133451244545839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3659353963022536652122237 1372257736133451244545839)
      ·
        refine ⟨2058386604200176866818759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1372257736133451244545839 2058386604200176866818759)
        ·
          refine ⟨3087579906300265300228139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2058386604200176866818759 3087579906300265300228139)
          ·
            refine ⟨4631369859450397950342209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3087579906300265300228139 4631369859450397950342209)
            ·
              refine ⟨3473527394587798462756657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4631369859450397950342209 3473527394587798462756657)
              ·
                refine ⟨2605145545940848847067493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3473527394587798462756657 2605145545940848847067493)
                ·
                  refine ⟨488464789863909158825155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2605145545940848847067493 488464789863909158825155)
                  ·
                    refine ⟨732697184795863738237733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 488464789863909158825155 732697184795863738237733)
                    ·
                      refine ⟨137380722149224450919575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 732697184795863738237733 137380722149224450919575)
                      ·
                        rfl

theorem cell23_267548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_267548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267548 prefixEnd_267548 := by exact prefixLift 267548
  have htrace : WordTrace (prefixWord ++ tailWord_267548) baseStart_267548 baseEnd_267548 := by
    simpa [prefixWord, tailWord_267548, baseEnd_267548] using wordTrace_append hprefix tailTrace_267548
  have hstable : (prefixWord ++ tailWord_267548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267548).length < 2 ^ (prefixWord ++ tailWord_267548).sum := by decide
  have hdescent : baseEnd_267548 < baseStart_267548 := by decide
  rcases family_descends (prefixWord ++ tailWord_267548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267562 : List Nat := [3, 1, 4, 2, 1, 3, 1, 1, 2, 5]
def baseStart_267562 : Nat := 118140960795 + 267562 * 2 ^ 59
def prefixEnd_267562 : Nat := 4983230072969 + 3 ^ 40 * 267562 * 2
def baseEnd_267562 : Nat := 45795970292795798714837

theorem tailTrace_267562 : CollatzResearch.WordTrace tailWord_267562 prefixEnd_267562 45795970292795798714837 := by
  unfold tailWord_267562
  simp only [CollatzResearch.WordTrace]
  refine ⟨2439696964169011199167235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6505858571117363197779293 2439696964169011199167235)
  ·
    refine ⟨3659545446253516798750853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2439696964169011199167235 3659545446253516798750853)
    ·
      refine ⟨686164771172534399765785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3659545446253516798750853 686164771172534399765785)
      ·
        refine ⟨514623578379400799824339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 686164771172534399765785 514623578379400799824339)
        ·
          refine ⟨771935367569101199736509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514623578379400799824339 771935367569101199736509)
          ·
            refine ⟨289475762838412949901191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 771935367569101199736509 289475762838412949901191)
            ·
              refine ⟨434213644257619424851787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289475762838412949901191 434213644257619424851787)
              ·
                refine ⟨651320466386429137277681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434213644257619424851787 651320466386429137277681)
                ·
                  refine ⟨488490349789821852958261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 651320466386429137277681 488490349789821852958261)
                  ·
                    refine ⟨45795970292795798714837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 488490349789821852958261 45795970292795798714837)
                    ·
                      rfl

theorem cell23_267562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_267562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267562 prefixEnd_267562 := by exact prefixLift 267562
  have htrace : WordTrace (prefixWord ++ tailWord_267562) baseStart_267562 baseEnd_267562 := by
    simpa [prefixWord, tailWord_267562, baseEnd_267562] using wordTrace_append hprefix tailTrace_267562
  have hstable : (prefixWord ++ tailWord_267562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267562).length < 2 ^ (prefixWord ++ tailWord_267562).sum := by decide
  have hdescent : baseEnd_267562 < baseStart_267562 := by decide
  rcases family_descends (prefixWord ++ tailWord_267562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267568 : List Nat := [2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 3]
def baseStart_267568 : Nat := 118140960795 + 267568 * 2 ^ 59
def prefixEnd_267568 : Nat := 4983230072969 + 3 ^ 40 * 267568 * 2
def baseEnd_267568 : Nat := 137390991762314372669483

theorem tailTrace_267568 : CollatzResearch.WordTrace tailWord_267568 prefixEnd_267568 137390991762314372669483 := by
  unfold tailWord_267568
  simp only [CollatzResearch.WordTrace]
  refine ⟨4879503347327153910693679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6506004463102871880924905 4879503347327153910693679)
  ·
    refine ⟨7319255020990730866040519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4879503347327153910693679 7319255020990730866040519)
    ·
      refine ⟨10978882531486096299060779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7319255020990730866040519 10978882531486096299060779)
      ·
        refine ⟨16468323797229144448591169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10978882531486096299060779 16468323797229144448591169)
        ·
          refine ⟨12351242847921858336443377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16468323797229144448591169 12351242847921858336443377)
          ·
            refine ⟨9263432135941393752332533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12351242847921858336443377 9263432135941393752332533)
            ·
              refine ⟨868446762744505664281175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9263432135941393752332533 868446762744505664281175)
              ·
                refine ⟨1302670144116758496421763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 868446762744505664281175 1302670144116758496421763)
                ·
                  refine ⟨1954005216175137744632645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1302670144116758496421763 1954005216175137744632645)
                  ·
                    refine ⟨366375978032838327118621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1954005216175137744632645 366375978032838327118621)
                    ·
                      refine ⟨137390991762314372669483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 366375978032838327118621 137390991762314372669483)
                      ·
                        rfl

theorem cell23_267568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 3].length) (baseStart_267568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267568 prefixEnd_267568 := by exact prefixLift 267568
  have htrace : WordTrace (prefixWord ++ tailWord_267568) baseStart_267568 baseEnd_267568 := by
    simpa [prefixWord, tailWord_267568, baseEnd_267568] using wordTrace_append hprefix tailTrace_267568
  have hstable : (prefixWord ++ tailWord_267568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267568).length < 2 ^ (prefixWord ++ tailWord_267568).sum := by decide
  have hdescent : baseEnd_267568 < baseStart_267568 := by decide
  rcases family_descends (prefixWord ++ tailWord_267568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267626 : List Nat := [3, 1, 3, 3, 2, 2, 1, 3, 1, 4]
def baseStart_267626 : Nat := 118140960795 + 267626 * 2 ^ 59
def prefixEnd_267626 : Nat := 4983230072969 + 3 ^ 40 * 267626 * 2
def baseEnd_267626 : Nat := 45806924546758381914739

theorem tailTrace_267626 : CollatzResearch.WordTrace tailWord_267626 prefixEnd_267626 45806924546758381914739 := by
  unfold tailWord_267626
  simp only [CollatzResearch.WordTrace]
  refine ⟨2440280532111045931749683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6507414752296122484665821 2440280532111045931749683)
  ·
    refine ⟨3660420798166568897624525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2440280532111045931749683 3660420798166568897624525)
    ·
      refine ⟨1372657799312463336609197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3660420798166568897624525 1372657799312463336609197)
      ·
        refine ⟨514746674742173751228449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1372657799312463336609197 514746674742173751228449)
        ·
          refine ⟨386060006056630313421337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 514746674742173751228449 386060006056630313421337)
          ·
            refine ⟨289545004542472735066003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386060006056630313421337 289545004542472735066003)
            ·
              refine ⟨434317506813709102599005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289545004542472735066003 434317506813709102599005)
              ·
                refine ⟨162869065055140913474627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 434317506813709102599005 162869065055140913474627)
                ·
                  refine ⟨244303597582711370211941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162869065055140913474627 244303597582711370211941)
                  ·
                    refine ⟨45806924546758381914739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 244303597582711370211941 45806924546758381914739)
                    ·
                      rfl

theorem cell23_267626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_267626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267626 prefixEnd_267626 := by exact prefixLift 267626
  have htrace : WordTrace (prefixWord ++ tailWord_267626) baseStart_267626 baseEnd_267626 := by
    simpa [prefixWord, tailWord_267626, baseEnd_267626] using wordTrace_append hprefix tailTrace_267626
  have hstable : (prefixWord ++ tailWord_267626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267626).length < 2 ^ (prefixWord ++ tailWord_267626).sum := by decide
  have hdescent : baseEnd_267626 < baseStart_267626 := by decide
  rcases family_descends (prefixWord ++ tailWord_267626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267665 : List Nat := [1, 2, 2, 1, 1, 1, 2, 7, 2, 4]
def baseStart_267665 : Nat := 118140960795 + 267665 * 2 ^ 59
def prefixEnd_267665 : Nat := 4983230072969 + 3 ^ 40 * 267665 * 2
def baseEnd_267665 : Nat := 45813599795266831052179

theorem tailTrace_267665 : CollatzResearch.WordTrace tailWord_267665 prefixEnd_267665 45813599795266831052179 := by
  unfold tailWord_267665
  simp only [CollatzResearch.WordTrace]
  refine ⟨9762544575302893387668449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6508363050201928925112299 9762544575302893387668449)
  ·
    refine ⟨7321908431477170040751337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9762544575302893387668449 7321908431477170040751337)
    ·
      refine ⟨5491431323607877530563503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7321908431477170040751337 5491431323607877530563503)
      ·
        refine ⟨8237146985411816295845255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5491431323607877530563503 8237146985411816295845255)
        ·
          refine ⟨12355720478117724443767883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8237146985411816295845255 12355720478117724443767883)
          ·
            refine ⟨18533580717176586665651825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12355720478117724443767883 18533580717176586665651825)
            ·
              refine ⟨13900185537882439999238869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18533580717176586665651825 13900185537882439999238869)
              ·
                refine ⟨325785598544119687482161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 13900185537882439999238869 325785598544119687482161)
                ·
                  refine ⟨244339198908089765611621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 325785598544119687482161 244339198908089765611621)
                  ·
                    refine ⟨45813599795266831052179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 244339198908089765611621 45813599795266831052179)
                    ·
                      rfl

theorem cell23_267665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 2, 4].length) (baseStart_267665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267665 prefixEnd_267665 := by exact prefixLift 267665
  have htrace : WordTrace (prefixWord ++ tailWord_267665) baseStart_267665 baseEnd_267665 := by
    simpa [prefixWord, tailWord_267665, baseEnd_267665] using wordTrace_append hprefix tailTrace_267665
  have hstable : (prefixWord ++ tailWord_267665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267665).length < 2 ^ (prefixWord ++ tailWord_267665).sum := by decide
  have hdescent : baseEnd_267665 < baseStart_267665 := by decide
  rcases family_descends (prefixWord ++ tailWord_267665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267672 : List Nat := [2, 1, 2, 5, 2, 1, 1, 1, 3, 1, 4]
def baseStart_267672 : Nat := 118140960795 + 267672 * 2 ^ 59
def prefixEnd_267672 : Nat := 4983230072969 + 3 ^ 40 * 267672 * 2
def baseEnd_267672 : Nat := 137444393750381965769005

theorem tailTrace_267672 : CollatzResearch.WordTrace tailWord_267672 prefixEnd_267672 137444393750381965769005 := by
  unfold tailWord_267672
  simp only [CollatzResearch.WordTrace]
  refine ⟨4881399943138766791586635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6508533257518355722115513 4881399943138766791586635)
  ·
    refine ⟨7322099914708150187379953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4881399943138766791586635 7322099914708150187379953)
    ·
      refine ⟨5491574936031112640534965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7322099914708150187379953 5491574936031112640534965)
      ·
        refine ⟨514835150252916810050153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5491574936031112640534965 514835150252916810050153)
        ·
          refine ⟨386126362689687607537615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 514835150252916810050153 386126362689687607537615)
          ·
            refine ⟨579189544034531411306423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386126362689687607537615 579189544034531411306423)
            ·
              refine ⟨868784316051797116959635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579189544034531411306423 868784316051797116959635)
              ·
                refine ⟨1303176474077695675439453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 868784316051797116959635 1303176474077695675439453)
                ·
                  refine ⟨488691177779135878289795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1303176474077695675439453 488691177779135878289795)
                  ·
                    refine ⟨733036766668703817434693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 488691177779135878289795 733036766668703817434693)
                    ·
                      refine ⟨137444393750381965769005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 733036766668703817434693 137444393750381965769005)
                      ·
                        rfl

theorem cell23_267672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_267672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267672 prefixEnd_267672 := by exact prefixLift 267672
  have htrace : WordTrace (prefixWord ++ tailWord_267672) baseStart_267672 baseEnd_267672 := by
    simpa [prefixWord, tailWord_267672, baseEnd_267672] using wordTrace_append hprefix tailTrace_267672
  have hstable : (prefixWord ++ tailWord_267672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267672).length < 2 ^ (prefixWord ++ tailWord_267672).sum := by decide
  have hdescent : baseEnd_267672 < baseStart_267672 := by decide
  rcases family_descends (prefixWord ++ tailWord_267672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267676 : List Nat := [2, 2, 3, 4, 1, 1, 2, 1, 2, 3, 2]
def baseStart_267676 : Nat := 118140960795 + 267676 * 2 ^ 59
def prefixEnd_267676 : Nat := 4983230072969 + 3 ^ 40 * 267676 * 2
def baseEnd_267676 : Nat := 137446447672999950118987

theorem tailTrace_267676 : CollatzResearch.WordTrace tailWord_267676 prefixEnd_267676 137446447672999950118987 := by
  unfold tailWord_267676
  simp only [CollatzResearch.WordTrace]
  refine ⟨4881472889131521133159441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6508630518842028177545921 4881472889131521133159441)
  ·
    refine ⟨3661104666848640849869581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4881472889131521133159441 3661104666848640849869581)
    ·
      refine ⟨1372914250068240318701093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3661104666848640849869581 1372914250068240318701093)
      ·
        refine ⟨257421421887795059756455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1372914250068240318701093 257421421887795059756455)
        ·
          refine ⟨386132132831692589634683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257421421887795059756455 386132132831692589634683)
          ·
            refine ⟨579198199247538884452025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386132132831692589634683 579198199247538884452025)
            ·
              refine ⟨434398649435654163339019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 579198199247538884452025 434398649435654163339019)
              ·
                refine ⟨651597974153481245008529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434398649435654163339019 651597974153481245008529)
                ·
                  refine ⟨488698480615110933756397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 651597974153481245008529 488698480615110933756397)
                  ·
                    refine ⟨183261930230666600158649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 488698480615110933756397 183261930230666600158649)
                    ·
                      refine ⟨137446447672999950118987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 183261930230666600158649 137446447672999950118987)
                      ·
                        rfl

theorem cell23_267676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_267676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267676 prefixEnd_267676 := by exact prefixLift 267676
  have htrace : WordTrace (prefixWord ++ tailWord_267676) baseStart_267676 baseEnd_267676 := by
    simpa [prefixWord, tailWord_267676, baseEnd_267676] using wordTrace_append hprefix tailTrace_267676
  have hstable : (prefixWord ++ tailWord_267676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267676).length < 2 ^ (prefixWord ++ tailWord_267676).sum := by decide
  have hdescent : baseEnd_267676 < baseStart_267676 := by decide
  rcases family_descends (prefixWord ++ tailWord_267676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267698 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6]
def baseStart_267698 : Nat := 118140960795 + 267698 * 2 ^ 59
def prefixEnd_267698 : Nat := 4983230072969 + 3 ^ 40 * 267698 * 2
def baseEnd_267698 : Nat := 137457744247398864043885

theorem tailTrace_267698 : CollatzResearch.WordTrace tailWord_267698 prefixEnd_267698 137457744247398864043885 := by
  unfold tailWord_267698
  simp only [CollatzResearch.WordTrace]
  refine ⟨2440937046045835005904937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6509165456122226682413165 2440937046045835005904937)
  ·
    refine ⟨1830702784534376254428703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2440937046045835005904937 1830702784534376254428703)
    ·
      refine ⟨2746054176801564381643055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1830702784534376254428703 2746054176801564381643055)
      ·
        refine ⟨4119081265202346572464583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2746054176801564381643055 4119081265202346572464583)
        ·
          refine ⟨6178621897803519858696875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4119081265202346572464583 6178621897803519858696875)
          ·
            refine ⟨9267932846705279788045313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6178621897803519858696875 9267932846705279788045313)
            ·
              refine ⟨6950949635028959841033985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9267932846705279788045313 6950949635028959841033985)
              ·
                refine ⟨5213212226271719880775489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6950949635028959841033985 5213212226271719880775489)
                ·
                  refine ⟨3909909169703789910581617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5213212226271719880775489 3909909169703789910581617)
                  ·
                    refine ⟨2932431877277842432936213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3909909169703789910581617 2932431877277842432936213)
                    ·
                      refine ⟨137457744247398864043885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2932431877277842432936213 137457744247398864043885)
                      ·
                        rfl

theorem cell23_267698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_267698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267698 prefixEnd_267698 := by exact prefixLift 267698
  have htrace : WordTrace (prefixWord ++ tailWord_267698) baseStart_267698 baseEnd_267698 := by
    simpa [prefixWord, tailWord_267698, baseEnd_267698] using wordTrace_append hprefix tailTrace_267698
  have hstable : (prefixWord ++ tailWord_267698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267698).length < 2 ^ (prefixWord ++ tailWord_267698).sum := by decide
  have hdescent : baseEnd_267698 < baseStart_267698 := by decide
  rcases family_descends (prefixWord ++ tailWord_267698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267722 : List Nat := [3, 1, 2, 1, 2, 4, 2, 1, 1, 3, 3]
def baseStart_267722 : Nat := 118140960795 + 267722 * 2 ^ 59
def prefixEnd_267722 : Nat := 4983230072969 + 3 ^ 40 * 267722 * 2
def baseEnd_267722 : Nat := 137470067783106770143775

theorem tailTrace_267722 : CollatzResearch.WordTrace tailWord_267722 prefixEnd_267722 137470067783106770143775 := by
  unfold tailWord_267722
  simp only [CollatzResearch.WordTrace]
  refine ⟨2441155884024098030623355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6509749024064261414995613 2441155884024098030623355)
  ·
    refine ⟨3661733826036147045935033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2441155884024098030623355 3661733826036147045935033)
    ·
      refine ⟨2746300369527110284451275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3661733826036147045935033 2746300369527110284451275)
      ·
        refine ⟨4119450554290665426676913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2746300369527110284451275 4119450554290665426676913)
        ·
          refine ⟨3089587915717999070007685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4119450554290665426676913 3089587915717999070007685)
          ·
            refine ⟨579297734197124825626441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3089587915717999070007685 579297734197124825626441)
            ·
              refine ⟨434473300647843619219831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 579297734197124825626441 434473300647843619219831)
              ·
                refine ⟨651709950971765428829747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434473300647843619219831 651709950971765428829747)
                ·
                  refine ⟨977564926457648143244621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 651709950971765428829747 977564926457648143244621)
                  ·
                    refine ⟨366586847421618053716733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 977564926457648143244621 366586847421618053716733)
                    ·
                      refine ⟨137470067783106770143775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 366586847421618053716733 137470067783106770143775)
                      ·
                        rfl

theorem cell23_267722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_267722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267722 prefixEnd_267722 := by exact prefixLift 267722
  have htrace : WordTrace (prefixWord ++ tailWord_267722) baseStart_267722 baseEnd_267722 := by
    simpa [prefixWord, tailWord_267722, baseEnd_267722] using wordTrace_append hprefix tailTrace_267722
  have hstable : (prefixWord ++ tailWord_267722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267722).length < 2 ^ (prefixWord ++ tailWord_267722).sum := by decide
  have hdescent : baseEnd_267722 < baseStart_267722 := by decide
  rcases family_descends (prefixWord ++ tailWord_267722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267852 : List Nat := [2, 2, 1, 3, 1, 3, 1, 3, 2, 1, 4]
def baseStart_267852 : Nat := 118140960795 + 267852 * 2 ^ 59
def prefixEnd_267852 : Nat := 4983230072969 + 3 ^ 40 * 267852 * 2
def baseEnd_267852 : Nat := 137536820268191261518177

theorem tailTrace_267852 : CollatzResearch.WordTrace tailWord_267852 prefixEnd_267852 137536820268191261518177 := by
  unfold tailWord_267852
  simp only [CollatzResearch.WordTrace]
  refine ⟨4884682512812712162362905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6512910017083616216483873 4884682512812712162362905)
  ·
    refine ⟨3663511884609534121772179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4884682512812712162362905 3663511884609534121772179)
    ·
      refine ⟨5495267826914301182658269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3663511884609534121772179 5495267826914301182658269)
      ·
        refine ⟨2060725435092862943496851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5495267826914301182658269 2060725435092862943496851)
        ·
          refine ⟨3091088152639294415245277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2060725435092862943496851 3091088152639294415245277)
          ·
            refine ⟨1159158057239735405716979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3091088152639294415245277 1159158057239735405716979)
            ·
              refine ⟨1738737085859603108575469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1159158057239735405716979 1738737085859603108575469)
              ·
                refine ⟨652026407197351165715801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1738737085859603108575469 652026407197351165715801)
                ·
                  refine ⟨489019805398013374286851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 652026407197351165715801 489019805398013374286851)
                  ·
                    refine ⟨733529708097020061430277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 489019805398013374286851 733529708097020061430277)
                    ·
                      refine ⟨137536820268191261518177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 733529708097020061430277 137536820268191261518177)
                      ·
                        rfl

theorem cell23_267852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_267852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267852 prefixEnd_267852 := by exact prefixLift 267852
  have htrace : WordTrace (prefixWord ++ tailWord_267852) baseStart_267852 baseEnd_267852 := by
    simpa [prefixWord, tailWord_267852, baseEnd_267852] using wordTrace_append hprefix tailTrace_267852
  have hstable : (prefixWord ++ tailWord_267852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267852).length < 2 ^ (prefixWord ++ tailWord_267852).sum := by decide
  have hdescent : baseEnd_267852 < baseStart_267852 := by decide
  rcases family_descends (prefixWord ++ tailWord_267852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267886 : List Nat := [4, 1, 2, 2, 3, 1, 1, 1, 2, 4, 2]
def baseStart_267886 : Nat := 118140960795 + 267886 * 2 ^ 59
def prefixEnd_267886 : Nat := 4983230072969 + 3 ^ 40 * 267886 * 2
def baseEnd_267886 : Nat := 137554278610444128493021

theorem tailTrace_267886 : CollatzResearch.WordTrace tailWord_267886 prefixEnd_267886 137554278610444128493021 := by
  unfold tailWord_267886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1221325638437781016432939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6513736738334832087642341 1221325638437781016432939)
  ·
    refine ⟨1831988457656671524649409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1221325638437781016432939 1831988457656671524649409)
    ·
      refine ⟨1373991343242503643487057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1831988457656671524649409 1373991343242503643487057)
      ·
        refine ⟨1030493507431877732615293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1373991343242503643487057 1030493507431877732615293)
        ·
          refine ⟨386435065286954149730735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1030493507431877732615293 386435065286954149730735)
          ·
            refine ⟨579652597930431224596103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386435065286954149730735 579652597930431224596103)
            ·
              refine ⟨869478896895646836894155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579652597930431224596103 869478896895646836894155)
              ·
                refine ⟨1304218345343470255341233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 869478896895646836894155 1304218345343470255341233)
                ·
                  refine ⟨978163759007602691505925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1304218345343470255341233 978163759007602691505925)
                  ·
                    refine ⟨183405704813925504657361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 978163759007602691505925 183405704813925504657361)
                    ·
                      refine ⟨137554278610444128493021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 183405704813925504657361 137554278610444128493021)
                      ·
                        rfl

theorem cell23_267886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_267886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267886 prefixEnd_267886 := by exact prefixLift 267886
  have htrace : WordTrace (prefixWord ++ tailWord_267886) baseStart_267886 baseEnd_267886 := by
    simpa [prefixWord, tailWord_267886, baseEnd_267886] using wordTrace_append hprefix tailTrace_267886
  have hstable : (prefixWord ++ tailWord_267886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267886).length < 2 ^ (prefixWord ++ tailWord_267886).sum := by decide
  have hdescent : baseEnd_267886 < baseStart_267886 := by decide
  rcases family_descends (prefixWord ++ tailWord_267886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267936 : List Nat := [2, 1, 1, 4, 3, 2, 2, 1, 3, 1, 3]
def baseStart_267936 : Nat := 118140960795 + 267936 * 2 ^ 59
def prefixEnd_267936 : Nat := 4983230072969 + 3 ^ 40 * 267936 * 2
def baseEnd_267936 : Nat := 137579952643168932867791

theorem tailTrace_267936 : CollatzResearch.WordTrace tailWord_267936 prefixEnd_267936 137579952643168932867791 := by
  unfold tailWord_267936
  simp only [CollatzResearch.WordTrace]
  refine ⟨4886214378660553335391831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6514952504880737780522441 4886214378660553335391831)
  ·
    refine ⟨7329321567990830003087747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4886214378660553335391831 7329321567990830003087747)
    ·
      refine ⟨10993982351986245004631621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7329321567990830003087747 10993982351986245004631621)
      ·
        refine ⟨2061371690997420938368429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10993982351986245004631621 2061371690997420938368429)
        ·
          refine ⟨773014384124032851888161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2061371690997420938368429 773014384124032851888161)
          ·
            refine ⟨579760788093024638916121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 773014384124032851888161 579760788093024638916121)
            ·
              refine ⟨434820591069768479187091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 579760788093024638916121 434820591069768479187091)
              ·
                refine ⟨652230886604652718780637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434820591069768479187091 652230886604652718780637)
                ·
                  refine ⟨244586582476744769542739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 652230886604652718780637 244586582476744769542739)
                  ·
                    refine ⟨366879873715117154314109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 244586582476744769542739 366879873715117154314109)
                    ·
                      refine ⟨137579952643168932867791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 366879873715117154314109 137579952643168932867791)
                      ·
                        rfl

theorem cell23_267936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_267936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267936 prefixEnd_267936 := by exact prefixLift 267936
  have htrace : WordTrace (prefixWord ++ tailWord_267936) baseStart_267936 baseEnd_267936 := by
    simpa [prefixWord, tailWord_267936, baseEnd_267936] using wordTrace_append hprefix tailTrace_267936
  have hstable : (prefixWord ++ tailWord_267936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267936).length < 2 ^ (prefixWord ++ tailWord_267936).sum := by decide
  have hdescent : baseEnd_267936 < baseStart_267936 := by decide
  rcases family_descends (prefixWord ++ tailWord_267936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267945 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 2, 5, 5]
def baseStart_267945 : Nat := 118140960795 + 267945 * 2 ^ 59
def prefixEnd_267945 : Nat := 4983230072969 + 3 ^ 40 * 267945 * 2
def baseEnd_267945 : Nat := 137584573969059397655249

theorem tailTrace_267945 : CollatzResearch.WordTrace tailWord_267945 prefixEnd_267945 137584573969059397655249 := by
  unfold tailWord_267945
  simp only [CollatzResearch.WordTrace]
  refine ⟨9772757014288501207861289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6515171342859000805240859 9772757014288501207861289)
  ·
    refine ⟨7329567760716375905895967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9772757014288501207861289 7329567760716375905895967)
    ·
      refine ⟨10994351641074563858843951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7329567760716375905895967 10994351641074563858843951)
      ·
        refine ⟨16491527461611845788265927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10994351641074563858843951 16491527461611845788265927)
        ·
          refine ⟨24737291192417768682398891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16491527461611845788265927 24737291192417768682398891)
          ·
            refine ⟨37105936788626653023598337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24737291192417768682398891 37105936788626653023598337)
            ·
              refine ⟨27829452591469989767698753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37105936788626653023598337 27829452591469989767698753)
              ·
                refine ⟨20872089443602492325774065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27829452591469989767698753 20872089443602492325774065)
                ·
                  refine ⟨15654067082701869244330549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20872089443602492325774065 15654067082701869244330549)
                  ·
                    refine ⟨1467568789003300241655989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15654067082701869244330549 1467568789003300241655989)
                    ·
                      refine ⟨137584573969059397655249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1467568789003300241655989 137584573969059397655249)
                      ·
                        rfl

theorem cell23_267945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 5, 5].length) (baseStart_267945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267945 prefixEnd_267945 := by exact prefixLift 267945
  have htrace : WordTrace (prefixWord ++ tailWord_267945) baseStart_267945 baseEnd_267945 := by
    simpa [prefixWord, tailWord_267945, baseEnd_267945] using wordTrace_append hprefix tailTrace_267945
  have hstable : (prefixWord ++ tailWord_267945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267945).length < 2 ^ (prefixWord ++ tailWord_267945).sum := by decide
  have hdescent : baseEnd_267945 < baseStart_267945 := by decide
  rcases family_descends (prefixWord ++ tailWord_267945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267952 : List Nat := [2, 1, 1, 1, 2, 1, 7, 1, 1, 6]
def baseStart_267952 : Nat := 118140960795 + 267952 * 2 ^ 59
def prefixEnd_267952 : Nat := 4983230072969 + 3 ^ 40 * 267952 * 2
def baseEnd_267952 : Nat := 45862722777880290089239

theorem tailTrace_267952 : CollatzResearch.WordTrace tailWord_267952 prefixEnd_267952 45862722777880290089239 := by
  unfold tailWord_267952
  simp only [CollatzResearch.WordTrace]
  refine ⟨4886506162631570701683055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6515341550175427602244073 4886506162631570701683055)
  ·
    refine ⟨7329759243947356052524583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4886506162631570701683055 7329759243947356052524583)
    ·
      refine ⟨10994638865921034078786875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7329759243947356052524583 10994638865921034078786875)
      ·
        refine ⟨16491958298881551118180313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10994638865921034078786875 16491958298881551118180313)
        ·
          refine ⟨12368968724161163338635235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16491958298881551118180313 12368968724161163338635235)
          ·
            refine ⟨18553453086241745007952853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12368968724161163338635235 18553453086241745007952853)
            ·
              refine ⟨434846556708790898623895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 18553453086241745007952853 434846556708790898623895)
              ·
                refine ⟨652269835063186347935843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434846556708790898623895 652269835063186347935843)
                ·
                  refine ⟨978404752594779521903765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 652269835063186347935843 978404752594779521903765)
                  ·
                    refine ⟨45862722777880290089239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 978404752594779521903765 45862722777880290089239)
                    ·
                      rfl

theorem cell23_267952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 1, 6].length) (baseStart_267952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267952 prefixEnd_267952 := by exact prefixLift 267952
  have htrace : WordTrace (prefixWord ++ tailWord_267952) baseStart_267952 baseEnd_267952 := by
    simpa [prefixWord, tailWord_267952, baseEnd_267952] using wordTrace_append hprefix tailTrace_267952
  have hstable : (prefixWord ++ tailWord_267952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267952).length < 2 ^ (prefixWord ++ tailWord_267952).sum := by decide
  have hdescent : baseEnd_267952 < baseStart_267952 := by decide
  rcases family_descends (prefixWord ++ tailWord_267952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267959 : List Nat := [1, 1, 3, 1, 5, 1, 1, 4, 1, 1, 4]
def baseStart_267959 : Nat := 118140960795 + 267959 * 2 ^ 59
def prefixEnd_267959 : Nat := 4983230072969 + 3 ^ 40 * 267959 * 2
def baseEnd_267959 : Nat := 137591762698222342880185

theorem tailTrace_267959 : CollatzResearch.WordTrace tailWord_267959 prefixEnd_267959 137591762698222342880185 := by
  unfold tailWord_267959
  simp only [CollatzResearch.WordTrace]
  refine ⟨9773267636237781598870931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6515511757491854399247287 9773267636237781598870931)
  ·
    refine ⟨14659901454356672398306397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9773267636237781598870931 14659901454356672398306397)
    ·
      refine ⟨5497463045383752149364899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14659901454356672398306397 5497463045383752149364899)
      ·
        refine ⟨8246194568075628224047349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5497463045383752149364899 8246194568075628224047349)
        ·
          refine ⟨773080740757090146004439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8246194568075628224047349 773080740757090146004439)
          ·
            refine ⟨1159621111135635219006659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 773080740757090146004439 1159621111135635219006659)
            ·
              refine ⟨1739431666703452828509989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1159621111135635219006659 1739431666703452828509989)
              ·
                refine ⟨326143437506897405345623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1739431666703452828509989 326143437506897405345623)
                ·
                  refine ⟨489215156260346108018435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 326143437506897405345623 489215156260346108018435)
                  ·
                    refine ⟨733822734390519162027653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 489215156260346108018435 733822734390519162027653)
                    ·
                      refine ⟨137591762698222342880185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 733822734390519162027653 137591762698222342880185)
                      ·
                        rfl

theorem cell23_267959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 1, 4].length) (baseStart_267959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267959 prefixEnd_267959 := by exact prefixLift 267959
  have htrace : WordTrace (prefixWord ++ tailWord_267959) baseStart_267959 baseEnd_267959 := by
    simpa [prefixWord, tailWord_267959, baseEnd_267959] using wordTrace_append hprefix tailTrace_267959
  have hstable : (prefixWord ++ tailWord_267959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267959).length < 2 ^ (prefixWord ++ tailWord_267959).sum := by decide
  have hdescent : baseEnd_267959 < baseStart_267959 := by decide
  rcases family_descends (prefixWord ++ tailWord_267959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267993 : List Nat := [1, 2, 1, 2, 3, 5, 1, 1, 3, 2, 2]
def baseStart_267993 : Nat := 118140960795 + 267993 * 2 ^ 59
def prefixEnd_267993 : Nat := 4983230072969 + 3 ^ 40 * 267993 * 2
def baseEnd_267993 : Nat := 137609221040475209855029

theorem tailTrace_267993 : CollatzResearch.WordTrace tailWord_267993 prefixEnd_267993 137609221040475209855029 := by
  unfold tailWord_267993
  simp only [CollatzResearch.WordTrace]
  refine ⟨9774507718114605405608633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6516338478743070270405755 9774507718114605405608633)
  ·
    refine ⟨7330880788585954054206475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9774507718114605405608633 7330880788585954054206475)
    ·
      refine ⟨10996321182878931081309713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7330880788585954054206475 10996321182878931081309713)
      ·
        refine ⟨8247240887159198310982285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10996321182878931081309713 8247240887159198310982285)
        ·
          refine ⟨3092715332684699366618357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8247240887159198310982285 3092715332684699366618357)
          ·
            refine ⟨289942062439190565620471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3092715332684699366618357 289942062439190565620471)
            ·
              refine ⟨434913093658785848430707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289942062439190565620471 434913093658785848430707)
              ·
                refine ⟨652369640488178772646061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434913093658785848430707 652369640488178772646061)
                ·
                  refine ⟨244638615183067039742273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 652369640488178772646061 244638615183067039742273)
                  ·
                    refine ⟨183478961387300279806705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 244638615183067039742273 183478961387300279806705)
                    ·
                      refine ⟨137609221040475209855029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 183478961387300279806705 137609221040475209855029)
                      ·
                        rfl

theorem cell23_267993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 3, 2, 2].length) (baseStart_267993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_267993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_267993 prefixEnd_267993 := by exact prefixLift 267993
  have htrace : WordTrace (prefixWord ++ tailWord_267993) baseStart_267993 baseEnd_267993 := by
    simpa [prefixWord, tailWord_267993, baseEnd_267993] using wordTrace_append hprefix tailTrace_267993
  have hstable : (prefixWord ++ tailWord_267993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267993).length < 2 ^ (prefixWord ++ tailWord_267993).sum := by decide
  have hdescent : baseEnd_267993 < baseStart_267993 := by decide
  rcases family_descends (prefixWord ++ tailWord_267993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268013 : List Nat := [1, 5, 1, 2, 1, 4, 1, 2, 1, 2, 3]
def baseStart_268013 : Nat := 118140960795 + 268013 * 2 ^ 59
def prefixEnd_268013 : Nat := 4983230072969 + 3 ^ 40 * 268013 * 2
def baseEnd_268013 : Nat := 137619490653565131604937

theorem tailTrace_268013 : CollatzResearch.WordTrace tailWord_268013 prefixEnd_268013 137619490653565131604937 := by
  unfold tailWord_268013
  simp only [CollatzResearch.WordTrace]
  refine ⟨9775237178042148821336693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6516824785361432547557795 9775237178042148821336693)
  ·
    refine ⟨916428485441451452000315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9775237178042148821336693 916428485441451452000315)
    ·
      refine ⟨1374642728162177178000473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 916428485441451452000315 1374642728162177178000473)
      ·
        refine ⟨1030982046121632883500355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1374642728162177178000473 1030982046121632883500355)
        ·
          refine ⟨1546473069182449325250533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1030982046121632883500355 1546473069182449325250533)
          ·
            refine ⟨289963700471709248484475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1546473069182449325250533 289963700471709248484475)
            ·
              refine ⟨434945550707563872726713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289963700471709248484475 434945550707563872726713)
              ·
                refine ⟨326209163030672904545035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 434945550707563872726713 326209163030672904545035)
                ·
                  refine ⟨489313744546009356817553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 326209163030672904545035 489313744546009356817553)
                  ·
                    refine ⟨366985308409507017613165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 489313744546009356817553 366985308409507017613165)
                    ·
                      refine ⟨137619490653565131604937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 366985308409507017613165 137619490653565131604937)
                      ·
                        rfl

theorem cell23_268013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_268013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268013 prefixEnd_268013 := by exact prefixLift 268013
  have htrace : WordTrace (prefixWord ++ tailWord_268013) baseStart_268013 baseEnd_268013 := by
    simpa [prefixWord, tailWord_268013, baseEnd_268013] using wordTrace_append hprefix tailTrace_268013
  have hstable : (prefixWord ++ tailWord_268013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268013).length < 2 ^ (prefixWord ++ tailWord_268013).sum := by decide
  have hdescent : baseEnd_268013 < baseStart_268013 := by decide
  rcases family_descends (prefixWord ++ tailWord_268013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268030 : List Nat := [4, 2, 2, 1, 3, 1, 3, 1, 1, 2, 3]
def baseStart_268030 : Nat := 118140960795 + 268030 * 2 ^ 59
def prefixEnd_268030 : Nat := 4983230072969 + 3 ^ 40 * 268030 * 2
def baseEnd_268030 : Nat := 137628219824691565092359

theorem tailTrace_268030 : CollatzResearch.WordTrace tailWord_268030 prefixEnd_268030 137628219824691565092359 := by
  unfold tailWord_268030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1221982152372570090588193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6517238145987040483137029 1221982152372570090588193)
  ·
    refine ⟨916486614279427567941145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1221982152372570090588193 916486614279427567941145)
    ·
      refine ⟨687364960709570675955859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 916486614279427567941145 687364960709570675955859)
      ·
        refine ⟨1031047441064356013933789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687364960709570675955859 1031047441064356013933789)
        ·
          refine ⟨386642790399133505225171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1031047441064356013933789 386642790399133505225171)
          ·
            refine ⟨579964185598700257837757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386642790399133505225171 579964185598700257837757)
            ·
              refine ⟨217486569599512596689159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 579964185598700257837757 217486569599512596689159)
              ·
                refine ⟨326229854399268895033739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217486569599512596689159 326229854399268895033739)
                ·
                  refine ⟨489344781598903342550609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 326229854399268895033739 489344781598903342550609)
                  ·
                    refine ⟨367008586199177506912957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 489344781598903342550609 367008586199177506912957)
                    ·
                      refine ⟨137628219824691565092359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 367008586199177506912957 137628219824691565092359)
                      ·
                        rfl

theorem cell23_268030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_268030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268030 prefixEnd_268030 := by exact prefixLift 268030
  have htrace : WordTrace (prefixWord ++ tailWord_268030) baseStart_268030 baseEnd_268030 := by
    simpa [prefixWord, tailWord_268030, baseEnd_268030] using wordTrace_append hprefix tailTrace_268030
  have hstable : (prefixWord ++ tailWord_268030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268030).length < 2 ^ (prefixWord ++ tailWord_268030).sum := by decide
  have hdescent : baseEnd_268030 < baseStart_268030 := by decide
  rcases family_descends (prefixWord ++ tailWord_268030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268049 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 5, 4, 2]
def baseStart_268049 : Nat := 118140960795 + 268049 * 2 ^ 59
def prefixEnd_268049 : Nat := 4983230072969 + 3 ^ 40 * 268049 * 2
def baseEnd_268049 : Nat := 137637975957126990754771

theorem tailTrace_268049 : CollatzResearch.WordTrace tailWord_268049 prefixEnd_268049 137637975957126990754771 := by
  unfold tailWord_268049
  simp only [CollatzResearch.WordTrace]
  refine ⟨9776550205911726969647201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6517700137274484646431467 9776550205911726969647201)
  ·
    refine ⟨7332412654433795227235401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9776550205911726969647201 7332412654433795227235401)
    ·
      refine ⟨5499309490825346420426551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7332412654433795227235401 5499309490825346420426551)
      ·
        refine ⟨8248964236238019630639827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5499309490825346420426551 8248964236238019630639827)
        ·
          refine ⟨12373446354357029445959741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8248964236238019630639827 12373446354357029445959741)
          ·
            refine ⟨4640042382883886042234903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12373446354357029445959741 4640042382883886042234903)
            ·
              refine ⟨6960063574325829063352355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4640042382883886042234903 6960063574325829063352355)
              ·
                refine ⟨10440095361488743595028533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6960063574325829063352355 10440095361488743595028533)
                ·
                  refine ⟨978758940139569712033925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10440095361488743595028533 978758940139569712033925)
                  ·
                    refine ⟨183517301276169321006361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 978758940139569712033925 183517301276169321006361)
                    ·
                      refine ⟨137637975957126990754771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 183517301276169321006361 137637975957126990754771)
                      ·
                        rfl

theorem cell23_268049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 4, 2].length) (baseStart_268049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268049 prefixEnd_268049 := by exact prefixLift 268049
  have htrace : WordTrace (prefixWord ++ tailWord_268049) baseStart_268049 baseEnd_268049 := by
    simpa [prefixWord, tailWord_268049, baseEnd_268049] using wordTrace_append hprefix tailTrace_268049
  have hstable : (prefixWord ++ tailWord_268049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268049).length < 2 ^ (prefixWord ++ tailWord_268049).sum := by decide
  have hdescent : baseEnd_268049 < baseStart_268049 := by decide
  rcases family_descends (prefixWord ++ tailWord_268049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268099 : List Nat := [1, 1, 1, 3, 1, 5, 1, 2, 2, 3, 3]
def baseStart_268099 : Nat := 118140960795 + 268099 * 2 ^ 59
def prefixEnd_268099 : Nat := 4983230072969 + 3 ^ 40 * 268099 * 2
def baseEnd_268099 : Nat := 137663649989851795129541

theorem tailTrace_268099 : CollatzResearch.WordTrace tailWord_268099 prefixEnd_268099 137663649989851795129541 := by
  unfold tailWord_268099
  simp only [CollatzResearch.WordTrace]
  refine ⟨9778373855730585508967351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6518915903820390339311567 9778373855730585508967351)
  ·
    refine ⟨14667560783595878263451027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9778373855730585508967351 14667560783595878263451027)
    ·
      refine ⟨22001341175393817395176541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14667560783595878263451027 22001341175393817395176541)
      ·
        refine ⟨8250502940772681523191203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22001341175393817395176541 8250502940772681523191203)
        ·
          refine ⟨12375754411159022284786805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8250502940772681523191203 12375754411159022284786805)
          ·
            refine ⟨1160226976046158339198763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12375754411159022284786805 1160226976046158339198763)
            ·
              refine ⟨1740340464069237508798145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1160226976046158339198763 1740340464069237508798145)
              ·
                refine ⟨1305255348051928131598609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1740340464069237508798145 1305255348051928131598609)
                ·
                  refine ⟨978941511038946098698957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1305255348051928131598609 978941511038946098698957)
                  ·
                    refine ⟨367103066639604787012109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 978941511038946098698957 367103066639604787012109)
                    ·
                      refine ⟨137663649989851795129541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 367103066639604787012109 137663649989851795129541)
                      ·
                        rfl

theorem cell23_268099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 3, 3].length) (baseStart_268099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268099 prefixEnd_268099 := by exact prefixLift 268099
  have htrace : WordTrace (prefixWord ++ tailWord_268099) baseStart_268099 baseEnd_268099 := by
    simpa [prefixWord, tailWord_268099, baseEnd_268099] using wordTrace_append hprefix tailTrace_268099
  have hstable : (prefixWord ++ tailWord_268099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268099).length < 2 ^ (prefixWord ++ tailWord_268099).sum := by decide
  have hdescent : baseEnd_268099 < baseStart_268099 := by decide
  rcases family_descends (prefixWord ++ tailWord_268099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268112 : List Nat := [2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 7]
def baseStart_268112 : Nat := 118140960795 + 268112 * 2 ^ 59
def prefixEnd_268112 : Nat := 4983230072969 + 3 ^ 40 * 268112 * 2
def baseEnd_268112 : Nat := 137670325238360244266981

theorem tailTrace_268112 : CollatzResearch.WordTrace tailWord_268112 prefixEnd_268112 137670325238360244266981 := by
  unfold tailWord_268112
  simp only [CollatzResearch.WordTrace]
  refine ⟨4889424002341744364595295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6519232003122325819460393 4889424002341744364595295)
  ·
    refine ⟨7334136003512616546892943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4889424002341744364595295 7334136003512616546892943)
    ·
      refine ⟨11001204005268924820339415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7334136003512616546892943 11001204005268924820339415)
      ·
        refine ⟨16501806007903387230509123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11001204005268924820339415 16501806007903387230509123)
        ·
          refine ⟨24752709011855080845763685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16501806007903387230509123 24752709011855080845763685)
          ·
            refine ⟨4641132939722827658580691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24752709011855080845763685 4641132939722827658580691)
            ·
              refine ⟨6961699409584241487871037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4641132939722827658580691 6961699409584241487871037)
              ·
                refine ⟨2610637278594090557951639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6961699409584241487871037 2610637278594090557951639)
                ·
                  refine ⟨3915955917891135836927459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2610637278594090557951639 3915955917891135836927459)
                  ·
                    refine ⟨5873933876836703755391189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3915955917891135836927459 5873933876836703755391189)
                    ·
                      refine ⟨137670325238360244266981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 5873933876836703755391189 137670325238360244266981)
                      ·
                        rfl

theorem cell23_268112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 7].length) (baseStart_268112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268112 prefixEnd_268112 := by exact prefixLift 268112
  have htrace : WordTrace (prefixWord ++ tailWord_268112) baseStart_268112 baseEnd_268112 := by
    simpa [prefixWord, tailWord_268112, baseEnd_268112] using wordTrace_append hprefix tailTrace_268112
  have hstable : (prefixWord ++ tailWord_268112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268112).length < 2 ^ (prefixWord ++ tailWord_268112).sum := by decide
  have hdescent : baseEnd_268112 < baseStart_268112 := by decide
  rcases family_descends (prefixWord ++ tailWord_268112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268116 : List Nat := [2, 4, 1, 1, 3, 1, 2, 1, 2, 3, 3]
def baseStart_268116 : Nat := 118140960795 + 268116 * 2 ^ 59
def prefixEnd_268116 : Nat := 4983230072969 + 3 ^ 40 * 268116 * 2
def baseEnd_268116 : Nat := 137672379160978228616963

theorem tailTrace_268116 : CollatzResearch.WordTrace tailWord_268116 prefixEnd_268116 137672379160978228616963 := by
  unfold tailWord_268116
  simp only [CollatzResearch.WordTrace]
  refine ⟨4889496948334498706168101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6519329264445998274890801 4889496948334498706168101)
  ·
    refine ⟨916780677812718507406519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4889496948334498706168101 916780677812718507406519)
    ·
      refine ⟨1375171016719077761109779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 916780677812718507406519 1375171016719077761109779)
      ·
        refine ⟨2062756525078616641664669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1375171016719077761109779 2062756525078616641664669)
        ·
          refine ⟨773533696904481240624251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2062756525078616641664669 773533696904481240624251)
          ·
            refine ⟨1160300545356721860936377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 773533696904481240624251 1160300545356721860936377)
            ·
              refine ⟨870225409017541395702283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1160300545356721860936377 870225409017541395702283)
              ·
                refine ⟨1305338113526312093553425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 870225409017541395702283 1305338113526312093553425)
                ·
                  refine ⟨979003585144734070165069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1305338113526312093553425 979003585144734070165069)
                  ·
                    refine ⟨367126344429275276311901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 979003585144734070165069 367126344429275276311901)
                    ·
                      refine ⟨137672379160978228616963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 367126344429275276311901 137672379160978228616963)
                      ·
                        rfl

theorem cell23_268116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_268116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268116 prefixEnd_268116 := by exact prefixLift 268116
  have htrace : WordTrace (prefixWord ++ tailWord_268116) baseStart_268116 baseEnd_268116 := by
    simpa [prefixWord, tailWord_268116, baseEnd_268116] using wordTrace_append hprefix tailTrace_268116
  have hstable : (prefixWord ++ tailWord_268116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268116).length < 2 ^ (prefixWord ++ tailWord_268116).sum := by decide
  have hdescent : baseEnd_268116 < baseStart_268116 := by decide
  rcases family_descends (prefixWord ++ tailWord_268116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268139 : List Nat := [1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 4]
def baseStart_268139 : Nat := 118140960795 + 268139 * 2 ^ 59
def prefixEnd_268139 : Nat := 4983230072969 + 3 ^ 40 * 268139 * 2
def baseEnd_268139 : Nat := 137684189216031638629357

theorem tailTrace_268139 : CollatzResearch.WordTrace tailWord_268139 prefixEnd_268139 137684189216031638629357 := by
  unfold tailWord_268139
  simp only [CollatzResearch.WordTrace]
  refine ⟨9779832775585672340423471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6519888517057114893615647 9779832775585672340423471)
  ·
    refine ⟨14669749163378508510635207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9779832775585672340423471 14669749163378508510635207)
    ·
      refine ⟨22004623745067762765952811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14669749163378508510635207 22004623745067762765952811)
      ·
        refine ⟨33006935617601644148929217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22004623745067762765952811 33006935617601644148929217)
        ·
          refine ⟨24755201713201233111696913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33006935617601644148929217 24755201713201233111696913)
          ·
            refine ⟨18566401284900924833772685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24755201713201233111696913 18566401284900924833772685)
            ·
              refine ⟨6962400481837846812664757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18566401284900924833772685 6962400481837846812664757)
              ·
                refine ⟨652725045172298138687321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6962400481837846812664757 652725045172298138687321)
                ·
                  refine ⟨489543783879223604015491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 652725045172298138687321 489543783879223604015491)
                  ·
                    refine ⟨734315675818835406023237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 489543783879223604015491 734315675818835406023237)
                    ·
                      refine ⟨137684189216031638629357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 734315675818835406023237 137684189216031638629357)
                      ·
                        rfl

theorem cell23_268139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 4].length) (baseStart_268139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268139 prefixEnd_268139 := by exact prefixLift 268139
  have htrace : WordTrace (prefixWord ++ tailWord_268139) baseStart_268139 baseEnd_268139 := by
    simpa [prefixWord, tailWord_268139, baseEnd_268139] using wordTrace_append hprefix tailTrace_268139
  have hstable : (prefixWord ++ tailWord_268139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268139).length < 2 ^ (prefixWord ++ tailWord_268139).sum := by decide
  have hdescent : baseEnd_268139 < baseStart_268139 := by decide
  rcases family_descends (prefixWord ++ tailWord_268139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268266 : List Nat := [3, 1, 3, 1, 2, 1, 2, 3, 1, 1, 5]
def baseStart_268266 : Nat := 118140960795 + 268266 * 2 ^ 59
def prefixEnd_268266 : Nat := 4983230072969 + 3 ^ 40 * 268266 * 2
def baseEnd_268266 : Nat := 137749401259152641741273

theorem tailTrace_268266 : CollatzResearch.WordTrace tailWord_268266 prefixEnd_268266 137749401259152641741273 := by
  unfold tailWord_268266
  simp only [CollatzResearch.WordTrace]
  refine ⟨2446116211531393257574163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6522976564083715353531101 2446116211531393257574163)
  ·
    refine ⟨3669174317297089886361245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2446116211531393257574163 3669174317297089886361245)
    ·
      refine ⟨1375940368986408707385467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3669174317297089886361245 1375940368986408707385467)
      ·
        refine ⟨2063910553479613061078201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1375940368986408707385467 2063910553479613061078201)
        ·
          refine ⟨1547932915109709795808651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2063910553479613061078201 1547932915109709795808651)
          ·
            refine ⟨2321899372664564693712977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1547932915109709795808651 2321899372664564693712977)
            ·
              refine ⟨1741424529498423520284733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2321899372664564693712977 1741424529498423520284733)
              ·
                refine ⟨653034198561908820106775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1741424529498423520284733 653034198561908820106775)
                ·
                  refine ⟨979551297842863230160163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 653034198561908820106775 979551297842863230160163)
                  ·
                    refine ⟨1469326946764294845240245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 979551297842863230160163 1469326946764294845240245)
                    ·
                      refine ⟨137749401259152641741273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1469326946764294845240245 137749401259152641741273)
                      ·
                        rfl

theorem cell23_268266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_268266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268266 prefixEnd_268266 := by exact prefixLift 268266
  have htrace : WordTrace (prefixWord ++ tailWord_268266) baseStart_268266 baseEnd_268266 := by
    simpa [prefixWord, tailWord_268266, baseEnd_268266] using wordTrace_append hprefix tailTrace_268266
  have hstable : (prefixWord ++ tailWord_268266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268266).length < 2 ^ (prefixWord ++ tailWord_268266).sum := by decide
  have hdescent : baseEnd_268266 < baseStart_268266 := by decide
  rcases family_descends (prefixWord ++ tailWord_268266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268273 : List Nat := [1, 2, 2, 2, 5, 1, 1, 1, 4, 4]
def baseStart_268273 : Nat := 118140960795 + 268273 * 2 ^ 59
def prefixEnd_268273 : Nat := 4983230072969 + 3 ^ 40 * 268273 * 2
def baseEnd_268273 : Nat := 45917665207911371451247

theorem tailTrace_268273 : CollatzResearch.WordTrace tailWord_268273 prefixEnd_268273 45917665207911371451247 := by
  unfold tailWord_268273
  simp only [CollatzResearch.WordTrace]
  refine ⟨9784720157100213225801473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6523146771400142150534315 9784720157100213225801473)
  ·
    refine ⟨7338540117825159919351105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9784720157100213225801473 7338540117825159919351105)
    ·
      refine ⟨5503905088368869939513329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7338540117825159919351105 5503905088368869939513329)
      ·
        refine ⟨4127928816276652454634997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5503905088368869939513329 4127928816276652454634997)
        ·
          refine ⟨386993326525936167622031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4127928816276652454634997 386993326525936167622031)
          ·
            refine ⟨580489989788904251433047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386993326525936167622031 580489989788904251433047)
            ·
              refine ⟨870734984683356377149571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 580489989788904251433047 870734984683356377149571)
              ·
                refine ⟨1306102477025034565724357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 870734984683356377149571 1306102477025034565724357)
                ·
                  refine ⟨244894214442193981073317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1306102477025034565724357 244894214442193981073317)
                  ·
                    refine ⟨45917665207911371451247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 244894214442193981073317 45917665207911371451247)
                    ·
                      rfl

theorem cell23_268273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 4, 4].length) (baseStart_268273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268273 prefixEnd_268273 := by exact prefixLift 268273
  have htrace : WordTrace (prefixWord ++ tailWord_268273) baseStart_268273 baseEnd_268273 := by
    simpa [prefixWord, tailWord_268273, baseEnd_268273] using wordTrace_append hprefix tailTrace_268273
  have hstable : (prefixWord ++ tailWord_268273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268273).length < 2 ^ (prefixWord ++ tailWord_268273).sum := by decide
  have hdescent : baseEnd_268273 < baseStart_268273 := by decide
  rcases family_descends (prefixWord ++ tailWord_268273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268293 : List Nat := [1, 3, 1, 1, 2, 6, 1, 1, 1, 2, 4]
def baseStart_268293 : Nat := 118140960795 + 268293 * 2 ^ 59
def prefixEnd_268293 : Nat := 4983230072969 + 3 ^ 40 * 268293 * 2
def baseEnd_268293 : Nat := 137763265236824036103649

theorem tailTrace_268293 : CollatzResearch.WordTrace tailWord_268293 prefixEnd_268293 137763265236824036103649 := by
  unfold tailWord_268293
  simp only [CollatzResearch.WordTrace]
  refine ⟨9785449617027756641529533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6523633078018504427686355 9785449617027756641529533)
  ·
    refine ⟨3669543606385408740573575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9785449617027756641529533 3669543606385408740573575)
    ·
      refine ⟨5504315409578113110860363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3669543606385408740573575 5504315409578113110860363)
      ·
        refine ⟨8256473114367169666290545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5504315409578113110860363 8256473114367169666290545)
        ·
          refine ⟨6192354835775377249717909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8256473114367169666290545 6192354835775377249717909)
          ·
            refine ⟨290266632926970808580527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6192354835775377249717909 290266632926970808580527)
            ·
              refine ⟨435399949390456212870791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290266632926970808580527 435399949390456212870791)
              ·
                refine ⟨653099924085684319306187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 435399949390456212870791 653099924085684319306187)
                ·
                  refine ⟨979649886128526478959281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 653099924085684319306187 979649886128526478959281)
                  ·
                    refine ⟨734737414596394859219461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 979649886128526478959281 734737414596394859219461)
                    ·
                      refine ⟨137763265236824036103649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 734737414596394859219461 137763265236824036103649)
                      ·
                        rfl

theorem cell23_268293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 2, 4].length) (baseStart_268293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268293 prefixEnd_268293 := by exact prefixLift 268293
  have htrace : WordTrace (prefixWord ++ tailWord_268293) baseStart_268293 baseEnd_268293 := by
    simpa [prefixWord, tailWord_268293, baseEnd_268293] using wordTrace_append hprefix tailTrace_268293
  have hstable : (prefixWord ++ tailWord_268293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268293).length < 2 ^ (prefixWord ++ tailWord_268293).sum := by decide
  have hdescent : baseEnd_268293 < baseStart_268293 := by decide
  rcases family_descends (prefixWord ++ tailWord_268293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268308 : List Nat := [2, 4, 3, 2, 2, 1, 1, 3, 1, 1, 3]
def baseStart_268308 : Nat := 118140960795 + 268308 * 2 ^ 59
def prefixEnd_268308 : Nat := 4983230072969 + 3 ^ 40 * 268308 * 2
def baseEnd_268308 : Nat := 137770967446641477416081

theorem tailTrace_268308 : CollatzResearch.WordTrace tailWord_268308 prefixEnd_268308 137770967446641477416081 := by
  unfold tailWord_268308
  simp only [CollatzResearch.WordTrace]
  refine ⟨4892998355986707101662789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6523997807982276135550385 4892998355986707101662789)
  ·
    refine ⟨917437191747507581561773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4892998355986707101662789 917437191747507581561773)
    ·
      refine ⟨344038946905315343085665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 917437191747507581561773 344038946905315343085665)
      ·
        refine ⟨258029210178986507314249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344038946905315343085665 258029210178986507314249)
        ·
          refine ⟨193521907634239880485687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258029210178986507314249 193521907634239880485687)
          ·
            refine ⟨290282861451359820728531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193521907634239880485687 290282861451359820728531)
            ·
              refine ⟨435424292177039731092797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290282861451359820728531 435424292177039731092797)
              ·
                refine ⟨163284109566389899159799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 435424292177039731092797 163284109566389899159799)
                ·
                  refine ⟨244926164349584848739699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163284109566389899159799 244926164349584848739699)
                  ·
                    refine ⟨367389246524377273109549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 244926164349584848739699 367389246524377273109549)
                    ·
                      refine ⟨137770967446641477416081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 367389246524377273109549 137770967446641477416081)
                      ·
                        rfl

theorem cell23_268308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_268308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268308 prefixEnd_268308 := by exact prefixLift 268308
  have htrace : WordTrace (prefixWord ++ tailWord_268308) baseStart_268308 baseEnd_268308 := by
    simpa [prefixWord, tailWord_268308, baseEnd_268308] using wordTrace_append hprefix tailTrace_268308
  have hstable : (prefixWord ++ tailWord_268308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268308).length < 2 ^ (prefixWord ++ tailWord_268308).sum := by decide
  have hdescent : baseEnd_268308 < baseStart_268308 := by decide
  rcases family_descends (prefixWord ++ tailWord_268308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268314 : List Nat := [3, 1, 1, 3, 1, 5, 1, 3, 1, 2, 2]
def baseStart_268314 : Nat := 118140960795 + 268314 * 2 ^ 59
def prefixEnd_268314 : Nat := 4983230072969 + 3 ^ 40 * 268314 * 2
def baseEnd_268314 : Nat := 137774048330568453941053

theorem tailTrace_268314 : CollatzResearch.WordTrace tailWord_268314 prefixEnd_268314 137774048330568453941053 := by
  unfold tailWord_268314
  simp only [CollatzResearch.WordTrace]
  refine ⟨2446553887487919307010999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6524143699967784818695997 2446553887487919307010999)
  ·
    refine ⟨3669830831231878960516499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2446553887487919307010999 3669830831231878960516499)
    ·
      refine ⟨5504746246847818440774749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3669830831231878960516499 5504746246847818440774749)
      ·
        refine ⟨2064279842567931915290531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5504746246847818440774749 2064279842567931915290531)
        ·
          refine ⟨3096419763851897872935797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2064279842567931915290531 3096419763851897872935797)
          ·
            refine ⟨290289352861115425587731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3096419763851897872935797 290289352861115425587731)
            ·
              refine ⟨435434029291673138381597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290289352861115425587731 435434029291673138381597)
              ·
                refine ⟨163287760984377426893099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 435434029291673138381597 163287760984377426893099)
                ·
                  refine ⟨244931641476566140339649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163287760984377426893099 244931641476566140339649)
                  ·
                    refine ⟨183698731107424605254737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 244931641476566140339649 183698731107424605254737)
                    ·
                      refine ⟨137774048330568453941053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 183698731107424605254737 137774048330568453941053)
                      ·
                        rfl

theorem cell23_268314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_268314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268314 prefixEnd_268314 := by exact prefixLift 268314
  have htrace : WordTrace (prefixWord ++ tailWord_268314) baseStart_268314 baseEnd_268314 := by
    simpa [prefixWord, tailWord_268314, baseEnd_268314] using wordTrace_append hprefix tailTrace_268314
  have hstable : (prefixWord ++ tailWord_268314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268314).length < 2 ^ (prefixWord ++ tailWord_268314).sum := by decide
  have hdescent : baseEnd_268314 < baseStart_268314 := by decide
  rcases family_descends (prefixWord ++ tailWord_268314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268330 : List Nat := [3, 1, 4, 1, 2, 1, 2, 1, 4, 1, 3]
def baseStart_268330 : Nat := 118140960795 + 268330 * 2 ^ 59
def prefixEnd_268330 : Nat := 4983230072969 + 3 ^ 40 * 268330 * 2
def baseEnd_268330 : Nat := 137782264021040391340979

theorem tailTrace_268330 : CollatzResearch.WordTrace tailWord_268330 prefixEnd_268330 137782264021040391340979 := by
  unfold tailWord_268330
  simp only [CollatzResearch.WordTrace]
  refine ⟨2446699779473427990156611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6524532745262474640417629 2446699779473427990156611)
  ·
    refine ⟨3670049669210141985234917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2446699779473427990156611 3670049669210141985234917)
    ·
      refine ⟨688134312976901622231547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3670049669210141985234917 688134312976901622231547)
      ·
        refine ⟨1032201469465352433347321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 688134312976901622231547 1032201469465352433347321)
        ·
          refine ⟨774151102099014325010491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1032201469465352433347321 774151102099014325010491)
          ·
            refine ⟨1161226653148521487515737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 774151102099014325010491 1161226653148521487515737)
            ·
              refine ⟨870919989861391115636803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1161226653148521487515737 870919989861391115636803)
              ·
                refine ⟨1306379984792086673455205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 870919989861391115636803 1306379984792086673455205)
                ·
                  refine ⟨244946247148516251272851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1306379984792086673455205 244946247148516251272851)
                  ·
                    refine ⟨367419370722774376909277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 244946247148516251272851 367419370722774376909277)
                    ·
                      refine ⟨137782264021040391340979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 367419370722774376909277 137782264021040391340979)
                      ·
                        rfl

theorem cell23_268330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_268330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268330 prefixEnd_268330 := by exact prefixLift 268330
  have htrace : WordTrace (prefixWord ++ tailWord_268330) baseStart_268330 baseEnd_268330 := by
    simpa [prefixWord, tailWord_268330, baseEnd_268330] using wordTrace_append hprefix tailTrace_268330
  have hstable : (prefixWord ++ tailWord_268330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268330).length < 2 ^ (prefixWord ++ tailWord_268330).sum := by decide
  have hdescent : baseEnd_268330 < baseStart_268330 := by decide
  rcases family_descends (prefixWord ++ tailWord_268330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268382 : List Nat := [4, 4, 1, 1, 3, 1, 2, 2, 1, 2, 2]
def baseStart_268382 : Nat := 118140960795 + 268382 * 2 ^ 59
def prefixEnd_268382 : Nat := 4983230072969 + 3 ^ 40 * 268382 * 2
def baseEnd_268382 : Nat := 137808965015074187890741

theorem tailTrace_268382 : CollatzResearch.WordTrace tailWord_268382 prefixEnd_268382 137808965015074187890741 := by
  unfold tailWord_268382
  simp only [CollatzResearch.WordTrace]
  refine ⟨1223586964213165605189925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6525797142470216561012933 1223586964213165605189925)
  ·
    refine ⟨229422555789968550973111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1223586964213165605189925 229422555789968550973111)
    ·
      refine ⟨344133833684952826459667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229422555789968550973111 344133833684952826459667)
      ·
        refine ⟨516200750527429239689501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344133833684952826459667 516200750527429239689501)
        ·
          refine ⟨193575281447785964883563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 516200750527429239689501 193575281447785964883563)
          ·
            refine ⟨290362922171678947325345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193575281447785964883563 290362922171678947325345)
            ·
              refine ⟨217772191628759210494009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290362922171678947325345 217772191628759210494009)
              ·
                refine ⟨163329143721569407870507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217772191628759210494009 163329143721569407870507)
                ·
                  refine ⟨244993715582354111805761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163329143721569407870507 244993715582354111805761)
                  ·
                    refine ⟨183745286686765583854321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 244993715582354111805761 183745286686765583854321)
                    ·
                      refine ⟨137808965015074187890741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 183745286686765583854321 137808965015074187890741)
                      ·
                        rfl

theorem cell23_268382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_268382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268382 prefixEnd_268382 := by exact prefixLift 268382
  have htrace : WordTrace (prefixWord ++ tailWord_268382) baseStart_268382 baseEnd_268382 := by
    simpa [prefixWord, tailWord_268382, baseEnd_268382] using wordTrace_append hprefix tailTrace_268382
  have hstable : (prefixWord ++ tailWord_268382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268382).length < 2 ^ (prefixWord ++ tailWord_268382).sum := by decide
  have hdescent : baseEnd_268382 < baseStart_268382 := by decide
  rcases family_descends (prefixWord ++ tailWord_268382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268393 : List Nat := [1, 2, 1, 1, 1, 5, 3, 4, 5]
def baseStart_268393 : Nat := 118140960795 + 268393 * 2 ^ 59
def prefixEnd_268393 : Nat := 4983230072969 + 3 ^ 40 * 268393 * 2
def baseEnd_268393 : Nat := 15312734811363738317021

theorem tailTrace_268393 : CollatzResearch.WordTrace tailWord_268393 prefixEnd_268393 15312734811363738317021 := by
  unfold tailWord_268393
  simp only [CollatzResearch.WordTrace]
  refine ⟨9789096916665473720169833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6526064611110315813446555 9789096916665473720169833)
  ·
    refine ⟨7341822687499105290127375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9789096916665473720169833 7341822687499105290127375)
    ·
      refine ⟨11012734031248657935191063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7341822687499105290127375 11012734031248657935191063)
      ·
        refine ⟨16519101046872986902786595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11012734031248657935191063 16519101046872986902786595)
        ·
          refine ⟨24778651570309480354179893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16519101046872986902786595 24778651570309480354179893)
          ·
            refine ⟨2322998584716513783204365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24778651570309480354179893 2322998584716513783204365)
            ·
              refine ⟨871124469268692668701637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2322998584716513783204365 871124469268692668701637)
              ·
                refine ⟨163335837987879875381557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 871124469268692668701637 163335837987879875381557)
                ·
                  refine ⟨15312734811363738317021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 163335837987879875381557 15312734811363738317021)
                  ·
                    rfl

theorem cell23_268393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 4, 5].length) (baseStart_268393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268393 prefixEnd_268393 := by exact prefixLift 268393
  have htrace : WordTrace (prefixWord ++ tailWord_268393) baseStart_268393 baseEnd_268393 := by
    simpa [prefixWord, tailWord_268393, baseEnd_268393] using wordTrace_append hprefix tailTrace_268393
  have hstable : (prefixWord ++ tailWord_268393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268393).length < 2 ^ (prefixWord ++ tailWord_268393).sum := by decide
  have hdescent : baseEnd_268393 < baseStart_268393 := by decide
  rcases family_descends (prefixWord ++ tailWord_268393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268423 : List Nat := [1, 1, 4, 2, 1, 1, 5, 1, 2, 5]
def baseStart_268423 : Nat := 118140960795 + 268423 * 2 ^ 59
def prefixEnd_268423 : Nat := 4983230072969 + 3 ^ 40 * 268423 * 2
def baseEnd_268423 : Nat := 45943339240636175826017

theorem tailTrace_268423 : CollatzResearch.WordTrace tailWord_268423 prefixEnd_268423 45943339240636175826017 := by
  unfold tailWord_268423
  simp only [CollatzResearch.WordTrace]
  refine ⟨9790191106556788843761923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6526794071037859229174615 9790191106556788843761923)
  ·
    refine ⟨14685286659835183265642885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9790191106556788843761923 14685286659835183265642885)
    ·
      refine ⟨2753491248719096862308041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14685286659835183265642885 2753491248719096862308041)
      ·
        refine ⟨2065118436539322646731031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2753491248719096862308041 2065118436539322646731031)
        ·
          refine ⟨3097677654808983970096547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2065118436539322646731031 3097677654808983970096547)
          ·
            refine ⟨4646516482213475955144821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3097677654808983970096547 4646516482213475955144821)
            ·
              refine ⟨435610920207513370794827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4646516482213475955144821 435610920207513370794827)
              ·
                refine ⟨653416380311270056192241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 435610920207513370794827 653416380311270056192241)
                ·
                  refine ⟨490062285233452542144181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 653416380311270056192241 490062285233452542144181)
                  ·
                    refine ⟨45943339240636175826017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 490062285233452542144181 45943339240636175826017)
                    ·
                      rfl

theorem cell23_268423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_268423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268423 prefixEnd_268423 := by exact prefixLift 268423
  have htrace : WordTrace (prefixWord ++ tailWord_268423) baseStart_268423 baseEnd_268423 := by
    simpa [prefixWord, tailWord_268423, baseEnd_268423] using wordTrace_append hprefix tailTrace_268423
  have hstable : (prefixWord ++ tailWord_268423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268423).length < 2 ^ (prefixWord ++ tailWord_268423).sum := by decide
  have hdescent : baseEnd_268423 < baseStart_268423 := by decide
  rcases family_descends (prefixWord ++ tailWord_268423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268443 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 4, 4, 2]
def baseStart_268443 : Nat := 118140960795 + 268443 * 2 ^ 59
def prefixEnd_268443 : Nat := 4983230072969 + 3 ^ 40 * 268443 * 2
def baseEnd_268443 : Nat := 137840287334998449227959

theorem tailTrace_268443 : CollatzResearch.WordTrace tailWord_268443 prefixEnd_268443 137840287334998449227959 := by
  unfold tailWord_268443
  simp only [CollatzResearch.WordTrace]
  refine ⟨9790920566484332259489983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6527280377656221506326655 9790920566484332259489983)
  ·
    refine ⟨14686380849726498389234975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9790920566484332259489983 14686380849726498389234975)
    ·
      refine ⟨22029571274589747583852463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14686380849726498389234975 22029571274589747583852463)
      ·
        refine ⟨33044356911884621375778695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22029571274589747583852463 33044356911884621375778695)
        ·
          refine ⟨49566535367826932063668043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33044356911884621375778695 49566535367826932063668043)
          ·
            refine ⟨74349803051740398095502065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49566535367826932063668043 74349803051740398095502065)
            ·
              refine ⟨55762352288805298571626549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74349803051740398095502065 55762352288805298571626549)
              ·
                refine ⟨5227720527075496741089989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55762352288805298571626549 5227720527075496741089989)
                ·
                  refine ⟨980197598826655638954373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5227720527075496741089989 980197598826655638954373)
                  ·
                    refine ⟨183787049779997932303945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 980197598826655638954373 183787049779997932303945)
                    ·
                      refine ⟨137840287334998449227959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 183787049779997932303945 137840287334998449227959)
                      ·
                        rfl

theorem cell23_268443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 4, 2].length) (baseStart_268443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268443 prefixEnd_268443 := by exact prefixLift 268443
  have htrace : WordTrace (prefixWord ++ tailWord_268443) baseStart_268443 baseEnd_268443 := by
    simpa [prefixWord, tailWord_268443, baseEnd_268443] using wordTrace_append hprefix tailTrace_268443
  have hstable : (prefixWord ++ tailWord_268443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268443).length < 2 ^ (prefixWord ++ tailWord_268443).sum := by decide
  have hdescent : baseEnd_268443 < baseStart_268443 := by decide
  rcases family_descends (prefixWord ++ tailWord_268443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268504 : List Nat := [2, 1, 2, 2, 4, 2, 3, 2, 1, 4]
def baseStart_268504 : Nat := 118140960795 + 268504 * 2 ^ 59
def prefixEnd_268504 : Nat := 4983230072969 + 3 ^ 40 * 268504 * 2
def baseEnd_268504 : Nat := 45957203218307570188393

theorem tailTrace_268504 : CollatzResearch.WordTrace tailWord_268504 prefixEnd_268504 45957203218307570188393 := by
  unfold tailWord_268504
  simp only [CollatzResearch.WordTrace]
  refine ⟨4896572709631669838730283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6528763612842226451640377 4896572709631669838730283)
  ·
    refine ⟨7344859064447504758095425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4896572709631669838730283 7344859064447504758095425)
    ·
      refine ⟨5508644298335628568571569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7344859064447504758095425 5508644298335628568571569)
      ·
        refine ⟨4131483223751721426428677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5508644298335628568571569 4131483223751721426428677)
        ·
          refine ⟨774653104453447767455377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4131483223751721426428677 774653104453447767455377)
          ·
            refine ⟨580989828340085825591533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 774653104453447767455377 580989828340085825591533)
            ·
              refine ⟨217871185627532184596825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 580989828340085825591533 217871185627532184596825)
              ·
                refine ⟨163403389220649138447619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217871185627532184596825 163403389220649138447619)
                ·
                  refine ⟨245105083830973707671429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163403389220649138447619 245105083830973707671429)
                  ·
                    refine ⟨45957203218307570188393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 245105083830973707671429 45957203218307570188393)
                    ·
                      rfl

theorem cell23_268504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 2, 1, 4].length) (baseStart_268504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268504 prefixEnd_268504 := by exact prefixLift 268504
  have htrace : WordTrace (prefixWord ++ tailWord_268504) baseStart_268504 baseEnd_268504 := by
    simpa [prefixWord, tailWord_268504, baseEnd_268504] using wordTrace_append hprefix tailTrace_268504
  have hstable : (prefixWord ++ tailWord_268504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268504).length < 2 ^ (prefixWord ++ tailWord_268504).sum := by decide
  have hdescent : baseEnd_268504 < baseStart_268504 := by decide
  rcases family_descends (prefixWord ++ tailWord_268504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268513 : List Nat := [1, 2, 3, 1, 3, 1, 2, 2, 3, 5]
def baseStart_268513 : Nat := 118140960795 + 268513 * 2 ^ 59
def prefixEnd_268513 : Nat := 4983230072969 + 3 ^ 40 * 268513 * 2
def baseEnd_268513 : Nat := 45958743660271058450879

theorem tailTrace_268513 : CollatzResearch.WordTrace tailWord_268513 prefixEnd_268513 45958743660271058450879 := by
  unfold tailWord_268513
  simp only [CollatzResearch.WordTrace]
  refine ⟨9793473676230734214538193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6528982450820489476358795 9793473676230734214538193)
  ·
    refine ⟨7345105257173050660903645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9793473676230734214538193 7345105257173050660903645)
    ·
      refine ⟨2754414471439893997838867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7345105257173050660903645 2754414471439893997838867)
      ·
        refine ⟨4131621707159840996758301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2754414471439893997838867 4131621707159840996758301)
        ·
          refine ⟨1549358140184940373784363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4131621707159840996758301 1549358140184940373784363)
          ·
            refine ⟨2324037210277410560676545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1549358140184940373784363 2324037210277410560676545)
            ·
              refine ⟨1743027907708057920507409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2324037210277410560676545 1743027907708057920507409)
              ·
                refine ⟨1307270930781043440380557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1743027907708057920507409 1307270930781043440380557)
                ·
                  refine ⟨490226599042891290142709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1307270930781043440380557 490226599042891290142709)
                  ·
                    refine ⟨45958743660271058450879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 490226599042891290142709 45958743660271058450879)
                    ·
                      rfl

theorem cell23_268513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_268513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268513 prefixEnd_268513 := by exact prefixLift 268513
  have htrace : WordTrace (prefixWord ++ tailWord_268513) baseStart_268513 baseEnd_268513 := by
    simpa [prefixWord, tailWord_268513, baseEnd_268513] using wordTrace_append hprefix tailTrace_268513
  have hstable : (prefixWord ++ tailWord_268513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268513).length < 2 ^ (prefixWord ++ tailWord_268513).sum := by decide
  have hdescent : baseEnd_268513 < baseStart_268513 := by decide
  rcases family_descends (prefixWord ++ tailWord_268513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268517 : List Nat := [1, 3, 1, 4, 2, 3, 2, 1, 6]
def baseStart_268517 : Nat := 118140960795 + 268517 * 2 ^ 59
def prefixEnd_268517 : Nat := 4983230072969 + 3 ^ 40 * 268517 * 2
def baseEnd_268517 : Nat := 15319809433714573300291

theorem tailTrace_268517 : CollatzResearch.WordTrace tailWord_268517 prefixEnd_268517 15319809433714573300291 := by
  unfold tailWord_268517
  simp only [CollatzResearch.WordTrace]
  refine ⟨9793619568216242897683805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6529079712144161931789203 9793619568216242897683805)
  ·
    refine ⟨3672607338081091086631427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9793619568216242897683805 3672607338081091086631427)
    ·
      refine ⟨5508911007121636629947141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3672607338081091086631427 5508911007121636629947141)
      ·
        refine ⟨1032920813835306868115089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5508911007121636629947141 1032920813835306868115089)
        ·
          refine ⟨774690610376480151086317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1032920813835306868115089 774690610376480151086317)
          ·
            refine ⟨290508978891180056657369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 774690610376480151086317 290508978891180056657369)
            ·
              refine ⟨217881734168385042493027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290508978891180056657369 217881734168385042493027)
              ·
                refine ⟨326822601252577563739541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217881734168385042493027 326822601252577563739541)
                ·
                  refine ⟨15319809433714573300291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 326822601252577563739541 15319809433714573300291)
                  ·
                    rfl

theorem cell23_268517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 6].length) (baseStart_268517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268517 prefixEnd_268517 := by exact prefixLift 268517
  have htrace : WordTrace (prefixWord ++ tailWord_268517) baseStart_268517 baseEnd_268517 := by
    simpa [prefixWord, tailWord_268517, baseEnd_268517] using wordTrace_append hprefix tailTrace_268517
  have hstable : (prefixWord ++ tailWord_268517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268517).length < 2 ^ (prefixWord ++ tailWord_268517).sum := by decide
  have hdescent : baseEnd_268517 < baseStart_268517 := by decide
  rcases family_descends (prefixWord ++ tailWord_268517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268530 : List Nat := [3, 2, 1, 3, 2, 2, 1, 1, 3, 5]
def baseStart_268530 : Nat := 118140960795 + 268530 * 2 ^ 59
def prefixEnd_268530 : Nat := 4983230072969 + 3 ^ 40 * 268530 * 2
def baseEnd_268530 : Nat := 45961653383979869613353

theorem tailTrace_268530 : CollatzResearch.WordTrace tailWord_268530 prefixEnd_268530 45961653383979869613353 := by
  unfold tailWord_268530
  simp only [CollatzResearch.WordTrace]
  refine ⟨2448523429292286529476761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6529395811446097411938029 2448523429292286529476761)
  ·
    refine ⟨1836392571969214897107571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2448523429292286529476761 1836392571969214897107571)
    ·
      refine ⟨2754588857953822345661357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1836392571969214897107571 2754588857953822345661357)
      ·
        refine ⟨1032970821732683379623009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2754588857953822345661357 1032970821732683379623009)
        ·
          refine ⟨774728116299512534717257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1032970821732683379623009 774728116299512534717257)
          ·
            refine ⟨581046087224634401037943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 774728116299512534717257 581046087224634401037943)
            ·
              refine ⟨871569130836951601556915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 581046087224634401037943 871569130836951601556915)
              ·
                refine ⟨1307353696255427402335373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 871569130836951601556915 1307353696255427402335373)
                ·
                  refine ⟨490257636095785275875765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1307353696255427402335373 490257636095785275875765)
                  ·
                    refine ⟨45961653383979869613353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 490257636095785275875765 45961653383979869613353)
                    ·
                      rfl

theorem cell23_268530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_268530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268530 prefixEnd_268530 := by exact prefixLift 268530
  have htrace : WordTrace (prefixWord ++ tailWord_268530) baseStart_268530 baseEnd_268530 := by
    simpa [prefixWord, tailWord_268530, baseEnd_268530] using wordTrace_append hprefix tailTrace_268530
  have hstable : (prefixWord ++ tailWord_268530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268530).length < 2 ^ (prefixWord ++ tailWord_268530).sum := by decide
  have hdescent : baseEnd_268530 < baseStart_268530 := by decide
  rcases family_descends (prefixWord ++ tailWord_268530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268543 : List Nat := [1, 1, 2, 2, 1, 4, 3, 2, 1, 6]
def baseStart_268543 : Nat := 118140960795 + 268543 * 2 ^ 59
def prefixEnd_268543 : Nat := 4983230072969 + 3 ^ 40 * 268543 * 2
def baseEnd_268543 : Nat := 45963878466816019325833

theorem tailTrace_268543 : CollatzResearch.WordTrace tailWord_268543 prefixEnd_268543 45963878466816019325833 := by
  unfold tailWord_268543
  simp only [CollatzResearch.WordTrace]
  refine ⟨9794567866122049338130283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6529711910748032892086855 9794567866122049338130283)
  ·
    refine ⟨14691851799183074007195425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9794567866122049338130283 14691851799183074007195425)
    ·
      refine ⟨11018888849387305505396569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14691851799183074007195425 11018888849387305505396569)
      ·
        refine ⟨8264166637040479129047427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11018888849387305505396569 8264166637040479129047427)
        ·
          refine ⟨12396249955560718693571141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8264166637040479129047427 12396249955560718693571141)
          ·
            refine ⟨2324296866667634755044589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12396249955560718693571141 2324296866667634755044589)
            ·
              refine ⟨871611325000363033141721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2324296866667634755044589 871611325000363033141721)
              ·
                refine ⟨653708493750272274856291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 871611325000363033141721 653708493750272274856291)
                ·
                  refine ⟨980562740625408412284437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 653708493750272274856291 980562740625408412284437)
                  ·
                    refine ⟨45963878466816019325833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 980562740625408412284437 45963878466816019325833)
                    ·
                      rfl

theorem cell23_268543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 6].length) (baseStart_268543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268543 prefixEnd_268543 := by exact prefixLift 268543
  have htrace : WordTrace (prefixWord ++ tailWord_268543) baseStart_268543 baseEnd_268543 := by
    simpa [prefixWord, tailWord_268543, baseEnd_268543] using wordTrace_append hprefix tailTrace_268543
  have hstable : (prefixWord ++ tailWord_268543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268543).length < 2 ^ (prefixWord ++ tailWord_268543).sum := by decide
  have hdescent : baseEnd_268543 < baseStart_268543 := by decide
  rcases family_descends (prefixWord ++ tailWord_268543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268561 : List Nat := [1, 2, 2, 1, 1, 7, 2, 2, 1, 1, 3]
def baseStart_268561 : Nat := 118140960795 + 268561 * 2 ^ 59
def prefixEnd_268561 : Nat := 4983230072969 + 3 ^ 40 * 268561 * 2
def baseEnd_268561 : Nat := 137900878052228987552417

theorem tailTrace_268561 : CollatzResearch.WordTrace tailWord_268561 prefixEnd_268561 137900878052228987552417 := by
  unfold tailWord_268561
  simp only [CollatzResearch.WordTrace]
  refine ⟨9795224380056838412285537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6530149586704558941523691 9795224380056838412285537)
  ·
    refine ⟨7346418285042628809214153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9795224380056838412285537 7346418285042628809214153)
    ·
      refine ⟨5509813713781971606910615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7346418285042628809214153 5509813713781971606910615)
      ·
        refine ⟨8264720570672957410365923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5509813713781971606910615 8264720570672957410365923)
        ·
          refine ⟨12397080856009436115548885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8264720570672957410365923 12397080856009436115548885)
          ·
            refine ⟨290556582562721158958177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 12397080856009436115548885 290556582562721158958177)
            ·
              refine ⟨217917436922040869218633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290556582562721158958177 217917436922040869218633)
              ·
                refine ⟨163438077691530651913975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217917436922040869218633 163438077691530651913975)
                ·
                  refine ⟨245157116537295977870963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163438077691530651913975 245157116537295977870963)
                  ·
                    refine ⟨367735674805943966806445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 245157116537295977870963 367735674805943966806445)
                    ·
                      refine ⟨137900878052228987552417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 367735674805943966806445 137900878052228987552417)
                      ·
                        rfl

theorem cell23_268561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 2, 1, 1, 3].length) (baseStart_268561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268561 prefixEnd_268561 := by exact prefixLift 268561
  have htrace : WordTrace (prefixWord ++ tailWord_268561) baseStart_268561 baseEnd_268561 := by
    simpa [prefixWord, tailWord_268561, baseEnd_268561] using wordTrace_append hprefix tailTrace_268561
  have hstable : (prefixWord ++ tailWord_268561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268561).length < 2 ^ (prefixWord ++ tailWord_268561).sum := by decide
  have hdescent : baseEnd_268561 < baseStart_268561 := by decide
  rcases family_descends (prefixWord ++ tailWord_268561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268580 : List Nat := [2, 3, 1, 3, 1, 2, 1, 3, 1, 2, 4]
def baseStart_268580 : Nat := 118140960795 + 268580 * 2 ^ 59
def prefixEnd_268580 : Nat := 4983230072969 + 3 ^ 40 * 268580 * 2
def baseEnd_268580 : Nat := 137910634184664413214829

theorem tailTrace_268580 : CollatzResearch.WordTrace tailWord_268580 prefixEnd_268580 137910634184664413214829 := by
  unfold tailWord_268580
  simp only [CollatzResearch.WordTrace]
  refine ⟨4897958683494002328613597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6530611577992003104818129 4897958683494002328613597)
  ·
    refine ⟨1836734506310250873230099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4897958683494002328613597 1836734506310250873230099)
    ·
      refine ⟨2755101759465376309845149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1836734506310250873230099 2755101759465376309845149)
      ·
        refine ⟨1033163159799516116191931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2755101759465376309845149 1033163159799516116191931)
        ·
          refine ⟨1549744739699274174287897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1033163159799516116191931 1549744739699274174287897)
          ·
            refine ⟨1162308554774455630715923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1549744739699274174287897 1162308554774455630715923)
            ·
              refine ⟨1743462832161683446073885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1162308554774455630715923 1743462832161683446073885)
              ·
                refine ⟨653798562060631292277707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1743462832161683446073885 653798562060631292277707)
                ·
                  refine ⟨980697843090946938416561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 653798562060631292277707 980697843090946938416561)
                  ·
                    refine ⟨735523382318210203812421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 980697843090946938416561 735523382318210203812421)
                    ·
                      refine ⟨137910634184664413214829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 735523382318210203812421 137910634184664413214829)
                      ·
                        rfl

theorem cell23_268580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_268580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268580 prefixEnd_268580 := by exact prefixLift 268580
  have htrace : WordTrace (prefixWord ++ tailWord_268580) baseStart_268580 baseEnd_268580 := by
    simpa [prefixWord, tailWord_268580, baseEnd_268580] using wordTrace_append hprefix tailTrace_268580
  have hstable : (prefixWord ++ tailWord_268580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268580).length < 2 ^ (prefixWord ++ tailWord_268580).sum := by decide
  have hdescent : baseEnd_268580 < baseStart_268580 := by decide
  rcases family_descends (prefixWord ++ tailWord_268580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268600 : List Nat := [2, 1, 2, 1, 3, 1, 4, 2, 1, 3, 3]
def baseStart_268600 : Nat := 118140960795 + 268600 * 2 ^ 59
def prefixEnd_268600 : Nat := 4983230072969 + 3 ^ 40 * 268600 * 2
def baseEnd_268600 : Nat := 137920903797754334964737

theorem tailTrace_268600 : CollatzResearch.WordTrace tailWord_268600 prefixEnd_268600 137920903797754334964737 := by
  unfold tailWord_268600
  simp only [CollatzResearch.WordTrace]
  refine ⟨4898323413457774036477627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6531097884610365381970169 4898323413457774036477627)
  ·
    refine ⟨7347485120186661054716441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4898323413457774036477627 7347485120186661054716441)
    ·
      refine ⟨5510613840139995791037331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7347485120186661054716441 5510613840139995791037331)
      ·
        refine ⟨8265920760209993686555997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5510613840139995791037331 8265920760209993686555997)
        ·
          refine ⟨3099720285078747632458499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8265920760209993686555997 3099720285078747632458499)
          ·
            refine ⟨4649580427618121448687749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3099720285078747632458499 4649580427618121448687749)
            ·
              refine ⟨871796330178397771628953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4649580427618121448687749 871796330178397771628953)
              ·
                refine ⟨653847247633798328721715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 871796330178397771628953 653847247633798328721715)
                ·
                  refine ⟨980770871450697493082573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 653847247633798328721715 980770871450697493082573)
                  ·
                    refine ⟨367789076794011559905965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 980770871450697493082573 367789076794011559905965)
                    ·
                      refine ⟨137920903797754334964737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 367789076794011559905965 137920903797754334964737)
                      ·
                        rfl

theorem cell23_268600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 1, 3, 3].length) (baseStart_268600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268600 prefixEnd_268600 := by exact prefixLift 268600
  have htrace : WordTrace (prefixWord ++ tailWord_268600) baseStart_268600 baseEnd_268600 := by
    simpa [prefixWord, tailWord_268600, baseEnd_268600] using wordTrace_append hprefix tailTrace_268600
  have hstable : (prefixWord ++ tailWord_268600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268600).length < 2 ^ (prefixWord ++ tailWord_268600).sum := by decide
  have hdescent : baseEnd_268600 < baseStart_268600 := by decide
  rcases family_descends (prefixWord ++ tailWord_268600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268601 : List Nat := [1, 2, 1, 6, 1, 1, 1, 5, 1, 2, 2]
def baseStart_268601 : Nat := 118140960795 + 268601 * 2 ^ 59
def prefixEnd_268601 : Nat := 4983230072969 + 3 ^ 40 * 268601 * 2
def baseEnd_268601 : Nat := 137921417278408831052233

theorem tailTrace_268601 : CollatzResearch.WordTrace tailWord_268601 prefixEnd_268601 137921417278408831052233 := by
  unfold tailWord_268601
  simp only [CollatzResearch.WordTrace]
  refine ⟨9796683299911925243741657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6531122199941283495827771 9796683299911925243741657)
  ·
    refine ⟨7347512474933943932806243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9796683299911925243741657 7347512474933943932806243)
    ·
      refine ⟨11021268712400915899209365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7347512474933943932806243 11021268712400915899209365)
      ·
        refine ⟨516621970893792932775439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11021268712400915899209365 516621970893792932775439)
        ·
          refine ⟨774932956340689399163159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516621970893792932775439 774932956340689399163159)
          ·
            refine ⟨1162399434511034098744739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 774932956340689399163159 1162399434511034098744739)
            ·
              refine ⟨1743599151766551148117109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1162399434511034098744739 1743599151766551148117109)
              ·
                refine ⟨163462420478114170135979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1743599151766551148117109 163462420478114170135979)
                ·
                  refine ⟨245193630717171255203969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163462420478114170135979 245193630717171255203969)
                  ·
                    refine ⟨183895223037878441402977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 245193630717171255203969 183895223037878441402977)
                    ·
                      refine ⟨137921417278408831052233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 183895223037878441402977 137921417278408831052233)
                      ·
                        rfl

theorem cell23_268601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_268601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268601 prefixEnd_268601 := by exact prefixLift 268601
  have htrace : WordTrace (prefixWord ++ tailWord_268601) baseStart_268601 baseEnd_268601 := by
    simpa [prefixWord, tailWord_268601, baseEnd_268601] using wordTrace_append hprefix tailTrace_268601
  have hstable : (prefixWord ++ tailWord_268601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268601).length < 2 ^ (prefixWord ++ tailWord_268601).sum := by decide
  have hdescent : baseEnd_268601 < baseStart_268601 := by decide
  rcases family_descends (prefixWord ++ tailWord_268601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268623 : List Nat := [1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 4]
def baseStart_268623 : Nat := 118140960795 + 268623 * 2 ^ 59
def prefixEnd_268623 : Nat := 4983230072969 + 3 ^ 40 * 268623 * 2
def baseEnd_268623 : Nat := 137932713852807744977131

theorem tailTrace_268623 : CollatzResearch.WordTrace tailWord_268623 prefixEnd_268623 137932713852807744977131 := by
  unfold tailWord_268623
  simp only [CollatzResearch.WordTrace]
  refine ⟨9797485705832223001042523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6531657137221482000695015 9797485705832223001042523)
  ·
    refine ⟨14696228558748334501563785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9797485705832223001042523 14696228558748334501563785)
    ·
      refine ⟨11022171419061250876172839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14696228558748334501563785 11022171419061250876172839)
      ·
        refine ⟨16533257128591876314259259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11022171419061250876172839 16533257128591876314259259)
        ·
          refine ⟨24799885692887814471388889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16533257128591876314259259 24799885692887814471388889)
          ·
            refine ⟨18599914269665860853541667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24799885692887814471388889 18599914269665860853541667)
            ·
              refine ⟨27899871404498791280312501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18599914269665860853541667 27899871404498791280312501)
              ·
                refine ⟨2615612944171761682529297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27899871404498791280312501 2615612944171761682529297)
                ·
                  refine ⟨1961709708128821261896973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2615612944171761682529297 1961709708128821261896973)
                  ·
                    refine ⟨735641140548307973211365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1961709708128821261896973 735641140548307973211365)
                    ·
                      refine ⟨137932713852807744977131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 735641140548307973211365 137932713852807744977131)
                      ·
                        rfl

theorem cell23_268623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 3, 4].length) (baseStart_268623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268623 prefixEnd_268623 := by exact prefixLift 268623
  have htrace : WordTrace (prefixWord ++ tailWord_268623) baseStart_268623 baseEnd_268623 := by
    simpa [prefixWord, tailWord_268623, baseEnd_268623] using wordTrace_append hprefix tailTrace_268623
  have hstable : (prefixWord ++ tailWord_268623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268623).length < 2 ^ (prefixWord ++ tailWord_268623).sum := by decide
  have hdescent : baseEnd_268623 < baseStart_268623 := by decide
  rcases family_descends (prefixWord ++ tailWord_268623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268644 : List Nat := [2, 3, 1, 1, 3, 1, 4, 2, 1, 3, 2]
def baseStart_268644 : Nat := 118140960795 + 268644 * 2 ^ 59
def prefixEnd_268644 : Nat := 4983230072969 + 3 ^ 40 * 268644 * 2
def baseEnd_268644 : Nat := 137943496946552162814535

theorem tailTrace_268644 : CollatzResearch.WordTrace tailWord_268644 prefixEnd_268644 137943496946552162814535 := by
  unfold tailWord_268644
  simp only [CollatzResearch.WordTrace]
  refine ⟨4899125819378071793778493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6532167759170762391704657 4899125819378071793778493)
  ·
    refine ⟨1837172182266776922666935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4899125819378071793778493 1837172182266776922666935)
    ·
      refine ⟨2755758273400165384000403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1837172182266776922666935 2755758273400165384000403)
      ·
        refine ⟨4133637410100248076000605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2755758273400165384000403 4133637410100248076000605)
        ·
          refine ⟨1550114028787593028500227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4133637410100248076000605 1550114028787593028500227)
          ·
            refine ⟨2325171043181389542750341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1550114028787593028500227 2325171043181389542750341)
            ·
              refine ⟨435969570596510539265689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2325171043181389542750341 435969570596510539265689)
              ·
                refine ⟨326977177947382904449267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 435969570596510539265689 326977177947382904449267)
                ·
                  refine ⟨490465766921074356673901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 326977177947382904449267 490465766921074356673901)
                  ·
                    refine ⟨183924662595402883752713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 490465766921074356673901 183924662595402883752713)
                    ·
                      refine ⟨137943496946552162814535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 183924662595402883752713 137943496946552162814535)
                      ·
                        rfl

theorem cell23_268644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 1, 3, 2].length) (baseStart_268644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268644 prefixEnd_268644 := by exact prefixLift 268644
  have htrace : WordTrace (prefixWord ++ tailWord_268644) baseStart_268644 baseEnd_268644 := by
    simpa [prefixWord, tailWord_268644, baseEnd_268644] using wordTrace_append hprefix tailTrace_268644
  have hstable : (prefixWord ++ tailWord_268644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268644).length < 2 ^ (prefixWord ++ tailWord_268644).sum := by decide
  have hdescent : baseEnd_268644 < baseStart_268644 := by decide
  rcases family_descends (prefixWord ++ tailWord_268644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268757 : List Nat := [1, 3, 2, 3, 1, 2, 1, 1, 5, 4]
def baseStart_268757 : Nat := 118140960795 + 268757 * 2 ^ 59
def prefixEnd_268757 : Nat := 4983230072969 + 3 ^ 40 * 268757 * 2
def baseEnd_268757 : Nat := 46000506753503406900505

theorem tailTrace_268757 : CollatzResearch.WordTrace tailWord_268757 prefixEnd_268757 46000506753503406900505 := by
  unfold tailWord_268757
  simp only [CollatzResearch.WordTrace]
  refine ⟨9802373087346763886420525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6534915391564509257613683 9802373087346763886420525)
  ·
    refine ⟨3675889907755036457407697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9802373087346763886420525 3675889907755036457407697)
    ·
      refine ⟨2756917430816277343055773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3675889907755036457407697 2756917430816277343055773)
      ·
        refine ⟨1033844036556104003645915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2756917430816277343055773 1033844036556104003645915)
        ·
          refine ⟨1550766054834156005468873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1033844036556104003645915 1550766054834156005468873)
          ·
            refine ⟨1163074541125617004101655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1550766054834156005468873 1163074541125617004101655)
            ·
              refine ⟨1744611811688425506152483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1163074541125617004101655 1744611811688425506152483)
              ·
                refine ⟨2616917717532638259228725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1744611811688425506152483 2616917717532638259228725)
                ·
                  refine ⟨245336036018684836802693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2616917717532638259228725 245336036018684836802693)
                  ·
                    refine ⟨46000506753503406900505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 245336036018684836802693 46000506753503406900505)
                    ·
                      rfl

theorem cell23_268757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_268757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268757 prefixEnd_268757 := by exact prefixLift 268757
  have htrace : WordTrace (prefixWord ++ tailWord_268757) baseStart_268757 baseEnd_268757 := by
    simpa [prefixWord, tailWord_268757, baseEnd_268757] using wordTrace_append hprefix tailTrace_268757
  have hstable : (prefixWord ++ tailWord_268757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268757).length < 2 ^ (prefixWord ++ tailWord_268757).sum := by decide
  have hdescent : baseEnd_268757 < baseStart_268757 := by decide
  rcases family_descends (prefixWord ++ tailWord_268757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268767 : List Nat := [1, 1, 2, 3, 3, 3, 1, 1, 1, 4, 3]
def baseStart_268767 : Nat := 118140960795 + 268767 * 2 ^ 59
def prefixEnd_268767 : Nat := 4983230072969 + 3 ^ 40 * 268767 * 2
def baseEnd_268767 : Nat := 138006655067055181576469

theorem tailTrace_268767 : CollatzResearch.WordTrace tailWord_268767 prefixEnd_268767 138006655067055181576469 := by
  unfold tailWord_268767
  simp only [CollatzResearch.WordTrace]
  refine ⟨9802737817310535594284555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6535158544873690396189703 9802737817310535594284555)
  ·
    refine ⟨14704106725965803391426833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9802737817310535594284555 14704106725965803391426833)
    ·
      refine ⟨11028080044474352543570125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14704106725965803391426833 11028080044474352543570125)
      ·
        refine ⟨4135530016677882203838797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11028080044474352543570125 4135530016677882203838797)
        ·
          refine ⟨1550823756254205826439549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4135530016677882203838797 1550823756254205826439549)
          ·
            refine ⟨581558908595327184914831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1550823756254205826439549 581558908595327184914831)
            ·
              refine ⟨872338362892990777372247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 581558908595327184914831 872338362892990777372247)
              ·
                refine ⟨1308507544339486166058371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 872338362892990777372247 1308507544339486166058371)
                ·
                  refine ⟨1962761316509229249087557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1308507544339486166058371 1962761316509229249087557)
                  ·
                    refine ⟨368017746845480484203917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1962761316509229249087557 368017746845480484203917)
                    ·
                      refine ⟨138006655067055181576469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 368017746845480484203917 138006655067055181576469)
                      ·
                        rfl

theorem cell23_268767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_268767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268767 prefixEnd_268767 := by exact prefixLift 268767
  have htrace : WordTrace (prefixWord ++ tailWord_268767) baseStart_268767 baseEnd_268767 := by
    simpa [prefixWord, tailWord_268767, baseEnd_268767] using wordTrace_append hprefix tailTrace_268767
  have hstable : (prefixWord ++ tailWord_268767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268767).length < 2 ^ (prefixWord ++ tailWord_268767).sum := by decide
  have hdescent : baseEnd_268767 < baseStart_268767 := by decide
  rcases family_descends (prefixWord ++ tailWord_268767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268824 : List Nat := [2, 1, 2, 3, 3, 1, 2, 1, 1, 5, 2]
def baseStart_268824 : Nat := 118140960795 + 268824 * 2 ^ 59
def prefixEnd_268824 : Nat := 4983230072969 + 3 ^ 40 * 268824 * 2
def baseEnd_268824 : Nat := 138035923464361458563707

theorem tailTrace_268824 : CollatzResearch.WordTrace tailWord_268824 prefixEnd_268824 138035923464361458563707 := by
  unfold tailWord_268824
  simp only [CollatzResearch.WordTrace]
  refine ⟨4902408389052017164554763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6536544518736022886073017 4902408389052017164554763)
  ·
    refine ⟨7353612583578025746832145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4902408389052017164554763 7353612583578025746832145)
    ·
      refine ⟨5515209437683519310124109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7353612583578025746832145 5515209437683519310124109)
      ·
        refine ⟨2068203539131319741296541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5515209437683519310124109 2068203539131319741296541)
        ·
          refine ⟨775576327174244902986203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2068203539131319741296541 775576327174244902986203)
          ·
            refine ⟨1163364490761367354479305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 775576327174244902986203 1163364490761367354479305)
            ·
              refine ⟨872523368071025515859479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1163364490761367354479305 872523368071025515859479)
              ·
                refine ⟨1308785052106538273789219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 872523368071025515859479 1308785052106538273789219)
                ·
                  refine ⟨1963177578159807410683829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1308785052106538273789219 1963177578159807410683829)
                  ·
                    refine ⟨184047897952481944751609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1963177578159807410683829 184047897952481944751609)
                    ·
                      refine ⟨138035923464361458563707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 184047897952481944751609 138035923464361458563707)
                      ·
                        rfl

theorem cell23_268824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_268824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268824 prefixEnd_268824 := by exact prefixLift 268824
  have htrace : WordTrace (prefixWord ++ tailWord_268824) baseStart_268824 baseEnd_268824 := by
    simpa [prefixWord, tailWord_268824, baseEnd_268824] using wordTrace_append hprefix tailTrace_268824
  have hstable : (prefixWord ++ tailWord_268824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268824).length < 2 ^ (prefixWord ++ tailWord_268824).sum := by decide
  have hdescent : baseEnd_268824 < baseStart_268824 := by decide
  rcases family_descends (prefixWord ++ tailWord_268824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268857 : List Nat := [1, 2, 1, 5, 1, 1, 1, 4, 1, 1, 5]
def baseStart_268857 : Nat := 118140960795 + 268857 * 2 ^ 59
def prefixEnd_268857 : Nat := 4983230072969 + 3 ^ 40 * 268857 * 2
def baseEnd_268857 : Nat := 138052868325959829451055

theorem tailTrace_268857 : CollatzResearch.WordTrace tailWord_268857 prefixEnd_268857 138052868325959829451055 := by
  unfold tailWord_268857
  simp only [CollatzResearch.WordTrace]
  refine ⟨9806020386984480965060825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6537346924656320643373883 9806020386984480965060825)
  ·
    refine ⟨7354515290238360723795619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9806020386984480965060825 7354515290238360723795619)
    ·
      refine ⟨11031772935357541085693429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7354515290238360723795619 11031772935357541085693429)
      ·
        refine ⟨1034228712689769476783759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11031772935357541085693429 1034228712689769476783759)
        ·
          refine ⟨1551343069034654215175639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1034228712689769476783759 1551343069034654215175639)
          ·
            refine ⟨2327014603551981322763459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1551343069034654215175639 2327014603551981322763459)
            ·
              refine ⟨3490521905327971984145189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2327014603551981322763459 3490521905327971984145189)
              ·
                refine ⟨654472857248994747027223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3490521905327971984145189 654472857248994747027223)
                ·
                  refine ⟨981709285873492120540835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 654472857248994747027223 981709285873492120540835)
                  ·
                    refine ⟨1472563928810238180811253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 981709285873492120540835 1472563928810238180811253)
                    ·
                      refine ⟨138052868325959829451055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1472563928810238180811253 138052868325959829451055)
                      ·
                        rfl

theorem cell23_268857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_268857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268857 prefixEnd_268857 := by exact prefixLift 268857
  have htrace : WordTrace (prefixWord ++ tailWord_268857) baseStart_268857 baseEnd_268857 := by
    simpa [prefixWord, tailWord_268857, baseEnd_268857] using wordTrace_append hprefix tailTrace_268857
  have hstable : (prefixWord ++ tailWord_268857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268857).length < 2 ^ (prefixWord ++ tailWord_268857).sum := by decide
  have hdescent : baseEnd_268857 < baseStart_268857 := by decide
  rcases family_descends (prefixWord ++ tailWord_268857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268868 : List Nat := [2, 3, 5, 1, 1, 1, 1, 1, 3, 5]
def baseStart_268868 : Nat := 118140960795 + 268868 * 2 ^ 59
def prefixEnd_268868 : Nat := 4983230072969 + 3 ^ 40 * 268868 * 2
def baseEnd_268868 : Nat := 46019505537719762137835

theorem tailTrace_268868 : CollatzResearch.WordTrace tailWord_268868 prefixEnd_268868 46019505537719762137835 := by
  unfold tailWord_268868
  simp only [CollatzResearch.WordTrace]
  refine ⟨4903210794972314921855629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6537614393296419895807505 4903210794972314921855629)
  ·
    refine ⟨1838704048114618095695861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4903210794972314921855629 1838704048114618095695861)
    ·
      refine ⟨172378504510745446471487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1838704048114618095695861 172378504510745446471487)
      ·
        refine ⟨258567756766118169707231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172378504510745446471487 258567756766118169707231)
        ·
          refine ⟨387851635149177254560847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258567756766118169707231 387851635149177254560847)
          ·
            refine ⟨581777452723765881841271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387851635149177254560847 581777452723765881841271)
            ·
              refine ⟨872666179085648822761907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 581777452723765881841271 872666179085648822761907)
              ·
                refine ⟨1308999268628473234142861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 872666179085648822761907 1308999268628473234142861)
                ·
                  refine ⟨490874725735677462803573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1308999268628473234142861 490874725735677462803573)
                  ·
                    refine ⟨46019505537719762137835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 490874725735677462803573 46019505537719762137835)
                    ·
                      rfl

theorem cell23_268868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_268868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268868 prefixEnd_268868 := by exact prefixLift 268868
  have htrace : WordTrace (prefixWord ++ tailWord_268868) baseStart_268868 baseEnd_268868 := by
    simpa [prefixWord, tailWord_268868, baseEnd_268868] using wordTrace_append hprefix tailTrace_268868
  have hstable : (prefixWord ++ tailWord_268868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268868).length < 2 ^ (prefixWord ++ tailWord_268868).sum := by decide
  have hdescent : baseEnd_268868 < baseStart_268868 := by decide
  rcases family_descends (prefixWord ++ tailWord_268868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268871 : List Nat := [1, 1, 4, 1, 4, 3, 1, 2, 1, 1, 4]
def baseStart_268871 : Nat := 118140960795 + 268871 * 2 ^ 59
def prefixEnd_268871 : Nat := 4983230072969 + 3 ^ 40 * 268871 * 2
def baseEnd_268871 : Nat := 138060057055122774675991

theorem tailTrace_268871 : CollatzResearch.WordTrace tailWord_268871 prefixEnd_268871 138060057055122774675991 := by
  unfold tailWord_268871
  simp only [CollatzResearch.WordTrace]
  refine ⟨9806531008933761356070467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6537687339289174237380311 9806531008933761356070467)
  ·
    refine ⟨14709796513400642034105701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9806531008933761356070467 14709796513400642034105701)
    ·
      refine ⟨2758086846262620381394819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14709796513400642034105701 2758086846262620381394819)
      ·
        refine ⟨4137130269393930572092229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2758086846262620381394819 4137130269393930572092229)
        ·
          refine ⟨775711925511361982267293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4137130269393930572092229 775711925511361982267293)
          ·
            refine ⟨290891972066760743350235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 775711925511361982267293 290891972066760743350235)
            ·
              refine ⟨436337958100141115025353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290891972066760743350235 436337958100141115025353)
              ·
                refine ⟨327253468575105836269015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 436337958100141115025353 327253468575105836269015)
                ·
                  refine ⟨490880202862658754403523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 327253468575105836269015 490880202862658754403523)
                  ·
                    refine ⟨736320304293988131605285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 490880202862658754403523 736320304293988131605285)
                    ·
                      refine ⟨138060057055122774675991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 736320304293988131605285 138060057055122774675991)
                      ·
                        rfl

theorem cell23_268871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 1, 4].length) (baseStart_268871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268871 prefixEnd_268871 := by exact prefixLift 268871
  have htrace : WordTrace (prefixWord ++ tailWord_268871) baseStart_268871 baseEnd_268871 := by
    simpa [prefixWord, tailWord_268871, baseEnd_268871] using wordTrace_append hprefix tailTrace_268871
  have hstable : (prefixWord ++ tailWord_268871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268871).length < 2 ^ (prefixWord ++ tailWord_268871).sum := by decide
  have hdescent : baseEnd_268871 < baseStart_268871 := by decide
  rcases family_descends (prefixWord ++ tailWord_268871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268874 : List Nat := [3, 1, 2, 1, 1, 5, 1, 1, 3, 2, 3]
def baseStart_268874 : Nat := 118140960795 + 268874 * 2 ^ 59
def prefixEnd_268874 : Nat := 4983230072969 + 3 ^ 40 * 268874 * 2
def baseEnd_268874 : Nat := 138061597497086262938477

theorem tailTrace_268874 : CollatzResearch.WordTrace tailWord_268874 prefixEnd_268874 138061597497086262938477 := by
  unfold tailWord_268874
  simp only [CollatzResearch.WordTrace]
  refine ⟨2451660106980723217107419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6537760285281928578953117 2451660106980723217107419)
  ·
    refine ⟨3677490160471084825661129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2451660106980723217107419 3677490160471084825661129)
    ·
      refine ⟨2758117620353313619245847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3677490160471084825661129 2758117620353313619245847)
      ·
        refine ⟨4137176430529970428868771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2758117620353313619245847 4137176430529970428868771)
        ·
          refine ⟨6205764645794955643303157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4137176430529970428868771 6205764645794955643303157)
          ·
            refine ⟨581790435543277091559671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6205764645794955643303157 581790435543277091559671)
            ·
              refine ⟨872685653314915637339507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 581790435543277091559671 872685653314915637339507)
              ·
                refine ⟨1309028479972373456009261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 872685653314915637339507 1309028479972373456009261)
                ·
                  refine ⟨490885679989640046003473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1309028479972373456009261 490885679989640046003473)
                  ·
                    refine ⟨368164259992230034502605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 490885679989640046003473 368164259992230034502605)
                    ·
                      refine ⟨138061597497086262938477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 368164259992230034502605 138061597497086262938477)
                      ·
                        rfl

theorem cell23_268874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_268874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268874 prefixEnd_268874 := by exact prefixLift 268874
  have htrace : WordTrace (prefixWord ++ tailWord_268874) baseStart_268874 baseEnd_268874 := by
    simpa [prefixWord, tailWord_268874, baseEnd_268874] using wordTrace_append hprefix tailTrace_268874
  have hstable : (prefixWord ++ tailWord_268874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268874).length < 2 ^ (prefixWord ++ tailWord_268874).sum := by decide
  have hdescent : baseEnd_268874 < baseStart_268874 := by decide
  rcases family_descends (prefixWord ++ tailWord_268874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268884 : List Nat := [2, 4, 1, 1, 1, 4, 1, 2, 1, 2, 4]
def baseStart_268884 : Nat := 118140960795 + 268884 * 2 ^ 59
def prefixEnd_268884 : Nat := 4983230072969 + 3 ^ 40 * 268884 * 2
def baseEnd_268884 : Nat := 138066732303631223813431

theorem tailTrace_268884 : CollatzResearch.WordTrace tailWord_268884 prefixEnd_268884 138066732303631223813431 := by
  unfold tailWord_268884
  simp only [CollatzResearch.WordTrace]
  refine ⟨4903502578943332288146853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6538003438591109717529137 4903502578943332288146853)
  ·
    refine ⟨919406733551874804027535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4903502578943332288146853 919406733551874804027535)
    ·
      refine ⟨1379110100327812206041303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 919406733551874804027535 1379110100327812206041303)
      ·
        refine ⟨2068665150491718309061955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1379110100327812206041303 2068665150491718309061955)
        ·
          refine ⟨3102997725737577463592933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2068665150491718309061955 3102997725737577463592933)
          ·
            refine ⟨581812073575795774423675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3102997725737577463592933 581812073575795774423675)
            ·
              refine ⟨872718110363693661635513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 581812073575795774423675 872718110363693661635513)
              ·
                refine ⟨654538582772770246226635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 872718110363693661635513 654538582772770246226635)
                ·
                  refine ⟨981807874159155369339953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 654538582772770246226635 981807874159155369339953)
                  ·
                    refine ⟨736355905619366527004965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 981807874159155369339953 736355905619366527004965)
                    ·
                      refine ⟨138066732303631223813431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 736355905619366527004965 138066732303631223813431)
                      ·
                        rfl

theorem cell23_268884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_268884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268884 prefixEnd_268884 := by exact prefixLift 268884
  have htrace : WordTrace (prefixWord ++ tailWord_268884) baseStart_268884 baseEnd_268884 := by
    simpa [prefixWord, tailWord_268884, baseEnd_268884] using wordTrace_append hprefix tailTrace_268884
  have hstable : (prefixWord ++ tailWord_268884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268884).length < 2 ^ (prefixWord ++ tailWord_268884).sum := by decide
  have hdescent : baseEnd_268884 < baseStart_268884 := by decide
  rcases family_descends (prefixWord ++ tailWord_268884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268921 : List Nat := [1, 2, 1, 3, 3, 2, 2, 3, 2, 1, 3]
def baseStart_268921 : Nat := 118140960795 + 268921 * 2 ^ 59
def prefixEnd_268921 : Nat := 4983230072969 + 3 ^ 40 * 268921 * 2
def baseEnd_268921 : Nat := 138085731087847579050761

theorem tailTrace_268921 : CollatzResearch.WordTrace tailWord_268921 prefixEnd_268921 138085731087847579050761 := by
  unfold tailWord_268921
  simp only [CollatzResearch.WordTrace]
  refine ⟨9808354658752619895390617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6538903105835079930260411 9808354658752619895390617)
  ·
    refine ⟨7356265994064464921542963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9808354658752619895390617 7356265994064464921542963)
    ·
      refine ⟨11034398991096697382314445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7356265994064464921542963 11034398991096697382314445)
      ·
        refine ⟨4137899621661261518367917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11034398991096697382314445 4137899621661261518367917)
        ·
          refine ⟨1551712358122973069387969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4137899621661261518367917 1551712358122973069387969)
          ·
            refine ⟨1163784268592229802040977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1551712358122973069387969 1163784268592229802040977)
            ·
              refine ⟨872838201444172351530733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1163784268592229802040977 872838201444172351530733)
              ·
                refine ⟨327314325541564631824025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 872838201444172351530733 327314325541564631824025)
                ·
                  refine ⟨245485744156173473868019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 327314325541564631824025 245485744156173473868019)
                  ·
                    refine ⟨368228616234260210802029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 245485744156173473868019 368228616234260210802029)
                    ·
                      refine ⟨138085731087847579050761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 368228616234260210802029 138085731087847579050761)
                      ·
                        rfl

theorem cell23_268921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 2, 1, 3].length) (baseStart_268921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268921 prefixEnd_268921 := by exact prefixLift 268921
  have htrace : WordTrace (prefixWord ++ tailWord_268921) baseStart_268921 baseEnd_268921 := by
    simpa [prefixWord, tailWord_268921, baseEnd_268921] using wordTrace_append hprefix tailTrace_268921
  have hstable : (prefixWord ++ tailWord_268921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268921).length < 2 ^ (prefixWord ++ tailWord_268921).sum := by decide
  have hdescent : baseEnd_268921 < baseStart_268921 := by decide
  rcases family_descends (prefixWord ++ tailWord_268921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268947 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 4, 4, 3]
def baseStart_268947 : Nat := 118140960795 + 268947 * 2 ^ 59
def prefixEnd_268947 : Nat := 4983230072969 + 3 ^ 40 * 268947 * 2
def baseEnd_268947 : Nat := 138099081584864477325641

theorem tailTrace_268947 : CollatzResearch.WordTrace tailWord_268947 prefixEnd_268947 138099081584864477325641 := by
  unfold tailWord_268947
  simp only [CollatzResearch.WordTrace]
  refine ⟨9809302956658426335837095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6539535304438950890558063 9809302956658426335837095)
  ·
    refine ⟨14713954434987639503755643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9809302956658426335837095 14713954434987639503755643)
    ·
      refine ⟨22070931652481459255633465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14713954434987639503755643 22070931652481459255633465)
      ·
        refine ⟨16553198739361094441725099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22070931652481459255633465 16553198739361094441725099)
        ·
          refine ⟨24829798109041641662587649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16553198739361094441725099 24829798109041641662587649)
          ·
            refine ⟨18622348581781231246940737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24829798109041641662587649 18622348581781231246940737)
            ·
              refine ⟨13966761436335923435205553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18622348581781231246940737 13966761436335923435205553)
              ·
                refine ⟨10475071077251942576404165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13966761436335923435205553 10475071077251942576404165)
                ·
                  refine ⟨1964075826984739233075781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10475071077251942576404165 1964075826984739233075781)
                  ·
                    refine ⟨368264217559638606201709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1964075826984739233075781 368264217559638606201709)
                    ·
                      refine ⟨138099081584864477325641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 368264217559638606201709 138099081584864477325641)
                      ·
                        rfl

theorem cell23_268947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 4, 3].length) (baseStart_268947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268947 prefixEnd_268947 := by exact prefixLift 268947
  have htrace : WordTrace (prefixWord ++ tailWord_268947) baseStart_268947 baseEnd_268947 := by
    simpa [prefixWord, tailWord_268947, baseEnd_268947] using wordTrace_append hprefix tailTrace_268947
  have hstable : (prefixWord ++ tailWord_268947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268947).length < 2 ^ (prefixWord ++ tailWord_268947).sum := by decide
  have hdescent : baseEnd_268947 < baseStart_268947 := by decide
  rcases family_descends (prefixWord ++ tailWord_268947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268982 : List Nat := [5, 1, 3, 1, 2, 1, 2, 2, 1, 3, 2]
def baseStart_268982 : Nat := 118140960795 + 268982 * 2 ^ 59
def prefixEnd_268982 : Nat := 4983230072969 + 3 ^ 40 * 268982 * 2
def baseEnd_268982 : Nat := 138117053407771840387981

theorem tailTrace_268982 : CollatzResearch.WordTrace tailWord_268982 prefixEnd_268982 138117053407771840387981 := by
  unfold tailWord_268982
  simp only [CollatzResearch.WordTrace]
  refine ⟨613161219470726707085075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6540386341021084875574133 613161219470726707085075)
  ·
    refine ⟨919741829206090060627613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 613161219470726707085075 919741829206090060627613)
    ·
      refine ⟨344903185952283772735355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 919741829206090060627613 344903185952283772735355)
      ·
        refine ⟨517354778928425659103033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344903185952283772735355 517354778928425659103033)
        ·
          refine ⟨388016084196319244327275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 517354778928425659103033 388016084196319244327275)
          ·
            refine ⟨582024126294478866490913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 388016084196319244327275 582024126294478866490913)
            ·
              refine ⟨436518094720859149868185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 582024126294478866490913 436518094720859149868185)
              ·
                refine ⟨327388571040644362401139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 436518094720859149868185 327388571040644362401139)
                ·
                  refine ⟨491082856560966543601709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 327388571040644362401139 491082856560966543601709)
                  ·
                    refine ⟨184156071210362453850641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 491082856560966543601709 184156071210362453850641)
                    ·
                      refine ⟨138117053407771840387981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 184156071210362453850641 138117053407771840387981)
                      ·
                        rfl

theorem cell23_268982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_268982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_268982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_268982 prefixEnd_268982 := by exact prefixLift 268982
  have htrace : WordTrace (prefixWord ++ tailWord_268982) baseStart_268982 baseEnd_268982 := by
    simpa [prefixWord, tailWord_268982, baseEnd_268982] using wordTrace_append hprefix tailTrace_268982
  have hstable : (prefixWord ++ tailWord_268982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268982).length < 2 ^ (prefixWord ++ tailWord_268982).sum := by decide
  have hdescent : baseEnd_268982 < baseStart_268982 := by decide
  rcases family_descends (prefixWord ++ tailWord_268982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269034 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 6, 1, 4]
def baseStart_269034 : Nat := 118140960795 + 269034 * 2 ^ 59
def prefixEnd_269034 : Nat := 4983230072969 + 3 ^ 40 * 269034 * 2
def baseEnd_269034 : Nat := 138143754401805636937741

theorem tailTrace_269034 : CollatzResearch.WordTrace tailWord_269034 prefixEnd_269034 138143754401805636937741 := by
  unfold tailWord_269034
  simp only [CollatzResearch.WordTrace]
  refine ⟨2453119026835810048563539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6541650738228826796169437 2453119026835810048563539)
  ·
    refine ⟨3679678540253715072845309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2453119026835810048563539 3679678540253715072845309)
    ·
      refine ⟨1379879452595143152316991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3679678540253715072845309 1379879452595143152316991)
      ·
        refine ⟨2069819178892714728475487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1379879452595143152316991 2069819178892714728475487)
        ·
          refine ⟨3104728768339072092713231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2069819178892714728475487 3104728768339072092713231)
          ·
            refine ⟨4657093152508608139069847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3104728768339072092713231 4657093152508608139069847)
            ·
              refine ⟨6985639728762912208604771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4657093152508608139069847 6985639728762912208604771)
              ·
                refine ⟨10478459593144368312907157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6985639728762912208604771 10478459593144368312907157)
                ·
                  refine ⟨491177793428642264667523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10478459593144368312907157 491177793428642264667523)
                  ·
                    refine ⟨736766690142963397001285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 491177793428642264667523 736766690142963397001285)
                    ·
                      refine ⟨138143754401805636937741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 736766690142963397001285 138143754401805636937741)
                      ·
                        rfl

theorem cell23_269034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_269034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269034 prefixEnd_269034 := by exact prefixLift 269034
  have htrace : WordTrace (prefixWord ++ tailWord_269034) baseStart_269034 baseEnd_269034 := by
    simpa [prefixWord, tailWord_269034, baseEnd_269034] using wordTrace_append hprefix tailTrace_269034
  have hstable : (prefixWord ++ tailWord_269034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269034).length < 2 ^ (prefixWord ++ tailWord_269034).sum := by decide
  have hdescent : baseEnd_269034 < baseStart_269034 := by decide
  rcases family_descends (prefixWord ++ tailWord_269034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269047 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 6]
def baseStart_269047 : Nat := 118140960795 + 269047 * 2 ^ 59
def prefixEnd_269047 : Nat := 4983230072969 + 3 ^ 40 * 269047 * 2
def baseEnd_269047 : Nat := 138150429650314086075181

theorem tailTrace_269047 : CollatzResearch.WordTrace tailWord_269047 prefixEnd_269047 138150429650314086075181 := by
  unfold tailWord_269047
  simp only [CollatzResearch.WordTrace]
  refine ⟨9812950256296143414477395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6541966837530762276318263 9812950256296143414477395)
  ·
    refine ⟨14719425384444215121716093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9812950256296143414477395 14719425384444215121716093)
    ·
      refine ⟨5519784519166580670643535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14719425384444215121716093 5519784519166580670643535)
      ·
        refine ⟨8279676778749871005965303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5519784519166580670643535 8279676778749871005965303)
        ·
          refine ⟨12419515168124806508947955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8279676778749871005965303 12419515168124806508947955)
          ·
            refine ⟨18629272752187209763421933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12419515168124806508947955 18629272752187209763421933)
            ·
              refine ⟨6985977282070203661283225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18629272752187209763421933 6985977282070203661283225)
              ·
                refine ⟨5239482961552652745962419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6985977282070203661283225 5239482961552652745962419)
                ·
                  refine ⟨7859224442328979118943629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5239482961552652745962419 7859224442328979118943629)
                  ·
                    refine ⟨2947209165873367169603861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7859224442328979118943629 2947209165873367169603861)
                    ·
                      refine ⟨138150429650314086075181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2947209165873367169603861 138150429650314086075181)
                      ·
                        rfl

theorem cell23_269047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_269047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269047 prefixEnd_269047 := by exact prefixLift 269047
  have htrace : WordTrace (prefixWord ++ tailWord_269047) baseStart_269047 baseEnd_269047 := by
    simpa [prefixWord, tailWord_269047, baseEnd_269047] using wordTrace_append hprefix tailTrace_269047
  have hstable : (prefixWord ++ tailWord_269047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269047).length < 2 ^ (prefixWord ++ tailWord_269047).sum := by decide
  have hdescent : baseEnd_269047 < baseStart_269047 := by decide
  rcases family_descends (prefixWord ++ tailWord_269047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269085 : List Nat := [1, 4, 2, 4, 1, 1, 1, 1, 2, 4, 2]
def baseStart_269085 : Nat := 118140960795 + 269085 * 2 ^ 59
def prefixEnd_269085 : Nat := 4983230072969 + 3 ^ 40 * 269085 * 2
def baseEnd_269085 : Nat := 138169941915184937400007

theorem tailTrace_269085 : CollatzResearch.WordTrace tailWord_269085 prefixEnd_269085 138169941915184937400007 := by
  unfold tailWord_269085
  simp only [CollatzResearch.WordTrace]
  refine ⟨9814336230158475904360709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6542890820105650602907139 9814336230158475904360709)
  ·
    refine ⟨1840188043154714232067633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9814336230158475904360709 1840188043154714232067633)
    ·
      refine ⟨1380141032366035674050725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1840188043154714232067633 1380141032366035674050725)
      ·
        refine ⟨258776443568631688884511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1380141032366035674050725 258776443568631688884511)
        ·
          refine ⟨388164665352947533326767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258776443568631688884511 388164665352947533326767)
          ·
            refine ⟨582246998029421299990151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 388164665352947533326767 582246998029421299990151)
            ·
              refine ⟨873370497044131949985227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 582246998029421299990151 873370497044131949985227)
              ·
                refine ⟨1310055745566197924977841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 873370497044131949985227 1310055745566197924977841)
                ·
                  refine ⟨982541809174648443733381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1310055745566197924977841 982541809174648443733381)
                  ·
                    refine ⟨184226589220246583200009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 982541809174648443733381 184226589220246583200009)
                    ·
                      refine ⟨138169941915184937400007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 184226589220246583200009 138169941915184937400007)
                      ·
                        rfl

theorem cell23_269085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_269085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269085 prefixEnd_269085 := by exact prefixLift 269085
  have htrace : WordTrace (prefixWord ++ tailWord_269085) baseStart_269085 baseEnd_269085 := by
    simpa [prefixWord, tailWord_269085, baseEnd_269085] using wordTrace_append hprefix tailTrace_269085
  have hstable : (prefixWord ++ tailWord_269085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269085).length < 2 ^ (prefixWord ++ tailWord_269085).sum := by decide
  have hdescent : baseEnd_269085 < baseStart_269085 := by decide
  rcases family_descends (prefixWord ++ tailWord_269085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269111 : List Nat := [1, 1, 3, 1, 2, 1, 5, 1, 1, 5, 2]
def baseStart_269111 : Nat := 118140960795 + 269111 * 2 ^ 59
def prefixEnd_269111 : Nat := 4983230072969 + 3 ^ 40 * 269111 * 2
def baseEnd_269111 : Nat := 138183292412201835674887

theorem tailTrace_269111 : CollatzResearch.WordTrace tailWord_269111 prefixEnd_269111 138183292412201835674887 := by
  unfold tailWord_269111
  simp only [CollatzResearch.WordTrace]
  refine ⟨9815284528064282344807187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6543523018709521563204791 9815284528064282344807187)
  ·
    refine ⟨14722926792096423517210781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9815284528064282344807187 14722926792096423517210781)
    ·
      refine ⟨5521097547036158818954043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14722926792096423517210781 5521097547036158818954043)
      ·
        refine ⟨8281646320554238228431065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5521097547036158818954043 8281646320554238228431065)
        ·
          refine ⟨6211234740415678671323299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8281646320554238228431065 6211234740415678671323299)
          ·
            refine ⟨9316852110623518006984949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6211234740415678671323299 9316852110623518006984949)
            ·
              refine ⟨873454885370954813154839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9316852110623518006984949 873454885370954813154839)
              ·
                refine ⟨1310182328056432219732259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 873454885370954813154839 1310182328056432219732259)
                ·
                  refine ⟨1965273492084648329598389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1310182328056432219732259 1965273492084648329598389)
                  ·
                    refine ⟨184244389882935780899849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1965273492084648329598389 184244389882935780899849)
                    ·
                      refine ⟨138183292412201835674887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 184244389882935780899849 138183292412201835674887)
                      ·
                        rfl

theorem cell23_269111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 5, 2].length) (baseStart_269111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269111 prefixEnd_269111 := by exact prefixLift 269111
  have htrace : WordTrace (prefixWord ++ tailWord_269111) baseStart_269111 baseEnd_269111 := by
    simpa [prefixWord, tailWord_269111, baseEnd_269111] using wordTrace_append hprefix tailTrace_269111
  have hstable : (prefixWord ++ tailWord_269111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269111).length < 2 ^ (prefixWord ++ tailWord_269111).sum := by decide
  have hdescent : baseEnd_269111 < baseStart_269111 := by decide
  rcases family_descends (prefixWord ++ tailWord_269111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269134 : List Nat := [4, 1, 1, 1, 1, 1, 1, 4, 3, 6]
def baseStart_269134 : Nat := 118140960795 + 269134 * 2 ^ 59
def prefixEnd_269134 : Nat := 4983230072969 + 3 ^ 40 * 269134 * 2
def baseEnd_269134 : Nat := 46065034155751748562427

theorem tailTrace_269134 : CollatzResearch.WordTrace tailWord_269134 prefixEnd_269134 46065034155751748562427 := by
  unfold tailWord_269134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1227015425872619659111807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6544082271320638181929637 1227015425872619659111807)
  ·
    refine ⟨1840523138808929488667711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1227015425872619659111807 1840523138808929488667711)
    ·
      refine ⟨2760784708213394233001567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1840523138808929488667711 2760784708213394233001567)
      ·
        refine ⟨4141177062320091349502351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2760784708213394233001567 4141177062320091349502351)
        ·
          refine ⟨6211765593480137024253527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4141177062320091349502351 6211765593480137024253527)
          ·
            refine ⟨9317648390220205536380291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6211765593480137024253527 9317648390220205536380291)
            ·
              refine ⟨13976472585330308304570437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9317648390220205536380291 13976472585330308304570437)
              ·
                refine ⟨2620588609749432807106957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13976472585330308304570437 2620588609749432807106957)
                ·
                  refine ⟨982720728656037302665109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2620588609749432807106957 982720728656037302665109)
                  ·
                    refine ⟨46065034155751748562427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 982720728656037302665109 46065034155751748562427)
                    ·
                      rfl

theorem cell23_269134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_269134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269134 prefixEnd_269134 := by exact prefixLift 269134
  have htrace : WordTrace (prefixWord ++ tailWord_269134) baseStart_269134 baseEnd_269134 := by
    simpa [prefixWord, tailWord_269134, baseEnd_269134] using wordTrace_append hprefix tailTrace_269134
  have hstable : (prefixWord ++ tailWord_269134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269134).length < 2 ^ (prefixWord ++ tailWord_269134).sum := by decide
  have hdescent : baseEnd_269134 < baseStart_269134 := by decide
  rcases family_descends (prefixWord ++ tailWord_269134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269164 : List Nat := [2, 2, 1, 1, 4, 1, 3, 9]
def baseStart_269164 : Nat := 118140960795 + 269164 * 2 ^ 59
def prefixEnd_269164 : Nat := 4983230072969 + 3 ^ 40 * 269164 * 2
def baseEnd_269164 : Nat := 5118907662477412159709

theorem tailTrace_269164 : CollatzResearch.WordTrace tailWord_269164 prefixEnd_269164 5118907662477412159709 := by
  unfold tailWord_269164
  simp only [CollatzResearch.WordTrace]
  refine ⟨4908608798436136198243273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6544811731248181597657697 4908608798436136198243273)
  ·
    refine ⟨3681456598827102148682455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4908608798436136198243273 3681456598827102148682455)
    ·
      refine ⟨5522184898240653223023683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3681456598827102148682455 5522184898240653223023683)
      ·
        refine ⟨8283277347360979834535525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5522184898240653223023683 8283277347360979834535525)
        ·
          refine ⟨1553114502630183718975411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8283277347360979834535525 1553114502630183718975411)
          ·
            refine ⟨2329671753945275578463117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1553114502630183718975411 2329671753945275578463117)
            ·
              refine ⟨873626907729478341923669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2329671753945275578463117 873626907729478341923669)
              ·
                refine ⟨5118907662477412159709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 873626907729478341923669 5118907662477412159709)
                ·
                  rfl

theorem cell23_269164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 9].length) (baseStart_269164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269164 prefixEnd_269164 := by exact prefixLift 269164
  have htrace : WordTrace (prefixWord ++ tailWord_269164) baseStart_269164 baseEnd_269164 := by
    simpa [prefixWord, tailWord_269164, baseEnd_269164] using wordTrace_append hprefix tailTrace_269164
  have hstable : (prefixWord ++ tailWord_269164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269164).length < 2 ^ (prefixWord ++ tailWord_269164).sum := by decide
  have hdescent : baseEnd_269164 < baseStart_269164 := by decide
  rcases family_descends (prefixWord ++ tailWord_269164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269186 : List Nat := [3, 4, 2, 2, 2, 1, 1, 1, 3, 1, 3]
def baseStart_269186 : Nat := 118140960795 + 269186 * 2 ^ 59
def prefixEnd_269186 : Nat := 4983230072969 + 3 ^ 40 * 269186 * 2
def baseEnd_269186 : Nat := 138221803461289042237043

theorem tailTrace_269186 : CollatzResearch.WordTrace tailWord_269186 prefixEnd_269186 138221803461289042237043 := by
  unfold tailWord_269186
  simp only [CollatzResearch.WordTrace]
  refine ⟨2454505000698142538446853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6545346668528380102524941 2454505000698142538446853)
  ·
    refine ⟨460219687630901725958785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2454505000698142538446853 460219687630901725958785)
    ·
      refine ⟨345164765723176294469089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 460219687630901725958785 345164765723176294469089)
      ·
        refine ⟨258873574292382220851817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 345164765723176294469089 258873574292382220851817)
        ·
          refine ⟨194155180719286665638863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258873574292382220851817 194155180719286665638863)
          ·
            refine ⟨291232771078929998458295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194155180719286665638863 291232771078929998458295)
            ·
              refine ⟨436849156618394997687443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291232771078929998458295 436849156618394997687443)
              ·
                refine ⟨655273734927592496531165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 436849156618394997687443 655273734927592496531165)
                ·
                  refine ⟨245727650597847186199187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 655273734927592496531165 245727650597847186199187)
                  ·
                    refine ⟨368591475896770779298781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 245727650597847186199187 368591475896770779298781)
                    ·
                      refine ⟨138221803461289042237043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 368591475896770779298781 138221803461289042237043)
                      ·
                        rfl

theorem cell23_269186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_269186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269186 prefixEnd_269186 := by exact prefixLift 269186
  have htrace : WordTrace (prefixWord ++ tailWord_269186) baseStart_269186 baseEnd_269186 := by
    simpa [prefixWord, tailWord_269186, baseEnd_269186] using wordTrace_append hprefix tailTrace_269186
  have hstable : (prefixWord ++ tailWord_269186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269186).length < 2 ^ (prefixWord ++ tailWord_269186).sum := by decide
  have hdescent : baseEnd_269186 < baseStart_269186 := by decide
  rcases family_descends (prefixWord ++ tailWord_269186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269192 : List Nat := [2, 1, 3, 3, 2, 3, 1, 1, 3, 2, 2]
def baseStart_269192 : Nat := 118140960795 + 269192 * 2 ^ 59
def prefixEnd_269192 : Nat := 4983230072969 + 3 ^ 40 * 269192 * 2
def baseEnd_269192 : Nat := 138224884345216018762015

theorem tailTrace_269192 : CollatzResearch.WordTrace tailWord_269192 prefixEnd_269192 138224884345216018762015 := by
  unfold tailWord_269192
  simp only [CollatzResearch.WordTrace]
  refine ⟨4909119420385416589252915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6545492560513888785670553 4909119420385416589252915)
  ·
    refine ⟨7363679130578124883879373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4909119420385416589252915 7363679130578124883879373)
    ·
      refine ⟨2761379673966796831454765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7363679130578124883879373 2761379673966796831454765)
      ·
        refine ⟨1035517377737548811795537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2761379673966796831454765 1035517377737548811795537)
        ·
          refine ⟨776638033303161608846653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1035517377737548811795537 776638033303161608846653)
          ·
            refine ⟨291239262488685603317495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 776638033303161608846653 291239262488685603317495)
            ·
              refine ⟨436858893733028404976243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291239262488685603317495 436858893733028404976243)
              ·
                refine ⟨655288340599542607464365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 436858893733028404976243 655288340599542607464365)
                ·
                  refine ⟨245733127724828477799137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 655288340599542607464365 245733127724828477799137)
                  ·
                    refine ⟨184299845793621358349353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 245733127724828477799137 184299845793621358349353)
                    ·
                      refine ⟨138224884345216018762015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 184299845793621358349353 138224884345216018762015)
                      ·
                        rfl

theorem cell23_269192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_269192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269192 prefixEnd_269192 := by exact prefixLift 269192
  have htrace : WordTrace (prefixWord ++ tailWord_269192) baseStart_269192 baseEnd_269192 := by
    simpa [prefixWord, tailWord_269192, baseEnd_269192] using wordTrace_append hprefix tailTrace_269192
  have hstable : (prefixWord ++ tailWord_269192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269192).length < 2 ^ (prefixWord ++ tailWord_269192).sum := by decide
  have hdescent : baseEnd_269192 < baseStart_269192 := by decide
  rcases family_descends (prefixWord ++ tailWord_269192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269201 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 2, 7, 2]
def baseStart_269201 : Nat := 118140960795 + 269201 * 2 ^ 59
def prefixEnd_269201 : Nat := 4983230072969 + 3 ^ 40 * 269201 * 2
def baseEnd_269201 : Nat := 138229505671106483549473

theorem tailTrace_269201 : CollatzResearch.WordTrace tailWord_269201 prefixEnd_269201 138229505671106483549473 := by
  unfold tailWord_269201
  simp only [CollatzResearch.WordTrace]
  refine ⟨9818567097738227715583457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6545711398492151810388971 9818567097738227715583457)
  ·
    refine ⟨7363925323303670786687593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9818567097738227715583457 7363925323303670786687593)
    ·
      refine ⟨5522943992477753090015695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7363925323303670786687593 5522943992477753090015695)
      ·
        refine ⟨8284415988716629635023543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5522943992477753090015695 8284415988716629635023543)
        ·
          refine ⟨12426623983074944452535315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8284415988716629635023543 12426623983074944452535315)
          ·
            refine ⟨18639935974612416678802973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12426623983074944452535315 18639935974612416678802973)
            ·
              refine ⟨6989975990479656254551115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18639935974612416678802973 6989975990479656254551115)
              ·
                refine ⟨10484963985719484381826673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6989975990479656254551115 10484963985719484381826673)
                ·
                  refine ⟨7863722989289613286370005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10484963985719484381826673 7863722989289613286370005)
                  ·
                    refine ⟨184306007561475311399297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7863722989289613286370005 184306007561475311399297)
                    ·
                      refine ⟨138229505671106483549473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 184306007561475311399297 138229505671106483549473)
                      ·
                        rfl

theorem cell23_269201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 7, 2].length) (baseStart_269201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269201 prefixEnd_269201 := by exact prefixLift 269201
  have htrace : WordTrace (prefixWord ++ tailWord_269201) baseStart_269201 baseEnd_269201 := by
    simpa [prefixWord, tailWord_269201, baseEnd_269201] using wordTrace_append hprefix tailTrace_269201
  have hstable : (prefixWord ++ tailWord_269201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269201).length < 2 ^ (prefixWord ++ tailWord_269201).sum := by decide
  have hdescent : baseEnd_269201 < baseStart_269201 := by decide
  rcases family_descends (prefixWord ++ tailWord_269201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269212 : List Nat := [2, 2, 3, 3, 2, 2, 1, 2, 1, 2, 3]
def baseStart_269212 : Nat := 118140960795 + 269212 * 2 ^ 59
def prefixEnd_269212 : Nat := 4983230072969 + 3 ^ 40 * 269212 * 2
def baseEnd_269212 : Nat := 138235153958305940511923

theorem tailTrace_269212 : CollatzResearch.WordTrace tailWord_269212 prefixEnd_269212 138235153958305940511923 := by
  unfold tailWord_269212
  simp only [CollatzResearch.WordTrace]
  refine ⟨4909484150349188297116945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6545978867132251062822593 4909484150349188297116945)
  ·
    refine ⟨3682113112761891222837709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4909484150349188297116945 3682113112761891222837709)
    ·
      refine ⟨1380792417285709208564141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3682113112761891222837709 1380792417285709208564141)
      ·
        refine ⟨517797156482140953211553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1380792417285709208564141 517797156482140953211553)
        ·
          refine ⟨388347867361605714908665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 517797156482140953211553 388347867361605714908665)
          ·
            refine ⟨291260900521204286181499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 388347867361605714908665 291260900521204286181499)
            ·
              refine ⟨436891350781806429272249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291260900521204286181499 436891350781806429272249)
              ·
                refine ⟨327668513086354821954187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 436891350781806429272249 327668513086354821954187)
                ·
                  refine ⟨491502769629532232931281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 327668513086354821954187 491502769629532232931281)
                  ·
                    refine ⟨368627077222149174698461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 491502769629532232931281 368627077222149174698461)
                    ·
                      refine ⟨138235153958305940511923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 368627077222149174698461 138235153958305940511923)
                      ·
                        rfl

theorem cell23_269212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_269212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269212 prefixEnd_269212 := by exact prefixLift 269212
  have htrace : WordTrace (prefixWord ++ tailWord_269212) baseStart_269212 baseEnd_269212 := by
    simpa [prefixWord, tailWord_269212, baseEnd_269212] using wordTrace_append hprefix tailTrace_269212
  have hstable : (prefixWord ++ tailWord_269212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269212).length < 2 ^ (prefixWord ++ tailWord_269212).sum := by decide
  have hdescent : baseEnd_269212 < baseStart_269212 := by decide
  rcases family_descends (prefixWord ++ tailWord_269212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269229 : List Nat := [1, 5, 2, 3, 1, 1, 3, 1, 1, 2, 3]
def baseStart_269229 : Nat := 118140960795 + 269229 * 2 ^ 59
def prefixEnd_269229 : Nat := 4983230072969 + 3 ^ 40 * 269229 * 2
def baseEnd_269229 : Nat := 138243883129432373999345

theorem tailTrace_269229 : CollatzResearch.WordTrace tailWord_269229 prefixEnd_269229 138243883129432373999345 := by
  unfold tailWord_269229
  simp only [CollatzResearch.WordTrace]
  refine ⟨9819588341636788497602741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6546392227757858998401827 9819588341636788497602741)
  ·
    refine ⟨920586407028448921650257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9819588341636788497602741 920586407028448921650257)
    ·
      refine ⟨690439805271336691237693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 920586407028448921650257 690439805271336691237693)
      ·
        refine ⟨258914926976751259214135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 690439805271336691237693 258914926976751259214135)
        ·
          refine ⟨388372390465126888821203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258914926976751259214135 388372390465126888821203)
          ·
            refine ⟨582558585697690333231805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 388372390465126888821203 582558585697690333231805)
            ·
              refine ⟨218459469636633874961927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 582558585697690333231805 218459469636633874961927)
              ·
                refine ⟨327689204454950812442891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218459469636633874961927 327689204454950812442891)
                ·
                  refine ⟨491533806682426218664337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 327689204454950812442891 491533806682426218664337)
                  ·
                    refine ⟨368650355011819663998253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 491533806682426218664337 368650355011819663998253)
                    ·
                      refine ⟨138243883129432373999345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 368650355011819663998253 138243883129432373999345)
                      ·
                        rfl

theorem cell23_269229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_269229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269229 prefixEnd_269229 := by exact prefixLift 269229
  have htrace : WordTrace (prefixWord ++ tailWord_269229) baseStart_269229 baseEnd_269229 := by
    simpa [prefixWord, tailWord_269229, baseEnd_269229] using wordTrace_append hprefix tailTrace_269229
  have hstable : (prefixWord ++ tailWord_269229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269229).length < 2 ^ (prefixWord ++ tailWord_269229).sum := by decide
  have hdescent : baseEnd_269229 < baseStart_269229 := by decide
  rcases family_descends (prefixWord ++ tailWord_269229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269265 : List Nat := [1, 2, 2, 1, 2, 1, 3, 5, 2, 2, 2]
def baseStart_269265 : Nat := 118140960795 + 269265 * 2 ^ 59
def prefixEnd_269265 : Nat := 4983230072969 + 3 ^ 40 * 269265 * 2
def baseEnd_269265 : Nat := 138262368432994233149179

theorem tailTrace_269265 : CollatzResearch.WordTrace tailWord_269265 prefixEnd_269265 138262368432994233149179 := by
  unfold tailWord_269265
  simp only [CollatzResearch.WordTrace]
  refine ⟨9820901369506366645913249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6547267579670911097275499 9820901369506366645913249)
  ·
    refine ⟨7365676027129774984434937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9820901369506366645913249 7365676027129774984434937)
    ·
      refine ⟨5524257020347331238326203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7365676027129774984434937 5524257020347331238326203)
      ·
        refine ⟨8286385530520996857489305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5524257020347331238326203 8286385530520996857489305)
        ·
          refine ⟨6214789147890747643116979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8286385530520996857489305 6214789147890747643116979)
          ·
            refine ⟨9322183721836121464675469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6214789147890747643116979 9322183721836121464675469)
            ·
              refine ⟨3495818895688545549253301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9322183721836121464675469 3495818895688545549253301)
              ·
                refine ⟨327733021470801145242497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3495818895688545549253301 327733021470801145242497)
                ·
                  refine ⟨245799766103100858931873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 327733021470801145242497 245799766103100858931873)
                  ·
                    refine ⟨184349824577325644198905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 245799766103100858931873 184349824577325644198905)
                    ·
                      refine ⟨138262368432994233149179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 184349824577325644198905 138262368432994233149179)
                      ·
                        rfl

theorem cell23_269265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 2, 2, 2].length) (baseStart_269265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269265 prefixEnd_269265 := by exact prefixLift 269265
  have htrace : WordTrace (prefixWord ++ tailWord_269265) baseStart_269265 baseEnd_269265 := by
    simpa [prefixWord, tailWord_269265, baseEnd_269265] using wordTrace_append hprefix tailTrace_269265
  have hstable : (prefixWord ++ tailWord_269265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269265).length < 2 ^ (prefixWord ++ tailWord_269265).sum := by decide
  have hdescent : baseEnd_269265 < baseStart_269265 := by decide
  rcases family_descends (prefixWord ++ tailWord_269265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269281 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 3, 5, 3]
def baseStart_269281 : Nat := 118140960795 + 269281 * 2 ^ 59
def prefixEnd_269281 : Nat := 4983230072969 + 3 ^ 40 * 269281 * 2
def baseEnd_269281 : Nat := 138270584123466170549105

theorem tailTrace_269281 : CollatzResearch.WordTrace tailWord_269281 prefixEnd_269281 138270584123466170549105 := by
  unfold tailWord_269281
  simp only [CollatzResearch.WordTrace]
  refine ⟨9821484937448401378495697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6547656624965600918997131 9821484937448401378495697)
  ·
    refine ⟨7366113703086301033871773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9821484937448401378495697 7366113703086301033871773)
    ·
      refine ⟨2762292638657362887701915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7366113703086301033871773 2762292638657362887701915)
      ·
        refine ⟨4143438957986044331552873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2762292638657362887701915 4143438957986044331552873)
        ·
          refine ⟨3107579218489533248664655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4143438957986044331552873 3107579218489533248664655)
          ·
            refine ⟨4661368827734299872996983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3107579218489533248664655 4661368827734299872996983)
            ·
              refine ⟨6992053241601449809495475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4661368827734299872996983 6992053241601449809495475)
              ·
                refine ⟨10488079862402174714243213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6992053241601449809495475 10488079862402174714243213)
                ·
                  refine ⟨3933029948400815517841205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10488079862402174714243213 3933029948400815517841205)
                  ·
                    refine ⟨368721557662576454797613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3933029948400815517841205 368721557662576454797613)
                    ·
                      refine ⟨138270584123466170549105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 368721557662576454797613 138270584123466170549105)
                      ·
                        rfl

theorem cell23_269281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_269281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269281 prefixEnd_269281 := by exact prefixLift 269281
  have htrace : WordTrace (prefixWord ++ tailWord_269281) baseStart_269281 baseEnd_269281 := by
    simpa [prefixWord, tailWord_269281, baseEnd_269281] using wordTrace_append hprefix tailTrace_269281
  have hstable : (prefixWord ++ tailWord_269281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269281).length < 2 ^ (prefixWord ++ tailWord_269281).sum := by decide
  have hdescent : baseEnd_269281 < baseStart_269281 := by decide
  rcases family_descends (prefixWord ++ tailWord_269281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269282 : List Nat := [3, 3, 3, 1, 1, 1, 2, 2, 1, 4, 2]
def baseStart_269282 : Nat := 118140960795 + 269282 * 2 ^ 59
def prefixEnd_269282 : Nat := 4983230072969 + 3 ^ 40 * 269282 * 2
def baseEnd_269282 : Nat := 138271097604120666636601

theorem tailTrace_269282 : CollatzResearch.WordTrace tailWord_269282 prefixEnd_269282 138271097604120666636601 := by
  unfold tailWord_269282
  simp only [CollatzResearch.WordTrace]
  refine ⟨2455380352611194637320525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6547680940296519032854733 2455380352611194637320525)
  ·
    refine ⟨920767632229197988995197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2455380352611194637320525 920767632229197988995197)
    ·
      refine ⟨345287862085949245873199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 920767632229197988995197 345287862085949245873199)
      ·
        refine ⟨517931793128923868809799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 345287862085949245873199 517931793128923868809799)
        ·
          refine ⟨776897689693385803214699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 517931793128923868809799 776897689693385803214699)
          ·
            refine ⟨1165346534540078704822049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 776897689693385803214699 1165346534540078704822049)
            ·
              refine ⟨874009900905059028616537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1165346534540078704822049 874009900905059028616537)
              ·
                refine ⟨655507425678794271462403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 874009900905059028616537 655507425678794271462403)
                ·
                  refine ⟨983261138518191407193605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 655507425678794271462403 983261138518191407193605)
                  ·
                    refine ⟨184361463472160888848801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 983261138518191407193605 184361463472160888848801)
                    ·
                      refine ⟨138271097604120666636601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 184361463472160888848801 138271097604120666636601)
                      ·
                        rfl

theorem cell23_269282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_269282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269282 prefixEnd_269282 := by exact prefixLift 269282
  have htrace : WordTrace (prefixWord ++ tailWord_269282) baseStart_269282 baseEnd_269282 := by
    simpa [prefixWord, tailWord_269282, baseEnd_269282] using wordTrace_append hprefix tailTrace_269282
  have hstable : (prefixWord ++ tailWord_269282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269282).length < 2 ^ (prefixWord ++ tailWord_269282).sum := by decide
  have hdescent : baseEnd_269282 < baseStart_269282 := by decide
  rcases family_descends (prefixWord ++ tailWord_269282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269288 : List Nat := [2, 1, 4, 1, 1, 1, 3, 5, 5]
def baseStart_269288 : Nat := 118140960795 + 269288 * 2 ^ 59
def prefixEnd_269288 : Nat := 4983230072969 + 3 ^ 40 * 269288 * 2
def baseEnd_269288 : Nat := 15363797609783071462397

theorem tailTrace_269288 : CollatzResearch.WordTrace tailWord_269288 prefixEnd_269288 15363797609783071462397 := by
  unfold tailWord_269288
  simp only [CollatzResearch.WordTrace]
  refine ⟨4910870124211520787000259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6547826832282027716000345 4910870124211520787000259)
  ·
    refine ⟨7366305186317281180500389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4910870124211520787000259 7366305186317281180500389)
    ·
      refine ⟨1381182222434490221343823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7366305186317281180500389 1381182222434490221343823)
      ·
        refine ⟨2071773333651735332015735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1381182222434490221343823 2071773333651735332015735)
        ·
          refine ⟨3107660000477602998023603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2071773333651735332015735 3107660000477602998023603)
          ·
            refine ⟨4661490000716404497035405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3107660000477602998023603 4661490000716404497035405)
            ·
              refine ⟨1748058750268651686388277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4661490000716404497035405 1748058750268651686388277)
              ·
                refine ⟨163880507837686095598901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1748058750268651686388277 163880507837686095598901)
                ·
                  refine ⟨15363797609783071462397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 163880507837686095598901 15363797609783071462397)
                  ·
                    rfl

theorem cell23_269288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 5, 5].length) (baseStart_269288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269288 prefixEnd_269288 := by exact prefixLift 269288
  have htrace : WordTrace (prefixWord ++ tailWord_269288) baseStart_269288 baseEnd_269288 := by
    simpa [prefixWord, tailWord_269288, baseEnd_269288] using wordTrace_append hprefix tailTrace_269288
  have hstable : (prefixWord ++ tailWord_269288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269288).length < 2 ^ (prefixWord ++ tailWord_269288).sum := by decide
  have hdescent : baseEnd_269288 < baseStart_269288 := by decide
  rcases family_descends (prefixWord ++ tailWord_269288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269338 : List Nat := [3, 1, 1, 3, 1, 2, 2, 3, 2, 1, 4]
def baseStart_269338 : Nat := 118140960795 + 269338 * 2 ^ 59
def prefixEnd_269338 : Nat := 4983230072969 + 3 ^ 40 * 269338 * 2
def baseEnd_269338 : Nat := 138299852520772447536343

theorem tailTrace_269338 : CollatzResearch.WordTrace tailWord_269338 prefixEnd_269338 138299852520772447536343 := by
  unfold tailWord_269338
  simp only [CollatzResearch.WordTrace]
  refine ⟨2455890974560475028330167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6549042598827933408880445 2455890974560475028330167)
  ·
    refine ⟨3683836461840712542495251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2455890974560475028330167 3683836461840712542495251)
    ·
      refine ⟨5525754692761068813742877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3683836461840712542495251 5525754692761068813742877)
      ·
        refine ⟨2072158009785400805153579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5525754692761068813742877 2072158009785400805153579)
        ·
          refine ⟨3108237014678101207730369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2072158009785400805153579 3108237014678101207730369)
          ·
            refine ⟨2331177761008575905797777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3108237014678101207730369 2331177761008575905797777)
            ·
              refine ⟨1748383320756431929348333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2331177761008575905797777 1748383320756431929348333)
              ·
                refine ⟨655643745283661973505625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1748383320756431929348333 655643745283661973505625)
                ·
                  refine ⟨491732808962746480129219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 655643745283661973505625 491732808962746480129219)
                  ·
                    refine ⟨737599213444119720193829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 491732808962746480129219 737599213444119720193829)
                    ·
                      refine ⟨138299852520772447536343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 737599213444119720193829 138299852520772447536343)
                      ·
                        rfl

theorem cell23_269338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_269338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269338 prefixEnd_269338 := by exact prefixLift 269338
  have htrace : WordTrace (prefixWord ++ tailWord_269338) baseStart_269338 baseEnd_269338 := by
    simpa [prefixWord, tailWord_269338, baseEnd_269338] using wordTrace_append hprefix tailTrace_269338
  have hstable : (prefixWord ++ tailWord_269338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269338).length < 2 ^ (prefixWord ++ tailWord_269338).sum := by decide
  have hdescent : baseEnd_269338 < baseStart_269338 := by decide
  rcases family_descends (prefixWord ++ tailWord_269338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269361 : List Nat := [1, 2, 2, 3, 1, 2, 1, 3, 8]
def baseStart_269361 : Nat := 118140960795 + 269361 * 2 ^ 59
def prefixEnd_269361 : Nat := 4983230072969 + 3 ^ 40 * 269361 * 2
def baseEnd_269361 : Nat := 15367962508425095283193

theorem tailTrace_269361 : CollatzResearch.WordTrace tailWord_269361 prefixEnd_269361 15367962508425095283193 := by
  unfold tailWord_269361
  simp only [CollatzResearch.WordTrace]
  refine ⟨9824402777158575041407937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6549601851439050027605291 9824402777158575041407937)
  ·
    refine ⟨7368302082868931281055953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9824402777158575041407937 7368302082868931281055953)
    ·
      refine ⟨5526226562151698460791965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7368302082868931281055953 5526226562151698460791965)
      ·
        refine ⟨2072334960806886922796987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5526226562151698460791965 2072334960806886922796987)
        ·
          refine ⟨3108502441210330384195481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2072334960806886922796987 3108502441210330384195481)
          ·
            refine ⟨2331376830907747788146611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3108502441210330384195481 2331376830907747788146611)
            ·
              refine ⟨3497065246361621682219917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2331376830907747788146611 3497065246361621682219917)
              ·
                refine ⟨1311399467385608130832469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3497065246361621682219917 1311399467385608130832469)
                ·
                  refine ⟨15367962508425095283193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1311399467385608130832469 15367962508425095283193)
                  ·
                    rfl

theorem cell23_269361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 8].length) (baseStart_269361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269361 prefixEnd_269361 := by exact prefixLift 269361
  have htrace : WordTrace (prefixWord ++ tailWord_269361) baseStart_269361 baseEnd_269361 := by
    simpa [prefixWord, tailWord_269361, baseEnd_269361] using wordTrace_append hprefix tailTrace_269361
  have hstable : (prefixWord ++ tailWord_269361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269361).length < 2 ^ (prefixWord ++ tailWord_269361).sum := by decide
  have hdescent : baseEnd_269361 < baseStart_269361 := by decide
  rcases family_descends (prefixWord ++ tailWord_269361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269381 : List Nat := [1, 3, 1, 1, 1, 3, 2, 2, 1, 2, 6]
def baseStart_269381 : Nat := 118140960795 + 269381 * 2 ^ 59
def prefixEnd_269381 : Nat := 4983230072969 + 3 ^ 40 * 269381 * 2
def baseEnd_269381 : Nat := 138321932188915779298645

theorem tailTrace_269381 : CollatzResearch.WordTrace tailWord_269381 prefixEnd_269381 138321932188915779298645 := by
  unfold tailWord_269381
  simp only [CollatzResearch.WordTrace]
  refine ⟨9825132237086118457135997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6550088158057412304757331 9825132237086118457135997)
  ·
    refine ⟨3684424588907294421425999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9825132237086118457135997 3684424588907294421425999)
    ·
      refine ⟨5526636883360941632138999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3684424588907294421425999 5526636883360941632138999)
      ·
        refine ⟨8289955325041412448208499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5526636883360941632138999 8289955325041412448208499)
        ·
          refine ⟨12434932987562118672312749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8289955325041412448208499 12434932987562118672312749)
          ·
            refine ⟨4663099870335794502117281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12434932987562118672312749 4663099870335794502117281)
            ·
              refine ⟨3497324902751845876587961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4663099870335794502117281 3497324902751845876587961)
              ·
                refine ⟨2622993677063884407440971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3497324902751845876587961 2622993677063884407440971)
                ·
                  refine ⟨3934490515595826611161457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2622993677063884407440971 3934490515595826611161457)
                  ·
                    refine ⟨2950867886696869958371093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3934490515595826611161457 2950867886696869958371093)
                    ·
                      refine ⟨138321932188915779298645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2950867886696869958371093 138321932188915779298645)
                      ·
                        rfl

theorem cell23_269381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_269381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269381 prefixEnd_269381 := by exact prefixLift 269381
  have htrace : WordTrace (prefixWord ++ tailWord_269381) baseStart_269381 baseEnd_269381 := by
    simpa [prefixWord, tailWord_269381, baseEnd_269381] using wordTrace_append hprefix tailTrace_269381
  have hstable : (prefixWord ++ tailWord_269381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269381).length < 2 ^ (prefixWord ++ tailWord_269381).sum := by decide
  have hdescent : baseEnd_269381 < baseStart_269381 := by decide
  rcases family_descends (prefixWord ++ tailWord_269381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269401 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 2, 4, 5]
def baseStart_269401 : Nat := 118140960795 + 269401 * 2 ^ 59
def prefixEnd_269401 : Nat := 4983230072969 + 3 ^ 40 * 269401 * 2
def baseEnd_269401 : Nat := 138332201802005701048553

theorem tailTrace_269401 : CollatzResearch.WordTrace tailWord_269401 prefixEnd_269401 138332201802005701048553 := by
  unfold tailWord_269401
  simp only [CollatzResearch.WordTrace]
  refine ⟨9825861697013661872864057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6550574464675774581909371 9825861697013661872864057)
  ·
    refine ⟨7369396272760246404648043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9825861697013661872864057 7369396272760246404648043)
    ·
      refine ⟨11054094409140369606972065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7369396272760246404648043 11054094409140369606972065)
      ·
        refine ⟨8290570806855277205229049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11054094409140369606972065 8290570806855277205229049)
        ·
          refine ⟨6217928105141457903921787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8290570806855277205229049 6217928105141457903921787)
          ·
            refine ⟨9326892157712186855882681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6217928105141457903921787 9326892157712186855882681)
            ·
              refine ⟨6995169118284140141912011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9326892157712186855882681 6995169118284140141912011)
              ·
                refine ⟨10492753677426210212868017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6995169118284140141912011 10492753677426210212868017)
                ·
                  refine ⟨7869565258069657659651013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10492753677426210212868017 7869565258069657659651013)
                  ·
                    refine ⟨1475543485888060811184565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7869565258069657659651013 1475543485888060811184565)
                    ·
                      refine ⟨138332201802005701048553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1475543485888060811184565 138332201802005701048553)
                      ·
                        rfl

theorem cell23_269401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_269401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269401 prefixEnd_269401 := by exact prefixLift 269401
  have htrace : WordTrace (prefixWord ++ tailWord_269401) baseStart_269401 baseEnd_269401 := by
    simpa [prefixWord, tailWord_269401, baseEnd_269401] using wordTrace_append hprefix tailTrace_269401
  have hstable : (prefixWord ++ tailWord_269401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269401).length < 2 ^ (prefixWord ++ tailWord_269401).sum := by decide
  have hdescent : baseEnd_269401 < baseStart_269401 := by decide
  rcases family_descends (prefixWord ++ tailWord_269401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269451 : List Nat := [1, 1, 1, 1, 4, 1, 1, 13]
def baseStart_269451 : Nat := 118140960795 + 269451 * 2 ^ 59
def prefixEnd_269451 : Nat := 4983230072969 + 3 ^ 40 * 269451 * 2
def baseEnd_269451 : Nat := 5124365771656685386049

theorem tailTrace_269451 : CollatzResearch.WordTrace tailWord_269451 prefixEnd_269451 5124365771656685386049 := by
  unfold tailWord_269451
  simp only [CollatzResearch.WordTrace]
  refine ⟨9827685346832520412184207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6551790231221680274789471 9827685346832520412184207)
  ·
    refine ⟨14741528020248780618276311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9827685346832520412184207 14741528020248780618276311)
    ·
      refine ⟨22112292030373170927414467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14741528020248780618276311 22112292030373170927414467)
      ·
        refine ⟨33168438045559756391121701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22112292030373170927414467 33168438045559756391121701)
        ·
          refine ⟨6219082133542454323335319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33168438045559756391121701 6219082133542454323335319)
          ·
            refine ⟨9328623200313681485002979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6219082133542454323335319 9328623200313681485002979)
            ·
              refine ⟨13992934800470522227504469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9328623200313681485002979 13992934800470522227504469)
              ·
                refine ⟨5124365771656685386049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 13992934800470522227504469 5124365771656685386049)
                ·
                  rfl

theorem cell23_269451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 13].length) (baseStart_269451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269451 prefixEnd_269451 := by exact prefixLift 269451
  have htrace : WordTrace (prefixWord ++ tailWord_269451) baseStart_269451 baseEnd_269451 := by
    simpa [prefixWord, tailWord_269451, baseEnd_269451] using wordTrace_append hprefix tailTrace_269451
  have hstable : (prefixWord ++ tailWord_269451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269451).length < 2 ^ (prefixWord ++ tailWord_269451).sum := by decide
  have hdescent : baseEnd_269451 < baseStart_269451 := by decide
  rcases family_descends (prefixWord ++ tailWord_269451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269468 : List Nat := [2, 2, 3, 2, 1, 3, 10]
def baseStart_269468 : Nat := 118140960795 + 269468 * 2 ^ 59
def prefixEnd_269468 : Nat := 4983230072969 + 3 ^ 40 * 269468 * 2
def baseEnd_269468 : Nat := 1708229691430332579145

theorem tailTrace_269468 : CollatzResearch.WordTrace tailWord_269468 prefixEnd_269468 1708229691430332579145 := by
  unfold tailWord_269468
  simp only [CollatzResearch.WordTrace]
  refine ⟨4914152693885466157776529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6552203591847288210368705 4914152693885466157776529)
  ·
    refine ⟨3685614520414099618332397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4914152693885466157776529 3685614520414099618332397)
    ·
      refine ⟨1382105445155287356874649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3685614520414099618332397 1382105445155287356874649)
      ·
        refine ⟨1036579083866465517655987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1382105445155287356874649 1036579083866465517655987)
        ·
          refine ⟨1554868625799698276483981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1036579083866465517655987 1554868625799698276483981)
          ·
            refine ⟨583075734674886853681493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1554868625799698276483981 583075734674886853681493)
            ·
              refine ⟨1708229691430332579145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 583075734674886853681493 1708229691430332579145)
              ·
                rfl

theorem cell23_269468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 10].length) (baseStart_269468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269468 prefixEnd_269468 := by exact prefixLift 269468
  have htrace : WordTrace (prefixWord ++ tailWord_269468) baseStart_269468 baseEnd_269468 := by
    simpa [prefixWord, tailWord_269468, baseEnd_269468] using wordTrace_append hprefix tailTrace_269468
  have hstable : (prefixWord ++ tailWord_269468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269468).length < 2 ^ (prefixWord ++ tailWord_269468).sum := by decide
  have hdescent : baseEnd_269468 < baseStart_269468 := by decide
  rcases family_descends (prefixWord ++ tailWord_269468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269479 : List Nat := [1, 1, 6, 2, 1, 1, 1, 3, 3, 2, 2]
def baseStart_269479 : Nat := 118140960795 + 269479 * 2 ^ 59
def prefixEnd_269479 : Nat := 4983230072969 + 3 ^ 40 * 269479 * 2
def baseEnd_269479 : Nat := 138372253293056395873195

theorem tailTrace_269479 : CollatzResearch.WordTrace tailWord_269479 prefixEnd_269479 138372253293056395873195 := by
  unfold tailWord_269479
  simp only [CollatzResearch.WordTrace]
  refine ⟨9828706590731081194203491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6552471060487387462802327 9828706590731081194203491)
  ·
    refine ⟨14743059886096621791305237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9828706590731081194203491 14743059886096621791305237)
    ·
      refine ⟨691080932160779146467433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14743059886096621791305237 691080932160779146467433)
      ·
        refine ⟨518310699120584359850575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 691080932160779146467433 518310699120584359850575)
        ·
          refine ⟨777466048680876539775863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 518310699120584359850575 777466048680876539775863)
          ·
            refine ⟨1166199073021314809663795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 777466048680876539775863 1166199073021314809663795)
            ·
              refine ⟨1749298609531972214495693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1166199073021314809663795 1749298609531972214495693)
              ·
                refine ⟨655986978574489580435885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1749298609531972214495693 655986978574489580435885)
                ·
                  refine ⟨245995116965433592663457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 655986978574489580435885 245995116965433592663457)
                  ·
                    refine ⟨184496337724075194497593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 245995116965433592663457 184496337724075194497593)
                    ·
                      refine ⟨138372253293056395873195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 184496337724075194497593 138372253293056395873195)
                      ·
                        rfl

theorem cell23_269479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_269479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269479 prefixEnd_269479 := by exact prefixLift 269479
  have htrace : WordTrace (prefixWord ++ tailWord_269479) baseStart_269479 baseEnd_269479 := by
    simpa [prefixWord, tailWord_269479, baseEnd_269479] using wordTrace_append hprefix tailTrace_269479
  have hstable : (prefixWord ++ tailWord_269479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269479).length < 2 ^ (prefixWord ++ tailWord_269479).sum := by decide
  have hdescent : baseEnd_269479 < baseStart_269479 := by decide
  rcases family_descends (prefixWord ++ tailWord_269479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269482 : List Nat := [3, 1, 5, 1, 1, 2, 1, 2, 1, 1, 5]
def baseStart_269482 : Nat := 118140960795 + 269482 * 2 ^ 59
def prefixEnd_269482 : Nat := 4983230072969 + 3 ^ 40 * 269482 * 2
def baseEnd_269482 : Nat := 138373793735019884135681

theorem tailTrace_269482 : CollatzResearch.WordTrace tailWord_269482 prefixEnd_269482 138373793735019884135681 := by
  unfold tailWord_269482
  simp only [CollatzResearch.WordTrace]
  refine ⟨2457204002430053176640675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6552544006480141804375133 2457204002430053176640675)
  ·
    refine ⟨3685806003645079764961013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2457204002430053176640675 3685806003645079764961013)
    ·
      refine ⟨345544312841726227965095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3685806003645079764961013 345544312841726227965095)
      ·
        refine ⟨518316469262589341947643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 345544312841726227965095 518316469262589341947643)
        ·
          refine ⟨777474703893884012921465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 518316469262589341947643 777474703893884012921465)
          ·
            refine ⟨583106027920413009691099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 777474703893884012921465 583106027920413009691099)
            ·
              refine ⟨874659041880619514536649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 583106027920413009691099 874659041880619514536649)
              ·
                refine ⟨655994281410464635902487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 874659041880619514536649 655994281410464635902487)
                ·
                  refine ⟨983991422115696953853731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 655994281410464635902487 983991422115696953853731)
                  ·
                    refine ⟨1475987133173545430780597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 983991422115696953853731 1475987133173545430780597)
                    ·
                      refine ⟨138373793735019884135681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1475987133173545430780597 138373793735019884135681)
                      ·
                        rfl

theorem cell23_269482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_269482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269482 prefixEnd_269482 := by exact prefixLift 269482
  have htrace : WordTrace (prefixWord ++ tailWord_269482) baseStart_269482 baseEnd_269482 := by
    simpa [prefixWord, tailWord_269482, baseEnd_269482] using wordTrace_append hprefix tailTrace_269482
  have hstable : (prefixWord ++ tailWord_269482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269482).length < 2 ^ (prefixWord ++ tailWord_269482).sum := by decide
  have hdescent : baseEnd_269482 < baseStart_269482 := by decide
  rcases family_descends (prefixWord ++ tailWord_269482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269489 : List Nat := [1, 2, 2, 5, 1, 2, 3, 1, 2, 4]
def baseStart_269489 : Nat := 118140960795 + 269489 * 2 ^ 59
def prefixEnd_269489 : Nat := 4983230072969 + 3 ^ 40 * 269489 * 2
def baseEnd_269489 : Nat := 46125796033200452249383

theorem tailTrace_269489 : CollatzResearch.WordTrace tailWord_269489 prefixEnd_269489 46125796033200452249383 := by
  unfold tailWord_269489
  simp only [CollatzResearch.WordTrace]
  refine ⟨9829071320694852902067521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6552714213796568601378347 9829071320694852902067521)
  ·
    refine ⟨7371803490521139676550641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9829071320694852902067521 7371803490521139676550641)
    ·
      refine ⟨5528852617890854757412981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7371803490521139676550641 5528852617890854757412981)
      ·
        refine ⟨518329932927267633507467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5528852617890854757412981 518329932927267633507467)
        ·
          refine ⟨777494899390901450261201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 518329932927267633507467 777494899390901450261201)
          ·
            refine ⟨583121174543176087695901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 777494899390901450261201 583121174543176087695901)
            ·
              refine ⟨218670440453691032885963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 583121174543176087695901 218670440453691032885963)
              ·
                refine ⟨328005660680536549328945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218670440453691032885963 328005660680536549328945)
                ·
                  refine ⟨246004245510402411996709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 328005660680536549328945 246004245510402411996709)
                  ·
                    refine ⟨46125796033200452249383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 246004245510402411996709 46125796033200452249383)
                    ·
                      rfl

theorem cell23_269489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 2, 4].length) (baseStart_269489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269489 prefixEnd_269489 := by exact prefixLift 269489
  have htrace : WordTrace (prefixWord ++ tailWord_269489) baseStart_269489 baseEnd_269489 := by
    simpa [prefixWord, tailWord_269489, baseEnd_269489] using wordTrace_append hprefix tailTrace_269489
  have hstable : (prefixWord ++ tailWord_269489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269489).length < 2 ^ (prefixWord ++ tailWord_269489).sum := by decide
  have hdescent : baseEnd_269489 < baseStart_269489 := by decide
  rcases family_descends (prefixWord ++ tailWord_269489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269502 : List Nat := [4, 2, 1, 1, 3, 3, 2, 7]
def baseStart_269502 : Nat := 118140960795 + 269502 * 2 ^ 59
def prefixEnd_269502 : Nat := 4983230072969 + 3 ^ 40 * 269502 * 2
def baseEnd_269502 : Nat := 5125335679559622440207

theorem tailTrace_269502 : CollatzResearch.WordTrace tailWord_269502 prefixEnd_269502 5125335679559622440207 := by
  unfold tailWord_269502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1228693183705969515286345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6553030313098504081527173 1228693183705969515286345)
  ·
    refine ⟨921519887779477136464759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1228693183705969515286345 921519887779477136464759)
    ·
      refine ⟨1382279831669215704697139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 921519887779477136464759 1382279831669215704697139)
      ·
        refine ⟨2073419747503823557045709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1382279831669215704697139 2073419747503823557045709)
        ·
          refine ⟨777532405313933833892141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2073419747503823557045709 777532405313933833892141)
          ·
            refine ⟨291574651992725187709553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 777532405313933833892141 291574651992725187709553)
            ·
              refine ⟨218680988994543890782165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 291574651992725187709553 218680988994543890782165)
              ·
                refine ⟨5125335679559622440207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 218680988994543890782165 5125335679559622440207)
                ·
                  rfl

theorem cell23_269502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 7].length) (baseStart_269502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269502 prefixEnd_269502 := by exact prefixLift 269502
  have htrace : WordTrace (prefixWord ++ tailWord_269502) baseStart_269502 baseEnd_269502 := by
    simpa [prefixWord, tailWord_269502, baseEnd_269502] using wordTrace_append hprefix tailTrace_269502
  have hstable : (prefixWord ++ tailWord_269502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269502).length < 2 ^ (prefixWord ++ tailWord_269502).sum := by decide
  have hdescent : baseEnd_269502 < baseStart_269502 := by decide
  rcases family_descends (prefixWord ++ tailWord_269502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269546 : List Nat := [3, 1, 3, 1, 1, 5, 2, 1, 2, 1, 3]
def baseStart_269546 : Nat := 118140960795 + 269546 * 2 ^ 59
def prefixEnd_269546 : Nat := 4983230072969 + 3 ^ 40 * 269546 * 2
def baseEnd_269546 : Nat := 138406656496907633735387

theorem tailTrace_269546 : CollatzResearch.WordTrace tailWord_269546 prefixEnd_269546 138406656496907633735387 := by
  unfold tailWord_269546
  simp only [CollatzResearch.WordTrace]
  refine ⟨2457787570372087909223123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6554100187658901091261661 2457787570372087909223123)
  ·
    refine ⟨3686681355558131863834685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2457787570372087909223123 3686681355558131863834685)
    ·
      refine ⟨1382505508334299448938007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3686681355558131863834685 1382505508334299448938007)
      ·
        refine ⟨2073758262501449173407011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1382505508334299448938007 2073758262501449173407011)
        ·
          refine ⟨3110637393752173760110517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2073758262501449173407011 3110637393752173760110517)
          ·
            refine ⟨291622255664266290010361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3110637393752173760110517 291622255664266290010361)
            ·
              refine ⟨218716691748199717507771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 291622255664266290010361 218716691748199717507771)
              ·
                refine ⟨328075037622299576261657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218716691748199717507771 328075037622299576261657)
                ·
                  refine ⟨246056278216724682196243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 328075037622299576261657 246056278216724682196243)
                  ·
                    refine ⟨369084417325087023294365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 246056278216724682196243 369084417325087023294365)
                    ·
                      refine ⟨138406656496907633735387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 369084417325087023294365 138406656496907633735387)
                      ·
                        rfl

theorem cell23_269546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_269546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269546 prefixEnd_269546 := by exact prefixLift 269546
  have htrace : WordTrace (prefixWord ++ tailWord_269546) baseStart_269546 baseEnd_269546 := by
    simpa [prefixWord, tailWord_269546, baseEnd_269546] using wordTrace_append hprefix tailTrace_269546
  have hstable : (prefixWord ++ tailWord_269546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269546).length < 2 ^ (prefixWord ++ tailWord_269546).sum := by decide
  have hdescent : baseEnd_269546 < baseStart_269546 := by decide
  rcases family_descends (prefixWord ++ tailWord_269546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269585 : List Nat := [1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 3]
def baseStart_269585 : Nat := 118140960795 + 269585 * 2 ^ 59
def prefixEnd_269585 : Nat := 4983230072969 + 3 ^ 40 * 269585 * 2
def baseEnd_269585 : Nat := 138426682242432981147707

theorem tailTrace_269585 : CollatzResearch.WordTrace tailWord_269585 prefixEnd_269585 138426682242432981147707 := by
  unfold tailWord_269585
  simp only [CollatzResearch.WordTrace]
  refine ⟨9832572728347061297562209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6555048485564707531708139 9832572728347061297562209)
  ·
    refine ⟨7374429546260295973171657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9832572728347061297562209 7374429546260295973171657)
    ·
      refine ⟨5530822159695221979878743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7374429546260295973171657 5530822159695221979878743)
      ·
        refine ⟨8296233239542832969818115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5530822159695221979878743 8296233239542832969818115)
        ·
          refine ⟨12444349859314249454727173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8296233239542832969818115 12444349859314249454727173)
          ·
            refine ⟨2333315598621421772761345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12444349859314249454727173 2333315598621421772761345)
            ·
              refine ⟨1749986698966066329571009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2333315598621421772761345 1749986698966066329571009)
              ·
                refine ⟨1312490024224549747178257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1749986698966066329571009 1312490024224549747178257)
                ·
                  refine ⟨984367518168412310383693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1312490024224549747178257 984367518168412310383693)
                  ·
                    refine ⟨369137819313154616393885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 984367518168412310383693 369137819313154616393885)
                    ·
                      refine ⟨138426682242432981147707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 369137819313154616393885 138426682242432981147707)
                      ·
                        rfl

theorem cell23_269585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 3].length) (baseStart_269585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269585 prefixEnd_269585 := by exact prefixLift 269585
  have htrace : WordTrace (prefixWord ++ tailWord_269585) baseStart_269585 baseEnd_269585 := by
    simpa [prefixWord, tailWord_269585, baseEnd_269585] using wordTrace_append hprefix tailTrace_269585
  have hstable : (prefixWord ++ tailWord_269585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269585).length < 2 ^ (prefixWord ++ tailWord_269585).sum := by decide
  have hdescent : baseEnd_269585 < baseStart_269585 := by decide
  rcases family_descends (prefixWord ++ tailWord_269585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269592 : List Nat := [2, 1, 2, 3, 1, 4, 1, 4, 5]
def baseStart_269592 : Nat := 118140960795 + 269592 * 2 ^ 59
def prefixEnd_269592 : Nat := 4983230072969 + 3 ^ 40 * 269592 * 2
def baseEnd_269592 : Nat := 15381141845223828195575

theorem tailTrace_269592 : CollatzResearch.WordTrace tailWord_269592 prefixEnd_269592 15381141845223828195575 := by
  unfold tailWord_269592
  simp only [CollatzResearch.WordTrace]
  refine ⟨4916414019660850746533515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6555218692881134328711353 4916414019660850746533515)
  ·
    refine ⟨7374621029491276119800273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4916414019660850746533515 7374621029491276119800273)
    ·
      refine ⟨5530965772118457089850205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7374621029491276119800273 5530965772118457089850205)
      ·
        refine ⟨2074112164544421408693827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5530965772118457089850205 2074112164544421408693827)
        ·
          refine ⟨3111168246816632113040741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2074112164544421408693827 3111168246816632113040741)
          ·
            refine ⟨583344046278118521195139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3111168246816632113040741 583344046278118521195139)
            ·
              refine ⟨875016069417177781792709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 583344046278118521195139 875016069417177781792709)
              ·
                refine ⟨164065513015720834086133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 875016069417177781792709 164065513015720834086133)
                ·
                  refine ⟨15381141845223828195575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 164065513015720834086133 15381141845223828195575)
                  ·
                    rfl

theorem cell23_269592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 4, 5].length) (baseStart_269592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269592 prefixEnd_269592 := by exact prefixLift 269592
  have htrace : WordTrace (prefixWord ++ tailWord_269592) baseStart_269592 baseEnd_269592 := by
    simpa [prefixWord, tailWord_269592, baseEnd_269592] using wordTrace_append hprefix tailTrace_269592
  have hstable : (prefixWord ++ tailWord_269592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269592).length < 2 ^ (prefixWord ++ tailWord_269592).sum := by decide
  have hdescent : baseEnd_269592 < baseStart_269592 := by decide
  rcases family_descends (prefixWord ++ tailWord_269592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269635 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 7, 4]
def baseStart_269635 : Nat := 118140960795 + 269635 * 2 ^ 59
def prefixEnd_269635 : Nat := 4983230072969 + 3 ^ 40 * 269635 * 2
def baseEnd_269635 : Nat := 46150785425052595174159

theorem tailTrace_269635 : CollatzResearch.WordTrace tailWord_269635 prefixEnd_269635 46150785425052595174159 := by
  unfold tailWord_269635
  simp only [CollatzResearch.WordTrace]
  refine ⟨9834396378165919836882359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6556264252110613224588239 9834396378165919836882359)
  ·
    refine ⟨14751594567248879755323539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9834396378165919836882359 14751594567248879755323539)
    ·
      refine ⟨22127391850873319632985309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14751594567248879755323539 22127391850873319632985309)
      ·
        refine ⟨8297771944077494862369491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22127391850873319632985309 8297771944077494862369491)
        ·
          refine ⟨12446657916116242293554237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8297771944077494862369491 12446657916116242293554237)
          ·
            refine ⟨4667496718543590860082839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12446657916116242293554237 4667496718543590860082839)
            ·
              refine ⟨7001245077815386290124259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4667496718543590860082839 7001245077815386290124259)
              ·
                refine ⟨10501867616723079435186389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7001245077815386290124259 10501867616723079435186389)
                ·
                  refine ⟨246137522266947174262181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10501867616723079435186389 246137522266947174262181)
                  ·
                    refine ⟨46150785425052595174159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 246137522266947174262181 46150785425052595174159)
                    ·
                      rfl

theorem cell23_269635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 7, 4].length) (baseStart_269635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269635 prefixEnd_269635 := by exact prefixLift 269635
  have htrace : WordTrace (prefixWord ++ tailWord_269635) baseStart_269635 baseEnd_269635 := by
    simpa [prefixWord, tailWord_269635, baseEnd_269635] using wordTrace_append hprefix tailTrace_269635
  have hstable : (prefixWord ++ tailWord_269635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269635).length < 2 ^ (prefixWord ++ tailWord_269635).sum := by decide
  have hdescent : baseEnd_269635 < baseStart_269635 := by decide
  rcases family_descends (prefixWord ++ tailWord_269635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269654 : List Nat := [5, 2, 3, 1, 1, 1, 3, 1, 2, 2, 2]
def baseStart_269654 : Nat := 118140960795 + 269654 * 2 ^ 59
def prefixEnd_269654 : Nat := 4983230072969 + 3 ^ 40 * 269654 * 2
def baseEnd_269654 : Nat := 138462112407593211184891

theorem tailTrace_269654 : CollatzResearch.WordTrace tailWord_269654 prefixEnd_269654 138462112407593211184891 := by
  unfold tailWord_269654
  simp only [CollatzResearch.WordTrace]
  refine ⟨614693085318567880114001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6556726243398057387882677 614693085318567880114001)
  ·
    refine ⟨461019813988925910085501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 614693085318567880114001 461019813988925910085501)
    ·
      refine ⟨172882430245847216282063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 461019813988925910085501 172882430245847216282063)
      ·
        refine ⟨259323645368770824423095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172882430245847216282063 259323645368770824423095)
        ·
          refine ⟨388985468053156236634643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259323645368770824423095 388985468053156236634643)
          ·
            refine ⟨583478202079734354951965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 388985468053156236634643 583478202079734354951965)
            ·
              refine ⟨218804325779900383106987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 583478202079734354951965 218804325779900383106987)
              ·
                refine ⟨328206488669850574660481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218804325779900383106987 328206488669850574660481)
                ·
                  refine ⟨246154866502387930995361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 328206488669850574660481 246154866502387930995361)
                  ·
                    refine ⟨184616149876790948246521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 246154866502387930995361 184616149876790948246521)
                    ·
                      refine ⟨138462112407593211184891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 184616149876790948246521 138462112407593211184891)
                      ·
                        rfl

theorem cell23_269654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_269654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269654 prefixEnd_269654 := by exact prefixLift 269654
  have htrace : WordTrace (prefixWord ++ tailWord_269654) baseStart_269654 baseEnd_269654 := by
    simpa [prefixWord, tailWord_269654, baseEnd_269654] using wordTrace_append hprefix tailTrace_269654
  have hstable : (prefixWord ++ tailWord_269654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269654).length < 2 ^ (prefixWord ++ tailWord_269654).sum := by decide
  have hdescent : baseEnd_269654 < baseStart_269654 := by decide
  rcases family_descends (prefixWord ++ tailWord_269654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269665 : List Nat := [1, 2, 3, 1, 1, 1, 1, 7, 6]
def baseStart_269665 : Nat := 118140960795 + 269665 * 2 ^ 59
def prefixEnd_269665 : Nat := 4983230072969 + 3 ^ 40 * 269665 * 2
def baseEnd_269665 : Nat := 15385306743865852016371

theorem tailTrace_269665 : CollatzResearch.WordTrace tailWord_269665 prefixEnd_269665 15385306743865852016371 := by
  unfold tailWord_269665
  simp only [CollatzResearch.WordTrace]
  refine ⟨9835490568057234960474449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6556993712038156640316299 9835490568057234960474449)
  ·
    refine ⟨7376617926042926220355837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9835490568057234960474449 7376617926042926220355837)
    ·
      refine ⟨2766231722266097332633439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7376617926042926220355837 2766231722266097332633439)
      ·
        refine ⟨4149347583399145998950159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2766231722266097332633439 4149347583399145998950159)
        ·
          refine ⟨6224021375098718998425239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4149347583399145998950159 6224021375098718998425239)
          ·
            refine ⟨9336032062648078497637859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6224021375098718998425239 9336032062648078497637859)
            ·
              refine ⟨14004048093972117746456789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9336032062648078497637859 14004048093972117746456789)
              ·
                refine ⟨328219877202471509682581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 14004048093972117746456789 328219877202471509682581)
                ·
                  refine ⟨15385306743865852016371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 328219877202471509682581 15385306743865852016371)
                  ·
                    rfl

theorem cell23_269665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 6].length) (baseStart_269665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269665 prefixEnd_269665 := by exact prefixLift 269665
  have htrace : WordTrace (prefixWord ++ tailWord_269665) baseStart_269665 baseEnd_269665 := by
    simpa [prefixWord, tailWord_269665, baseEnd_269665] using wordTrace_append hprefix tailTrace_269665
  have hstable : (prefixWord ++ tailWord_269665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269665).length < 2 ^ (prefixWord ++ tailWord_269665).sum := by decide
  have hdescent : baseEnd_269665 < baseStart_269665 := by decide
  rcases family_descends (prefixWord ++ tailWord_269665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269716 : List Nat := [2, 4, 2, 1, 2, 3, 2, 1, 6]
def baseStart_269716 : Nat := 118140960795 + 269716 * 2 ^ 59
def prefixEnd_269716 : Nat := 4983230072969 + 3 ^ 40 * 269716 * 2
def baseEnd_269716 : Nat := 15388216467574663178845

theorem tailTrace_269716 : CollatzResearch.WordTrace tailWord_269716 prefixEnd_269716 15388216467574663178845 := by
  unfold tailWord_269716
  simp only [CollatzResearch.WordTrace]
  refine ⟨4918675345436235335290501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6558233793914980447054001 4918675345436235335290501)
  ·
    refine ⟨922251627269294125366969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4918675345436235335290501 922251627269294125366969)
    ·
      refine ⟨691688720451970594025227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 922251627269294125366969 691688720451970594025227)
      ·
        refine ⟨1037533080677955891037841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 691688720451970594025227 1037533080677955891037841)
        ·
          refine ⟨778149810508466918278381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1037533080677955891037841 778149810508466918278381)
          ·
            refine ⟨291806178940675094354393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 778149810508466918278381 291806178940675094354393)
            ·
              refine ⟨218854634205506320765795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 291806178940675094354393 218854634205506320765795)
              ·
                refine ⟨328281951308259481148693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218854634205506320765795 328281951308259481148693)
                ·
                  refine ⟨15388216467574663178845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 328281951308259481148693 15388216467574663178845)
                  ·
                    rfl

theorem cell23_269716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_269716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269716 prefixEnd_269716 := by exact prefixLift 269716
  have htrace : WordTrace (prefixWord ++ tailWord_269716) baseStart_269716 baseEnd_269716 := by
    simpa [prefixWord, tailWord_269716, baseEnd_269716] using wordTrace_append hprefix tailTrace_269716
  have hstable : (prefixWord ++ tailWord_269716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269716).length < 2 ^ (prefixWord ++ tailWord_269716).sum := by decide
  have hdescent : baseEnd_269716 < baseStart_269716 := by decide
  rcases family_descends (prefixWord ++ tailWord_269716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269752 : List Nat := [2, 1, 2, 1, 2, 2, 5, 1, 1, 1, 5]
def baseStart_269752 : Nat := 118140960795 + 269752 * 2 ^ 59
def prefixEnd_269752 : Nat := 4983230072969 + 3 ^ 40 * 269752 * 2
def baseEnd_269752 : Nat := 138512433511733827759439

theorem tailTrace_269752 : CollatzResearch.WordTrace tailWord_269752 prefixEnd_269752 138512433511733827759439 := by
  unfold tailWord_269752
  simp only [CollatzResearch.WordTrace]
  refine ⟨4919331859371024409445755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6559109145828032545927673 4919331859371024409445755)
  ·
    refine ⟨7378997789056536614168633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4919331859371024409445755 7378997789056536614168633)
    ·
      refine ⟨5534248341792402460626475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7378997789056536614168633 5534248341792402460626475)
      ·
        refine ⟨8301372512688603690939713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5534248341792402460626475 8301372512688603690939713)
        ·
          refine ⟨6226029384516452768204785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8301372512688603690939713 6226029384516452768204785)
          ·
            refine ⟨4669522038387339576153589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6226029384516452768204785 4669522038387339576153589)
            ·
              refine ⟨437767691098813085264399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4669522038387339576153589 437767691098813085264399)
              ·
                refine ⟨656651536648219627896599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 437767691098813085264399 656651536648219627896599)
                ·
                  refine ⟨984977304972329441844899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 656651536648219627896599 984977304972329441844899)
                  ·
                    refine ⟨1477465957458494162767349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 984977304972329441844899 1477465957458494162767349)
                    ·
                      refine ⟨138512433511733827759439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1477465957458494162767349 138512433511733827759439)
                      ·
                        rfl

theorem cell23_269752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 1, 1, 5].length) (baseStart_269752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269752 prefixEnd_269752 := by exact prefixLift 269752
  have htrace : WordTrace (prefixWord ++ tailWord_269752) baseStart_269752 baseEnd_269752 := by
    simpa [prefixWord, tailWord_269752, baseEnd_269752] using wordTrace_append hprefix tailTrace_269752
  have hstable : (prefixWord ++ tailWord_269752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269752).length < 2 ^ (prefixWord ++ tailWord_269752).sum := by decide
  have hdescent : baseEnd_269752 < baseStart_269752 := by decide
  rcases family_descends (prefixWord ++ tailWord_269752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269772 : List Nat := [2, 2, 1, 4, 2, 1, 3, 8]
def baseStart_269772 : Nat := 118140960795 + 269772 * 2 ^ 59
def prefixEnd_269772 : Nat := 4983230072969 + 3 ^ 40 * 269772 * 2
def baseEnd_269772 : Nat := 5130470486104583315161

theorem tailTrace_269772 : CollatzResearch.WordTrace tailWord_269772 prefixEnd_269772 5130470486104583315161 := by
  unfold tailWord_269772
  simp only [CollatzResearch.WordTrace]
  refine ⟨4919696589334796117309785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6559595452446394823079713 4919696589334796117309785)
  ·
    refine ⟨3689772442001097087982339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4919696589334796117309785 3689772442001097087982339)
    ·
      refine ⟨5534658663001645631973509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3689772442001097087982339 5534658663001645631973509)
      ·
        refine ⟨1037748499312808555995033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5534658663001645631973509 1037748499312808555995033)
        ·
          refine ⟨778311374484606416996275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1037748499312808555995033 778311374484606416996275)
          ·
            refine ⟨1167467061726909625494413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 778311374484606416996275 1167467061726909625494413)
            ·
              refine ⟨437800148147591109560405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1167467061726909625494413 437800148147591109560405)
              ·
                refine ⟨5130470486104583315161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 437800148147591109560405 5130470486104583315161)
                ·
                  rfl

theorem cell23_269772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 8].length) (baseStart_269772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269772 prefixEnd_269772 := by exact prefixLift 269772
  have htrace : WordTrace (prefixWord ++ tailWord_269772) baseStart_269772 baseEnd_269772 := by
    simpa [prefixWord, tailWord_269772, baseEnd_269772] using wordTrace_append hprefix tailTrace_269772
  have hstable : (prefixWord ++ tailWord_269772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269772).length < 2 ^ (prefixWord ++ tailWord_269772).sum := by decide
  have hdescent : baseEnd_269772 < baseStart_269772 := by decide
  rcases family_descends (prefixWord ++ tailWord_269772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269775 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 6]
def baseStart_269775 : Nat := 118140960795 + 269775 * 2 ^ 59
def prefixEnd_269775 : Nat := 4983230072969 + 3 ^ 40 * 269775 * 2
def baseEnd_269775 : Nat := 138524243566787237771833

theorem tailTrace_269775 : CollatzResearch.WordTrace tailWord_269775 prefixEnd_269775 138524243566787237771833 := by
  unfold tailWord_269775
  simp only [CollatzResearch.WordTrace]
  refine ⟨9839502597658723746978779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6559668398439149164652519 9839502597658723746978779)
  ·
    refine ⟨14759253896488085620468169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9839502597658723746978779 14759253896488085620468169)
    ·
      refine ⟨11069440422366064215351127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14759253896488085620468169 11069440422366064215351127)
      ·
        refine ⟨16604160633549096323026691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11069440422366064215351127 16604160633549096323026691)
        ·
          refine ⟨24906240950323644484540037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16604160633549096323026691 24906240950323644484540037)
          ·
            refine ⟨4669920178185683340851257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24906240950323644484540037 4669920178185683340851257)
            ·
              refine ⟨3502440133639262505638443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4669920178185683340851257 3502440133639262505638443)
              ·
                refine ⟨5253660200458893758457665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3502440133639262505638443 5253660200458893758457665)
                ·
                  refine ⟨3940245150344170318843249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5253660200458893758457665 3940245150344170318843249)
                  ·
                    refine ⟨2955183862758127739132437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3940245150344170318843249 2955183862758127739132437)
                    ·
                      refine ⟨138524243566787237771833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2955183862758127739132437 138524243566787237771833)
                      ·
                        rfl

theorem cell23_269775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 6].length) (baseStart_269775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269775 prefixEnd_269775 := by exact prefixLift 269775
  have htrace : WordTrace (prefixWord ++ tailWord_269775) baseStart_269775 baseEnd_269775 := by
    simpa [prefixWord, tailWord_269775, baseEnd_269775] using wordTrace_append hprefix tailTrace_269775
  have hstable : (prefixWord ++ tailWord_269775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269775).length < 2 ^ (prefixWord ++ tailWord_269775).sum := by decide
  have hdescent : baseEnd_269775 < baseStart_269775 := by decide
  rcases family_descends (prefixWord ++ tailWord_269775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269789 : List Nat := [1, 4, 3, 1, 1, 3, 3, 7]
def baseStart_269789 : Nat := 118140960795 + 269789 * 2 ^ 59
def prefixEnd_269789 : Nat := 4983230072969 + 3 ^ 40 * 269789 * 2
def baseEnd_269789 : Nat := 5130793788738895666547

theorem tailTrace_269789 : CollatzResearch.WordTrace tailWord_269789 prefixEnd_269789 5130793788738895666547 := by
  unfold tailWord_269789
  simp only [CollatzResearch.WordTrace]
  refine ⟨9840013219608004137988421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6560008813072002758658947 9840013219608004137988421)
  ·
    refine ⟨1845002478676500775872829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9840013219608004137988421 1845002478676500775872829)
    ·
      refine ⟨691875929503687790952311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1845002478676500775872829 691875929503687790952311)
      ·
        refine ⟨1037813894255531686428467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 691875929503687790952311 1037813894255531686428467)
        ·
          refine ⟨1556720841383297529642701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1037813894255531686428467 1556720841383297529642701)
          ·
            refine ⟨583770315518736573616013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1556720841383297529642701 583770315518736573616013)
            ·
              refine ⟨218913868319526215106005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 583770315518736573616013 218913868319526215106005)
              ·
                refine ⟨5130793788738895666547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 218913868319526215106005 5130793788738895666547)
                ·
                  rfl

theorem cell23_269789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 7].length) (baseStart_269789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269789 prefixEnd_269789 := by exact prefixLift 269789
  have htrace : WordTrace (prefixWord ++ tailWord_269789) baseStart_269789 baseEnd_269789 := by
    simpa [prefixWord, tailWord_269789, baseEnd_269789] using wordTrace_append hprefix tailTrace_269789
  have hstable : (prefixWord ++ tailWord_269789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269789).length < 2 ^ (prefixWord ++ tailWord_269789).sum := by decide
  have hdescent : baseEnd_269789 < baseStart_269789 := by decide
  rcases family_descends (prefixWord ++ tailWord_269789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269799 : List Nat := [1, 1, 5, 2, 1, 2, 2, 2, 1, 3, 3]
def baseStart_269799 : Nat := 118140960795 + 269799 * 2 ^ 59
def prefixEnd_269799 : Nat := 4983230072969 + 3 ^ 40 * 269799 * 2
def baseEnd_269799 : Nat := 138536567102495143871723

theorem tailTrace_269799 : CollatzResearch.WordTrace tailWord_269799 prefixEnd_269799 138536567102495143871723 := by
  unfold tailWord_269799
  simp only [CollatzResearch.WordTrace]
  refine ⟨9840377949571775845852451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6560251966381183897234967 9840377949571775845852451)
  ·
    refine ⟨14760566924357663768778677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9840377949571775845852451 14760566924357663768778677)
    ·
      refine ⟨1383803149158530978323001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14760566924357663768778677 1383803149158530978323001)
      ·
        refine ⟨1037852361868898233742251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1383803149158530978323001 1037852361868898233742251)
        ·
          refine ⟨1556778542803347350613377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1037852361868898233742251 1556778542803347350613377)
          ·
            refine ⟨1167583907102510512960033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1556778542803347350613377 1167583907102510512960033)
            ·
              refine ⟨875687930326882884720025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1167583907102510512960033 875687930326882884720025)
              ·
                refine ⟨656765947745162163540019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 875687930326882884720025 656765947745162163540019)
                ·
                  refine ⟨985148921617743245310029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 656765947745162163540019 985148921617743245310029)
                  ·
                    refine ⟨369430845606653716991261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 985148921617743245310029 369430845606653716991261)
                    ·
                      refine ⟨138536567102495143871723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 369430845606653716991261 138536567102495143871723)
                      ·
                        rfl

theorem cell23_269799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_269799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269799 prefixEnd_269799 := by exact prefixLift 269799
  have htrace : WordTrace (prefixWord ++ tailWord_269799) baseStart_269799 baseEnd_269799 := by
    simpa [prefixWord, tailWord_269799, baseEnd_269799] using wordTrace_append hprefix tailTrace_269799
  have hstable : (prefixWord ++ tailWord_269799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269799).length < 2 ^ (prefixWord ++ tailWord_269799).sum := by decide
  have hdescent : baseEnd_269799 < baseStart_269799 := by decide
  rcases family_descends (prefixWord ++ tailWord_269799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269816 : List Nat := [2, 1, 2, 1, 1, 5, 3, 2, 2, 1, 3]
def baseStart_269816 : Nat := 118140960795 + 269816 * 2 ^ 59
def prefixEnd_269816 : Nat := 4983230072969 + 3 ^ 40 * 269816 * 2
def baseEnd_269816 : Nat := 138545296273621577359145

theorem tailTrace_269816 : CollatzResearch.WordTrace tailWord_269816 prefixEnd_269816 138545296273621577359145 := by
  unfold tailWord_269816
  simp only [CollatzResearch.WordTrace]
  refine ⟨4920498995255093874610651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6560665327006791832814201 4920498995255093874610651)
  ·
    refine ⟨7380748492882640811915977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4920498995255093874610651 7380748492882640811915977)
    ·
      refine ⟨5535561369661980608936983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7380748492882640811915977 5535561369661980608936983)
      ·
        refine ⟨8303342054492970913405475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5535561369661980608936983 8303342054492970913405475)
        ·
          refine ⟨12455013081739456370108213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8303342054492970913405475 12455013081739456370108213)
          ·
            refine ⟨1167657476413074034697645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12455013081739456370108213 1167657476413074034697645)
            ·
              refine ⟨437871553654902763011617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1167657476413074034697645 437871553654902763011617)
              ·
                refine ⟨328403665241177072258713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 437871553654902763011617 328403665241177072258713)
                ·
                  refine ⟨246302748930882804194035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 328403665241177072258713 246302748930882804194035)
                  ·
                    refine ⟨369454123396324206291053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 246302748930882804194035 369454123396324206291053)
                    ·
                      refine ⟨138545296273621577359145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 369454123396324206291053 138545296273621577359145)
                      ·
                        rfl

theorem cell23_269816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 2, 1, 3].length) (baseStart_269816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269816 prefixEnd_269816 := by exact prefixLift 269816
  have htrace : WordTrace (prefixWord ++ tailWord_269816) baseStart_269816 baseEnd_269816 := by
    simpa [prefixWord, tailWord_269816, baseEnd_269816] using wordTrace_append hprefix tailTrace_269816
  have hstable : (prefixWord ++ tailWord_269816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269816).length < 2 ^ (prefixWord ++ tailWord_269816).sum := by decide
  have hdescent : baseEnd_269816 < baseStart_269816 := by decide
  rcases family_descends (prefixWord ++ tailWord_269816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269832 : List Nat := [2, 1, 3, 2, 1, 1, 4, 1, 2, 6]
def baseStart_269832 : Nat := 118140960795 + 269832 * 2 ^ 59
def prefixEnd_269832 : Nat := 4983230072969 + 3 ^ 40 * 269832 * 2
def baseEnd_269832 : Nat := 46184503988031171586357

theorem tailTrace_269832 : CollatzResearch.WordTrace tailWord_269832 prefixEnd_269832 46184503988031171586357 := by
  unfold tailWord_269832
  simp only [CollatzResearch.WordTrace]
  refine ⟨4920790779226111240901875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6561054372301481654535833 4920790779226111240901875)
  ·
    refine ⟨7381186168839166861352813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4920790779226111240901875 7381186168839166861352813)
    ·
      refine ⟨2767944813314687573007305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7381186168839166861352813 2767944813314687573007305)
      ·
        refine ⟨2075958609986015679755479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2767944813314687573007305 2075958609986015679755479)
        ·
          refine ⟨3113937914979023519633219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2075958609986015679755479 3113937914979023519633219)
          ·
            refine ⟨4670906872468535279449829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3113937914979023519633219 4670906872468535279449829)
            ·
              refine ⟨875795038587850364896843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4670906872468535279449829 875795038587850364896843)
              ·
                refine ⟨1313692557881775547345265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 875795038587850364896843 1313692557881775547345265)
                ·
                  refine ⟨985269418411331660508949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1313692557881775547345265 985269418411331660508949)
                  ·
                    refine ⟨46184503988031171586357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 985269418411331660508949 46184503988031171586357)
                    ·
                      rfl

theorem cell23_269832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_269832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269832 prefixEnd_269832 := by exact prefixLift 269832
  have htrace : WordTrace (prefixWord ++ tailWord_269832) baseStart_269832 baseEnd_269832 := by
    simpa [prefixWord, tailWord_269832, baseEnd_269832] using wordTrace_append hprefix tailTrace_269832
  have hstable : (prefixWord ++ tailWord_269832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269832).length < 2 ^ (prefixWord ++ tailWord_269832).sum := by decide
  have hdescent : baseEnd_269832 < baseStart_269832 := by decide
  rcases family_descends (prefixWord ++ tailWord_269832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269859 : List Nat := [1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 5]
def baseStart_269859 : Nat := 118140960795 + 269859 * 2 ^ 59
def prefixEnd_269859 : Nat := 4983230072969 + 3 ^ 40 * 269859 * 2
def baseEnd_269859 : Nat := 138567375941764909121447

theorem tailTrace_269859 : CollatzResearch.WordTrace tailWord_269859 prefixEnd_269859 138567375941764909121447 := by
  unfold tailWord_269859
  simp only [CollatzResearch.WordTrace]
  refine ⟨9842566329354406093036631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6561710886236270728691087 9842566329354406093036631)
  ·
    refine ⟨14763849494031609139554947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9842566329354406093036631 14763849494031609139554947)
    ·
      refine ⟨22145774241047413709332421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14763849494031609139554947 22145774241047413709332421)
      ·
        refine ⟨4152332670196390070499829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22145774241047413709332421 4152332670196390070499829)
        ·
          refine ⟨389281187830911569109359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4152332670196390070499829 389281187830911569109359)
          ·
            refine ⟨583921781746367353664039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 389281187830911569109359 583921781746367353664039)
            ·
              refine ⟨875882672619551030496059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 583921781746367353664039 875882672619551030496059)
              ·
                refine ⟨1313824008929326545744089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 875882672619551030496059 1313824008929326545744089)
                ·
                  refine ⟨985368006696994909308067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1313824008929326545744089 985368006696994909308067)
                  ·
                    refine ⟨1478052010045492363962101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 985368006696994909308067 1478052010045492363962101)
                    ·
                      refine ⟨138567375941764909121447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1478052010045492363962101 138567375941764909121447)
                      ·
                        rfl

theorem cell23_269859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_269859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269859 prefixEnd_269859 := by exact prefixLift 269859
  have htrace : WordTrace (prefixWord ++ tailWord_269859) baseStart_269859 baseEnd_269859 := by
    simpa [prefixWord, tailWord_269859, baseEnd_269859] using wordTrace_append hprefix tailTrace_269859
  have hstable : (prefixWord ++ tailWord_269859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269859).length < 2 ^ (prefixWord ++ tailWord_269859).sum := by decide
  have hdescent : baseEnd_269859 < baseStart_269859 := by decide
  rcases family_descends (prefixWord ++ tailWord_269859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269879 : List Nat := [1, 1, 3, 1, 2, 6, 1, 1, 7]
def baseStart_269879 : Nat := 118140960795 + 269879 * 2 ^ 59
def prefixEnd_269879 : Nat := 4983230072969 + 3 ^ 40 * 269879 * 2
def baseEnd_269879 : Nat := 15397516172761647874595

theorem tailTrace_269879 : CollatzResearch.WordTrace tailWord_269879 prefixEnd_269879 15397516172761647874595 := by
  unfold tailWord_269879
  simp only [CollatzResearch.WordTrace]
  refine ⟨9843295789281949508764691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6562197192854633005843127 9843295789281949508764691)
  ·
    refine ⟨14764943683922924263147037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9843295789281949508764691 14764943683922924263147037)
    ·
      refine ⟨5536853881471096598680139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14764943683922924263147037 5536853881471096598680139)
      ·
        refine ⟨8305280822206644898020209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5536853881471096598680139 8305280822206644898020209)
        ·
          refine ⟨6228960616654983673515157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8305280822206644898020209 6228960616654983673515157)
          ·
            refine ⟨291982528905702359696023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6228960616654983673515157 291982528905702359696023)
            ·
              refine ⟨437973793358553539544035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291982528905702359696023 437973793358553539544035)
              ·
                refine ⟨656960690037830309316053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 437973793358553539544035 656960690037830309316053)
                ·
                  refine ⟨15397516172761647874595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 656960690037830309316053 15397516172761647874595)
                  ·
                    rfl

theorem cell23_269879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 7].length) (baseStart_269879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269879 prefixEnd_269879 := by exact prefixLift 269879
  have htrace : WordTrace (prefixWord ++ tailWord_269879) baseStart_269879 baseEnd_269879 := by
    simpa [prefixWord, tailWord_269879, baseEnd_269879] using wordTrace_append hprefix tailTrace_269879
  have hstable : (prefixWord ++ tailWord_269879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269879).length < 2 ^ (prefixWord ++ tailWord_269879).sum := by decide
  have hdescent : baseEnd_269879 < baseStart_269879 := by decide
  rcases family_descends (prefixWord ++ tailWord_269879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269889 : List Nat := [1, 2, 5, 1, 1, 1, 2, 1, 1, 5, 3]
def baseStart_269889 : Nat := 118140960795 + 269889 * 2 ^ 59
def prefixEnd_269889 : Nat := 4983230072969 + 3 ^ 40 * 269889 * 2
def baseEnd_269889 : Nat := 138582780361399791746309

theorem tailTrace_269889 : CollatzResearch.WordTrace tailWord_269889 prefixEnd_269889 138582780361399791746309 := by
  unfold tailWord_269889
  simp only [CollatzResearch.WordTrace]
  refine ⟨9843660519245721216628721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6562440346163814144419147 9843660519245721216628721)
  ·
    refine ⟨7382745389434290912471541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9843660519245721216628721 7382745389434290912471541)
    ·
      refine ⟨692132380259464773044207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7382745389434290912471541 692132380259464773044207)
      ·
        refine ⟨1038198570389197159566311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 692132380259464773044207 1038198570389197159566311)
        ·
          refine ⟨1557297855583795739349467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1038198570389197159566311 1557297855583795739349467)
          ·
            refine ⟨2335946783375693609024201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1557297855583795739349467 2335946783375693609024201)
            ·
              refine ⟨1751960087531770206768151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2335946783375693609024201 1751960087531770206768151)
              ·
                refine ⟨2627940131297655310152227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1751960087531770206768151 2627940131297655310152227)
                ·
                  refine ⟨3941910196946482965228341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2627940131297655310152227 3941910196946482965228341)
                  ·
                    refine ⟨369554080963732777990157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3941910196946482965228341 369554080963732777990157)
                    ·
                      refine ⟨138582780361399791746309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 369554080963732777990157 138582780361399791746309)
                      ·
                        rfl

theorem cell23_269889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_269889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269889 prefixEnd_269889 := by exact prefixLift 269889
  have htrace : WordTrace (prefixWord ++ tailWord_269889) baseStart_269889 baseEnd_269889 := by
    simpa [prefixWord, tailWord_269889, baseEnd_269889] using wordTrace_append hprefix tailTrace_269889
  have hstable : (prefixWord ++ tailWord_269889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269889).length < 2 ^ (prefixWord ++ tailWord_269889).sum := by decide
  have hdescent : baseEnd_269889 < baseStart_269889 := by decide
  rcases family_descends (prefixWord ++ tailWord_269889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269894 : List Nat := [6, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2]
def baseStart_269894 : Nat := 118140960795 + 269894 * 2 ^ 59
def prefixEnd_269894 : Nat := 4983230072969 + 3 ^ 40 * 269894 * 2
def baseEnd_269894 : Nat := 138585347764672272183787

theorem tailTrace_269894 : CollatzResearch.WordTrace tailWord_269894 prefixEnd_269894 138585347764672272183787 := by
  unfold tailWord_269894
  simp only [CollatzResearch.WordTrace]
  refine ⟨307620090132112720955023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6562561922818404713707157 307620090132112720955023)
  ·
    refine ⟨461430135198169081432535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 307620090132112720955023 461430135198169081432535)
    ·
      refine ⟨692145202797253622148803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 461430135198169081432535 692145202797253622148803)
      ·
        refine ⟨1038217804195880433223205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 692145202797253622148803 1038217804195880433223205)
        ·
          refine ⟨194665838286727581229351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1038217804195880433223205 194665838286727581229351)
          ·
            refine ⟨291998757430091371844027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194665838286727581229351 291998757430091371844027)
            ·
              refine ⟨437998136145137057766041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291998757430091371844027 437998136145137057766041)
              ·
                refine ⟨328498602108852793324531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 437998136145137057766041 328498602108852793324531)
                ·
                  refine ⟨492747903163279189986797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 328498602108852793324531 492747903163279189986797)
                  ·
                    refine ⟨184780463686229696245049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 492747903163279189986797 184780463686229696245049)
                    ·
                      refine ⟨138585347764672272183787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 184780463686229696245049 138585347764672272183787)
                      ·
                        rfl

theorem cell23_269894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_269894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269894 prefixEnd_269894 := by exact prefixLift 269894
  have htrace : WordTrace (prefixWord ++ tailWord_269894) baseStart_269894 baseEnd_269894 := by
    simpa [prefixWord, tailWord_269894, baseEnd_269894] using wordTrace_append hprefix tailTrace_269894
  have hstable : (prefixWord ++ tailWord_269894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269894).length < 2 ^ (prefixWord ++ tailWord_269894).sum := by decide
  have hdescent : baseEnd_269894 < baseStart_269894 := by decide
  rcases family_descends (prefixWord ++ tailWord_269894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269902 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7]
def baseStart_269902 : Nat := 118140960795 + 269902 * 2 ^ 59
def prefixEnd_269902 : Nat := 4983230072969 + 3 ^ 40 * 269902 * 2
def baseEnd_269902 : Nat := 138589455609908240883749

theorem tailTrace_269902 : CollatzResearch.WordTrace tailWord_269902 prefixEnd_269902 138589455609908240883749 := by
  unfold tailWord_269902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1230516833524828054606495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6562756445465749624567973 1230516833524828054606495)
  ·
    refine ⟨1845775250287242081909743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1230516833524828054606495 1845775250287242081909743)
    ·
      refine ⟨2768662875430863122864615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1845775250287242081909743 2768662875430863122864615)
      ·
        refine ⟨4152994313146294684296923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2768662875430863122864615 4152994313146294684296923)
        ·
          refine ⟨6229491469719442026445385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4152994313146294684296923 6229491469719442026445385)
          ·
            refine ⟨4672118602289581519834039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6229491469719442026445385 4672118602289581519834039)
            ·
              refine ⟨7008177903434372279751059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4672118602289581519834039 7008177903434372279751059)
              ·
                refine ⟨10512266855151558419626589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7008177903434372279751059 10512266855151558419626589)
                ·
                  refine ⟨3942100070681834407359971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10512266855151558419626589 3942100070681834407359971)
                  ·
                    refine ⟨5913150106022751611039957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3942100070681834407359971 5913150106022751611039957)
                    ·
                      refine ⟨138589455609908240883749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 5913150106022751611039957 138589455609908240883749)
                      ·
                        rfl

theorem cell23_269902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_269902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269902 prefixEnd_269902 := by exact prefixLift 269902
  have htrace : WordTrace (prefixWord ++ tailWord_269902) baseStart_269902 baseEnd_269902 := by
    simpa [prefixWord, tailWord_269902, baseEnd_269902] using wordTrace_append hprefix tailTrace_269902
  have hstable : (prefixWord ++ tailWord_269902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269902).length < 2 ^ (prefixWord ++ tailWord_269902).sum := by decide
  have hdescent : baseEnd_269902 < baseStart_269902 := by decide
  rcases family_descends (prefixWord ++ tailWord_269902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269929 : List Nat := [1, 2, 1, 1, 1, 4, 4, 2, 2, 1, 4]
def baseStart_269929 : Nat := 118140960795 + 269929 * 2 ^ 59
def prefixEnd_269929 : Nat := 4983230072969 + 3 ^ 40 * 269929 * 2
def baseEnd_269929 : Nat := 138603319587579635246125

theorem tailTrace_269929 : CollatzResearch.WordTrace tailWord_269929 prefixEnd_269929 138603319587579635246125 := by
  unfold tailWord_269929
  simp only [CollatzResearch.WordTrace]
  refine ⟨9845119439100808048084841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6563412959400538698723227 9845119439100808048084841)
  ·
    refine ⟨7383839579325606036063631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9845119439100808048084841 7383839579325606036063631)
    ·
      refine ⟨11075759368988409054095447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7383839579325606036063631 11075759368988409054095447)
      ·
        refine ⟨16613639053482613581143171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11075759368988409054095447 16613639053482613581143171)
        ·
          refine ⟨24920458580223920371714757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16613639053482613581143171 24920458580223920371714757)
          ·
            refine ⟨4672585983791985069696517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24920458580223920371714757 4672585983791985069696517)
            ·
              refine ⟨876109871960997200568097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4672585983791985069696517 876109871960997200568097)
              ·
                refine ⟨657082403970747900426073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 876109871960997200568097 657082403970747900426073)
                ·
                  refine ⟨492811802978060925319555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 657082403970747900426073 492811802978060925319555)
                  ·
                    refine ⟨739217704467091387979333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 492811802978060925319555 739217704467091387979333)
                    ·
                      refine ⟨138603319587579635246125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 739217704467091387979333 138603319587579635246125)
                      ·
                        rfl

theorem cell23_269929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 1, 4].length) (baseStart_269929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269929 prefixEnd_269929 := by exact prefixLift 269929
  have htrace : WordTrace (prefixWord ++ tailWord_269929) baseStart_269929 baseEnd_269929 := by
    simpa [prefixWord, tailWord_269929, baseEnd_269929] using wordTrace_append hprefix tailTrace_269929
  have hstable : (prefixWord ++ tailWord_269929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269929).length < 2 ^ (prefixWord ++ tailWord_269929).sum := by decide
  have hdescent : baseEnd_269929 < baseStart_269929 := by decide
  rcases family_descends (prefixWord ++ tailWord_269929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269932 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 5]
def baseStart_269932 : Nat := 118140960795 + 269932 * 2 ^ 59
def prefixEnd_269932 : Nat := 4983230072969 + 3 ^ 40 * 269932 * 2
def baseEnd_269932 : Nat := 138604860029543123508611

theorem tailTrace_269932 : CollatzResearch.WordTrace tailWord_269932 prefixEnd_269932 138604860029543123508611 := by
  unfold tailWord_269932
  simp only [CollatzResearch.WordTrace]
  refine ⟨4922614429044969780222025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6563485905393293040296033 4922614429044969780222025)
  ·
    refine ⟨3691960821783727335166519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4922614429044969780222025 3691960821783727335166519)
    ·
      refine ⟨5537941232675591002749779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3691960821783727335166519 5537941232675591002749779)
      ·
        refine ⟨8306911849013386504124669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5537941232675591002749779 8306911849013386504124669)
        ·
          refine ⟨3115091943380019939046751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8306911849013386504124669 3115091943380019939046751)
          ·
            refine ⟨4672637915070029908570127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3115091943380019939046751 4672637915070029908570127)
            ·
              refine ⟨7008956872605044862855191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4672637915070029908570127 7008956872605044862855191)
              ·
                refine ⟨10513435308907567294282787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7008956872605044862855191 10513435308907567294282787)
                ·
                  refine ⟨15770152963361350941424181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10513435308907567294282787 15770152963361350941424181)
                  ·
                    refine ⟨1478451840315126650758517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15770152963361350941424181 1478451840315126650758517)
                    ·
                      refine ⟨138604860029543123508611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1478451840315126650758517 138604860029543123508611)
                      ·
                        rfl

theorem cell23_269932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_269932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269932 prefixEnd_269932 := by exact prefixLift 269932
  have htrace : WordTrace (prefixWord ++ tailWord_269932) baseStart_269932 baseEnd_269932 := by
    simpa [prefixWord, tailWord_269932, baseEnd_269932] using wordTrace_append hprefix tailTrace_269932
  have hstable : (prefixWord ++ tailWord_269932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269932).length < 2 ^ (prefixWord ++ tailWord_269932).sum := by decide
  have hdescent : baseEnd_269932 < baseStart_269932 := by decide
  rcases family_descends (prefixWord ++ tailWord_269932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269960 : List Nat := [2, 1, 3, 5, 2, 1, 1, 1, 2, 5]
def baseStart_269960 : Nat := 118140960795 + 269960 * 2 ^ 59
def prefixEnd_269960 : Nat := 4983230072969 + 3 ^ 40 * 269960 * 2
def baseEnd_269960 : Nat := 46206412495956337986161

theorem tailTrace_269960 : CollatzResearch.WordTrace tailWord_269960 prefixEnd_269960 46206412495956337986161 := by
  unfold tailWord_269960
  simp only [CollatzResearch.WordTrace]
  refine ⟨4923125050994250171231667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6564166734659000228308889 4923125050994250171231667)
  ·
    refine ⟨7384687576491375256847501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4923125050994250171231667 7384687576491375256847501)
    ·
      refine ⟨2769257841184265721317813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7384687576491375256847501 2769257841184265721317813)
      ·
        refine ⟨259617922611024911373545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2769257841184265721317813 259617922611024911373545)
        ·
          refine ⟨194713441958268683530159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 259617922611024911373545 194713441958268683530159)
          ·
            refine ⟨292070162937403025295239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194713441958268683530159 292070162937403025295239)
            ·
              refine ⟨438105244406104537942859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292070162937403025295239 438105244406104537942859)
              ·
                refine ⟨657157866609156806914289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 438105244406104537942859 657157866609156806914289)
                ·
                  refine ⟨492868399956867605185717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 657157866609156806914289 492868399956867605185717)
                  ·
                    refine ⟨46206412495956337986161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 492868399956867605185717 46206412495956337986161)
                    ·
                      rfl

theorem cell23_269960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 2, 5].length) (baseStart_269960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269960 prefixEnd_269960 := by exact prefixLift 269960
  have htrace : WordTrace (prefixWord ++ tailWord_269960) baseStart_269960 baseEnd_269960 := by
    simpa [prefixWord, tailWord_269960, baseEnd_269960] using wordTrace_append hprefix tailTrace_269960
  have hstable : (prefixWord ++ tailWord_269960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269960).length < 2 ^ (prefixWord ++ tailWord_269960).sum := by decide
  have hdescent : baseEnd_269960 < baseStart_269960 := by decide
  rcases family_descends (prefixWord ++ tailWord_269960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269966 : List Nat := [4, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3]
def baseStart_269966 : Nat := 118140960795 + 269966 * 2 ^ 59
def prefixEnd_269966 : Nat := 4983230072969 + 3 ^ 40 * 269966 * 2
def baseEnd_269966 : Nat := 138622318371795990483455

theorem tailTrace_269966 : CollatzResearch.WordTrace tailWord_269966 prefixEnd_269966 138622318371795990483455 := by
  unfold tailWord_269966
  simp only [CollatzResearch.WordTrace]
  refine ⟨1230808617495845420897719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6564312626644508911454501 1230808617495845420897719)
  ·
    refine ⟨1846212926243768131346579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1230808617495845420897719 1846212926243768131346579)
    ·
      refine ⟨2769319389365652197019869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1846212926243768131346579 2769319389365652197019869)
      ·
        refine ⟨1038494771012119573882451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2769319389365652197019869 1038494771012119573882451)
        ·
          refine ⟨1557742156518179360823677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1038494771012119573882451 1557742156518179360823677)
          ·
            refine ⟨584153308694317260308879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1557742156518179360823677 584153308694317260308879)
            ·
              refine ⟨876229963041475890463319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 584153308694317260308879 876229963041475890463319)
              ·
                refine ⟨1314344944562213835694979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 876229963041475890463319 1314344944562213835694979)
                ·
                  refine ⟨1971517416843320753542469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1314344944562213835694979 1971517416843320753542469)
                  ·
                    refine ⟨369659515658122641289213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1971517416843320753542469 369659515658122641289213)
                    ·
                      refine ⟨138622318371795990483455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 369659515658122641289213 138622318371795990483455)
                      ·
                        rfl

theorem cell23_269966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_269966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_269966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_269966 prefixEnd_269966 := by exact prefixLift 269966
  have htrace : WordTrace (prefixWord ++ tailWord_269966) baseStart_269966 baseEnd_269966 := by
    simpa [prefixWord, tailWord_269966, baseEnd_269966] using wordTrace_append hprefix tailTrace_269966
  have hstable : (prefixWord ++ tailWord_269966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269966).length < 2 ^ (prefixWord ++ tailWord_269966).sum := by decide
  have hdescent : baseEnd_269966 < baseStart_269966 := by decide
  rcases family_descends (prefixWord ++ tailWord_269966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270016 : List Nat := [2, 1, 1, 2, 4, 1, 4, 2, 1, 5]
def baseStart_270016 : Nat := 118140960795 + 270016 * 2 ^ 59
def prefixEnd_270016 : Nat := 4983230072969 + 3 ^ 40 * 270016 * 2
def baseEnd_270016 : Nat := 46215997468173598286075

theorem tailTrace_270016 : CollatzResearch.WordTrace tailWord_270016 prefixEnd_270016 46215997468173598286075 := by
  unfold tailWord_270016
  simp only [CollatzResearch.WordTrace]
  refine ⟨4924146294892810953250951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6565528393190414604334601 4924146294892810953250951)
  ·
    refine ⟨7386219442339216429876427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4924146294892810953250951 7386219442339216429876427)
    ·
      refine ⟨11079329163508824644814641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7386219442339216429876427 11079329163508824644814641)
      ·
        refine ⟨8309496872631618483610981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11079329163508824644814641 8309496872631618483610981)
        ·
          refine ⟨1558030663618428465677059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8309496872631618483610981 1558030663618428465677059)
          ·
            refine ⟨2337045995427642698515589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1558030663618428465677059 2337045995427642698515589)
            ·
              refine ⟨438196124142683005971673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2337045995427642698515589 438196124142683005971673)
              ·
                refine ⟨328647093107012254478755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 438196124142683005971673 328647093107012254478755)
                ·
                  refine ⟨492970639660518381718133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 328647093107012254478755 492970639660518381718133)
                  ·
                    refine ⟨46215997468173598286075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 492970639660518381718133 46215997468173598286075)
                    ·
                      rfl

theorem cell23_270016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 1, 5].length) (baseStart_270016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270016 prefixEnd_270016 := by exact prefixLift 270016
  have htrace : WordTrace (prefixWord ++ tailWord_270016) baseStart_270016 baseEnd_270016 := by
    simpa [prefixWord, tailWord_270016, baseEnd_270016] using wordTrace_append hprefix tailTrace_270016
  have hstable : (prefixWord ++ tailWord_270016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270016).length < 2 ^ (prefixWord ++ tailWord_270016).sum := by decide
  have hdescent : baseEnd_270016 < baseStart_270016 := by decide
  rcases family_descends (prefixWord ++ tailWord_270016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270056 : List Nat := [2, 1, 4, 1, 3, 1, 2, 2, 1, 1, 5]
def baseStart_270056 : Nat := 118140960795 + 270056 * 2 ^ 59
def prefixEnd_270056 : Nat := 4983230072969 + 3 ^ 40 * 270056 * 2
def baseEnd_270056 : Nat := 138668531630700638358041

theorem tailTrace_270056 : CollatzResearch.WordTrace tailWord_270056 prefixEnd_270056 138668531630700638358041 := by
  unfold tailWord_270056
  simp only [CollatzResearch.WordTrace]
  refine ⟨4924875754820354368979011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6566501006427139158638681 4924875754820354368979011)
  ·
    refine ⟨7387313632230531553468517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4924875754820354368979011 7387313632230531553468517)
    ·
      refine ⟨1385121306043224666275347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7387313632230531553468517 1385121306043224666275347)
      ·
        refine ⟨2077681959064836999413021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1385121306043224666275347 2077681959064836999413021)
        ·
          refine ⟨779130734649313874779883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2077681959064836999413021 779130734649313874779883)
          ·
            refine ⟨1168696101973970812169825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 779130734649313874779883 1168696101973970812169825)
            ·
              refine ⟨876522076480478109127369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1168696101973970812169825 876522076480478109127369)
              ·
                refine ⟨657391557360358581845527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 876522076480478109127369 657391557360358581845527)
                ·
                  refine ⟨986087336040537872768291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 657391557360358581845527 986087336040537872768291)
                  ·
                    refine ⟨1479131004060806809152437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 986087336040537872768291 1479131004060806809152437)
                    ·
                      refine ⟨138668531630700638358041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1479131004060806809152437 138668531630700638358041)
                      ·
                        rfl

theorem cell23_270056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_270056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270056 prefixEnd_270056 := by exact prefixLift 270056
  have htrace : WordTrace (prefixWord ++ tailWord_270056) baseStart_270056 baseEnd_270056 := by
    simpa [prefixWord, tailWord_270056, baseEnd_270056] using wordTrace_append hprefix tailTrace_270056
  have hstable : (prefixWord ++ tailWord_270056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270056).length < 2 ^ (prefixWord ++ tailWord_270056).sum := by decide
  have hdescent : baseEnd_270056 < baseStart_270056 := by decide
  rcases family_descends (prefixWord ++ tailWord_270056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270066 : List Nat := [3, 2, 1, 3, 1, 1, 2, 3, 1, 2, 4]
def baseStart_270066 : Nat := 118140960795 + 270066 * 2 ^ 59
def prefixEnd_270066 : Nat := 4983230072969 + 3 ^ 40 * 270066 * 2
def baseEnd_270066 : Nat := 138673666437245599232995

theorem tailTrace_270066 : CollatzResearch.WordTrace tailWord_270066 prefixEnd_270066 138673666437245599232995 := by
  unfold tailWord_270066
  simp only [CollatzResearch.WordTrace]
  refine ⟨2462529059901120111455513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6566744159736320297214701 2462529059901120111455513)
  ·
    refine ⟨1846896794925840083591635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2462529059901120111455513 1846896794925840083591635)
    ·
      refine ⟨2770345192388760125387453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1846896794925840083591635 2770345192388760125387453)
      ·
        refine ⟨1038879447145785047020295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2770345192388760125387453 1038879447145785047020295)
        ·
          refine ⟨1558319170718677570530443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1038879447145785047020295 1558319170718677570530443)
          ·
            refine ⟨2337478756078016355795665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1558319170718677570530443 2337478756078016355795665)
            ·
              refine ⟨1753109067058512266846749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2337478756078016355795665 1753109067058512266846749)
              ·
                refine ⟨657415900146942100067531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1753109067058512266846749 657415900146942100067531)
                ·
                  refine ⟨986123850220413150101297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 657415900146942100067531 986123850220413150101297)
                  ·
                    refine ⟨739592887665309862575973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 986123850220413150101297 739592887665309862575973)
                    ·
                      refine ⟨138673666437245599232995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 739592887665309862575973 138673666437245599232995)
                      ·
                        rfl

theorem cell23_270066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_270066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270066 prefixEnd_270066 := by exact prefixLift 270066
  have htrace : WordTrace (prefixWord ++ tailWord_270066) baseStart_270066 baseEnd_270066 := by
    simpa [prefixWord, tailWord_270066, baseEnd_270066] using wordTrace_append hprefix tailTrace_270066
  have hstable : (prefixWord ++ tailWord_270066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270066).length < 2 ^ (prefixWord ++ tailWord_270066).sum := by decide
  have hdescent : baseEnd_270066 < baseStart_270066 := by decide
  rcases family_descends (prefixWord ++ tailWord_270066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270070 : List Nat := [5, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4]
def baseStart_270070 : Nat := 118140960795 + 270070 * 2 ^ 59
def prefixEnd_270070 : Nat := 4983230072969 + 3 ^ 40 * 270070 * 2
def baseEnd_270070 : Nat := 138675720359863583582977

theorem tailTrace_270070 : CollatzResearch.WordTrace tailWord_270070 prefixEnd_270070 138675720359863583582977 := by
  unfold tailWord_270070
  simp only [CollatzResearch.WordTrace]
  refine ⟨615641383224374320560479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6566841421059992752645109 615641383224374320560479)
  ·
    refine ⟨923462074836561480840719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 615641383224374320560479 923462074836561480840719)
    ·
      refine ⟨1385193112254842221261079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 923462074836561480840719 1385193112254842221261079)
      ·
        refine ⟨2077789668382263331891619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1385193112254842221261079 2077789668382263331891619)
        ·
          refine ⟨3116684502573394997837429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2077789668382263331891619 3116684502573394997837429)
          ·
            refine ⟨292189172116255781047259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3116684502573394997837429 292189172116255781047259)
            ·
              refine ⟨438283758174383671570889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292189172116255781047259 438283758174383671570889)
              ·
                refine ⟨328712818630787753678167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 438283758174383671570889 328712818630787753678167)
                ·
                  refine ⟨493069227946181630517251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 328712818630787753678167 493069227946181630517251)
                  ·
                    refine ⟨739603841919272445775877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 493069227946181630517251 739603841919272445775877)
                    ·
                      refine ⟨138675720359863583582977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 739603841919272445775877 138675720359863583582977)
                      ·
                        rfl

theorem cell23_270070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_270070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270070 prefixEnd_270070 := by exact prefixLift 270070
  have htrace : WordTrace (prefixWord ++ tailWord_270070) baseStart_270070 baseEnd_270070 := by
    simpa [prefixWord, tailWord_270070, baseEnd_270070] using wordTrace_append hprefix tailTrace_270070
  have hstable : (prefixWord ++ tailWord_270070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270070).length < 2 ^ (prefixWord ++ tailWord_270070).sum := by decide
  have hdescent : baseEnd_270070 < baseStart_270070 := by decide
  rcases family_descends (prefixWord ++ tailWord_270070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270090 : List Nat := [3, 1, 2, 2, 1, 4, 3, 1, 1, 2, 3]
def baseStart_270090 : Nat := 118140960795 + 270090 * 2 ^ 59
def prefixEnd_270090 : Nat := 4983230072969 + 3 ^ 40 * 270090 * 2
def baseEnd_270090 : Nat := 138685989972953505332885

theorem tailTrace_270090 : CollatzResearch.WordTrace tailWord_270090 prefixEnd_270090 138685989972953505332885 := by
  unfold tailWord_270090
  simp only [CollatzResearch.WordTrace]
  refine ⟨2462747897879383136173931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6567327727678355029797149 2462747897879383136173931)
  ·
    refine ⟨3694121846819074704260897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2462747897879383136173931 3694121846819074704260897)
    ·
      refine ⟨2770591385114306028195673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3694121846819074704260897 2770591385114306028195673)
      ·
        refine ⟨2077943538835729521146755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2770591385114306028195673 2077943538835729521146755)
        ·
          refine ⟨3116915308253594281720133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2077943538835729521146755 3116915308253594281720133)
          ·
            refine ⟨584421620297548927822525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3116915308253594281720133 584421620297548927822525)
            ·
              refine ⟨219158107611580847933447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 584421620297548927822525 219158107611580847933447)
              ·
                refine ⟨328737161417371271900171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219158107611580847933447 328737161417371271900171)
                ·
                  refine ⟨493105742126056907850257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 328737161417371271900171 493105742126056907850257)
                  ·
                    refine ⟨369829306594542680887693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 493105742126056907850257 369829306594542680887693)
                    ·
                      refine ⟨138685989972953505332885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 369829306594542680887693 138685989972953505332885)
                      ·
                        rfl

theorem cell23_270090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_270090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270090 prefixEnd_270090 := by exact prefixLift 270090
  have htrace : WordTrace (prefixWord ++ tailWord_270090) baseStart_270090 baseEnd_270090 := by
    simpa [prefixWord, tailWord_270090, baseEnd_270090] using wordTrace_append hprefix tailTrace_270090
  have hstable : (prefixWord ++ tailWord_270090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270090).length < 2 ^ (prefixWord ++ tailWord_270090).sum := by decide
  have hdescent : baseEnd_270090 < baseStart_270090 := by decide
  rcases family_descends (prefixWord ++ tailWord_270090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270113 : List Nat := [1, 2, 3, 2, 1, 3, 1, 2, 3, 3, 2]
def baseStart_270113 : Nat := 118140960795 + 270113 * 2 ^ 59
def prefixEnd_270113 : Nat := 4983230072969 + 3 ^ 40 * 270113 * 2
def baseEnd_270113 : Nat := 138697800028006915345279

theorem tailTrace_270113 : CollatzResearch.WordTrace tailWord_270113 prefixEnd_270113 138697800028006915345279 := by
  unfold tailWord_270113
  simp only [CollatzResearch.WordTrace]
  refine ⟨9851830470434207472782993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6567886980289471648521995 9851830470434207472782993)
  ·
    refine ⟨7388872852825655604587245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9851830470434207472782993 7388872852825655604587245)
    ·
      refine ⟨2770827319809620851720217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7388872852825655604587245 2770827319809620851720217)
      ·
        refine ⟨2078120489857215638790163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2770827319809620851720217 2078120489857215638790163)
        ·
          refine ⟨3117180734785823458185245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2078120489857215638790163 3117180734785823458185245)
          ·
            refine ⟨1168942775544683796819467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3117180734785823458185245 1168942775544683796819467)
            ·
              refine ⟨1753414163317025695229201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1168942775544683796819467 1753414163317025695229201)
              ·
                refine ⟨1315060622487769271421901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1753414163317025695229201 1315060622487769271421901)
                ·
                  refine ⟨493147733432913476783213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1315060622487769271421901 493147733432913476783213)
                  ·
                    refine ⟨184930400037342553793705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 493147733432913476783213 184930400037342553793705)
                    ·
                      refine ⟨138697800028006915345279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 184930400037342553793705 138697800028006915345279)
                      ·
                        rfl

theorem cell23_270113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_270113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270113 prefixEnd_270113 := by exact prefixLift 270113
  have htrace : WordTrace (prefixWord ++ tailWord_270113) baseStart_270113 baseEnd_270113 := by
    simpa [prefixWord, tailWord_270113, baseEnd_270113] using wordTrace_append hprefix tailTrace_270113
  have hstable : (prefixWord ++ tailWord_270113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270113).length < 2 ^ (prefixWord ++ tailWord_270113).sum := by decide
  have hdescent : baseEnd_270113 < baseStart_270113 := by decide
  rcases family_descends (prefixWord ++ tailWord_270113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270120 : List Nat := [2, 1, 5, 1, 1, 2, 2, 3, 2, 1, 3]
def baseStart_270120 : Nat := 118140960795 + 270120 * 2 ^ 59
def prefixEnd_270120 : Nat := 4983230072969 + 3 ^ 40 * 270120 * 2
def baseEnd_270120 : Nat := 138701394392588387957747

theorem tailTrace_270120 : CollatzResearch.WordTrace tailWord_270120 prefixEnd_270120 138701394392588387957747 := by
  unfold tailWord_270120
  simp only [CollatzResearch.WordTrace]
  refine ⟨4926042890704423834143907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6568057187605898445525209 4926042890704423834143907)
  ·
    refine ⟨7389064336056635751215861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4926042890704423834143907 7389064336056635751215861)
    ·
      refine ⟨692724781505309601676487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7389064336056635751215861 692724781505309601676487)
      ·
        refine ⟨1039087172257964402514731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 692724781505309601676487 1039087172257964402514731)
        ·
          refine ⟨1558630758386946603772097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1039087172257964402514731 1558630758386946603772097)
          ·
            refine ⟨1168973068790209952829073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1558630758386946603772097 1168973068790209952829073)
            ·
              refine ⟨876729801592657464621805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1168973068790209952829073 876729801592657464621805)
              ·
                refine ⟨328773675597246549233177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 876729801592657464621805 328773675597246549233177)
                ·
                  refine ⟨246580256697934911924883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 328773675597246549233177 246580256697934911924883)
                  ·
                    refine ⟨369870385046902367887325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 246580256697934911924883 369870385046902367887325)
                    ·
                      refine ⟨138701394392588387957747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 369870385046902367887325 138701394392588387957747)
                      ·
                        rfl

theorem cell23_270120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_270120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270120 prefixEnd_270120 := by exact prefixLift 270120
  have htrace : WordTrace (prefixWord ++ tailWord_270120) baseStart_270120 baseEnd_270120 := by
    simpa [prefixWord, tailWord_270120, baseEnd_270120] using wordTrace_append hprefix tailTrace_270120
  have hstable : (prefixWord ++ tailWord_270120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270120).length < 2 ^ (prefixWord ++ tailWord_270120).sum := by decide
  have hdescent : baseEnd_270120 < baseStart_270120 := by decide
  rcases family_descends (prefixWord ++ tailWord_270120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270147 : List Nat := [1, 1, 1, 3, 1, 7, 2, 1, 1, 3, 2]
def baseStart_270147 : Nat := 118140960795 + 270147 * 2 ^ 59
def prefixEnd_270147 : Nat := 4983230072969 + 3 ^ 40 * 270147 * 2
def baseEnd_270147 : Nat := 138715258370259782320123

theorem tailTrace_270147 : CollatzResearch.WordTrace tailWord_270147 prefixEnd_270147 138715258370259782320123 := by
  unfold tailWord_270147
  simp only [CollatzResearch.WordTrace]
  refine ⟨9853070552311031279520695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6568713701540687519680463 9853070552311031279520695)
  ·
    refine ⟨14779605828466546919281043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9853070552311031279520695 14779605828466546919281043)
    ·
      refine ⟨22169408742699820378921565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14779605828466546919281043 22169408742699820378921565)
      ·
        refine ⟨8313528278512432642095587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22169408742699820378921565 8313528278512432642095587)
        ·
          refine ⟨12470292417768648963143381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8313528278512432642095587 12470292417768648963143381)
          ·
            refine ⟨292272478541452710073673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 12470292417768648963143381 292272478541452710073673)
            ·
              refine ⟨219204358906089532555255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 292272478541452710073673 219204358906089532555255)
              ·
                refine ⟨328806538359134298832883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219204358906089532555255 328806538359134298832883)
                ·
                  refine ⟨493209807538701448249325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 328806538359134298832883 493209807538701448249325)
                  ·
                    refine ⟨184953677827013043093497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 493209807538701448249325 184953677827013043093497)
                    ·
                      refine ⟨138715258370259782320123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 184953677827013043093497 138715258370259782320123)
                      ·
                        rfl

theorem cell23_270147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 1, 3, 2].length) (baseStart_270147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270147 prefixEnd_270147 := by exact prefixLift 270147
  have htrace : WordTrace (prefixWord ++ tailWord_270147) baseStart_270147 baseEnd_270147 := by
    simpa [prefixWord, tailWord_270147, baseEnd_270147] using wordTrace_append hprefix tailTrace_270147
  have hstable : (prefixWord ++ tailWord_270147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270147).length < 2 ^ (prefixWord ++ tailWord_270147).sum := by decide
  have hdescent : baseEnd_270147 < baseStart_270147 := by decide
  rcases family_descends (prefixWord ++ tailWord_270147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270149 : List Nat := [1, 3, 1, 1, 1, 2, 3, 2, 9]
def baseStart_270149 : Nat := 118140960795 + 270149 * 2 ^ 59
def prefixEnd_270149 : Nat := 4983230072969 + 3 ^ 40 * 270149 * 2
def baseEnd_270149 : Nat := 15412920592396530499457

theorem tailTrace_270149 : CollatzResearch.WordTrace tailWord_270149 prefixEnd_270149 15412920592396530499457 := by
  unfold tailWord_270149
  simp only [CollatzResearch.WordTrace]
  refine ⟨9853143498303785621093501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6568762332202523747395667 9853143498303785621093501)
  ·
    refine ⟨3694928811863919607910063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9853143498303785621093501 3694928811863919607910063)
    ·
      refine ⟨5542393217795879411865095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3694928811863919607910063 5542393217795879411865095)
      ·
        refine ⟨8313589826693819117797643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5542393217795879411865095 8313589826693819117797643)
        ·
          refine ⟨12470384740040728676696465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8313589826693819117797643 12470384740040728676696465)
          ·
            refine ⟨9352788555030546507522349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12470384740040728676696465 9352788555030546507522349)
            ·
              refine ⟨3507295708136454940320881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9352788555030546507522349 3507295708136454940320881)
              ·
                refine ⟨2630471781102341205240661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3507295708136454940320881 2630471781102341205240661)
                ·
                  refine ⟨15412920592396530499457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2630471781102341205240661 15412920592396530499457)
                  ·
                    rfl

theorem cell23_270149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 9].length) (baseStart_270149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270149 prefixEnd_270149 := by exact prefixLift 270149
  have htrace : WordTrace (prefixWord ++ tailWord_270149) baseStart_270149 baseEnd_270149 := by
    simpa [prefixWord, tailWord_270149, baseEnd_270149] using wordTrace_append hprefix tailTrace_270149
  have hstable : (prefixWord ++ tailWord_270149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270149).length < 2 ^ (prefixWord ++ tailWord_270149).sum := by decide
  have hdescent : baseEnd_270149 < baseStart_270149 := by decide
  rcases family_descends (prefixWord ++ tailWord_270149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270177 : List Nat := [1, 2, 3, 1, 1, 1, 7, 1, 2, 2, 2]
def baseStart_270177 : Nat := 118140960795 + 270177 * 2 ^ 59
def prefixEnd_270177 : Nat := 4983230072969 + 3 ^ 40 * 270177 * 2
def baseEnd_270177 : Nat := 138730662789894664944985

theorem tailTrace_270177 : CollatzResearch.WordTrace tailWord_270177 prefixEnd_270177 138730662789894664944985 := by
  unfold tailWord_270177
  simp only [CollatzResearch.WordTrace]
  refine ⟨9854164742202346403112785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6569443161468230935408523 9854164742202346403112785)
  ·
    refine ⟨7390623556651759802334589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9854164742202346403112785 7390623556651759802334589)
    ·
      refine ⟨2771483833744409925875471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7390623556651759802334589 2771483833744409925875471)
      ·
        refine ⟨4157225750616614888813207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2771483833744409925875471 4157225750616614888813207)
        ·
          refine ⟨6235838625924922333219811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4157225750616614888813207 6235838625924922333219811)
          ·
            refine ⟨9353757938887383499829717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6235838625924922333219811 9353757938887383499829717)
            ·
              refine ⟨219228701692673050777259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 9353757938887383499829717 219228701692673050777259)
              ·
                refine ⟨328843052539009576165889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219228701692673050777259 328843052539009576165889)
                ·
                  refine ⟨246632289404257182124417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 328843052539009576165889 246632289404257182124417)
                  ·
                    refine ⟨184974217053192886593313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 246632289404257182124417 184974217053192886593313)
                    ·
                      refine ⟨138730662789894664944985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 184974217053192886593313 138730662789894664944985)
                      ·
                        rfl

theorem cell23_270177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 2, 2, 2].length) (baseStart_270177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270177 prefixEnd_270177 := by exact prefixLift 270177
  have htrace : WordTrace (prefixWord ++ tailWord_270177) baseStart_270177 baseEnd_270177 := by
    simpa [prefixWord, tailWord_270177, baseEnd_270177] using wordTrace_append hprefix tailTrace_270177
  have hstable : (prefixWord ++ tailWord_270177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270177).length < 2 ^ (prefixWord ++ tailWord_270177).sum := by decide
  have hdescent : baseEnd_270177 < baseStart_270177 := by decide
  rcases family_descends (prefixWord ++ tailWord_270177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270233 : List Nat := [1, 2, 1, 2, 1, 3, 2, 3, 2, 4, 2]
def baseStart_270233 : Nat := 118140960795 + 270233 * 2 ^ 59
def prefixEnd_270233 : Nat := 4983230072969 + 3 ^ 40 * 270233 * 2
def baseEnd_270233 : Nat := 138759417706546445844727

theorem tailTrace_270233 : CollatzResearch.WordTrace tailWord_270233 prefixEnd_270233 138759417706546445844727 := by
  unfold tailWord_270233
  simp only [CollatzResearch.WordTrace]
  refine ⟨9856207229999467967151353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6570804819999645311434235 9856207229999467967151353)
  ·
    refine ⟨7392155422499600975363515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9856207229999467967151353 7392155422499600975363515)
    ·
      refine ⟨11088233133749401463045273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7392155422499600975363515 11088233133749401463045273)
      ·
        refine ⟨8316174850312051097283955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11088233133749401463045273 8316174850312051097283955)
        ·
          refine ⟨12474262275468076645925933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8316174850312051097283955 12474262275468076645925933)
          ·
            refine ⟨4677848353300528742222225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12474262275468076645925933 4677848353300528742222225)
            ·
              refine ⟨3508386264975396556666669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4677848353300528742222225 3508386264975396556666669)
              ·
                refine ⟨1315644849365773708750001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3508386264975396556666669 1315644849365773708750001)
                ·
                  refine ⟨986733637024330281562501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1315644849365773708750001 986733637024330281562501)
                  ·
                    refine ⟨185012556942061927792969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 986733637024330281562501 185012556942061927792969)
                    ·
                      refine ⟨138759417706546445844727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 185012556942061927792969 138759417706546445844727)
                      ·
                        rfl

theorem cell23_270233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 4, 2].length) (baseStart_270233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270233 prefixEnd_270233 := by exact prefixLift 270233
  have htrace : WordTrace (prefixWord ++ tailWord_270233) baseStart_270233 baseEnd_270233 := by
    simpa [prefixWord, tailWord_270233, baseEnd_270233] using wordTrace_append hprefix tailTrace_270233
  have hstable : (prefixWord ++ tailWord_270233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270233).length < 2 ^ (prefixWord ++ tailWord_270233).sum := by decide
  have hdescent : baseEnd_270233 < baseStart_270233 := by decide
  rcases family_descends (prefixWord ++ tailWord_270233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270270 : List Nat := [4, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3]
def baseStart_270270 : Nat := 118140960795 + 270270 * 2 ^ 59
def prefixEnd_270270 : Nat := 4983230072969 + 3 ^ 40 * 270270 * 2
def baseEnd_270270 : Nat := 138778416490762801082057

theorem tailTrace_270270 : CollatzResearch.WordTrace tailWord_270270 prefixEnd_270270 138778416490762801082057 := by
  unfold tailWord_270270
  simp only [CollatzResearch.WordTrace]
  refine ⟨1232194591358177910781033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6571704487243615524165509 1232194591358177910781033)
  ·
    refine ⟨924145943518633433085775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1232194591358177910781033 924145943518633433085775)
    ·
      refine ⟨1386218915277950149628663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 924145943518633433085775 1386218915277950149628663)
      ·
        refine ⟨2079328372916925224442995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1386218915277950149628663 2079328372916925224442995)
        ·
          refine ⟨3118992559375387836664493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2079328372916925224442995 3118992559375387836664493)
          ·
            refine ⟨1169622209765770438749185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3118992559375387836664493 1169622209765770438749185)
            ·
              refine ⟨877216657324327829061889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1169622209765770438749185 877216657324327829061889)
              ·
                refine ⟨657912492993245871796417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 877216657324327829061889 657912492993245871796417)
                ·
                  refine ⟨493434369744934403847313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 657912492993245871796417 493434369744934403847313)
                  ·
                    refine ⟨370075777308700802885485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 493434369744934403847313 370075777308700802885485)
                    ·
                      refine ⟨138778416490762801082057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 370075777308700802885485 138778416490762801082057)
                      ·
                        rfl

theorem cell23_270270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_270270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270270 prefixEnd_270270 := by exact prefixLift 270270
  have htrace : WordTrace (prefixWord ++ tailWord_270270) baseStart_270270 baseEnd_270270 := by
    simpa [prefixWord, tailWord_270270, baseEnd_270270] using wordTrace_append hprefix tailTrace_270270
  have hstable : (prefixWord ++ tailWord_270270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270270).length < 2 ^ (prefixWord ++ tailWord_270270).sum := by decide
  have hdescent : baseEnd_270270 < baseStart_270270 := by decide
  rcases family_descends (prefixWord ++ tailWord_270270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270296 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 2, 1, 7]
def baseStart_270296 : Nat := 118140960795 + 270296 * 2 ^ 59
def prefixEnd_270296 : Nat := 4983230072969 + 3 ^ 40 * 270296 * 2
def baseEnd_270296 : Nat := 138791766987779699356937

theorem tailTrace_270296 : CollatzResearch.WordTrace tailWord_270296 prefixEnd_270296 138791766987779699356937 := by
  unfold tailWord_270296
  simp only [CollatzResearch.WordTrace]
  refine ⟨4929252514385614863347371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6572336685847486484463161 4929252514385614863347371)
  ·
    refine ⟨7393878771578422295021057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4929252514385614863347371 7393878771578422295021057)
    ·
      refine ⟨5545409078683816721265793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7393878771578422295021057 5545409078683816721265793)
      ·
        refine ⟨4159056809012862540949345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5545409078683816721265793 4159056809012862540949345)
        ·
          refine ⟨3119292606759646905712009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4159056809012862540949345 3119292606759646905712009)
          ·
            refine ⟨2339469455069735179284007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3119292606759646905712009 2339469455069735179284007)
            ·
              refine ⟨3509204182604602768926011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2339469455069735179284007 3509204182604602768926011)
              ·
                refine ⟨5263806273906904153389017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3509204182604602768926011 5263806273906904153389017)
                ·
                  refine ⟨3947854705430178115041763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5263806273906904153389017 3947854705430178115041763)
                  ·
                    refine ⟨5921782058145267172562645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3947854705430178115041763 5921782058145267172562645)
                    ·
                      refine ⟨138791766987779699356937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 5921782058145267172562645 138791766987779699356937)
                      ·
                        rfl

theorem cell23_270296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_270296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270296 prefixEnd_270296 := by exact prefixLift 270296
  have htrace : WordTrace (prefixWord ++ tailWord_270296) baseStart_270296 baseEnd_270296 := by
    simpa [prefixWord, tailWord_270296, baseEnd_270296] using wordTrace_append hprefix tailTrace_270296
  have hstable : (prefixWord ++ tailWord_270296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270296).length < 2 ^ (prefixWord ++ tailWord_270296).sum := by decide
  have hdescent : baseEnd_270296 < baseStart_270296 := by decide
  rcases family_descends (prefixWord ++ tailWord_270296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270303 : List Nat := [1, 1, 2, 3, 4, 1, 2, 1, 3, 5]
def baseStart_270303 : Nat := 118140960795 + 270303 * 2 ^ 59
def prefixEnd_270303 : Nat := 4983230072969 + 3 ^ 40 * 270303 * 2
def baseEnd_270303 : Nat := 46265120450787057323135

theorem tailTrace_270303 : CollatzResearch.WordTrace tailWord_270303 prefixEnd_270303 46265120450787057323135 := by
  unfold tailWord_270303
  simp only [CollatzResearch.WordTrace]
  refine ⟨9858760339745869922199563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6572506893163913281466375 9858760339745869922199563)
  ·
    refine ⟨14788140509618804883299345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9858760339745869922199563 14788140509618804883299345)
    ·
      refine ⟨11091105382214103662474509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14788140509618804883299345 11091105382214103662474509)
      ·
        refine ⟨4159164518330288873427941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11091105382214103662474509 4159164518330288873427941)
        ·
          refine ⟨779843347186929163767739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4159164518330288873427941 779843347186929163767739)
          ·
            refine ⟨1169765020780393745651609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 779843347186929163767739 1169765020780393745651609)
            ·
              refine ⟨877323765585295309238707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1169765020780393745651609 877323765585295309238707)
              ·
                refine ⟨1315985648377942963858061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 877323765585295309238707 1315985648377942963858061)
                ·
                  refine ⟨493494618141728611446773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1315985648377942963858061 493494618141728611446773)
                  ·
                    refine ⟨46265120450787057323135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 493494618141728611446773 46265120450787057323135)
                    ·
                      rfl

theorem cell23_270303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 5].length) (baseStart_270303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270303 prefixEnd_270303 := by exact prefixLift 270303
  have htrace : WordTrace (prefixWord ++ tailWord_270303) baseStart_270303 baseEnd_270303 := by
    simpa [prefixWord, tailWord_270303, baseEnd_270303] using wordTrace_append hprefix tailTrace_270303
  have hstable : (prefixWord ++ tailWord_270303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270303).length < 2 ^ (prefixWord ++ tailWord_270303).sum := by decide
  have hdescent : baseEnd_270303 < baseStart_270303 := by decide
  rcases family_descends (prefixWord ++ tailWord_270303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270320 : List Nat := [2, 1, 1, 1, 3, 2, 6, 1, 1, 5]
def baseStart_270320 : Nat := 118140960795 + 270320 * 2 ^ 59
def prefixEnd_270320 : Nat := 4983230072969 + 3 ^ 40 * 270320 * 2
def baseEnd_270320 : Nat := 46268030174495868485609

theorem tailTrace_270320 : CollatzResearch.WordTrace tailWord_270320 prefixEnd_270320 46268030174495868485609 := by
  unfold tailWord_270320
  simp only [CollatzResearch.WordTrace]
  refine ⟨4929690190342140912784207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6572920253789521217045609 4929690190342140912784207)
  ·
    refine ⟨7394535285513211369176311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4929690190342140912784207 7394535285513211369176311)
    ·
      refine ⟨11091802928269817053764467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7394535285513211369176311 11091802928269817053764467)
      ·
        refine ⟨16637704392404725580646701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11091802928269817053764467 16637704392404725580646701)
        ·
          refine ⟨6239139147151772092742513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16637704392404725580646701 6239139147151772092742513)
          ·
            refine ⟨4679354360363829069556885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6239139147151772092742513 4679354360363829069556885)
            ·
              refine ⟨219344735642054487635479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4679354360363829069556885 219344735642054487635479)
              ·
                refine ⟨329017103463081731453219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219344735642054487635479 329017103463081731453219)
                ·
                  refine ⟨493525655194622597179829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 329017103463081731453219 493525655194622597179829)
                  ·
                    refine ⟨46268030174495868485609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 493525655194622597179829 46268030174495868485609)
                    ·
                      rfl

theorem cell23_270320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 1, 5].length) (baseStart_270320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270320 prefixEnd_270320 := by exact prefixLift 270320
  have htrace : WordTrace (prefixWord ++ tailWord_270320) baseStart_270320 baseEnd_270320 := by
    simpa [prefixWord, tailWord_270320, baseEnd_270320] using wordTrace_append hprefix tailTrace_270320
  have hstable : (prefixWord ++ tailWord_270320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270320).length < 2 ^ (prefixWord ++ tailWord_270320).sum := by decide
  have hdescent : baseEnd_270320 < baseStart_270320 := by decide
  rcases family_descends (prefixWord ++ tailWord_270320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270323 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 1, 8, 2]
def baseStart_270323 : Nat := 118140960795 + 270323 * 2 ^ 59
def prefixEnd_270323 : Nat := 4983230072969 + 3 ^ 40 * 270323 * 2
def baseEnd_270323 : Nat := 138805630965451093719313

theorem tailTrace_270323 : CollatzResearch.WordTrace tailWord_270323 prefixEnd_270323 138805630965451093719313 := by
  unfold tailWord_270323
  simp only [CollatzResearch.WordTrace]
  refine ⟨9859489799673413337927623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6572993199782275558618415 9859489799673413337927623)
  ·
    refine ⟨14789234699510120006891435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9859489799673413337927623 14789234699510120006891435)
    ·
      refine ⟨22183852049265180010337153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14789234699510120006891435 22183852049265180010337153)
      ·
        refine ⟨16637889036948885007752865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22183852049265180010337153 16637889036948885007752865)
        ·
          refine ⟨12478416777711663755814649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16637889036948885007752865 12478416777711663755814649)
          ·
            refine ⟨9358812583283747816860987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12478416777711663755814649 9358812583283747816860987)
            ·
              refine ⟨14038218874925621725291481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9358812583283747816860987 14038218874925621725291481)
              ·
                refine ⟨10528664156194216293968611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14038218874925621725291481 10528664156194216293968611)
                ·
                  refine ⟨15792996234291324440952917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10528664156194216293968611 15792996234291324440952917)
                  ·
                    refine ⟨185074174620601458292417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15792996234291324440952917 185074174620601458292417)
                    ·
                      refine ⟨138805630965451093719313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 185074174620601458292417 138805630965451093719313)
                      ·
                        rfl

theorem cell23_270323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 8, 2].length) (baseStart_270323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270323 prefixEnd_270323 := by exact prefixLift 270323
  have htrace : WordTrace (prefixWord ++ tailWord_270323) baseStart_270323 baseEnd_270323 := by
    simpa [prefixWord, tailWord_270323, baseEnd_270323] using wordTrace_append hprefix tailTrace_270323
  have hstable : (prefixWord ++ tailWord_270323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270323).length < 2 ^ (prefixWord ++ tailWord_270323).sum := by decide
  have hdescent : baseEnd_270323 < baseStart_270323 := by decide
  rcases family_descends (prefixWord ++ tailWord_270323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270334 : List Nat := [4, 2, 2, 2, 1, 2, 2, 1, 3, 1, 3]
def baseStart_270334 : Nat := 118140960795 + 270334 * 2 ^ 59
def prefixEnd_270334 : Nat := 4983230072969 + 3 ^ 40 * 270334 * 2
def baseEnd_270334 : Nat := 138811279252650550681763

theorem tailTrace_270334 : CollatzResearch.WordTrace tailWord_270334 prefixEnd_270334 138811279252650550681763 := by
  unfold tailWord_270334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1232486375329195277072257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6573260668422374811052037 1232486375329195277072257)
  ·
    refine ⟨924364781496896457804193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1232486375329195277072257 924364781496896457804193)
    ·
      refine ⟨693273586122672343353145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 924364781496896457804193 693273586122672343353145)
      ·
        refine ⟨519955189592004257514859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 693273586122672343353145 519955189592004257514859)
        ·
          refine ⟨779932784388006386272289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 519955189592004257514859 779932784388006386272289)
          ·
            refine ⟨584949588291004789704217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 779932784388006386272289 584949588291004789704217)
            ·
              refine ⟨438712191218253592278163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 584949588291004789704217 438712191218253592278163)
              ·
                refine ⟨658068286827380388417245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 438712191218253592278163 658068286827380388417245)
                ·
                  refine ⟨246775607560267645656467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 658068286827380388417245 246775607560267645656467)
                  ·
                    refine ⟨370163411340401468484701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 246775607560267645656467 370163411340401468484701)
                    ·
                      refine ⟨138811279252650550681763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 370163411340401468484701 138811279252650550681763)
                      ·
                        rfl

theorem cell23_270334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_270334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270334 prefixEnd_270334 := by exact prefixLift 270334
  have htrace : WordTrace (prefixWord ++ tailWord_270334) baseStart_270334 baseEnd_270334 := by
    simpa [prefixWord, tailWord_270334, baseEnd_270334] using wordTrace_append hprefix tailTrace_270334
  have hstable : (prefixWord ++ tailWord_270334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270334).length < 2 ^ (prefixWord ++ tailWord_270334).sum := by decide
  have hdescent : baseEnd_270334 < baseStart_270334 := by decide
  rcases family_descends (prefixWord ++ tailWord_270334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270343 : List Nat := [1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 5]
def baseStart_270343 : Nat := 118140960795 + 270343 * 2 ^ 59
def prefixEnd_270343 : Nat := 4983230072969 + 3 ^ 40 * 270343 * 2
def baseEnd_270343 : Nat := 138815900578541015469221

theorem tailTrace_270343 : CollatzResearch.WordTrace tailWord_270343 prefixEnd_270343 138815900578541015469221 := by
  unfold tailWord_270343
  simp only [CollatzResearch.WordTrace]
  refine ⟨9860219259600956753655683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6573479506400637835770455 9860219259600956753655683)
  ·
    refine ⟨14790328889401435130483525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9860219259600956753655683 14790328889401435130483525)
    ·
      refine ⟨2773186666762769086965661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14790328889401435130483525 2773186666762769086965661)
      ·
        refine ⟨1039945000036038407612123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2773186666762769086965661 1039945000036038407612123)
        ·
          refine ⟨1559917500054057611418185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1039945000036038407612123 1559917500054057611418185)
          ·
            refine ⟨1169938125040543208563639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1559917500054057611418185 1169938125040543208563639)
            ·
              refine ⟨1754907187560814812845459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1169938125040543208563639 1754907187560814812845459)
              ·
                refine ⟨2632360781341222219268189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1754907187560814812845459 2632360781341222219268189)
                ·
                  refine ⟨987135293002958332225571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2632360781341222219268189 987135293002958332225571)
                  ·
                    refine ⟨1480702939504437498338357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 987135293002958332225571 1480702939504437498338357)
                    ·
                      refine ⟨138815900578541015469221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1480702939504437498338357 138815900578541015469221)
                      ·
                        rfl

theorem cell23_270343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_270343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270343 prefixEnd_270343 := by exact prefixLift 270343
  have htrace : WordTrace (prefixWord ++ tailWord_270343) baseStart_270343 baseEnd_270343 := by
    simpa [prefixWord, tailWord_270343, baseEnd_270343] using wordTrace_append hprefix tailTrace_270343
  have hstable : (prefixWord ++ tailWord_270343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270343).length < 2 ^ (prefixWord ++ tailWord_270343).sum := by decide
  have hdescent : baseEnd_270343 < baseStart_270343 := by decide
  rcases family_descends (prefixWord ++ tailWord_270343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270357 : List Nat := [1, 3, 2, 1, 5, 1, 2, 2, 1, 1, 4]
def baseStart_270357 : Nat := 118140960795 + 270357 * 2 ^ 59
def prefixEnd_270357 : Nat := 4983230072969 + 3 ^ 40 * 270357 * 2
def baseEnd_270357 : Nat := 138823089307703960694157

theorem tailTrace_270357 : CollatzResearch.WordTrace tailWord_270357 prefixEnd_270357 138823089307703960694157 := by
  unfold tailWord_270357
  simp only [CollatzResearch.WordTrace]
  refine ⟨9860729881550237144665325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6573819921033491429776883 9860729881550237144665325)
  ·
    refine ⟨3697773705581338929249497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9860729881550237144665325 3697773705581338929249497)
    ·
      refine ⟨2773330279186004196937123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3697773705581338929249497 2773330279186004196937123)
      ·
        refine ⟨4159995418779006295405685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2773330279186004196937123 4159995418779006295405685)
        ·
          refine ⟨389999570510531840194283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4159995418779006295405685 389999570510531840194283)
          ·
            refine ⟨584999355765797760291425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 389999570510531840194283 584999355765797760291425)
            ·
              refine ⟨438749516824348320218569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 584999355765797760291425 438749516824348320218569)
              ·
                refine ⟨329062137618261240163927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 438749516824348320218569 329062137618261240163927)
                ·
                  refine ⟨493593206427391860245891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 329062137618261240163927 493593206427391860245891)
                  ·
                    refine ⟨740389809641087790368837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 493593206427391860245891 740389809641087790368837)
                    ·
                      refine ⟨138823089307703960694157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 740389809641087790368837 138823089307703960694157)
                      ·
                        rfl

theorem cell23_270357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 1, 4].length) (baseStart_270357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270357 prefixEnd_270357 := by exact prefixLift 270357
  have htrace : WordTrace (prefixWord ++ tailWord_270357) baseStart_270357 baseEnd_270357 := by
    simpa [prefixWord, tailWord_270357, baseEnd_270357] using wordTrace_append hprefix tailTrace_270357
  have hstable : (prefixWord ++ tailWord_270357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270357).length < 2 ^ (prefixWord ++ tailWord_270357).sum := by decide
  have hdescent : baseEnd_270357 < baseStart_270357 := by decide
  rcases family_descends (prefixWord ++ tailWord_270357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270407 : List Nat := [1, 1, 4, 1, 3, 1, 3, 3, 2, 1, 3]
def baseStart_270407 : Nat := 118140960795 + 270407 * 2 ^ 59
def prefixEnd_270407 : Nat := 4983230072969 + 3 ^ 40 * 270407 * 2
def baseEnd_270407 : Nat := 138848763340428765068927

theorem tailTrace_270407 : CollatzResearch.WordTrace tailWord_270407 prefixEnd_270407 138848763340428765068927 := by
  unfold tailWord_270407
  simp only [CollatzResearch.WordTrace]
  refine ⟨9862553531369095683985475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6575035687579397122656983 9862553531369095683985475)
  ·
    refine ⟨14793830297053643525978213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9862553531369095683985475 14793830297053643525978213)
    ·
      refine ⟨2773843180697558161120915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14793830297053643525978213 2773843180697558161120915)
      ·
        refine ⟨4160764771046337241681373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2773843180697558161120915 4160764771046337241681373)
        ·
          refine ⟨1560286789142376465630515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4160764771046337241681373 1560286789142376465630515)
          ·
            refine ⟨2340430183713564698445773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1560286789142376465630515 2340430183713564698445773)
            ·
              refine ⟨877661318892586761917165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2340430183713564698445773 877661318892586761917165)
              ·
                refine ⟨329122994584720035718937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 877661318892586761917165 329122994584720035718937)
                ·
                  refine ⟨246842245938540026789203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 329122994584720035718937 246842245938540026789203)
                  ·
                    refine ⟨370263368907810040183805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 246842245938540026789203 370263368907810040183805)
                    ·
                      refine ⟨138848763340428765068927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 370263368907810040183805 138848763340428765068927)
                      ·
                        rfl

theorem cell23_270407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 2, 1, 3].length) (baseStart_270407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270407 prefixEnd_270407 := by exact prefixLift 270407
  have htrace : WordTrace (prefixWord ++ tailWord_270407) baseStart_270407 baseEnd_270407 := by
    simpa [prefixWord, tailWord_270407, baseEnd_270407] using wordTrace_append hprefix tailTrace_270407
  have hstable : (prefixWord ++ tailWord_270407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270407).length < 2 ^ (prefixWord ++ tailWord_270407).sum := by decide
  have hdescent : baseEnd_270407 < baseStart_270407 := by decide
  rcases family_descends (prefixWord ++ tailWord_270407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270450 : List Nat := [3, 2, 1, 2, 2, 2, 1, 1, 2, 4, 3]
def baseStart_270450 : Nat := 118140960795 + 270450 * 2 ^ 59
def prefixEnd_270450 : Nat := 4983230072969 + 3 ^ 40 * 270450 * 2
def baseEnd_270450 : Nat := 138870843008572096831229

theorem tailTrace_270450 : CollatzResearch.WordTrace tailWord_270450 prefixEnd_270450 138870843008572096831229 := by
  unfold tailWord_270450
  simp only [CollatzResearch.WordTrace]
  refine ⟨2466030467553328506950201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6576081246808876018533869 2466030467553328506950201)
  ·
    refine ⟨1849522850664996380212651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2466030467553328506950201 1849522850664996380212651)
    ·
      refine ⟨2774284275997494570318977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1849522850664996380212651 2774284275997494570318977)
      ·
        refine ⟨2080713206998120927739233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2774284275997494570318977 2080713206998120927739233)
        ·
          refine ⟨1560534905248590695804425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2080713206998120927739233 1560534905248590695804425)
          ·
            refine ⟨1170401178936443021853319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1560534905248590695804425 1170401178936443021853319)
            ·
              refine ⟨1755601768404664532779979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1170401178936443021853319 1755601768404664532779979)
              ·
                refine ⟨2633402652606996799169969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1755601768404664532779979 2633402652606996799169969)
                ·
                  refine ⟨1975051989455247599377477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2633402652606996799169969 1975051989455247599377477)
                  ·
                    refine ⟨370322248022858924883277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1975051989455247599377477 370322248022858924883277)
                    ·
                      refine ⟨138870843008572096831229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 370322248022858924883277 138870843008572096831229)
                      ·
                        rfl

theorem cell23_270450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_270450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270450 prefixEnd_270450 := by exact prefixLift 270450
  have htrace : WordTrace (prefixWord ++ tailWord_270450) baseStart_270450 baseEnd_270450 := by
    simpa [prefixWord, tailWord_270450, baseEnd_270450] using wordTrace_append hprefix tailTrace_270450
  have hstable : (prefixWord ++ tailWord_270450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270450).length < 2 ^ (prefixWord ++ tailWord_270450).sum := by decide
  have hdescent : baseEnd_270450 < baseStart_270450 := by decide
  rcases family_descends (prefixWord ++ tailWord_270450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270460 : List Nat := [2, 2, 2, 1, 1, 5, 1, 1, 2, 2, 4]
def baseStart_270460 : Nat := 118140960795 + 270460 * 2 ^ 59
def prefixEnd_270460 : Nat := 4983230072969 + 3 ^ 40 * 270460 * 2
def baseEnd_270460 : Nat := 138875977815117057706183

theorem tailTrace_270460 : CollatzResearch.WordTrace tailWord_270460 prefixEnd_270460 138875977815117057706183 := by
  unfold tailWord_270460
  simp only [CollatzResearch.WordTrace]
  refine ⟨4932243300088542867832417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6576324400118057157109889 4932243300088542867832417)
  ·
    refine ⟨3699182475066407150874313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4932243300088542867832417 3699182475066407150874313)
    ·
      refine ⟨2774386856299805363155735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3699182475066407150874313 2774386856299805363155735)
      ·
        refine ⟨4161580284449708044733603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2774386856299805363155735 4161580284449708044733603)
        ·
          refine ⟨6242370426674562067100405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4161580284449708044733603 6242370426674562067100405)
          ·
            refine ⟨585222227500740193790663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6242370426674562067100405 585222227500740193790663)
            ·
              refine ⟨877833341251110290685995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 585222227500740193790663 877833341251110290685995)
              ·
                refine ⟨1316750011876665436028993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 877833341251110290685995 1316750011876665436028993)
                ·
                  refine ⟨987562508907499077021745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1316750011876665436028993 987562508907499077021745)
                  ·
                    refine ⟨740671881680624307766309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 987562508907499077021745 740671881680624307766309)
                    ·
                      refine ⟨138875977815117057706183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 740671881680624307766309 138875977815117057706183)
                      ·
                        rfl

theorem cell23_270460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_270460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270460 prefixEnd_270460 := by exact prefixLift 270460
  have htrace : WordTrace (prefixWord ++ tailWord_270460) baseStart_270460 baseEnd_270460 := by
    simpa [prefixWord, tailWord_270460, baseEnd_270460] using wordTrace_append hprefix tailTrace_270460
  have hstable : (prefixWord ++ tailWord_270460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270460).length < 2 ^ (prefixWord ++ tailWord_270460).sum := by decide
  have hdescent : baseEnd_270460 < baseStart_270460 := by decide
  rcases family_descends (prefixWord ++ tailWord_270460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270498 : List Nat := [3, 3, 1, 3, 1, 3, 1, 2, 2, 2, 2]
def baseStart_270498 : Nat := 118140960795 + 270498 * 2 ^ 59
def prefixEnd_270498 : Nat := 4983230072969 + 3 ^ 40 * 270498 * 2
def baseEnd_270498 : Nat := 138895490079987909031009

theorem tailTrace_270498 : CollatzResearch.WordTrace tailWord_270498 prefixEnd_270498 138895490079987909031009 := by
  unfold tailWord_270498
  simp only [CollatzResearch.WordTrace]
  refine ⟨2466468143509854556387037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6577248382692945483698765 2466468143509854556387037)
  ·
    refine ⟨924925553816195458645139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2466468143509854556387037 924925553816195458645139)
    ·
      refine ⟨1387388330724293187967709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 924925553816195458645139 1387388330724293187967709)
      ·
        refine ⟨520270624021609945487891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1387388330724293187967709 520270624021609945487891)
        ·
          refine ⟨780405936032414918231837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 520270624021609945487891 780405936032414918231837)
          ·
            refine ⟨292652226012155594336939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 780405936032414918231837 292652226012155594336939)
            ·
              refine ⟨438978339018233391505409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292652226012155594336939 438978339018233391505409)
              ·
                refine ⟨329233754263675043629057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 438978339018233391505409 329233754263675043629057)
                ·
                  refine ⟨246925315697756282721793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 329233754263675043629057 246925315697756282721793)
                  ·
                    refine ⟨185193986773317212041345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 246925315697756282721793 185193986773317212041345)
                    ·
                      refine ⟨138895490079987909031009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 185193986773317212041345 138895490079987909031009)
                      ·
                        rfl

theorem cell23_270498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_270498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270498 prefixEnd_270498 := by exact prefixLift 270498
  have htrace : WordTrace (prefixWord ++ tailWord_270498) baseStart_270498 baseEnd_270498 := by
    simpa [prefixWord, tailWord_270498, baseEnd_270498] using wordTrace_append hprefix tailTrace_270498
  have hstable : (prefixWord ++ tailWord_270498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270498).length < 2 ^ (prefixWord ++ tailWord_270498).sum := by decide
  have hdescent : baseEnd_270498 < baseStart_270498 := by decide
  rcases family_descends (prefixWord ++ tailWord_270498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270543 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 10]
def baseStart_270543 : Nat := 118140960795 + 270543 * 2 ^ 59
def prefixEnd_270543 : Nat := 4983230072969 + 3 ^ 40 * 270543 * 2
def baseEnd_270543 : Nat := 15435399634382248107589

theorem tailTrace_270543 : CollatzResearch.WordTrace tailWord_270543 prefixEnd_270543 15435399634382248107589 := by
  unfold tailWord_270543
  simp only [CollatzResearch.WordTrace]
  refine ⟨9867513858876390910936283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6578342572584260607290855 9867513858876390910936283)
  ·
    refine ⟨14801270788314586366404425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9867513858876390910936283 14801270788314586366404425)
    ·
      refine ⟨11100953091235939774803319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14801270788314586366404425 11100953091235939774803319)
      ·
        refine ⟨16651429636853909662204979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11100953091235939774803319 16651429636853909662204979)
        ·
          refine ⟨24977144455280864493307469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16651429636853909662204979 24977144455280864493307469)
          ·
            refine ⟨9366429170730324184990301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24977144455280864493307469 9366429170730324184990301)
            ·
              refine ⟨3512410939023871569371363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9366429170730324184990301 3512410939023871569371363)
              ·
                refine ⟨5268616408535807354057045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3512410939023871569371363 5268616408535807354057045)
                ·
                  refine ⟨15435399634382248107589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 5268616408535807354057045 15435399634382248107589)
                  ·
                    rfl

theorem cell23_270543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 10].length) (baseStart_270543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270543 prefixEnd_270543 := by exact prefixLift 270543
  have htrace : WordTrace (prefixWord ++ tailWord_270543) baseStart_270543 baseEnd_270543 := by
    simpa [prefixWord, tailWord_270543, baseEnd_270543] using wordTrace_append hprefix tailTrace_270543
  have hstable : (prefixWord ++ tailWord_270543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270543).length < 2 ^ (prefixWord ++ tailWord_270543).sum := by decide
  have hdescent : baseEnd_270543 < baseStart_270543 := by decide
  rcases family_descends (prefixWord ++ tailWord_270543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270560 : List Nat := [2, 1, 1, 3, 1, 3, 2, 4, 6]
def baseStart_270560 : Nat := 118140960795 + 270560 * 2 ^ 59
def prefixEnd_270560 : Nat := 4983230072969 + 3 ^ 40 * 270560 * 2
def baseEnd_270560 : Nat := 15436369542285185161747

theorem tailTrace_270560 : CollatzResearch.WordTrace tailWord_270560 prefixEnd_270560 15436369542285185161747 := by
  unfold tailWord_270560
  simp only [CollatzResearch.WordTrace]
  refine ⟨4934066949907401407152567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6578755933209868542870089 4934066949907401407152567)
  ·
    refine ⟨7401100424861102110728851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4934066949907401407152567 7401100424861102110728851)
    ·
      refine ⟨11101650637291653166093277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7401100424861102110728851 11101650637291653166093277)
      ·
        refine ⟨4163118988984369937284979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11101650637291653166093277 4163118988984369937284979)
        ·
          refine ⟨6244678483476554905927469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4163118988984369937284979 6244678483476554905927469)
          ·
            refine ⟨2341754431303708089722801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6244678483476554905927469 2341754431303708089722801)
            ·
              refine ⟨1756315823477781067292101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2341754431303708089722801 1756315823477781067292101)
              ·
                refine ⟨329309216902083950117269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1756315823477781067292101 329309216902083950117269)
                ·
                  refine ⟨15436369542285185161747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 329309216902083950117269 15436369542285185161747)
                  ·
                    rfl

theorem cell23_270560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 6].length) (baseStart_270560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270560 prefixEnd_270560 := by exact prefixLift 270560
  have htrace : WordTrace (prefixWord ++ tailWord_270560) baseStart_270560 baseEnd_270560 := by
    simpa [prefixWord, tailWord_270560, baseEnd_270560] using wordTrace_append hprefix tailTrace_270560
  have hstable : (prefixWord ++ tailWord_270560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270560).length < 2 ^ (prefixWord ++ tailWord_270560).sum := by decide
  have hdescent : baseEnd_270560 < baseStart_270560 := by decide
  rcases family_descends (prefixWord ++ tailWord_270560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270577 : List Nat := [1, 2, 2, 2, 2, 1, 6, 1, 6]
def baseStart_270577 : Nat := 118140960795 + 270577 * 2 ^ 59
def prefixEnd_270577 : Nat := 4983230072969 + 3 ^ 40 * 270577 * 2
def baseEnd_270577 : Nat := 15437339450188122215905

theorem tailTrace_270577 : CollatzResearch.WordTrace tailWord_270577 prefixEnd_270577 15437339450188122215905 := by
  unfold tailWord_270577
  simp only [CollatzResearch.WordTrace]
  refine ⟨9868753940753214717673985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6579169293835476478449323 9868753940753214717673985)
  ·
    refine ⟨7401565455564911038255489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9868753940753214717673985 7401565455564911038255489)
    ·
      refine ⟨5551174091673683278691617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7401565455564911038255489 5551174091673683278691617)
      ·
        refine ⟨4163380568755262459018713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5551174091673683278691617 4163380568755262459018713)
        ·
          refine ⟨3122535426566446844264035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4163380568755262459018713 3122535426566446844264035)
          ·
            refine ⟨4683803139849670266396053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3122535426566446844264035 4683803139849670266396053)
            ·
              refine ⟨219553272180453293737315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4683803139849670266396053 219553272180453293737315)
              ·
                refine ⟨329329908270679940605973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219553272180453293737315 329329908270679940605973)
                ·
                  refine ⟨15437339450188122215905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 329329908270679940605973 15437339450188122215905)
                  ·
                    rfl

theorem cell23_270577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 6].length) (baseStart_270577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270577 prefixEnd_270577 := by exact prefixLift 270577
  have htrace : WordTrace (prefixWord ++ tailWord_270577) baseStart_270577 baseEnd_270577 := by
    simpa [prefixWord, tailWord_270577, baseEnd_270577] using wordTrace_append hprefix tailTrace_270577
  have hstable : (prefixWord ++ tailWord_270577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270577).length < 2 ^ (prefixWord ++ tailWord_270577).sum := by decide
  have hdescent : baseEnd_270577 < baseStart_270577 := by decide
  rcases family_descends (prefixWord ++ tailWord_270577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270620 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 5, 6]
def baseStart_270620 : Nat := 118140960795 + 270620 * 2 ^ 59
def prefixEnd_270620 : Nat := 4983230072969 + 3 ^ 40 * 270620 * 2
def baseEnd_270620 : Nat := 46319378239945477235149

theorem tailTrace_270620 : CollatzResearch.WordTrace tailWord_270620 prefixEnd_270620 46319378239945477235149 := by
  unfold tailWord_270620
  simp only [CollatzResearch.WordTrace]
  refine ⟨4935161139798716530744657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6580214853064955374326209 4935161139798716530744657)
  ·
    refine ⟨3701370854849037398058493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4935161139798716530744657 3701370854849037398058493)
    ·
      refine ⟨1388014070568389024271935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3701370854849037398058493 1388014070568389024271935)
      ·
        refine ⟨2082021105852583536407903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1388014070568389024271935 2082021105852583536407903)
        ·
          refine ⟨3123031658778875304611855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2082021105852583536407903 3123031658778875304611855)
          ·
            refine ⟨4684547488168312956917783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3123031658778875304611855 4684547488168312956917783)
            ·
              refine ⟨7026821232252469435376675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4684547488168312956917783 7026821232252469435376675)
              ·
                refine ⟨10540231848378704153065013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7026821232252469435376675 10540231848378704153065013)
                ·
                  refine ⟨988146735785503514349845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10540231848378704153065013 988146735785503514349845)
                  ·
                    refine ⟨46319378239945477235149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 988146735785503514349845 46319378239945477235149)
                    ·
                      rfl

theorem cell23_270620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_270620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270620 prefixEnd_270620 := by exact prefixLift 270620
  have htrace : WordTrace (prefixWord ++ tailWord_270620) baseStart_270620 baseEnd_270620 := by
    simpa [prefixWord, tailWord_270620, baseEnd_270620] using wordTrace_append hprefix tailTrace_270620
  have hstable : (prefixWord ++ tailWord_270620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270620).length < 2 ^ (prefixWord ++ tailWord_270620).sum := by decide
  have hdescent : baseEnd_270620 < baseStart_270620 := by decide
  rcases family_descends (prefixWord ++ tailWord_270620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270638 : List Nat := [4, 1, 3, 3, 1, 1, 1, 2, 3, 1, 3]
def baseStart_270638 : Nat := 118140960795 + 270638 * 2 ^ 59
def prefixEnd_270638 : Nat := 4983230072969 + 3 ^ 40 * 270638 * 2
def baseEnd_270638 : Nat := 138967377371617361280365

theorem tailTrace_270638 : CollatzResearch.WordTrace tailWord_270638 prefixEnd_270638 138967377371617361280365 := by
  unfold tailWord_270638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1233872349191527766955571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6580652529021481423763045 1233872349191527766955571)
  ·
    refine ⟨1850808523787291650433357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1233872349191527766955571 1850808523787291650433357)
    ·
      refine ⟨694053196420234368912509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1850808523787291650433357 694053196420234368912509)
      ·
        refine ⟨260269948657587888342191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 694053196420234368912509 260269948657587888342191)
        ·
          refine ⟨390404922986381832513287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260269948657587888342191 390404922986381832513287)
          ·
            refine ⟨585607384479572748769931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 390404922986381832513287 585607384479572748769931)
            ·
              refine ⟨878411076719359123154897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 585607384479572748769931 878411076719359123154897)
              ·
                refine ⟨658808307539519342366173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 878411076719359123154897 658808307539519342366173)
                ·
                  refine ⟨247053115327319753387315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 658808307539519342366173 247053115327319753387315)
                  ·
                    refine ⟨370579672990979630080973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 247053115327319753387315 370579672990979630080973)
                    ·
                      refine ⟨138967377371617361280365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 370579672990979630080973 138967377371617361280365)
                      ·
                        rfl

theorem cell23_270638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_270638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270638 prefixEnd_270638 := by exact prefixLift 270638
  have htrace : WordTrace (prefixWord ++ tailWord_270638) baseStart_270638 baseEnd_270638 := by
    simpa [prefixWord, tailWord_270638, baseEnd_270638] using wordTrace_append hprefix tailTrace_270638
  have hstable : (prefixWord ++ tailWord_270638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270638).length < 2 ^ (prefixWord ++ tailWord_270638).sum := by decide
  have hdescent : baseEnd_270638 < baseStart_270638 := by decide
  rcases family_descends (prefixWord ++ tailWord_270638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270644 : List Nat := [2, 5, 1, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_270644 : Nat := 118140960795 + 270644 * 2 ^ 59
def prefixEnd_270644 : Nat := 4983230072969 + 3 ^ 40 * 270644 * 2
def baseEnd_270644 : Nat := 138970458255544337805337

theorem tailTrace_270644 : CollatzResearch.WordTrace tailWord_270644 prefixEnd_270644 138970458255544337805337 := by
  unfold tailWord_270644
  simp only [CollatzResearch.WordTrace]
  refine ⟨4935598815755242580181493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6580798421006990106908657 4935598815755242580181493)
  ·
    refine ⟨462712388977053991892015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4935598815755242580181493 462712388977053991892015)
    ·
      refine ⟨694068583465580987838023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 462712388977053991892015 694068583465580987838023)
      ·
        refine ⟨1041102875198371481757035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 694068583465580987838023 1041102875198371481757035)
        ·
          refine ⟨1561654312797557222635553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1041102875198371481757035 1561654312797557222635553)
          ·
            refine ⟨1171240734598167916976665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1561654312797557222635553 1171240734598167916976665)
            ·
              refine ⟨878430550948625937732499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1171240734598167916976665 878430550948625937732499)
              ·
                refine ⟨1317645826422938906598749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 878430550948625937732499 1317645826422938906598749)
                ·
                  refine ⟨494117184908602089974531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1317645826422938906598749 494117184908602089974531)
                  ·
                    refine ⟨741175777362903134961797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 494117184908602089974531 741175777362903134961797)
                    ·
                      refine ⟨138970458255544337805337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 741175777362903134961797 138970458255544337805337)
                      ·
                        rfl

theorem cell23_270644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_270644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270644 prefixEnd_270644 := by exact prefixLift 270644
  have htrace : WordTrace (prefixWord ++ tailWord_270644) baseStart_270644 baseEnd_270644 := by
    simpa [prefixWord, tailWord_270644, baseEnd_270644] using wordTrace_append hprefix tailTrace_270644
  have hstable : (prefixWord ++ tailWord_270644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270644).length < 2 ^ (prefixWord ++ tailWord_270644).sum := by decide
  have hdescent : baseEnd_270644 < baseStart_270644 := by decide
  rcases family_descends (prefixWord ++ tailWord_270644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270680 : List Nat := [2, 1, 2, 2, 1, 1, 2, 3, 2, 7]
def baseStart_270680 : Nat := 118140960795 + 270680 * 2 ^ 59
def prefixEnd_270680 : Nat := 4983230072969 + 3 ^ 40 * 270680 * 2
def baseEnd_270680 : Nat := 46329647853035398985057

theorem tailTrace_270680 : CollatzResearch.WordTrace tailWord_270680 prefixEnd_270680 46329647853035398985057 := by
  unfold tailWord_270680
  simp only [CollatzResearch.WordTrace]
  refine ⟨4936255329690031654336747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6581673772920042205782329 4936255329690031654336747)
  ·
    refine ⟨7404382994535047481505121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4936255329690031654336747 7404382994535047481505121)
    ·
      refine ⟨5553287245901285611128841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7404382994535047481505121 5553287245901285611128841)
      ·
        refine ⟨4164965434425964208346631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5553287245901285611128841 4164965434425964208346631)
        ·
          refine ⟨6247448151638946312519947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4164965434425964208346631 6247448151638946312519947)
          ·
            refine ⟨9371172227458419468779921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6247448151638946312519947 9371172227458419468779921)
            ·
              refine ⟨7028379170593814601584941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9371172227458419468779921 7028379170593814601584941)
              ·
                refine ⟨2635642188972680475594353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7028379170593814601584941 2635642188972680475594353)
                ·
                  refine ⟨1976731641729510356695765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2635642188972680475594353 1976731641729510356695765)
                  ·
                    refine ⟨46329647853035398985057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1976731641729510356695765 46329647853035398985057)
                    ·
                      rfl

theorem cell23_270680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 2, 7].length) (baseStart_270680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270680 prefixEnd_270680 := by exact prefixLift 270680
  have htrace : WordTrace (prefixWord ++ tailWord_270680) baseStart_270680 baseEnd_270680 := by
    simpa [prefixWord, tailWord_270680, baseEnd_270680] using wordTrace_append hprefix tailTrace_270680
  have hstable : (prefixWord ++ tailWord_270680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270680).length < 2 ^ (prefixWord ++ tailWord_270680).sum := by decide
  have hdescent : baseEnd_270680 < baseStart_270680 := by decide
  rcases family_descends (prefixWord ++ tailWord_270680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270767 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 6, 3, 3]
def baseStart_270767 : Nat := 118140960795 + 270767 * 2 ^ 59
def prefixEnd_270767 : Nat := 4983230072969 + 3 ^ 40 * 270767 * 2
def baseEnd_270767 : Nat := 139033616376047356567271

theorem tailTrace_270767 : CollatzResearch.WordTrace tailWord_270767 prefixEnd_270767 139033616376047356567271 := by
  unfold tailWord_270767
  simp only [CollatzResearch.WordTrace]
  refine ⟨9875683810064877167090555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6583789206709918111393703 9875683810064877167090555)
  ·
    refine ⟨14813525715097315750635833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9875683810064877167090555 14813525715097315750635833)
    ·
      refine ⟨11110144286322986812976875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14813525715097315750635833 11110144286322986812976875)
      ·
        refine ⟨16665216429484480219465313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11110144286322986812976875 16665216429484480219465313)
        ·
          refine ⟨12498912322113360164598985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16665216429484480219465313 12498912322113360164598985)
          ·
            refine ⟨9374184241585020123449239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12498912322113360164598985 9374184241585020123449239)
            ·
              refine ⟨14061276362377530185173859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9374184241585020123449239 14061276362377530185173859)
              ·
                refine ⟨21091914543566295277760789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14061276362377530185173859 21091914543566295277760789)
                ·
                  refine ⟨988683494229670091145037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 21091914543566295277760789 988683494229670091145037)
                  ·
                    refine ⟨370756310336126284179389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 988683494229670091145037 370756310336126284179389)
                    ·
                      refine ⟨139033616376047356567271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 370756310336126284179389 139033616376047356567271)
                      ·
                        rfl

theorem cell23_270767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 3, 3].length) (baseStart_270767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270767 prefixEnd_270767 := by exact prefixLift 270767
  have htrace : WordTrace (prefixWord ++ tailWord_270767) baseStart_270767 baseEnd_270767 := by
    simpa [prefixWord, tailWord_270767, baseEnd_270767] using wordTrace_append hprefix tailTrace_270767
  have hstable : (prefixWord ++ tailWord_270767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270767).length < 2 ^ (prefixWord ++ tailWord_270767).sum := by decide
  have hdescent : baseEnd_270767 < baseStart_270767 := by decide
  rcases family_descends (prefixWord ++ tailWord_270767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270791 : List Nat := [1, 1, 4, 1, 1, 4, 4, 2, 5]
def baseStart_270791 : Nat := 118140960795 + 270791 * 2 ^ 59
def prefixEnd_270791 : Nat := 4983230072969 + 3 ^ 40 * 270791 * 2
def baseEnd_270791 : Nat := 15449548879083918074129

theorem tailTrace_270791 : CollatzResearch.WordTrace tailWord_270791 prefixEnd_270791 15449548879083918074129 := by
  unfold tailWord_270791
  simp only [CollatzResearch.WordTrace]
  refine ⟨9876559161977929265964227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6584372774651952843976151 9876559161977929265964227)
  ·
    refine ⟨14814838742966893898946341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9876559161977929265964227 14814838742966893898946341)
    ·
      refine ⟨2777782264306292606052439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14814838742966893898946341 2777782264306292606052439)
      ·
        refine ⟨4166673396459438909078659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2777782264306292606052439 4166673396459438909078659)
        ·
          refine ⟨6250010094689158363617989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4166673396459438909078659 6250010094689158363617989)
          ·
            refine ⟨1171876892754217193178373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6250010094689158363617989 1171876892754217193178373)
            ·
              refine ⟨219726917391415723720945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1171876892754217193178373 219726917391415723720945)
              ·
                refine ⟨164795188043561792790709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 219726917391415723720945 164795188043561792790709)
                ·
                  refine ⟨15449548879083918074129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 164795188043561792790709 15449548879083918074129)
                  ·
                    rfl

theorem cell23_270791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 2, 5].length) (baseStart_270791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270791 prefixEnd_270791 := by exact prefixLift 270791
  have htrace : WordTrace (prefixWord ++ tailWord_270791) baseStart_270791 baseEnd_270791 := by
    simpa [prefixWord, tailWord_270791, baseEnd_270791] using wordTrace_append hprefix tailTrace_270791
  have hstable : (prefixWord ++ tailWord_270791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270791).length < 2 ^ (prefixWord ++ tailWord_270791).sum := by decide
  have hdescent : baseEnd_270791 < baseStart_270791 := by decide
  rcases family_descends (prefixWord ++ tailWord_270791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270794 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 1, 7, 2]
def baseStart_270794 : Nat := 118140960795 + 270794 * 2 ^ 59
def prefixEnd_270794 : Nat := 4983230072969 + 3 ^ 40 * 270794 * 2
def baseEnd_270794 : Nat := 139047480353718750929647

theorem tailTrace_270794 : CollatzResearch.WordTrace tailWord_270794 prefixEnd_270794 139047480353718750929647 := by
  unfold tailWord_270794
  simp only [CollatzResearch.WordTrace]
  refine ⟨2469167145241765194580859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6584445720644707185548957 2469167145241765194580859)
  ·
    refine ⟨3703750717862647791871289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2469167145241765194580859 3703750717862647791871289)
    ·
      refine ⟨2777813038396985843903467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3703750717862647791871289 2777813038396985843903467)
      ·
        refine ⟨4166719557595478765855201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2777813038396985843903467 4166719557595478765855201)
        ·
          refine ⟨3125039668196609074391401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4166719557595478765855201 3125039668196609074391401)
          ·
            refine ⟨2343779751147456805793551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3125039668196609074391401 2343779751147456805793551)
            ·
              refine ⟨3515669626721185208690327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2343779751147456805793551 3515669626721185208690327)
              ·
                refine ⟨5273504440081777813035491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3515669626721185208690327 5273504440081777813035491)
                ·
                  refine ⟨7910256660122666719553237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5273504440081777813035491 7910256660122666719553237)
                  ·
                    refine ⟨185396640471625001239529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7910256660122666719553237 185396640471625001239529)
                    ·
                      refine ⟨139047480353718750929647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 185396640471625001239529 139047480353718750929647)
                      ·
                        rfl

theorem cell23_270794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 1, 7, 2].length) (baseStart_270794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270794 prefixEnd_270794 := by exact prefixLift 270794
  have htrace : WordTrace (prefixWord ++ tailWord_270794) baseStart_270794 baseEnd_270794 := by
    simpa [prefixWord, tailWord_270794, baseEnd_270794] using wordTrace_append hprefix tailTrace_270794
  have hstable : (prefixWord ++ tailWord_270794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270794).length < 2 ^ (prefixWord ++ tailWord_270794).sum := by decide
  have hdescent : baseEnd_270794 < baseStart_270794 := by decide
  rcases family_descends (prefixWord ++ tailWord_270794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270824 : List Nat := [2, 1, 4, 1, 1, 4, 1, 1, 1, 3, 4]
def baseStart_270824 : Nat := 118140960795 + 270824 * 2 ^ 59
def prefixEnd_270824 : Nat := 4983230072969 + 3 ^ 40 * 270824 * 2
def baseEnd_270824 : Nat := 139062884773353633554509

theorem tailTrace_270824 : CollatzResearch.WordTrace tailWord_270824 prefixEnd_270824 139062884773353633554509 := by
  unfold tailWord_270824
  simp only [CollatzResearch.WordTrace]
  refine ⟨4938881385429187950957763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6585175180572250601277017 4938881385429187950957763)
  ·
    refine ⟨7408322078143781926436645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4938881385429187950957763 7408322078143781926436645)
    ·
      refine ⟨1389060389651959111206871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7408322078143781926436645 1389060389651959111206871)
      ·
        refine ⟨2083590584477938666810307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1389060389651959111206871 2083590584477938666810307)
        ·
          refine ⟨3125385876716908000215461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2083590584477938666810307 3125385876716908000215461)
          ·
            refine ⟨586009851884420250040399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3125385876716908000215461 586009851884420250040399)
            ·
              refine ⟨879014777826630375060599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 586009851884420250040399 879014777826630375060599)
              ·
                refine ⟨1318522166739945562590899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 879014777826630375060599 1318522166739945562590899)
                ·
                  refine ⟨1977783250109918343886349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1318522166739945562590899 1977783250109918343886349)
                  ·
                    refine ⟨741668718791219378957381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1977783250109918343886349 741668718791219378957381)
                    ·
                      refine ⟨139062884773353633554509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 741668718791219378957381 139062884773353633554509)
                      ·
                        rfl

theorem cell23_270824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_270824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270824 prefixEnd_270824 := by exact prefixLift 270824
  have htrace : WordTrace (prefixWord ++ tailWord_270824) baseStart_270824 baseEnd_270824 := by
    simpa [prefixWord, tailWord_270824, baseEnd_270824] using wordTrace_append hprefix tailTrace_270824
  have hstable : (prefixWord ++ tailWord_270824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270824).length < 2 ^ (prefixWord ++ tailWord_270824).sum := by decide
  have hdescent : baseEnd_270824 < baseStart_270824 := by decide
  rcases family_descends (prefixWord ++ tailWord_270824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270844 : List Nat := [2, 2, 2, 1, 2, 1, 1, 3, 4, 2, 3]
def baseStart_270844 : Nat := 118140960795 + 270844 * 2 ^ 59
def prefixEnd_270844 : Nat := 4983230072969 + 3 ^ 40 * 270844 * 2
def baseEnd_270844 : Nat := 139073154386443555304417

theorem tailTrace_270844 : CollatzResearch.WordTrace tailWord_270844 prefixEnd_270844 139073154386443555304417 := by
  unfold tailWord_270844
  simp only [CollatzResearch.WordTrace]
  refine ⟨4939246115392959658821793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6585661487190612878429057 4939246115392959658821793)
  ·
    refine ⟨3704434586544719744116345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4939246115392959658821793 3704434586544719744116345)
    ·
      refine ⟨2778325939908539808087259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3704434586544719744116345 2778325939908539808087259)
      ·
        refine ⟨4167488909862809712130889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2778325939908539808087259 4167488909862809712130889)
        ·
          refine ⟨3125616682397107284098167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4167488909862809712130889 3125616682397107284098167)
          ·
            refine ⟨4688425023595660926147251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3125616682397107284098167 4688425023595660926147251)
            ·
              refine ⟨7032637535393491389220877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4688425023595660926147251 7032637535393491389220877)
              ·
                refine ⟨2637239075772559270957829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7032637535393491389220877 2637239075772559270957829)
                ·
                  refine ⟨494482326707354863304593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2637239075772559270957829 494482326707354863304593)
                  ·
                    refine ⟨370861745030516147478445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 494482326707354863304593 370861745030516147478445)
                    ·
                      refine ⟨139073154386443555304417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 370861745030516147478445 139073154386443555304417)
                      ·
                        rfl

theorem cell23_270844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_270844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270844 prefixEnd_270844 := by exact prefixLift 270844
  have htrace : WordTrace (prefixWord ++ tailWord_270844) baseStart_270844 baseEnd_270844 := by
    simpa [prefixWord, tailWord_270844, baseEnd_270844] using wordTrace_append hprefix tailTrace_270844
  have hstable : (prefixWord ++ tailWord_270844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270844).length < 2 ^ (prefixWord ++ tailWord_270844).sum := by decide
  have hdescent : baseEnd_270844 < baseStart_270844 := by decide
  rcases family_descends (prefixWord ++ tailWord_270844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270847 : List Nat := [1, 1, 2, 2, 1, 2, 5, 1, 8]
def baseStart_270847 : Nat := 118140960795 + 270847 * 2 ^ 59
def prefixEnd_270847 : Nat := 4983230072969 + 3 ^ 40 * 270847 * 2
def baseEnd_270847 : Nat := 15452743869823004840767

theorem tailTrace_270847 : CollatzResearch.WordTrace tailWord_270847 prefixEnd_270847 15452743869823004840767 := by
  unfold tailWord_270847
  simp only [CollatzResearch.WordTrace]
  refine ⟨9878601649775050830002795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6585734433183367220001863 9878601649775050830002795)
  ·
    refine ⟨14817902474662576245004193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9878601649775050830002795 14817902474662576245004193)
    ·
      refine ⟨11113426855996932183753145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14817902474662576245004193 11113426855996932183753145)
      ·
        refine ⟨8335070141997699137814859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11113426855996932183753145 8335070141997699137814859)
        ·
          refine ⟨12502605212996548706722289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8335070141997699137814859 12502605212996548706722289)
          ·
            refine ⟨9376953909747411530041717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12502605212996548706722289 9376953909747411530041717)
            ·
              refine ⟨879089429038819830941411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9376953909747411530041717 879089429038819830941411)
              ·
                refine ⟨1318634143558229746412117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 879089429038819830941411 1318634143558229746412117)
                ·
                  refine ⟨15452743869823004840767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1318634143558229746412117 15452743869823004840767)
                  ·
                    rfl

theorem cell23_270847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 8].length) (baseStart_270847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270847 prefixEnd_270847 := by exact prefixLift 270847
  have htrace : WordTrace (prefixWord ++ tailWord_270847) baseStart_270847 baseEnd_270847 := by
    simpa [prefixWord, tailWord_270847, baseEnd_270847] using wordTrace_append hprefix tailTrace_270847
  have hstable : (prefixWord ++ tailWord_270847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270847).length < 2 ^ (prefixWord ++ tailWord_270847).sum := by decide
  have hdescent : baseEnd_270847 < baseStart_270847 := by decide
  rcases family_descends (prefixWord ++ tailWord_270847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270851 : List Nat := [1, 1, 1, 3, 2, 1, 3, 6, 1, 4]
def baseStart_270851 : Nat := 118140960795 + 270851 * 2 ^ 59
def prefixEnd_270851 : Nat := 4983230072969 + 3 ^ 40 * 270851 * 2
def baseEnd_270851 : Nat := 46358916250341675972295

theorem tailTrace_270851 : CollatzResearch.WordTrace tailWord_270851 prefixEnd_270851 46358916250341675972295 := by
  unfold tailWord_270851
  simp only [CollatzResearch.WordTrace]
  refine ⟨9878747541760559513148407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6585831694507039675432271 9878747541760559513148407)
  ·
    refine ⟨14818121312640839269722611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9878747541760559513148407 14818121312640839269722611)
    ·
      refine ⟨22227181968961258904583917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14818121312640839269722611 22227181968961258904583917)
      ·
        refine ⟨8335193238360472089218969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22227181968961258904583917 8335193238360472089218969)
        ·
          refine ⟨6251394928770354066914227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8335193238360472089218969 6251394928770354066914227)
          ·
            refine ⟨9377092393155531100371341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6251394928770354066914227 9377092393155531100371341)
            ·
              refine ⟨3516409647433324162639253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9377092393155531100371341 3516409647433324162639253)
              ·
                refine ⟨164831702223437070123715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3516409647433324162639253 164831702223437070123715)
                ·
                  refine ⟨247247553335155605185573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 164831702223437070123715 247247553335155605185573)
                  ·
                    refine ⟨46358916250341675972295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 247247553335155605185573 46358916250341675972295)
                    ·
                      rfl

theorem cell23_270851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 6, 1, 4].length) (baseStart_270851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270851 prefixEnd_270851 := by exact prefixLift 270851
  have htrace : WordTrace (prefixWord ++ tailWord_270851) baseStart_270851 baseEnd_270851 := by
    simpa [prefixWord, tailWord_270851, baseEnd_270851] using wordTrace_append hprefix tailTrace_270851
  have hstable : (prefixWord ++ tailWord_270851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270851).length < 2 ^ (prefixWord ++ tailWord_270851).sum := by decide
  have hdescent : baseEnd_270851 < baseStart_270851 := by decide
  rcases family_descends (prefixWord ++ tailWord_270851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270867 : List Nat := [1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 6]
def baseStart_270867 : Nat := 118140960795 + 270867 * 2 ^ 59
def prefixEnd_270867 : Nat := 4983230072969 + 3 ^ 40 * 270867 * 2
def baseEnd_270867 : Nat := 139084964441496965316811

theorem tailTrace_270867 : CollatzResearch.WordTrace tailWord_270867 prefixEnd_270867 139084964441496965316811 := by
  unfold tailWord_270867
  simp only [CollatzResearch.WordTrace]
  refine ⟨9879331109702594245730855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6586220739801729497153903 9879331109702594245730855)
  ·
    refine ⟨14818996664553891368596283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9879331109702594245730855 14818996664553891368596283)
    ·
      refine ⟨22228494996830837052894425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14818996664553891368596283 22228494996830837052894425)
      ·
        refine ⟨16671371247623127789670819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22228494996830837052894425 16671371247623127789670819)
        ·
          refine ⟨25007056871434691684506229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16671371247623127789670819 25007056871434691684506229)
          ·
            refine ⟨2344411581697002345422459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25007056871434691684506229 2344411581697002345422459)
            ·
              refine ⟨3516617372545503518133689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2344411581697002345422459 3516617372545503518133689)
              ·
                refine ⟨2637463029409127638600267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3516617372545503518133689 2637463029409127638600267)
                ·
                  refine ⟨3956194544113691457900401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2637463029409127638600267 3956194544113691457900401)
                  ·
                    refine ⟨2967145908085268593425301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3956194544113691457900401 2967145908085268593425301)
                    ·
                      refine ⟨139084964441496965316811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2967145908085268593425301 139084964441496965316811)
                      ·
                        rfl

theorem cell23_270867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 6].length) (baseStart_270867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270867 prefixEnd_270867 := by exact prefixLift 270867
  have htrace : WordTrace (prefixWord ++ tailWord_270867) baseStart_270867 baseEnd_270867 := by
    simpa [prefixWord, tailWord_270867, baseEnd_270867] using wordTrace_append hprefix tailTrace_270867
  have hstable : (prefixWord ++ tailWord_270867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270867).length < 2 ^ (prefixWord ++ tailWord_270867).sum := by decide
  have hdescent : baseEnd_270867 < baseStart_270867 := by decide
  rcases family_descends (prefixWord ++ tailWord_270867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270868 : List Nat := [2, 4, 3, 1, 1, 1, 2, 2, 3, 4]
def baseStart_270868 : Nat := 118140960795 + 270868 * 2 ^ 59
def prefixEnd_270868 : Nat := 4983230072969 + 3 ^ 40 * 270868 * 2
def baseEnd_270868 : Nat := 46361825974050487134769

theorem tailTrace_270868 : CollatzResearch.WordTrace tailWord_270868 prefixEnd_270868 46361825974050487134769 := by
  unfold tailWord_270868
  simp only [CollatzResearch.WordTrace]
  refine ⟨4939683791349485708258629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6586245055132647611011505 4939683791349485708258629)
  ·
    refine ⟨926190710878028570298493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4939683791349485708258629 926190710878028570298493)
    ·
      refine ⟨347321516579260713861935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 926190710878028570298493 347321516579260713861935)
      ·
        refine ⟨520982274868891070792903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347321516579260713861935 520982274868891070792903)
        ·
          refine ⟨781473412303336606189355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 520982274868891070792903 781473412303336606189355)
          ·
            refine ⟨1172210118455004909284033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 781473412303336606189355 1172210118455004909284033)
            ·
              refine ⟨879157588841253681963025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1172210118455004909284033 879157588841253681963025)
              ·
                refine ⟨659368191630940261472269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 879157588841253681963025 659368191630940261472269)
                ·
                  refine ⟨247263071861602598052101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 659368191630940261472269 247263071861602598052101)
                  ·
                    refine ⟨46361825974050487134769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 247263071861602598052101 46361825974050487134769)
                    ·
                      rfl

theorem cell23_270868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_270868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270868 prefixEnd_270868 := by exact prefixLift 270868
  have htrace : WordTrace (prefixWord ++ tailWord_270868) baseStart_270868 baseEnd_270868 := by
    simpa [prefixWord, tailWord_270868, baseEnd_270868] using wordTrace_append hprefix tailTrace_270868
  have hstable : (prefixWord ++ tailWord_270868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270868).length < 2 ^ (prefixWord ++ tailWord_270868).sum := by decide
  have hdescent : baseEnd_270868 < baseStart_270868 := by decide
  rcases family_descends (prefixWord ++ tailWord_270868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270902 : List Nat := [5, 1, 2, 1, 2, 2, 3, 2, 1, 4]
def baseStart_270902 : Nat := 118140960795 + 270902 * 2 ^ 59
def prefixEnd_270902 : Nat := 4983230072969 + 3 ^ 40 * 270902 * 2
def baseEnd_270902 : Nat := 46367645421468109459717

theorem tailTrace_270902 : CollatzResearch.WordTrace tailWord_270902 prefixEnd_270902 46367645421468109459717 := by
  unfold tailWord_270902
  simp only [CollatzResearch.WordTrace]
  refine ⟨617537979035987201453435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6587071776383863482169973 617537979035987201453435)
  ·
    refine ⟨926306968553980802180153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 617537979035987201453435 926306968553980802180153)
    ·
      refine ⟨694730226415485601635115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 926306968553980802180153 694730226415485601635115)
      ·
        refine ⟨1042095339623228402452673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 694730226415485601635115 1042095339623228402452673)
        ·
          refine ⟨781571504717421301839505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1042095339623228402452673 781571504717421301839505)
          ·
            refine ⟨586178628538065976379629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 781571504717421301839505 586178628538065976379629)
            ·
              refine ⟨219816985701774741142361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 586178628538065976379629 219816985701774741142361)
              ·
                refine ⟨164862739276331055856771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 219816985701774741142361 164862739276331055856771)
                ·
                  refine ⟨247294108914496583785157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 164862739276331055856771 247294108914496583785157)
                  ·
                    refine ⟨46367645421468109459717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 247294108914496583785157 46367645421468109459717)
                    ·
                      rfl

theorem cell23_270902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_270902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270902 prefixEnd_270902 := by exact prefixLift 270902
  have htrace : WordTrace (prefixWord ++ tailWord_270902) baseStart_270902 baseEnd_270902 := by
    simpa [prefixWord, tailWord_270902, baseEnd_270902] using wordTrace_append hprefix tailTrace_270902
  have hstable : (prefixWord ++ tailWord_270902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270902).length < 2 ^ (prefixWord ++ tailWord_270902).sum := by decide
  have hdescent : baseEnd_270902 < baseStart_270902 := by decide
  rcases family_descends (prefixWord ++ tailWord_270902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270908 : List Nat := [2, 2, 2, 2, 3, 1, 3, 1, 3, 1, 3]
def baseStart_270908 : Nat := 118140960795 + 270908 * 2 ^ 59
def prefixEnd_270908 : Nat := 4983230072969 + 3 ^ 40 * 270908 * 2
def baseEnd_270908 : Nat := 139106017148331304904123

theorem tailTrace_270908 : CollatzResearch.WordTrace tailWord_270908 prefixEnd_270908 139106017148331304904123 := by
  unfold tailWord_270908
  simp only [CollatzResearch.WordTrace]
  refine ⟨4940413251277029123986689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6587217668369372165315585 4940413251277029123986689)
  ·
    refine ⟨3705309938457771842990017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4940413251277029123986689 3705309938457771842990017)
    ·
      refine ⟨2778982453843328882242513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3705309938457771842990017 2778982453843328882242513)
      ·
        refine ⟨2084236840382496661681885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2778982453843328882242513 2084236840382496661681885)
        ·
          refine ⟨781588815143436248130707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2084236840382496661681885 781588815143436248130707)
          ·
            refine ⟨1172383222715154372196061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 781588815143436248130707 1172383222715154372196061)
            ·
              refine ⟨439643708518182889573523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1172383222715154372196061 439643708518182889573523)
              ·
                refine ⟨659465562777274334360285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 439643708518182889573523 659465562777274334360285)
                ·
                  refine ⟨247299586041477875385107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 659465562777274334360285 247299586041477875385107)
                  ·
                    refine ⟨370949379062216813077661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 247299586041477875385107 370949379062216813077661)
                    ·
                      refine ⟨139106017148331304904123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 370949379062216813077661 139106017148331304904123)
                      ·
                        rfl

theorem cell23_270908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_270908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270908 prefixEnd_270908 := by exact prefixLift 270908
  have htrace : WordTrace (prefixWord ++ tailWord_270908) baseStart_270908 baseEnd_270908 := by
    simpa [prefixWord, tailWord_270908, baseEnd_270908] using wordTrace_append hprefix tailTrace_270908
  have hstable : (prefixWord ++ tailWord_270908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270908).length < 2 ^ (prefixWord ++ tailWord_270908).sum := by decide
  have hdescent : baseEnd_270908 < baseStart_270908 := by decide
  rcases family_descends (prefixWord ++ tailWord_270908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270924 : List Nat := [2, 2, 1, 3, 1, 2, 2, 3, 1, 6]
def baseStart_270924 : Nat := 118140960795 + 270924 * 2 ^ 59
def prefixEnd_270924 : Nat := 4983230072969 + 3 ^ 40 * 270924 * 2
def baseEnd_270924 : Nat := 46371410946267747434683

theorem tailTrace_270924 : CollatzResearch.WordTrace tailWord_270924 prefixEnd_270924 46371410946267747434683 := by
  unfold tailWord_270924
  simp only [CollatzResearch.WordTrace]
  refine ⟨4940705035248046490277913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6587606713664061987037217 4940705035248046490277913)
  ·
    refine ⟨3705528776436034867708435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4940705035248046490277913 3705528776436034867708435)
    ·
      refine ⟨5558293164654052301562653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3705528776436034867708435 5558293164654052301562653)
      ·
        refine ⟨2084359936745269613085995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5558293164654052301562653 2084359936745269613085995)
        ·
          refine ⟨3126539905117904419628993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2084359936745269613085995 3126539905117904419628993)
          ·
            refine ⟨2344904928838428314721745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3126539905117904419628993 2344904928838428314721745)
            ·
              refine ⟨1758678696628821236041309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2344904928838428314721745 1758678696628821236041309)
              ·
                refine ⟨659504511235807963515491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1758678696628821236041309 659504511235807963515491)
                ·
                  refine ⟨989256766853711945273237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 659504511235807963515491 989256766853711945273237)
                  ·
                    refine ⟨46371410946267747434683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 989256766853711945273237 46371410946267747434683)
                    ·
                      rfl

theorem cell23_270924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 1, 6].length) (baseStart_270924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270924 prefixEnd_270924 := by exact prefixLift 270924
  have htrace : WordTrace (prefixWord ++ tailWord_270924) baseStart_270924 baseEnd_270924 := by
    simpa [prefixWord, tailWord_270924, baseEnd_270924] using wordTrace_append hprefix tailTrace_270924
  have hstable : (prefixWord ++ tailWord_270924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270924).length < 2 ^ (prefixWord ++ tailWord_270924).sum := by decide
  have hdescent : baseEnd_270924 < baseStart_270924 := by decide
  rcases family_descends (prefixWord ++ tailWord_270924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270944 : List Nat := [2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 4]
def baseStart_270944 : Nat := 118140960795 + 270944 * 2 ^ 59
def prefixEnd_270944 : Nat := 4983230072969 + 3 ^ 40 * 270944 * 2
def baseEnd_270944 : Nat := 139124502451893164053957

theorem tailTrace_270944 : CollatzResearch.WordTrace tailWord_270944 prefixEnd_270944 139124502451893164053957 := by
  unfold tailWord_270944
  simp only [CollatzResearch.WordTrace]
  refine ⟨4941069765211818198141943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6588093020282424264189257 4941069765211818198141943)
  ·
    refine ⟨7411604647817727297212915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4941069765211818198141943 7411604647817727297212915)
    ·
      refine ⟨11117406971726590945819373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7411604647817727297212915 11117406971726590945819373)
      ·
        refine ⟨4169027614397471604682265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11117406971726590945819373 4169027614397471604682265)
        ·
          refine ⟨3126770710798103703511699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4169027614397471604682265 3126770710798103703511699)
          ·
            refine ⟨4690156066197155555267549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3126770710798103703511699 4690156066197155555267549)
            ·
              refine ⟨1758808524823933333225331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4690156066197155555267549 1758808524823933333225331)
              ·
                refine ⟨2638212787235899999837997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1758808524823933333225331 2638212787235899999837997)
                ·
                  refine ⟨989329795213462499939249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2638212787235899999837997 989329795213462499939249)
                  ·
                    refine ⟨741997346410096874954437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 989329795213462499939249 741997346410096874954437)
                    ·
                      refine ⟨139124502451893164053957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 741997346410096874954437 139124502451893164053957)
                      ·
                        rfl

theorem cell23_270944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_270944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270944 prefixEnd_270944 := by exact prefixLift 270944
  have htrace : WordTrace (prefixWord ++ tailWord_270944) baseStart_270944 baseEnd_270944 := by
    simpa [prefixWord, tailWord_270944, baseEnd_270944] using wordTrace_append hprefix tailTrace_270944
  have hstable : (prefixWord ++ tailWord_270944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270944).length < 2 ^ (prefixWord ++ tailWord_270944).sum := by decide
  have hdescent : baseEnd_270944 < baseStart_270944 := by decide
  rcases family_descends (prefixWord ++ tailWord_270944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270948 : List Nat := [2, 3, 1, 1, 2, 2, 5, 1, 1, 1, 4]
def baseStart_270948 : Nat := 118140960795 + 270948 * 2 ^ 59
def prefixEnd_270948 : Nat := 4983230072969 + 3 ^ 40 * 270948 * 2
def baseEnd_270948 : Nat := 139126556374511148403939

theorem tailTrace_270948 : CollatzResearch.WordTrace tailWord_270948 prefixEnd_270948 139126556374511148403939 := by
  unfold tailWord_270948
  simp only [CollatzResearch.WordTrace]
  refine ⟨4941142711204572539714749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6588190281606096719619665 4941142711204572539714749)
  ·
    refine ⟨1852928516701714702393031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4941142711204572539714749 1852928516701714702393031)
    ·
      refine ⟨2779392775052572053589547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1852928516701714702393031 2779392775052572053589547)
      ·
        refine ⟨4169089162578858080384321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2779392775052572053589547 4169089162578858080384321)
        ·
          refine ⟨3126816871934143560288241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4169089162578858080384321 3126816871934143560288241)
          ·
            refine ⟨2345112653950607670216181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3126816871934143560288241 2345112653950607670216181)
            ·
              refine ⟨219854311307869469082767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2345112653950607670216181 219854311307869469082767)
              ·
                refine ⟨329781466961804203624151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219854311307869469082767 329781466961804203624151)
                ·
                  refine ⟨494672200442706305436227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 329781466961804203624151 494672200442706305436227)
                  ·
                    refine ⟨742008300664059458154341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 494672200442706305436227 742008300664059458154341)
                    ·
                      refine ⟨139126556374511148403939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 742008300664059458154341 139126556374511148403939)
                      ·
                        rfl

theorem cell23_270948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 1, 1, 4].length) (baseStart_270948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270948 prefixEnd_270948 := by exact prefixLift 270948
  have htrace : WordTrace (prefixWord ++ tailWord_270948) baseStart_270948 baseEnd_270948 := by
    simpa [prefixWord, tailWord_270948, baseEnd_270948] using wordTrace_append hprefix tailTrace_270948
  have hstable : (prefixWord ++ tailWord_270948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270948).length < 2 ^ (prefixWord ++ tailWord_270948).sum := by decide
  have hdescent : baseEnd_270948 < baseStart_270948 := by decide
  rcases family_descends (prefixWord ++ tailWord_270948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270958 : List Nat := [4, 1, 2, 2, 2, 1, 1, 4, 2, 4]
def baseStart_270958 : Nat := 118140960795 + 270958 * 2 ^ 59
def prefixEnd_270958 : Nat := 4983230072969 + 3 ^ 40 * 270958 * 2
def baseEnd_270958 : Nat := 46377230393685369759631

theorem tailTrace_270958 : CollatzResearch.WordTrace tailWord_270958 prefixEnd_270958 46377230393685369759631 := by
  unfold tailWord_270958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1235331269046614598411691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6588433434915277858195685 1235331269046614598411691)
  ·
    refine ⟨1852996903569921897617537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1235331269046614598411691 1852996903569921897617537)
    ·
      refine ⟨1389747677677441423213153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1852996903569921897617537 1389747677677441423213153)
      ·
        refine ⟨1042310758258081067409865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1389747677677441423213153 1042310758258081067409865)
        ·
          refine ⟨781733068693560800557399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1042310758258081067409865 781733068693560800557399)
          ·
            refine ⟨1172599603040341200836099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 781733068693560800557399 1172599603040341200836099)
            ·
              refine ⟨1758899404560511801254149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1172599603040341200836099 1758899404560511801254149)
              ·
                refine ⟨329793638355095962735153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1758899404560511801254149 329793638355095962735153)
                ·
                  refine ⟨247345228766321972051365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 329793638355095962735153 247345228766321972051365)
                  ·
                    refine ⟨46377230393685369759631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 247345228766321972051365 46377230393685369759631)
                    ·
                      rfl

theorem cell23_270958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_270958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270958 prefixEnd_270958 := by exact prefixLift 270958
  have htrace : WordTrace (prefixWord ++ tailWord_270958) baseStart_270958 baseEnd_270958 := by
    simpa [prefixWord, tailWord_270958, baseEnd_270958] using wordTrace_append hprefix tailTrace_270958
  have hstable : (prefixWord ++ tailWord_270958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270958).length < 2 ^ (prefixWord ++ tailWord_270958).sum := by decide
  have hdescent : baseEnd_270958 < baseStart_270958 := by decide
  rcases family_descends (prefixWord ++ tailWord_270958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270981 : List Nat := [1, 3, 1, 1, 4, 2, 1, 3, 1, 3, 3]
def baseStart_270981 : Nat := 118140960795 + 270981 * 2 ^ 59
def prefixEnd_270981 : Nat := 4983230072969 + 3 ^ 40 * 270981 * 2
def baseEnd_270981 : Nat := 139143501236109519291287

theorem tailTrace_270981 : CollatzResearch.WordTrace tailWord_270981 prefixEnd_270981 139143501236109519291287 := by
  unfold tailWord_270981
  simp only [CollatzResearch.WordTrace]
  refine ⟨9883489031289591715380797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6588992687526394476920531 9883489031289591715380797)
  ·
    refine ⟨3706308386733596893267799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9883489031289591715380797 3706308386733596893267799)
    ·
      refine ⟨5559462580100395339901699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3706308386733596893267799 5559462580100395339901699)
      ·
        refine ⟨8339193870150593009852549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5559462580100395339901699 8339193870150593009852549)
        ·
          refine ⟨1563598850653236189347353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8339193870150593009852549 1563598850653236189347353)
          ·
            refine ⟨1172699137989927142010515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1563598850653236189347353 1172699137989927142010515)
            ·
              refine ⟨1759048706984890713015773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1172699137989927142010515 1759048706984890713015773)
              ·
                refine ⟨659643265119334017380915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1759048706984890713015773 659643265119334017380915)
                ·
                  refine ⟨989464897679001026071373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 659643265119334017380915 989464897679001026071373)
                  ·
                    refine ⟨371049336629625384776765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 989464897679001026071373 371049336629625384776765)
                    ·
                      refine ⟨139143501236109519291287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 371049336629625384776765 139143501236109519291287)
                      ·
                        rfl

theorem cell23_270981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 3, 3].length) (baseStart_270981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_270981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_270981 prefixEnd_270981 := by exact prefixLift 270981
  have htrace : WordTrace (prefixWord ++ tailWord_270981) baseStart_270981 baseEnd_270981 := by
    simpa [prefixWord, tailWord_270981, baseEnd_270981] using wordTrace_append hprefix tailTrace_270981
  have hstable : (prefixWord ++ tailWord_270981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270981).length < 2 ^ (prefixWord ++ tailWord_270981).sum := by decide
  have hdescent : baseEnd_270981 < baseStart_270981 := by decide
  rcases family_descends (prefixWord ++ tailWord_270981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271024 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 5]
def baseStart_271024 : Nat := 118140960795 + 271024 * 2 ^ 59
def prefixEnd_271024 : Nat := 4983230072969 + 3 ^ 40 * 271024 * 2
def baseEnd_271024 : Nat := 139165580904252851053589

theorem tailTrace_271024 : CollatzResearch.WordTrace tailWord_271024 prefixEnd_271024 139165580904252851053589 := by
  unfold tailWord_271024
  simp only [CollatzResearch.WordTrace]
  refine ⟨4942528685066905029598063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6590038246755873372797417 4942528685066905029598063)
  ·
    refine ⟨7413793027600357544397095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4942528685066905029598063 7413793027600357544397095)
    ·
      refine ⟨11120689541400536316595643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7413793027600357544397095 11120689541400536316595643)
      ·
        refine ⟨16681034312100804474893465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11120689541400536316595643 16681034312100804474893465)
        ·
          refine ⟨12510775734075603356170099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16681034312100804474893465 12510775734075603356170099)
          ·
            refine ⟨18766163601113405034255149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12510775734075603356170099 18766163601113405034255149)
            ·
              refine ⟨7037311350417526887845681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18766163601113405034255149 7037311350417526887845681)
              ·
                refine ⟨5277983512813145165884261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7037311350417526887845681 5277983512813145165884261)
                ·
                  refine ⟨989621908652464718603299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5277983512813145165884261 989621908652464718603299)
                  ·
                    refine ⟨1484432862978697077904949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 989621908652464718603299 1484432862978697077904949)
                    ·
                      refine ⟨139165580904252851053589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1484432862978697077904949 139165580904252851053589)
                      ·
                        rfl

theorem cell23_271024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 5].length) (baseStart_271024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271024 prefixEnd_271024 := by exact prefixLift 271024
  have htrace : WordTrace (prefixWord ++ tailWord_271024) baseStart_271024 baseEnd_271024 := by
    simpa [prefixWord, tailWord_271024, baseEnd_271024] using wordTrace_append hprefix tailTrace_271024
  have hstable : (prefixWord ++ tailWord_271024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271024).length < 2 ^ (prefixWord ++ tailWord_271024).sum := by decide
  have hdescent : baseEnd_271024 < baseStart_271024 := by decide
  rcases family_descends (prefixWord ++ tailWord_271024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271058 : List Nat := [3, 2, 2, 2, 3, 1, 1, 1, 2, 1, 5]
def baseStart_271058 : Nat := 118140960795 + 271058 * 2 ^ 59
def prefixEnd_271058 : Nat := 4983230072969 + 3 ^ 40 * 271058 * 2
def baseEnd_271058 : Nat := 139183039246505718028433

theorem tailTrace_271058 : CollatzResearch.WordTrace tailWord_271058 prefixEnd_271058 139183039246505718028433 := by
  unfold tailWord_271058
  simp only [CollatzResearch.WordTrace]
  refine ⟨2471574363002658466483457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6590864968007089243955885 2471574363002658466483457)
  ·
    refine ⟨1853680772251993849862593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2471574363002658466483457 1853680772251993849862593)
    ·
      refine ⟨1390260579188995387396945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1853680772251993849862593 1390260579188995387396945)
      ·
        refine ⟨1042695434391746540547709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1390260579188995387396945 1042695434391746540547709)
        ·
          refine ⟨391010787896904952705391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1042695434391746540547709 391010787896904952705391)
          ·
            refine ⟨586516181845357429058087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391010787896904952705391 586516181845357429058087)
            ·
              refine ⟨879774272768036143587131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 586516181845357429058087 879774272768036143587131)
              ·
                refine ⟨1319661409152054215380697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 879774272768036143587131 1319661409152054215380697)
                ·
                  refine ⟨989746056864040661535523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1319661409152054215380697 989746056864040661535523)
                  ·
                    refine ⟨1484619085296060992303285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 989746056864040661535523 1484619085296060992303285)
                    ·
                      refine ⟨139183039246505718028433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1484619085296060992303285 139183039246505718028433)
                      ·
                        rfl

theorem cell23_271058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_271058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271058 prefixEnd_271058 := by exact prefixLift 271058
  have htrace : WordTrace (prefixWord ++ tailWord_271058) baseStart_271058 baseEnd_271058 := by
    simpa [prefixWord, tailWord_271058, baseEnd_271058] using wordTrace_append hprefix tailTrace_271058
  have hstable : (prefixWord ++ tailWord_271058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271058).length < 2 ^ (prefixWord ++ tailWord_271058).sum := by decide
  have hdescent : baseEnd_271058 < baseStart_271058 := by decide
  rcases family_descends (prefixWord ++ tailWord_271058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271093 : List Nat := [1, 3, 6, 1, 2, 1, 1, 2, 1, 3, 2]
def baseStart_271093 : Nat := 118140960795 + 271093 * 2 ^ 59
def prefixEnd_271093 : Nat := 4983230072969 + 3 ^ 40 * 271093 * 2
def baseEnd_271093 : Nat := 139201011069413081090773

theorem tailTrace_271093 : CollatzResearch.WordTrace tailWord_271093 prefixEnd_271093 139201011069413081090773 := by
  unfold tailWord_271093
  simp only [CollatzResearch.WordTrace]
  refine ⟨9887574006883834843457933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6591716004589223228971955 9887574006883834843457933)
  ·
    refine ⟨3707840252581438066296725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9887574006883834843457933 3707840252581438066296725)
    ·
      refine ⟨173805011839754909357659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3707840252581438066296725 173805011839754909357659)
      ·
        refine ⟨260707517759632364036489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173805011839754909357659 260707517759632364036489)
        ·
          refine ⟨195530638319724273027367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 260707517759632364036489 195530638319724273027367)
          ·
            refine ⟨293295957479586409541051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195530638319724273027367 293295957479586409541051)
            ·
              refine ⟨439943936219379614311577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 293295957479586409541051 439943936219379614311577)
              ·
                refine ⟨329957952164534710733683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 439943936219379614311577 329957952164534710733683)
                ·
                  refine ⟨494936928246802066100525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 329957952164534710733683 494936928246802066100525)
                  ·
                    refine ⟨185601348092550774787697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 494936928246802066100525 185601348092550774787697)
                    ·
                      refine ⟨139201011069413081090773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 185601348092550774787697 139201011069413081090773)
                      ·
                        rfl

theorem cell23_271093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_271093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271093 prefixEnd_271093 := by exact prefixLift 271093
  have htrace : WordTrace (prefixWord ++ tailWord_271093) baseStart_271093 baseEnd_271093 := by
    simpa [prefixWord, tailWord_271093, baseEnd_271093] using wordTrace_append hprefix tailTrace_271093
  have hstable : (prefixWord ++ tailWord_271093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271093).length < 2 ^ (prefixWord ++ tailWord_271093).sum := by decide
  have hdescent : baseEnd_271093 < baseStart_271093 := by decide
  rcases family_descends (prefixWord ++ tailWord_271093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271108 : List Nat := [2, 3, 2, 2, 1, 1, 4, 1, 2, 5]
def baseStart_271108 : Nat := 118140960795 + 271108 * 2 ^ 59
def prefixEnd_271108 : Nat := 4983230072969 + 3 ^ 40 * 271108 * 2
def baseEnd_271108 : Nat := 46402904426410174134401

theorem tailTrace_271108 : CollatzResearch.WordTrace tailWord_271108 prefixEnd_271108 46402904426410174134401 := by
  unfold tailWord_271108
  simp only [CollatzResearch.WordTrace]
  refine ⟨4944060550914746202626989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6592080734552994936835985 4944060550914746202626989)
  ·
    refine ⟨1854022706593029825985121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4944060550914746202626989 1854022706593029825985121)
    ·
      refine ⟨1390517029944772369488841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1854022706593029825985121 1390517029944772369488841)
      ·
        refine ⟨1042887772458579277116631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1390517029944772369488841 1042887772458579277116631)
        ·
          refine ⟨1564331658687868915674947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1042887772458579277116631 1564331658687868915674947)
          ·
            refine ⟨2346497488031803373512421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1564331658687868915674947 2346497488031803373512421)
            ·
              refine ⟨439968279005963132533579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2346497488031803373512421 439968279005963132533579)
              ·
                refine ⟨659952418508944698800369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 439968279005963132533579 659952418508944698800369)
                ·
                  refine ⟨494964313881708524100277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 659952418508944698800369 494964313881708524100277)
                  ·
                    refine ⟨46402904426410174134401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 494964313881708524100277 46402904426410174134401)
                    ·
                      rfl

theorem cell23_271108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_271108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271108 prefixEnd_271108 := by exact prefixLift 271108
  have htrace : WordTrace (prefixWord ++ tailWord_271108) baseStart_271108 baseEnd_271108 := by
    simpa [prefixWord, tailWord_271108, baseEnd_271108] using wordTrace_append hprefix tailTrace_271108
  have hstable : (prefixWord ++ tailWord_271108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271108).length < 2 ^ (prefixWord ++ tailWord_271108).sum := by decide
  have hdescent : baseEnd_271108 < baseStart_271108 := by decide
  rcases family_descends (prefixWord ++ tailWord_271108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271128 : List Nat := [2, 1, 2, 3, 1, 1, 1, 4, 2, 4, 2]
def baseStart_271128 : Nat := 118140960795 + 271128 * 2 ^ 59
def prefixEnd_271128 : Nat := 4983230072969 + 3 ^ 40 * 271128 * 2
def baseEnd_271128 : Nat := 139218982892320444153111

theorem tailTrace_271128 : CollatzResearch.WordTrace tailWord_271128 prefixEnd_271128 139218982892320444153111 := by
  unfold tailWord_271128
  simp only [CollatzResearch.WordTrace]
  refine ⟨4944425280878517910491019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6592567041171357213988025 4944425280878517910491019)
  ·
    refine ⟨7416637921317776865736529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4944425280878517910491019 7416637921317776865736529)
    ·
      refine ⟨5562478440988332649302397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7416637921317776865736529 5562478440988332649302397)
      ·
        refine ⟨2085929415370624743488399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5562478440988332649302397 2085929415370624743488399)
        ·
          refine ⟨3128894123055937115232599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2085929415370624743488399 3128894123055937115232599)
          ·
            refine ⟨4693341184583905672848899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3128894123055937115232599 4693341184583905672848899)
            ·
              refine ⟨7040011776875858509273349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4693341184583905672848899 7040011776875858509273349)
              ·
                refine ⟨1320002208164223470488753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7040011776875858509273349 1320002208164223470488753)
                ·
                  refine ⟨990001656123167602866565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1320002208164223470488753 990001656123167602866565)
                  ·
                    refine ⟨185625310523093925537481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 990001656123167602866565 185625310523093925537481)
                    ·
                      refine ⟨139218982892320444153111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 185625310523093925537481 139218982892320444153111)
                      ·
                        rfl

theorem cell23_271128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_271128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271128 prefixEnd_271128 := by exact prefixLift 271128
  have htrace : WordTrace (prefixWord ++ tailWord_271128) baseStart_271128 baseEnd_271128 := by
    simpa [prefixWord, tailWord_271128, baseEnd_271128] using wordTrace_append hprefix tailTrace_271128
  have hstable : (prefixWord ++ tailWord_271128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271128).length < 2 ^ (prefixWord ++ tailWord_271128).sum := by decide
  have hdescent : baseEnd_271128 < baseStart_271128 := by decide
  rcases family_descends (prefixWord ++ tailWord_271128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271162 : List Nat := [3, 1, 1, 1, 7, 1, 1, 1, 2, 1, 4]
def baseStart_271162 : Nat := 118140960795 + 271162 * 2 ^ 59
def prefixEnd_271162 : Nat := 4983230072969 + 3 ^ 40 * 271162 * 2
def baseEnd_271162 : Nat := 139236441234573311127955

theorem tailTrace_271162 : CollatzResearch.WordTrace tailWord_271162 prefixEnd_271162 139236441234573311127955 := by
  unfold tailWord_271162
  simp only [CollatzResearch.WordTrace]
  refine ⟨2472522660908464906929935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6593393762422573085146493 2472522660908464906929935)
  ·
    refine ⟨3708783991362697360394903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2472522660908464906929935 3708783991362697360394903)
    ·
      refine ⟨5563175987044046040592355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3708783991362697360394903 5563175987044046040592355)
      ·
        refine ⟨8344763980566069060888533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5563175987044046040592355 8344763980566069060888533)
        ·
          refine ⟨195580405794517243614575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 8344763980566069060888533 195580405794517243614575)
          ·
            refine ⟨293370608691775865421863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195580405794517243614575 293370608691775865421863)
            ·
              refine ⟨440055913037663798132795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 293370608691775865421863 440055913037663798132795)
              ·
                refine ⟨660083869556495697199193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 440055913037663798132795 660083869556495697199193)
                ·
                  refine ⟨495062902167371772899395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 660083869556495697199193 495062902167371772899395)
                  ·
                    refine ⟨742594353251057659349093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 495062902167371772899395 742594353251057659349093)
                    ·
                      refine ⟨139236441234573311127955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 742594353251057659349093 139236441234573311127955)
                      ·
                        rfl

theorem cell23_271162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 2, 1, 4].length) (baseStart_271162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271162 prefixEnd_271162 := by exact prefixLift 271162
  have htrace : WordTrace (prefixWord ++ tailWord_271162) baseStart_271162 baseEnd_271162 := by
    simpa [prefixWord, tailWord_271162, baseEnd_271162] using wordTrace_append hprefix tailTrace_271162
  have hstable : (prefixWord ++ tailWord_271162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271162).length < 2 ^ (prefixWord ++ tailWord_271162).sum := by decide
  have hdescent : baseEnd_271162 < baseStart_271162 := by decide
  rcases family_descends (prefixWord ++ tailWord_271162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271165 : List Nat := [1, 4, 1, 4, 2, 1, 1, 1, 1, 4, 3]
def baseStart_271165 : Nat := 118140960795 + 271165 * 2 ^ 59
def prefixEnd_271165 : Nat := 4983230072969 + 3 ^ 40 * 271165 * 2
def baseEnd_271165 : Nat := 139237981676536799390441

theorem tailTrace_271165 : CollatzResearch.WordTrace tailWord_271165 prefixEnd_271165 139237981676536799390441 := by
  unfold tailWord_271165
  simp only [CollatzResearch.WordTrace]
  refine ⟨9890200062622991140078949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6593466708415327426719299 9890200062622991140078949)
  ·
    refine ⟨1854412511741810838764803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9890200062622991140078949 1854412511741810838764803)
    ·
      refine ⟨2781618767612716258147205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1854412511741810838764803 2781618767612716258147205)
      ·
        refine ⟨521553518927384298402601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2781618767612716258147205 521553518927384298402601)
        ·
          refine ⟨391165139195538223801951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 521553518927384298402601 391165139195538223801951)
          ·
            refine ⟨586747708793307335702927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391165139195538223801951 586747708793307335702927)
            ·
              refine ⟨880121563189961003554391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 586747708793307335702927 880121563189961003554391)
              ·
                refine ⟨1320182344784941505331587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 880121563189961003554391 1320182344784941505331587)
                ·
                  refine ⟨1980273517177412257997381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1320182344784941505331587 1980273517177412257997381)
                  ·
                    refine ⟨371301284470764798374509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1980273517177412257997381 371301284470764798374509)
                    ·
                      refine ⟨139237981676536799390441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 371301284470764798374509 139237981676536799390441)
                      ·
                        rfl

theorem cell23_271165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_271165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271165 prefixEnd_271165 := by exact prefixLift 271165
  have htrace : WordTrace (prefixWord ++ tailWord_271165) baseStart_271165 baseEnd_271165 := by
    simpa [prefixWord, tailWord_271165, baseEnd_271165] using wordTrace_append hprefix tailTrace_271165
  have hstable : (prefixWord ++ tailWord_271165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271165).length < 2 ^ (prefixWord ++ tailWord_271165).sum := by decide
  have hdescent : baseEnd_271165 < baseStart_271165 := by decide
  rcases family_descends (prefixWord ++ tailWord_271165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271185 : List Nat := [1, 2, 2, 1, 6, 2, 1, 2, 6]
def baseStart_271185 : Nat := 118140960795 + 271185 * 2 ^ 59
def prefixEnd_271185 : Nat := 4983230072969 + 3 ^ 40 * 271185 * 2
def baseEnd_271185 : Nat := 15472027921069635682261

theorem tailTrace_271185 : CollatzResearch.WordTrace tailWord_271185 prefixEnd_271185 15472027921069635682261 := by
  unfold tailWord_271185
  simp only [CollatzResearch.WordTrace]
  refine ⟨9890929522550534555807009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6593953015033689703871339 9890929522550534555807009)
  ·
    refine ⟨7418197141912900916855257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9890929522550534555807009 7418197141912900916855257)
    ·
      refine ⟨5563647856434675687641443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7418197141912900916855257 5563647856434675687641443)
      ·
        refine ⟨8345471784652013531462165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5563647856434675687641443 8345471784652013531462165)
        ·
          refine ⟨391193989905563134287289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8345471784652013531462165 391193989905563134287289)
          ·
            refine ⟨293395492429172350715467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 391193989905563134287289 293395492429172350715467)
            ·
              refine ⟨440093238643758526073201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 293395492429172350715467 440093238643758526073201)
              ·
                refine ⟨330069928982818894554901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 440093238643758526073201 330069928982818894554901)
                ·
                  refine ⟨15472027921069635682261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 330069928982818894554901 15472027921069635682261)
                  ·
                    rfl

theorem cell23_271185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 6].length) (baseStart_271185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271185 prefixEnd_271185 := by exact prefixLift 271185
  have htrace : WordTrace (prefixWord ++ tailWord_271185) baseStart_271185 baseEnd_271185 := by
    simpa [prefixWord, tailWord_271185, baseEnd_271185] using wordTrace_append hprefix tailTrace_271185
  have hstable : (prefixWord ++ tailWord_271185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271185).length < 2 ^ (prefixWord ++ tailWord_271185).sum := by decide
  have hdescent : baseEnd_271185 < baseStart_271185 := by decide
  rcases family_descends (prefixWord ++ tailWord_271185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271201 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 2, 5, 4]
def baseStart_271201 : Nat := 118140960795 + 271201 * 2 ^ 59
def prefixEnd_271201 : Nat := 4983230072969 + 3 ^ 40 * 271201 * 2
def baseEnd_271201 : Nat := 139256466980098658540275

theorem tailTrace_271201 : CollatzResearch.WordTrace tailWord_271201 prefixEnd_271201 139256466980098658540275 := by
  unfold tailWord_271201
  simp only [CollatzResearch.WordTrace]
  refine ⟨9891513090492569288389457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6594342060328379525592971 9891513090492569288389457)
  ·
    refine ⟨7418634817869426966292093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9891513090492569288389457 7418634817869426966292093)
    ·
      refine ⟨2781988056701035112359535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7418634817869426966292093 2781988056701035112359535)
      ·
        refine ⟨4172982085051552668539303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2781988056701035112359535 4172982085051552668539303)
        ·
          refine ⟨6259473127577329002808955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4172982085051552668539303 6259473127577329002808955)
          ·
            refine ⟨9389209691365993504213433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6259473127577329002808955 9389209691365993504213433)
            ·
              refine ⟨7041907268524495128160075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9389209691365993504213433 7041907268524495128160075)
              ·
                refine ⟨10562860902786742692240113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7041907268524495128160075 10562860902786742692240113)
                ·
                  refine ⟨7922145677090057019180085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10562860902786742692240113 7922145677090057019180085)
                  ·
                    refine ⟨742701157227192845548133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7922145677090057019180085 742701157227192845548133)
                    ·
                      refine ⟨139256466980098658540275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 742701157227192845548133 139256466980098658540275)
                      ·
                        rfl

theorem cell23_271201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_271201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271201 prefixEnd_271201 := by exact prefixLift 271201
  have htrace : WordTrace (prefixWord ++ tailWord_271201) baseStart_271201 baseEnd_271201 := by
    simpa [prefixWord, tailWord_271201, baseEnd_271201] using wordTrace_append hprefix tailTrace_271201
  have hstable : (prefixWord ++ tailWord_271201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271201).length < 2 ^ (prefixWord ++ tailWord_271201).sum := by decide
  have hdescent : baseEnd_271201 < baseStart_271201 := by decide
  rcases family_descends (prefixWord ++ tailWord_271201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271202 : List Nat := [3, 3, 2, 1, 3, 1, 3, 1, 6]
def baseStart_271202 : Nat := 118140960795 + 271202 * 2 ^ 59
def prefixEnd_271202 : Nat := 4983230072969 + 3 ^ 40 * 271202 * 2
def baseEnd_271202 : Nat := 15472997828972572736419

theorem tailTrace_271202 : CollatzResearch.WordTrace tailWord_271202 prefixEnd_271202 15472997828972572736419 := by
  unfold tailWord_271202
  simp only [CollatzResearch.WordTrace]
  refine ⟨2472887390872236614793965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6594366375659297639450573 2472887390872236614793965)
  ·
    refine ⟨927332771577088730547737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2472887390872236614793965 927332771577088730547737)
    ·
      refine ⟨695499578682816547910803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 927332771577088730547737 695499578682816547910803)
      ·
        refine ⟨1043249368024224821866205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 695499578682816547910803 1043249368024224821866205)
        ·
          refine ⟨391218513009084308199827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1043249368024224821866205 391218513009084308199827)
          ·
            refine ⟨586827769513626462299741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391218513009084308199827 586827769513626462299741)
            ·
              refine ⟨220060413567609923362403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 586827769513626462299741 220060413567609923362403)
              ·
                refine ⟨330090620351414885043605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220060413567609923362403 330090620351414885043605)
                ·
                  refine ⟨15472997828972572736419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 330090620351414885043605 15472997828972572736419)
                  ·
                    rfl

theorem cell23_271202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_271202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271202 prefixEnd_271202 := by exact prefixLift 271202
  have htrace : WordTrace (prefixWord ++ tailWord_271202) baseStart_271202 baseEnd_271202 := by
    simpa [prefixWord, tailWord_271202, baseEnd_271202] using wordTrace_append hprefix tailTrace_271202
  have hstable : (prefixWord ++ tailWord_271202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271202).length < 2 ^ (prefixWord ++ tailWord_271202).sum := by decide
  have hdescent : baseEnd_271202 < baseStart_271202 := by decide
  rcases family_descends (prefixWord ++ tailWord_271202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271218 : List Nat := [3, 2, 1, 2, 1, 1, 2, 3, 3, 1, 4]
def baseStart_271218 : Nat := 118140960795 + 271218 * 2 ^ 59
def prefixEnd_271218 : Nat := 4983230072969 + 3 ^ 40 * 271218 * 2
def baseEnd_271218 : Nat := 139265196151225092027697

theorem tailTrace_271218 : CollatzResearch.WordTrace tailWord_271218 prefixEnd_271218 139265196151225092027697 := by
  unfold tailWord_271218
  simp only [CollatzResearch.WordTrace]
  refine ⟨2473033282857745297939577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6594755420953987461172205 2473033282857745297939577)
  ·
    refine ⟨1854774962143308973454683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2473033282857745297939577 1854774962143308973454683)
    ·
      refine ⟨2782162443214963460182025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1854774962143308973454683 2782162443214963460182025)
      ·
        refine ⟨2086621832411222595136519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2782162443214963460182025 2086621832411222595136519)
        ·
          refine ⟨3129932748616833892704779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2086621832411222595136519 3129932748616833892704779)
          ·
            refine ⟨4694899122925250839057169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3129932748616833892704779 4694899122925250839057169)
            ·
              refine ⟨3521174342193938129292877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4694899122925250839057169 3521174342193938129292877)
              ·
                refine ⟨1320440378322726798484829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3521174342193938129292877 1320440378322726798484829)
                ·
                  refine ⟨495165141871022549431811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1320440378322726798484829 495165141871022549431811)
                  ·
                    refine ⟨742747712806533824147717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 495165141871022549431811 742747712806533824147717)
                    ·
                      refine ⟨139265196151225092027697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 742747712806533824147717 139265196151225092027697)
                      ·
                        rfl

theorem cell23_271218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_271218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271218 prefixEnd_271218 := by exact prefixLift 271218
  have htrace : WordTrace (prefixWord ++ tailWord_271218) baseStart_271218 baseEnd_271218 := by
    simpa [prefixWord, tailWord_271218, baseEnd_271218] using wordTrace_append hprefix tailTrace_271218
  have hstable : (prefixWord ++ tailWord_271218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271218).length < 2 ^ (prefixWord ++ tailWord_271218).sum := by decide
  have hdescent : baseEnd_271218 < baseStart_271218 := by decide
  rcases family_descends (prefixWord ++ tailWord_271218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271222 : List Nat := [5, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2]
def baseStart_271222 : Nat := 118140960795 + 271222 * 2 ^ 59
def prefixEnd_271222 : Nat := 4983230072969 + 3 ^ 40 * 271222 * 2
def baseEnd_271222 : Nat := 139267250073843076377679

theorem tailTrace_271222 : CollatzResearch.WordTrace tailWord_271222 prefixEnd_271222 139267250073843076377679 := by
  unfold tailWord_271222
  simp only [CollatzResearch.WordTrace]
  refine ⟨618267438963530617181495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6594852682277659916602613 618267438963530617181495)
  ·
    refine ⟨927401158445295925772243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 618267438963530617181495 927401158445295925772243)
    ·
      refine ⟨1391101737667943888658365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 927401158445295925772243 1391101737667943888658365)
      ·
        refine ⟨521663151625478958246887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1391101737667943888658365 521663151625478958246887)
        ·
          refine ⟨782494727438218437370331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 521663151625478958246887 782494727438218437370331)
          ·
            refine ⟨1173742091157327656055497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 782494727438218437370331 1173742091157327656055497)
            ·
              refine ⟨880306568367995742041623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1173742091157327656055497 880306568367995742041623)
              ·
                refine ⟨1320459852551993613062435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 880306568367995742041623 1320459852551993613062435)
                ·
                  refine ⟨1980689778827990419593653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1320459852551993613062435 1980689778827990419593653)
                  ·
                    refine ⟨185689666765124101836905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1980689778827990419593653 185689666765124101836905)
                    ·
                      refine ⟨139267250073843076377679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 185689666765124101836905 139267250073843076377679)
                      ·
                        rfl

theorem cell23_271222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_271222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271222 prefixEnd_271222 := by exact prefixLift 271222
  have htrace : WordTrace (prefixWord ++ tailWord_271222) baseStart_271222 baseEnd_271222 := by
    simpa [prefixWord, tailWord_271222, baseEnd_271222] using wordTrace_append hprefix tailTrace_271222
  have hstable : (prefixWord ++ tailWord_271222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271222).length < 2 ^ (prefixWord ++ tailWord_271222).sum := by decide
  have hdescent : baseEnd_271222 < baseStart_271222 := by decide
  rcases family_descends (prefixWord ++ tailWord_271222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271241 : List Nat := [1, 2, 1, 1, 5, 2, 11]
def baseStart_271241 : Nat := 118140960795 + 271241 * 2 ^ 59
def prefixEnd_271241 : Nat := 4983230072969 + 3 ^ 40 * 271241 * 2
def baseEnd_271241 : Nat := 1719469212423191383211

theorem tailTrace_271241 : CollatzResearch.WordTrace tailWord_271241 prefixEnd_271241 1719469212423191383211 := by
  unfold tailWord_271241
  simp only [CollatzResearch.WordTrace]
  refine ⟨9892972010347656119845577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6595314673565104079897051 9892972010347656119845577)
  ·
    refine ⟨7419729007760742089884183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9892972010347656119845577 7419729007760742089884183)
    ·
      refine ⟨11129593511641113134826275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7419729007760742089884183 11129593511641113134826275)
      ·
        refine ⟨16694390267461669702239413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11129593511641113134826275 16694390267461669702239413)
        ·
          refine ⟨1565099087574531534584945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16694390267461669702239413 1565099087574531534584945)
          ·
            refine ⟨1173824315680898650938709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1565099087574531534584945 1173824315680898650938709)
            ·
              refine ⟨1719469212423191383211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 1173824315680898650938709 1719469212423191383211)
              ·
                rfl

theorem cell23_271241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 11].length) (baseStart_271241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271241 prefixEnd_271241 := by exact prefixLift 271241
  have htrace : WordTrace (prefixWord ++ tailWord_271241) baseStart_271241 baseEnd_271241 := by
    simpa [prefixWord, tailWord_271241, baseEnd_271241] using wordTrace_append hprefix tailTrace_271241
  have hstable : (prefixWord ++ tailWord_271241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271241).length < 2 ^ (prefixWord ++ tailWord_271241).sum := by decide
  have hdescent : baseEnd_271241 < baseStart_271241 := by decide
  rcases family_descends (prefixWord ++ tailWord_271241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271285 : List Nat := [1, 3, 3, 2, 1, 1, 3, 2, 1, 3, 3]
def baseStart_271285 : Nat := 118140960795 + 271285 * 2 ^ 59
def prefixEnd_271285 : Nat := 4983230072969 + 3 ^ 40 * 271285 * 2
def baseEnd_271285 : Nat := 139299599355076329889889

theorem tailTrace_271285 : CollatzResearch.WordTrace tailWord_271285 prefixEnd_271285 139299599355076329889889 := by
  unfold tailWord_271285
  simp only [CollatzResearch.WordTrace]
  refine ⟨9894576822188251634447309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6596384548125501089631539 9894576822188251634447309)
  ·
    refine ⟨3710466308320594362917741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9894576822188251634447309 3710466308320594362917741)
    ·
      refine ⟨1391424865620222886094153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3710466308320594362917741 1391424865620222886094153)
      ·
        refine ⟨1043568649215167164570615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1391424865620222886094153 1043568649215167164570615)
        ·
          refine ⟨1565352973822750746855923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1043568649215167164570615 1565352973822750746855923)
          ·
            refine ⟨2348029460734126120283885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1565352973822750746855923 2348029460734126120283885)
            ·
              refine ⟨880511047775297295106457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2348029460734126120283885 880511047775297295106457)
              ·
                refine ⟨660383285831472971329843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 880511047775297295106457 660383285831472971329843)
                ·
                  refine ⟨990574928747209456994765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 660383285831472971329843 990574928747209456994765)
                  ·
                    refine ⟨371465598280203546373037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 990574928747209456994765 371465598280203546373037)
                    ·
                      refine ⟨139299599355076329889889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 371465598280203546373037 139299599355076329889889)
                      ·
                        rfl

theorem cell23_271285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_271285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271285 prefixEnd_271285 := by exact prefixLift 271285
  have htrace : WordTrace (prefixWord ++ tailWord_271285) baseStart_271285 baseEnd_271285 := by
    simpa [prefixWord, tailWord_271285, baseEnd_271285] using wordTrace_append hprefix tailTrace_271285
  have hstable : (prefixWord ++ tailWord_271285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271285).length < 2 ^ (prefixWord ++ tailWord_271285).sum := by decide
  have hdescent : baseEnd_271285 < baseStart_271285 := by decide
  rcases family_descends (prefixWord ++ tailWord_271285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271308 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 1, 5, 4]
def baseStart_271308 : Nat := 118140960795 + 271308 * 2 ^ 59
def prefixEnd_271308 : Nat := 4983230072969 + 3 ^ 40 * 271308 * 2
def baseEnd_271308 : Nat := 139311409410129739902283

theorem tailTrace_271308 : CollatzResearch.WordTrace tailWord_271308 prefixEnd_271308 139311409410129739902283 := by
  unfold tailWord_271308
  simp only [CollatzResearch.WordTrace]
  refine ⟨4947707850552463281267289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6596943800736617708356385 4947707850552463281267289)
  ·
    refine ⟨3710780887914347460950467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4947707850552463281267289 3710780887914347460950467)
    ·
      refine ⟨5566171331871521191425701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3710780887914347460950467 5566171331871521191425701)
      ·
        refine ⟨1043657124725910223392319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5566171331871521191425701 1043657124725910223392319)
        ·
          refine ⟨1565485687088865335088479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1043657124725910223392319 1565485687088865335088479)
          ·
            refine ⟨2348228530633298002632719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1565485687088865335088479 2348228530633298002632719)
            ·
              refine ⟨3522342795949947003949079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2348228530633298002632719 3522342795949947003949079)
              ·
                refine ⟨5283514193924920505923619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3522342795949947003949079 5283514193924920505923619)
                ·
                  refine ⟨7925271290887380758885429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5283514193924920505923619 7925271290887380758885429)
                  ·
                    refine ⟨742994183520691946145509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7925271290887380758885429 742994183520691946145509)
                    ·
                      refine ⟨139311409410129739902283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 742994183520691946145509 139311409410129739902283)
                      ·
                        rfl

theorem cell23_271308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_271308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271308 prefixEnd_271308 := by exact prefixLift 271308
  have htrace : WordTrace (prefixWord ++ tailWord_271308) baseStart_271308 baseEnd_271308 := by
    simpa [prefixWord, tailWord_271308, baseEnd_271308] using wordTrace_append hprefix tailTrace_271308
  have hstable : (prefixWord ++ tailWord_271308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271308).length < 2 ^ (prefixWord ++ tailWord_271308).sum := by decide
  have hdescent : baseEnd_271308 < baseStart_271308 := by decide
  rcases family_descends (prefixWord ++ tailWord_271308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271346 : List Nat := [3, 2, 1, 5, 1, 1, 1, 3, 1, 3, 2]
def baseStart_271346 : Nat := 118140960795 + 271346 * 2 ^ 59
def prefixEnd_271346 : Nat := 4983230072969 + 3 ^ 40 * 271346 * 2
def baseEnd_271346 : Nat := 139330921675000591227109

theorem tailTrace_271346 : CollatzResearch.WordTrace tailWord_271346 prefixEnd_271346 139330921675000591227109 := by
  unfold tailWord_271346
  simp only [CollatzResearch.WordTrace]
  refine ⟨2474200418741814763104473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6597867783311506034945261 2474200418741814763104473)
  ·
    refine ⟨1855650314056361072328355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2474200418741814763104473 1855650314056361072328355)
    ·
      refine ⟨2783475471084541608492533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1855650314056361072328355 2783475471084541608492533)
      ·
        refine ⟨260950825414175775796175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2783475471084541608492533 260950825414175775796175)
        ·
          refine ⟨391426238121263663694263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260950825414175775796175 391426238121263663694263)
          ·
            refine ⟨587139357181895495541395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391426238121263663694263 587139357181895495541395)
            ·
              refine ⟨880709035772843243312093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 587139357181895495541395 880709035772843243312093)
              ·
                refine ⟨330265888414816216242035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 880709035772843243312093 330265888414816216242035)
                ·
                  refine ⟨495398832622224324363053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 330265888414816216242035 495398832622224324363053)
                  ·
                    refine ⟨185774562233334121636145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 495398832622224324363053 185774562233334121636145)
                    ·
                      refine ⟨139330921675000591227109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 185774562233334121636145 139330921675000591227109)
                      ·
                        rfl

theorem cell23_271346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_271346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271346 prefixEnd_271346 := by exact prefixLift 271346
  have htrace : WordTrace (prefixWord ++ tailWord_271346) baseStart_271346 baseEnd_271346 := by
    simpa [prefixWord, tailWord_271346, baseEnd_271346] using wordTrace_append hprefix tailTrace_271346
  have hstable : (prefixWord ++ tailWord_271346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271346).length < 2 ^ (prefixWord ++ tailWord_271346).sum := by decide
  have hdescent : baseEnd_271346 < baseStart_271346 := by decide
  rcases family_descends (prefixWord ++ tailWord_271346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271365 : List Nat := [1, 3, 1, 1, 2, 3, 1, 6, 5]
def baseStart_271365 : Nat := 118140960795 + 271365 * 2 ^ 59
def prefixEnd_271365 : Nat := 4983230072969 + 3 ^ 40 * 271365 * 2
def baseEnd_271365 : Nat := 15482297534159557432169

theorem tailTrace_271365 : CollatzResearch.WordTrace tailWord_271365 prefixEnd_271365 15482297534159557432169 := by
  unfold tailWord_271365
  simp only [CollatzResearch.WordTrace]
  refine ⟨9897494661898425297359549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6598329774598950198239699 9897494661898425297359549)
  ·
    refine ⟨3711560498211909486509831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9897494661898425297359549 3711560498211909486509831)
    ·
      refine ⟨5567340747317864229764747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3711560498211909486509831 5567340747317864229764747)
      ·
        refine ⟨8351011120976796344647121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5567340747317864229764747 8351011120976796344647121)
        ·
          refine ⟨6263258340732597258485341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8351011120976796344647121 6263258340732597258485341)
          ·
            refine ⟨2348721877774723971932003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6263258340732597258485341 2348721877774723971932003)
            ·
              refine ⟨3523082816662085957898005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2348721877774723971932003 3523082816662085957898005)
              ·
                refine ⟨165144507031035279276469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3523082816662085957898005 165144507031035279276469)
                ·
                  refine ⟨15482297534159557432169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 165144507031035279276469 15482297534159557432169)
                  ·
                    rfl

theorem cell23_271365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 6, 5].length) (baseStart_271365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271365 prefixEnd_271365 := by exact prefixLift 271365
  have htrace : WordTrace (prefixWord ++ tailWord_271365) baseStart_271365 baseEnd_271365 := by
    simpa [prefixWord, tailWord_271365, baseEnd_271365] using wordTrace_append hprefix tailTrace_271365
  have hstable : (prefixWord ++ tailWord_271365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271365).length < 2 ^ (prefixWord ++ tailWord_271365).sum := by decide
  have hdescent : baseEnd_271365 < baseStart_271365 := by decide
  rcases family_descends (prefixWord ++ tailWord_271365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271385 : List Nat := [1, 2, 1, 2, 1, 1, 4, 2, 2, 5, 2]
def baseStart_271385 : Nat := 118140960795 + 271385 * 2 ^ 59
def prefixEnd_271385 : Nat := 4983230072969 + 3 ^ 40 * 271385 * 2
def baseEnd_271385 : Nat := 139350947420525938639429

theorem tailTrace_271385 : CollatzResearch.WordTrace tailWord_271385 prefixEnd_271385 139350947420525938639429 := by
  unfold tailWord_271385
  simp only [CollatzResearch.WordTrace]
  refine ⟨9898224121825968713087609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6598816081217312475391739 9898224121825968713087609)
  ·
    refine ⟨7423668091369476534815707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9898224121825968713087609 7423668091369476534815707)
    ·
      refine ⟨11135502137054214802223561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7423668091369476534815707 11135502137054214802223561)
      ·
        refine ⟨8351626602790661101667671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11135502137054214802223561 8351626602790661101667671)
        ·
          refine ⟨12527439904185991652501507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8351626602790661101667671 12527439904185991652501507)
          ·
            refine ⟨18791159856278987478752261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12527439904185991652501507 18791159856278987478752261)
            ·
              refine ⟨3523342473052310152266049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18791159856278987478752261 3523342473052310152266049)
              ·
                refine ⟨2642506854789232614199537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3523342473052310152266049 2642506854789232614199537)
                ·
                  refine ⟨1981880141091924460649653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2642506854789232614199537 1981880141091924460649653)
                  ·
                    refine ⟨185801263227367918185905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1981880141091924460649653 185801263227367918185905)
                    ·
                      refine ⟨139350947420525938639429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 185801263227367918185905 139350947420525938639429)
                      ·
                        rfl

theorem cell23_271385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 5, 2].length) (baseStart_271385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271385 prefixEnd_271385 := by exact prefixLift 271385
  have htrace : WordTrace (prefixWord ++ tailWord_271385) baseStart_271385 baseEnd_271385 := by
    simpa [prefixWord, tailWord_271385, baseEnd_271385] using wordTrace_append hprefix tailTrace_271385
  have hstable : (prefixWord ++ tailWord_271385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271385).length < 2 ^ (prefixWord ++ tailWord_271385).sum := by decide
  have hdescent : baseEnd_271385 < baseStart_271385 := by decide
  rcases family_descends (prefixWord ++ tailWord_271385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271399 : List Nat := [1, 1, 7, 1, 1, 1, 3, 3, 5]
def baseStart_271399 : Nat := 118140960795 + 271399 * 2 ^ 59
def prefixEnd_271399 : Nat := 4983230072969 + 3 ^ 40 * 271399 * 2
def baseEnd_271399 : Nat := 15484237349965431540485

theorem tailTrace_271399 : CollatzResearch.WordTrace tailWord_271399 prefixEnd_271399 15484237349965431540485 := by
  unfold tailWord_271399
  simp only [CollatzResearch.WordTrace]
  refine ⟨9898734743775249104097251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6599156495850166069398167 9898734743775249104097251)
  ·
    refine ⟨14848102115662873656145877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9898734743775249104097251 14848102115662873656145877)
    ·
      refine ⟨348002393335848601315919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 14848102115662873656145877 348002393335848601315919)
      ·
        refine ⟨522003590003772901973879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348002393335848601315919 522003590003772901973879)
        ·
          refine ⟨783005385005659352960819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 522003590003772901973879 783005385005659352960819)
          ·
            refine ⟨1174508077508489029441229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 783005385005659352960819 1174508077508489029441229)
            ·
              refine ⟨440440529065683386040461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1174508077508489029441229 440440529065683386040461)
              ·
                refine ⟨165165198399631269765173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 440440529065683386040461 165165198399631269765173)
                ·
                  refine ⟨15484237349965431540485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 165165198399631269765173 15484237349965431540485)
                  ·
                    rfl

theorem cell23_271399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 3, 5].length) (baseStart_271399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271399 prefixEnd_271399 := by exact prefixLift 271399
  have htrace : WordTrace (prefixWord ++ tailWord_271399) baseStart_271399 baseEnd_271399 := by
    simpa [prefixWord, tailWord_271399, baseEnd_271399] using wordTrace_append hprefix tailTrace_271399
  have hstable : (prefixWord ++ tailWord_271399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271399).length < 2 ^ (prefixWord ++ tailWord_271399).sum := by decide
  have hdescent : baseEnd_271399 < baseStart_271399 := by decide
  rcases family_descends (prefixWord ++ tailWord_271399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271412 : List Nat := [2, 5, 1, 2, 1, 1, 1, 1, 4, 5]
def baseStart_271412 : Nat := 118140960795 + 271412 * 2 ^ 59
def prefixEnd_271412 : Nat := 4983230072969 + 3 ^ 40 * 271412 * 2
def baseEnd_271412 : Nat := 46454937132732444333935

theorem tailTrace_271412 : CollatzResearch.WordTrace tailWord_271412 prefixEnd_271412 46454937132732444333935 := by
  unfold tailWord_271412
  simp only [CollatzResearch.WordTrace]
  refine ⟨4949604446364076162160245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6599472595152101549546993 4949604446364076162160245)
  ·
    refine ⟨464025416846632140202523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4949604446364076162160245 464025416846632140202523)
    ·
      refine ⟨696038125269948210303785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 464025416846632140202523 696038125269948210303785)
      ·
        refine ⟨522028593952461157727839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 696038125269948210303785 522028593952461157727839)
        ·
          refine ⟨783042890928691736591759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 522028593952461157727839 783042890928691736591759)
          ·
            refine ⟨1174564336393037604887639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 783042890928691736591759 1174564336393037604887639)
            ·
              refine ⟨1761846504589556407331459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1174564336393037604887639 1761846504589556407331459)
              ·
                refine ⟨2642769756884334610997189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1761846504589556407331459 2642769756884334610997189)
                ·
                  refine ⟨495519329415812739561973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2642769756884334610997189 495519329415812739561973)
                  ·
                    refine ⟨46454937132732444333935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 495519329415812739561973 46454937132732444333935)
                    ·
                      rfl

theorem cell23_271412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_271412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271412 prefixEnd_271412 := by exact prefixLift 271412
  have htrace : WordTrace (prefixWord ++ tailWord_271412) baseStart_271412 baseEnd_271412 := by
    simpa [prefixWord, tailWord_271412, baseEnd_271412] using wordTrace_append hprefix tailTrace_271412
  have hstable : (prefixWord ++ tailWord_271412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271412).length < 2 ^ (prefixWord ++ tailWord_271412).sum := by decide
  have hdescent : baseEnd_271412 < baseStart_271412 := by decide
  rcases family_descends (prefixWord ++ tailWord_271412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271422 : List Nat := [4, 2, 1, 3, 1, 2, 1, 1, 1, 2, 5]
def baseStart_271422 : Nat := 118140960795 + 271422 * 2 ^ 59
def prefixEnd_271422 : Nat := 4983230072969 + 3 ^ 40 * 271422 * 2
def baseEnd_271422 : Nat := 139369946204742293876759

theorem tailTrace_271422 : CollatzResearch.WordTrace tailWord_271422 prefixEnd_271422 139369946204742293876759 := by
  unfold tailWord_271422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1237446702836490504023065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6599715748461282688123013 1237446702836490504023065)
  ·
    refine ⟨928085027127367878017299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1237446702836490504023065 928085027127367878017299)
    ·
      refine ⟨1392127540691051817025949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 928085027127367878017299 1392127540691051817025949)
      ·
        refine ⟨522047827759144431384731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1392127540691051817025949 522047827759144431384731)
        ·
          refine ⟨783071741638716647077097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 522047827759144431384731 783071741638716647077097)
          ·
            refine ⟨587303806229037485307823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 783071741638716647077097 587303806229037485307823)
            ·
              refine ⟨880955709343556227961735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 587303806229037485307823 880955709343556227961735)
              ·
                refine ⟨1321433564015334341942603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 880955709343556227961735 1321433564015334341942603)
                ·
                  refine ⟨1982150346023001512913905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1321433564015334341942603 1982150346023001512913905)
                  ·
                    refine ⟨1486612759517251134685429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1982150346023001512913905 1486612759517251134685429)
                    ·
                      refine ⟨139369946204742293876759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1486612759517251134685429 139369946204742293876759)
                      ·
                        rfl

theorem cell23_271422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_271422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271422 prefixEnd_271422 := by exact prefixLift 271422
  have htrace : WordTrace (prefixWord ++ tailWord_271422) baseStart_271422 baseEnd_271422 := by
    simpa [prefixWord, tailWord_271422, baseEnd_271422] using wordTrace_append hprefix tailTrace_271422
  have hstable : (prefixWord ++ tailWord_271422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271422).length < 2 ^ (prefixWord ++ tailWord_271422).sum := by decide
  have hdescent : baseEnd_271422 < baseStart_271422 := by decide
  rcases family_descends (prefixWord ++ tailWord_271422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271446 : List Nat := [5, 2, 2, 1, 2, 1, 2, 1, 2, 5]
def baseStart_271446 : Nat := 118140960795 + 271446 * 2 ^ 59
def prefixEnd_271446 : Nat := 4983230072969 + 3 ^ 40 * 271446 * 2
def baseEnd_271446 : Nat := 46460756580150066658883

theorem tailTrace_271446 : CollatzResearch.WordTrace tailWord_271446 prefixEnd_271446 46460756580150066658883 := by
  unfold tailWord_271446
  simp only [CollatzResearch.WordTrace]
  refine ⟨618778060912811008191137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6600299316403317420705461 618778060912811008191137)
  ·
    refine ⟨464083545684608256143353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 618778060912811008191137 464083545684608256143353)
    ·
      refine ⟨348062659263456192107515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 464083545684608256143353 348062659263456192107515)
      ·
        refine ⟨522093988895184288161273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348062659263456192107515 522093988895184288161273)
        ·
          refine ⟨391570491671388216120955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 522093988895184288161273 391570491671388216120955)
          ·
            refine ⟨587355737507082324181433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391570491671388216120955 587355737507082324181433)
            ·
              refine ⟨440516803130311743136075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 587355737507082324181433 440516803130311743136075)
              ·
                refine ⟨660775204695467614704113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 440516803130311743136075 660775204695467614704113)
                ·
                  refine ⟨495581403521600711028085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 660775204695467614704113 495581403521600711028085)
                  ·
                    refine ⟨46460756580150066658883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 495581403521600711028085 46460756580150066658883)
                    ·
                      rfl

theorem cell23_271446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_271446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271446 prefixEnd_271446 := by exact prefixLift 271446
  have htrace : WordTrace (prefixWord ++ tailWord_271446) baseStart_271446 baseEnd_271446 := by
    simpa [prefixWord, tailWord_271446, baseEnd_271446] using wordTrace_append hprefix tailTrace_271446
  have hstable : (prefixWord ++ tailWord_271446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271446).length < 2 ^ (prefixWord ++ tailWord_271446).sum := by decide
  have hdescent : baseEnd_271446 < baseStart_271446 := by decide
  rcases family_descends (prefixWord ++ tailWord_271446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271485 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 5, 5]
def baseStart_271485 : Nat := 118140960795 + 271485 * 2 ^ 59
def prefixEnd_271485 : Nat := 4983230072969 + 3 ^ 40 * 271485 * 2
def baseEnd_271485 : Nat := 46467431828658515796323

theorem tailTrace_271485 : CollatzResearch.WordTrace tailWord_271485 prefixEnd_271485 46467431828658515796323 := by
  unfold tailWord_271485
  simp only [CollatzResearch.WordTrace]
  refine ⟨9901871421463685791727909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6601247614309123861151939 9901871421463685791727909)
  ·
    refine ⟨1856600891524441085948983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9901871421463685791727909 1856600891524441085948983)
    ·
      refine ⟨2784901337286661628923475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1856600891524441085948983 2784901337286661628923475)
      ·
        refine ⟨4177352005929992443385213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2784901337286661628923475 4177352005929992443385213)
        ·
          refine ⟨1566507002223747166269455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4177352005929992443385213 1566507002223747166269455)
          ·
            refine ⟨2349760503335620749404183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1566507002223747166269455 2349760503335620749404183)
            ·
              refine ⟨3524640755003431124106275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2349760503335620749404183 3524640755003431124106275)
              ·
                refine ⟨5286961132505146686159413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3524640755003431124106275 5286961132505146686159413)
                ·
                  refine ⟨495652606172357501827445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5286961132505146686159413 495652606172357501827445)
                  ·
                    refine ⟨46467431828658515796323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 495652606172357501827445 46467431828658515796323)
                    ·
                      rfl

theorem cell23_271485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_271485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271485 prefixEnd_271485 := by exact prefixLift 271485
  have htrace : WordTrace (prefixWord ++ tailWord_271485) baseStart_271485 baseEnd_271485 := by
    simpa [prefixWord, tailWord_271485, baseEnd_271485] using wordTrace_append hprefix tailTrace_271485
  have hstable : (prefixWord ++ tailWord_271485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271485).length < 2 ^ (prefixWord ++ tailWord_271485).sum := by decide
  have hdescent : baseEnd_271485 < baseStart_271485 := by decide
  rcases family_descends (prefixWord ++ tailWord_271485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271502 : List Nat := [4, 1, 1, 3, 2, 1, 2, 1, 3, 5]
def baseStart_271502 : Nat := 118140960795 + 271502 * 2 ^ 59
def prefixEnd_271502 : Nat := 4983230072969 + 3 ^ 40 * 271502 * 2
def baseEnd_271502 : Nat := 46470341552367326958797

theorem tailTrace_271502 : CollatzResearch.WordTrace tailWord_271502 prefixEnd_271502 46470341552367326958797 := by
  unfold tailWord_271502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1237811432800262211887095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6601660974934731796731173 1237811432800262211887095)
  ·
    refine ⟨1856717149200393317830643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1237811432800262211887095 1856717149200393317830643)
    ·
      refine ⟨2785075723800589976745965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1856717149200393317830643 2785075723800589976745965)
      ·
        refine ⟨1044403396425221241279737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2785075723800589976745965 1044403396425221241279737)
        ·
          refine ⟨783302547318915930959803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1044403396425221241279737 783302547318915930959803)
          ·
            refine ⟨1174953820978373896439705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 783302547318915930959803 1174953820978373896439705)
            ·
              refine ⟨881215365733780422329779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1174953820978373896439705 881215365733780422329779)
              ·
                refine ⟨1321823048600670633494669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 881215365733780422329779 1321823048600670633494669)
                ·
                  refine ⟨495683643225251487560501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1321823048600670633494669 495683643225251487560501)
                  ·
                    refine ⟨46470341552367326958797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 495683643225251487560501 46470341552367326958797)
                    ·
                      rfl

theorem cell23_271502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_271502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271502 prefixEnd_271502 := by exact prefixLift 271502
  have htrace : WordTrace (prefixWord ++ tailWord_271502) baseStart_271502 baseEnd_271502 := by
    simpa [prefixWord, tailWord_271502, baseEnd_271502] using wordTrace_append hprefix tailTrace_271502
  have hstable : (prefixWord ++ tailWord_271502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271502).length < 2 ^ (prefixWord ++ tailWord_271502).sum := by decide
  have hdescent : baseEnd_271502 < baseStart_271502 := by decide
  rcases family_descends (prefixWord ++ tailWord_271502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271516 : List Nat := [2, 2, 3, 2, 1, 2, 1, 5, 1, 1, 3]
def baseStart_271516 : Nat := 118140960795 + 271516 * 2 ^ 59
def prefixEnd_271516 : Nat := 4983230072969 + 3 ^ 40 * 271516 * 2
def baseEnd_271516 : Nat := 139418213386264926101327

theorem tailTrace_271516 : CollatzResearch.WordTrace tailWord_271516 prefixEnd_271516 139418213386264926101327 := by
  unfold tailWord_271516
  simp only [CollatzResearch.WordTrace]
  refine ⟨4951501042175689043053201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6602001389567585390737601 4951501042175689043053201)
  ·
    refine ⟨3713625781631766782289901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4951501042175689043053201 3713625781631766782289901)
    ·
      refine ⟨1392609668111912543358713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3713625781631766782289901 1392609668111912543358713)
      ·
        refine ⟨1044457251083934407519035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1392609668111912543358713 1044457251083934407519035)
        ·
          refine ⟨1566685876625901611278553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1044457251083934407519035 1566685876625901611278553)
          ·
            refine ⟨1175014407469426208458915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1566685876625901611278553 1175014407469426208458915)
            ·
              refine ⟨1762521611204139312688373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1175014407469426208458915 1762521611204139312688373)
              ·
                refine ⟨165236401050388060564535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1762521611204139312688373 165236401050388060564535)
                ·
                  refine ⟨247854601575582090846803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 165236401050388060564535 247854601575582090846803)
                  ·
                    refine ⟨371781902363373136270205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 247854601575582090846803 371781902363373136270205)
                    ·
                      refine ⟨139418213386264926101327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 371781902363373136270205 139418213386264926101327)
                      ·
                        rfl

theorem cell23_271516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_271516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271516 prefixEnd_271516 := by exact prefixLift 271516
  have htrace : WordTrace (prefixWord ++ tailWord_271516) baseStart_271516 baseEnd_271516 := by
    simpa [prefixWord, tailWord_271516, baseEnd_271516] using wordTrace_append hprefix tailTrace_271516
  have hstable : (prefixWord ++ tailWord_271516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271516).length < 2 ^ (prefixWord ++ tailWord_271516).sum := by decide
  have hdescent : baseEnd_271516 < baseStart_271516 := by decide
  rcases family_descends (prefixWord ++ tailWord_271516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271519 : List Nat := [1, 1, 2, 6, 2, 1, 1, 3, 1, 5]
def baseStart_271519 : Nat := 118140960795 + 271519 * 2 ^ 59
def prefixEnd_271519 : Nat := 4983230072969 + 3 ^ 40 * 271519 * 2
def baseEnd_271519 : Nat := 46473251276076138121271

theorem tailTrace_271519 : CollatzResearch.WordTrace tailWord_271519 prefixEnd_271519 46473251276076138121271 := by
  unfold tailWord_271519
  simp only [CollatzResearch.WordTrace]
  refine ⟨9903111503340509598465611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6602074335560339732310407 9903111503340509598465611)
  ·
    refine ⟨14854667255010764397698417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9903111503340509598465611 14854667255010764397698417)
    ·
      refine ⟨11141000441258073298273813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14854667255010764397698417 11141000441258073298273813)
      ·
        refine ⟨522234395683972185856585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11141000441258073298273813 522234395683972185856585)
        ·
          refine ⟨391675796762979139392439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 522234395683972185856585 391675796762979139392439)
          ·
            refine ⟨587513695144468709088659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391675796762979139392439 587513695144468709088659)
            ·
              refine ⟨881270542716703063632989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 587513695144468709088659 881270542716703063632989)
              ·
                refine ⟨330476453518763648862371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 881270542716703063632989 330476453518763648862371)
                ·
                  refine ⟨495714680278145473293557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 330476453518763648862371 495714680278145473293557)
                  ·
                    refine ⟨46473251276076138121271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 495714680278145473293557 46473251276076138121271)
                    ·
                      rfl

theorem cell23_271519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 5].length) (baseStart_271519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271519 prefixEnd_271519 := by exact prefixLift 271519
  have htrace : WordTrace (prefixWord ++ tailWord_271519) baseStart_271519 baseEnd_271519 := by
    simpa [prefixWord, tailWord_271519, baseEnd_271519] using wordTrace_append hprefix tailTrace_271519
  have hstable : (prefixWord ++ tailWord_271519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271519).length < 2 ^ (prefixWord ++ tailWord_271519).sum := by decide
  have hdescent : baseEnd_271519 < baseStart_271519 := by decide
  rcases family_descends (prefixWord ++ tailWord_271519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271532 : List Nat := [2, 2, 1, 1, 1, 1, 1, 8, 2, 4]
def baseStart_271532 : Nat := 118140960795 + 271532 * 2 ^ 59
def prefixEnd_271532 : Nat := 4983230072969 + 3 ^ 40 * 271532 * 2
def baseEnd_271532 : Nat := 46475476358912287833751

theorem tailTrace_271532 : CollatzResearch.WordTrace tailWord_271532 prefixEnd_271532 46475476358912287833751 := by
  unfold tailWord_271532
  simp only [CollatzResearch.WordTrace]
  refine ⟨4951792826146706409344425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6602390434862275212459233 4951792826146706409344425)
  ·
    refine ⟨3713844619610029807008319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4951792826146706409344425 3713844619610029807008319)
    ·
      refine ⟨5570766929415044710512479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3713844619610029807008319 5570766929415044710512479)
      ·
        refine ⟨8356150394122567065768719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5570766929415044710512479 8356150394122567065768719)
        ·
          refine ⟨12534225591183850598653079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8356150394122567065768719 12534225591183850598653079)
          ·
            refine ⟨18801338386775775897979619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12534225591183850598653079 18801338386775775897979619)
            ·
              refine ⟨28202007580163663846969429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18801338386775775897979619 28202007580163663846969429)
              ·
                refine ⟨330492276330042935706673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 28202007580163663846969429 330492276330042935706673)
                ·
                  refine ⟨247869207247532201780005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 330492276330042935706673 247869207247532201780005)
                  ·
                    refine ⟨46475476358912287833751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 247869207247532201780005 46475476358912287833751)
                    ·
                      rfl

theorem cell23_271532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 4].length) (baseStart_271532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271532 prefixEnd_271532 := by exact prefixLift 271532
  have htrace : WordTrace (prefixWord ++ tailWord_271532) baseStart_271532 baseEnd_271532 := by
    simpa [prefixWord, tailWord_271532, baseEnd_271532] using wordTrace_append hprefix tailTrace_271532
  have hstable : (prefixWord ++ tailWord_271532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271532).length < 2 ^ (prefixWord ++ tailWord_271532).sum := by decide
  have hdescent : baseEnd_271532 < baseStart_271532 := by decide
  rcases family_descends (prefixWord ++ tailWord_271532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271535 : List Nat := [1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 4]
def baseStart_271535 : Nat := 118140960795 + 271535 * 2 ^ 59
def prefixEnd_271535 : Nat := 4983230072969 + 3 ^ 40 * 271535 * 2
def baseEnd_271535 : Nat := 139427969518700351763739

theorem tailTrace_271535 : CollatzResearch.WordTrace tailWord_271535 prefixEnd_271535 139427969518700351763739 := by
  unfold tailWord_271535
  simp only [CollatzResearch.WordTrace]
  refine ⟨9903695071282544331048059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6602463380855029554032039 9903695071282544331048059)
  ·
    refine ⟨14855542606923816496572089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9903695071282544331048059 14855542606923816496572089)
    ·
      refine ⟨11141656955192862372429067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14855542606923816496572089 11141656955192862372429067)
      ·
        refine ⟨16712485432789293558643601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11141656955192862372429067 16712485432789293558643601)
        ·
          refine ⟨12534364074591970168982701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16712485432789293558643601 12534364074591970168982701)
          ·
            refine ⟨4700386527971988813368513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12534364074591970168982701 4700386527971988813368513)
            ·
              refine ⟨3525289895978991610026385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4700386527971988813368513 3525289895978991610026385)
              ·
                refine ⟨2643967421984243707519789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3525289895978991610026385 2643967421984243707519789)
                ·
                  refine ⟨991487783244091390319921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2643967421984243707519789 991487783244091390319921)
                  ·
                    refine ⟨743615837433068542739941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 991487783244091390319921 743615837433068542739941)
                    ·
                      refine ⟨139427969518700351763739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 743615837433068542739941 139427969518700351763739)
                      ·
                        rfl

theorem cell23_271535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 4].length) (baseStart_271535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271535 prefixEnd_271535 := by exact prefixLift 271535
  have htrace : WordTrace (prefixWord ++ tailWord_271535) baseStart_271535 baseEnd_271535 := by
    simpa [prefixWord, tailWord_271535, baseEnd_271535] using wordTrace_append hprefix tailTrace_271535
  have hstable : (prefixWord ++ tailWord_271535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271535).length < 2 ^ (prefixWord ++ tailWord_271535).sum := by decide
  have hdescent : baseEnd_271535 < baseStart_271535 := by decide
  rcases family_descends (prefixWord ++ tailWord_271535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271539 : List Nat := [1, 1, 1, 2, 3, 2, 3, 3, 3, 2, 2]
def baseStart_271539 : Nat := 118140960795 + 271539 * 2 ^ 59
def prefixEnd_271539 : Nat := 4983230072969 + 3 ^ 40 * 271539 * 2
def baseEnd_271539 : Nat := 139430023441318336113721

theorem tailTrace_271539 : CollatzResearch.WordTrace tailWord_271539 prefixEnd_271539 139430023441318336113721 := by
  unfold tailWord_271539
  simp only [CollatzResearch.WordTrace]
  refine ⟨9903840963268053014193671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6602560642178702009462447 9903840963268053014193671)
  ·
    refine ⟨14855761444902079521290507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9903840963268053014193671 14855761444902079521290507)
    ·
      refine ⟨22283642167353119281935761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14855761444902079521290507 22283642167353119281935761)
      ·
        refine ⟨16712731625514839461451821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22283642167353119281935761 16712731625514839461451821)
        ·
          refine ⟨6267274359568064798044433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16712731625514839461451821 6267274359568064798044433)
          ·
            refine ⟨4700455769676048598533325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6267274359568064798044433 4700455769676048598533325)
            ·
              refine ⟨1762670913628518224449997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4700455769676048598533325 1762670913628518224449997)
              ·
                refine ⟨661001592610694334168749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1762670913628518224449997 661001592610694334168749)
                ·
                  refine ⟨247875597229010375313281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 661001592610694334168749 247875597229010375313281)
                  ·
                    refine ⟨185906697921757781484961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 247875597229010375313281 185906697921757781484961)
                    ·
                      refine ⟨139430023441318336113721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 185906697921757781484961 139430023441318336113721)
                      ·
                        rfl

theorem cell23_271539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 3, 2, 2].length) (baseStart_271539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271539 prefixEnd_271539 := by exact prefixLift 271539
  have htrace : WordTrace (prefixWord ++ tailWord_271539) baseStart_271539 baseEnd_271539 := by
    simpa [prefixWord, tailWord_271539, baseEnd_271539] using wordTrace_append hprefix tailTrace_271539
  have hstable : (prefixWord ++ tailWord_271539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271539).length < 2 ^ (prefixWord ++ tailWord_271539).sum := by decide
  have hdescent : baseEnd_271539 < baseStart_271539 := by decide
  rcases family_descends (prefixWord ++ tailWord_271539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271552 : List Nat := [2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 6]
def baseStart_271552 : Nat := 118140960795 + 271552 * 2 ^ 59
def prefixEnd_271552 : Nat := 4983230072969 + 3 ^ 40 * 271552 * 2
def baseEnd_271552 : Nat := 139436698689826785251161

theorem tailTrace_271552 : CollatzResearch.WordTrace tailWord_271552 prefixEnd_271552 139436698689826785251161 := by
  unfold tailWord_271552
  simp only [CollatzResearch.WordTrace]
  refine ⟨4952157556110478117208455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6602876741480637489611273 4952157556110478117208455)
  ·
    refine ⟨7428236334165717175812683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4952157556110478117208455 7428236334165717175812683)
    ·
      refine ⟨11142354501248575763719025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7428236334165717175812683 11142354501248575763719025)
      ·
        refine ⟨8356765875936431822789269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11142354501248575763719025 8356765875936431822789269)
        ·
          refine ⟨391723400434520241693247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8356765875936431822789269 391723400434520241693247)
          ·
            refine ⟨587585100651780362539871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391723400434520241693247 587585100651780362539871)
            ·
              refine ⟨881377650977670543809807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 587585100651780362539871 881377650977670543809807)
              ·
                refine ⟨1322066476466505815714711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 881377650977670543809807 1322066476466505815714711)
                ·
                  refine ⟨1983099714699758723572067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1322066476466505815714711 1983099714699758723572067)
                  ·
                    refine ⟨2974649572049638085358101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1983099714699758723572067 2974649572049638085358101)
                    ·
                      refine ⟨139436698689826785251161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2974649572049638085358101 139436698689826785251161)
                      ·
                        rfl

theorem cell23_271552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 6].length) (baseStart_271552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271552 prefixEnd_271552 := by exact prefixLift 271552
  have htrace : WordTrace (prefixWord ++ tailWord_271552) baseStart_271552 baseEnd_271552 := by
    simpa [prefixWord, tailWord_271552, baseEnd_271552] using wordTrace_append hprefix tailTrace_271552
  have hstable : (prefixWord ++ tailWord_271552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271552).length < 2 ^ (prefixWord ++ tailWord_271552).sum := by decide
  have hdescent : baseEnd_271552 < baseStart_271552 := by decide
  rcases family_descends (prefixWord ++ tailWord_271552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271556 : List Nat := [2, 3, 3, 1, 3, 1, 2, 2, 1, 1, 4]
def baseStart_271556 : Nat := 118140960795 + 271556 * 2 ^ 59
def prefixEnd_271556 : Nat := 4983230072969 + 3 ^ 40 * 271556 * 2
def baseEnd_271556 : Nat := 139438752612444769601143

theorem tailTrace_271556 : CollatzResearch.WordTrace tailWord_271556 prefixEnd_271556 139438752612444769601143 := by
  unfold tailWord_271556
  simp only [CollatzResearch.WordTrace]
  refine ⟨4952230502103232458781261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6602974002804309945041681 4952230502103232458781261)
  ·
    refine ⟨1857086438288712172042973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4952230502103232458781261 1857086438288712172042973)
    ·
      refine ⟨696407414358267064516115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1857086438288712172042973 696407414358267064516115)
      ·
        refine ⟨1044611121537400596774173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 696407414358267064516115 1044611121537400596774173)
        ·
          refine ⟨391729170576525223790315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1044611121537400596774173 391729170576525223790315)
          ·
            refine ⟨587593755864787835685473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391729170576525223790315 587593755864787835685473)
            ·
              refine ⟨440695316898590876764105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 587593755864787835685473 440695316898590876764105)
              ·
                refine ⟨330521487673943157573079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 440695316898590876764105 330521487673943157573079)
                ·
                  refine ⟨495782231510914736359619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 330521487673943157573079 495782231510914736359619)
                  ·
                    refine ⟨743673347266372104539429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 495782231510914736359619 743673347266372104539429)
                    ·
                      refine ⟨139438752612444769601143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 743673347266372104539429 139438752612444769601143)
                      ·
                        rfl

theorem cell23_271556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_271556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271556 prefixEnd_271556 := by exact prefixLift 271556
  have htrace : WordTrace (prefixWord ++ tailWord_271556) baseStart_271556 baseEnd_271556 := by
    simpa [prefixWord, tailWord_271556, baseEnd_271556] using wordTrace_append hprefix tailTrace_271556
  have hstable : (prefixWord ++ tailWord_271556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271556).length < 2 ^ (prefixWord ++ tailWord_271556).sum := by decide
  have hdescent : baseEnd_271556 < baseStart_271556 := by decide
  rcases family_descends (prefixWord ++ tailWord_271556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271562 : List Nat := [3, 1, 2, 1, 3, 2, 4, 7]
def baseStart_271562 : Nat := 118140960795 + 271562 * 2 ^ 59
def prefixEnd_271562 : Nat := 4983230072969 + 3 ^ 40 * 271562 * 2
def baseEnd_271562 : Nat := 5164512351717472078745

theorem tailTrace_271562 : CollatzResearch.WordTrace tailWord_271562 prefixEnd_271562 5164512351717472078745 := by
  unfold tailWord_271562
  simp only [CollatzResearch.WordTrace]
  refine ⟨2476169960546181985570235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6603119894789818628187293 2476169960546181985570235)
  ·
    refine ⟨3714254940819272978355353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2476169960546181985570235 3714254940819272978355353)
    ·
      refine ⟨2785691205614454733766515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3714254940819272978355353 2785691205614454733766515)
      ·
        refine ⟨4178536808421682100649773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2785691205614454733766515 4178536808421682100649773)
        ·
          refine ⟨1566951303158130787743665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4178536808421682100649773 1566951303158130787743665)
          ·
            refine ⟨1175213477368598090807749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1566951303158130787743665 1175213477368598090807749)
            ·
              refine ⟨220352527006612142026453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1175213477368598090807749 220352527006612142026453)
              ·
                refine ⟨5164512351717472078745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 220352527006612142026453 5164512351717472078745)
                ·
                  rfl

theorem cell23_271562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 7].length) (baseStart_271562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271562 prefixEnd_271562 := by exact prefixLift 271562
  have htrace : WordTrace (prefixWord ++ tailWord_271562) baseStart_271562 baseEnd_271562 := by
    simpa [prefixWord, tailWord_271562, baseEnd_271562] using wordTrace_append hprefix tailTrace_271562
  have hstable : (prefixWord ++ tailWord_271562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271562).length < 2 ^ (prefixWord ++ tailWord_271562).sum := by decide
  have hdescent : baseEnd_271562 < baseStart_271562 := by decide
  rcases family_descends (prefixWord ++ tailWord_271562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271652 : List Nat := [2, 3, 1, 3, 1, 1, 2, 3, 7]
def baseStart_271652 : Nat := 118140960795 + 271652 * 2 ^ 59
def prefixEnd_271652 : Nat := 4983230072969 + 3 ^ 40 * 271652 * 2
def baseEnd_271652 : Nat := 15498671861697377111189

theorem tailTrace_271652 : CollatzResearch.WordTrace tailWord_271652 prefixEnd_271652 15498671861697377111189 := by
  unfold tailWord_271652
  simp only [CollatzResearch.WordTrace]
  refine ⟨4953981205929336656528605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6605308274572448875371473 4953981205929336656528605)
  ·
    refine ⟨1857742952223501246198227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4953981205929336656528605 1857742952223501246198227)
    ·
      refine ⟨2786614428335251869297341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1857742952223501246198227 2786614428335251869297341)
      ·
        refine ⟨1044980410625719450986503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2786614428335251869297341 1044980410625719450986503)
        ·
          refine ⟨1567470615938579176479755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1044980410625719450986503 1567470615938579176479755)
          ·
            refine ⟨2351205923907868764719633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1567470615938579176479755 2351205923907868764719633)
            ·
              refine ⟨1763404442930901573539725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2351205923907868764719633 1763404442930901573539725)
              ·
                refine ⟨661276666099088090077397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1763404442930901573539725 661276666099088090077397)
                ·
                  refine ⟨15498671861697377111189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 661276666099088090077397 15498671861697377111189)
                  ·
                    rfl

theorem cell23_271652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 7].length) (baseStart_271652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271652 prefixEnd_271652 := by exact prefixLift 271652
  have htrace : WordTrace (prefixWord ++ tailWord_271652) baseStart_271652 baseEnd_271652 := by
    simpa [prefixWord, tailWord_271652, baseEnd_271652] using wordTrace_append hprefix tailTrace_271652
  have hstable : (prefixWord ++ tailWord_271652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271652).length < 2 ^ (prefixWord ++ tailWord_271652).sum := by decide
  have hdescent : baseEnd_271652 < baseStart_271652 := by decide
  rcases family_descends (prefixWord ++ tailWord_271652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271729 : List Nat := [1, 2, 2, 2, 1, 2, 4, 2, 3, 4]
def baseStart_271729 : Nat := 118140960795 + 271729 * 2 ^ 59
def prefixEnd_271729 : Nat := 4983230072969 + 3 ^ 40 * 271729 * 2
def baseEnd_271729 : Nat := 46509194921890864245949

theorem tailTrace_271729 : CollatzResearch.WordTrace tailWord_271729 prefixEnd_271729 46509194921890864245949 := by
  unfold tailWord_271729
  simp only [CollatzResearch.WordTrace]
  refine ⟨9910770832579715463610241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6607180555053143642406827 9910770832579715463610241)
  ·
    refine ⟨7433078124434786597707681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9910770832579715463610241 7433078124434786597707681)
    ·
      refine ⟨5574808593326089948280761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7433078124434786597707681 5574808593326089948280761)
      ·
        refine ⟨4181106444994567461210571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5574808593326089948280761 4181106444994567461210571)
        ·
          refine ⟨6271659667491851191815857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4181106444994567461210571 6271659667491851191815857)
          ·
            refine ⟨4703744750618888393861893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6271659667491851191815857 4703744750618888393861893)
            ·
              refine ⟨881952140741041573849105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4703744750618888393861893 881952140741041573849105)
              ·
                refine ⟨661464105555781180386829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 881952140741041573849105 661464105555781180386829)
                ·
                  refine ⟨248049039583417942645061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 661464105555781180386829 248049039583417942645061)
                  ·
                    refine ⟨46509194921890864245949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 248049039583417942645061 46509194921890864245949)
                    ·
                      rfl

theorem cell23_271729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 3, 4].length) (baseStart_271729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271729 prefixEnd_271729 := by exact prefixLift 271729
  have htrace : WordTrace (prefixWord ++ tailWord_271729) baseStart_271729 baseEnd_271729 := by
    simpa [prefixWord, tailWord_271729, baseEnd_271729] using wordTrace_append hprefix tailTrace_271729
  have hstable : (prefixWord ++ tailWord_271729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271729).length < 2 ^ (prefixWord ++ tailWord_271729).sum := by decide
  have hdescent : baseEnd_271729 < baseStart_271729 := by decide
  rcases family_descends (prefixWord ++ tailWord_271729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271739 : List Nat := [1, 1, 1, 1, 1, 6, 2, 3, 2, 2, 3]
def baseStart_271739 : Nat := 118140960795 + 271739 * 2 ^ 59
def prefixEnd_271739 : Nat := 4983230072969 + 3 ^ 40 * 271739 * 2
def baseEnd_271739 : Nat := 139532719572217553612801

theorem tailTrace_271739 : CollatzResearch.WordTrace tailWord_271739 prefixEnd_271739 139532719572217553612801 := by
  unfold tailWord_271739
  simp only [CollatzResearch.WordTrace]
  refine ⟨9911135562543487171474271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6607423708362324780982847 9911135562543487171474271)
  ·
    refine ⟨14866703343815230757211407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9911135562543487171474271 14866703343815230757211407)
    ·
      refine ⟨22300055015722846135817111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14866703343815230757211407 22300055015722846135817111)
      ·
        refine ⟨33450082523584269203725667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22300055015722846135817111 33450082523584269203725667)
        ·
          refine ⟨50175123785376403805588501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33450082523584269203725667 50175123785376403805588501)
          ·
            refine ⟨2351958927439518928386961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 50175123785376403805588501 2351958927439518928386961)
            ·
              refine ⟨1763969195579639196290221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2351958927439518928386961 1763969195579639196290221)
              ·
                refine ⟨661488448342364698608833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1763969195579639196290221 661488448342364698608833)
                ·
                  refine ⟨496116336256773523956625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 661488448342364698608833 496116336256773523956625)
                  ·
                    refine ⟨372087252192580142967469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 496116336256773523956625 372087252192580142967469)
                    ·
                      refine ⟨139532719572217553612801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 372087252192580142967469 139532719572217553612801)
                      ·
                        rfl

theorem cell23_271739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 2, 3].length) (baseStart_271739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271739 prefixEnd_271739 := by exact prefixLift 271739
  have htrace : WordTrace (prefixWord ++ tailWord_271739) baseStart_271739 baseEnd_271739 := by
    simpa [prefixWord, tailWord_271739, baseEnd_271739] using wordTrace_append hprefix tailTrace_271739
  have hstable : (prefixWord ++ tailWord_271739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271739).length < 2 ^ (prefixWord ++ tailWord_271739).sum := by decide
  have hdescent : baseEnd_271739 < baseStart_271739 := by decide
  rcases family_descends (prefixWord ++ tailWord_271739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271819 : List Nat := [1, 1, 1, 1, 3, 3, 2, 3, 4, 4]
def baseStart_271819 : Nat := 118140960795 + 271819 * 2 ^ 59
def prefixEnd_271819 : Nat := 4983230072969 + 3 ^ 40 * 271819 * 2
def baseEnd_271819 : Nat := 46524599341525746870811

theorem tailTrace_271819 : CollatzResearch.WordTrace tailWord_271819 prefixEnd_271819 46524599341525746870811 := by
  unfold tailWord_271819
  simp only [CollatzResearch.WordTrace]
  refine ⟨9914053402253660834386511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6609368934835773889591007 9914053402253660834386511)
  ·
    refine ⟨14871080103380491251579767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9914053402253660834386511 14871080103380491251579767)
    ·
      refine ⟨22306620155070736877369651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14871080103380491251579767 22306620155070736877369651)
      ·
        refine ⟨33459930232606105316054477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22306620155070736877369651 33459930232606105316054477)
        ·
          refine ⟨12547473837227289493520429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33459930232606105316054477 12547473837227289493520429)
          ·
            refine ⟨4705302688960233560070161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12547473837227289493520429 4705302688960233560070161)
            ·
              refine ⟨3528977016720175170052621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4705302688960233560070161 3528977016720175170052621)
              ·
                refine ⟨1323366381270065688769733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3528977016720175170052621 1323366381270065688769733)
                ·
                  refine ⟨248131196488137316644325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1323366381270065688769733 248131196488137316644325)
                  ·
                    refine ⟨46524599341525746870811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 248131196488137316644325 46524599341525746870811)
                    ·
                      rfl

theorem cell23_271819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 4, 4].length) (baseStart_271819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271819 prefixEnd_271819 := by exact prefixLift 271819
  have htrace : WordTrace (prefixWord ++ tailWord_271819) baseStart_271819 baseEnd_271819 := by
    simpa [prefixWord, tailWord_271819, baseEnd_271819] using wordTrace_append hprefix tailTrace_271819
  have hstable : (prefixWord ++ tailWord_271819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271819).length < 2 ^ (prefixWord ++ tailWord_271819).sum := by decide
  have hdescent : baseEnd_271819 < baseStart_271819 := by decide
  rcases family_descends (prefixWord ++ tailWord_271819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271820 : List Nat := [2, 2, 1, 4, 2, 2, 1, 4, 1, 1, 3]
def baseStart_271820 : Nat := 118140960795 + 271820 * 2 ^ 59
def prefixEnd_271820 : Nat := 4983230072969 + 3 ^ 40 * 271820 * 2
def baseEnd_271820 : Nat := 139574311505231736699929

theorem tailTrace_271820 : CollatzResearch.WordTrace tailWord_271820 prefixEnd_271820 139574311505231736699929 := by
  unfold tailWord_271820
  simp only [CollatzResearch.WordTrace]
  refine ⟨4957044937625019002586457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6609393250166692003448609 4957044937625019002586457)
  ·
    refine ⟨3717783703218764251939843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4957044937625019002586457 3717783703218764251939843)
    ·
      refine ⟨5576675554828146377909765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3717783703218764251939843 5576675554828146377909765)
      ·
        refine ⟨1045626666530277445858081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5576675554828146377909765 1045626666530277445858081)
        ·
          refine ⟨784219999897708084393561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1045626666530277445858081 784219999897708084393561)
          ·
            refine ⟨588164999923281063295171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 784219999897708084393561 588164999923281063295171)
            ·
              refine ⟨882247499884921594942757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 588164999923281063295171 882247499884921594942757)
              ·
                refine ⟨165421406228422799051767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 882247499884921594942757 165421406228422799051767)
                ·
                  refine ⟨248132109342634198577651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 165421406228422799051767 248132109342634198577651)
                  ·
                    refine ⟨372198164013951297866477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 248132109342634198577651 372198164013951297866477)
                    ·
                      refine ⟨139574311505231736699929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 372198164013951297866477 139574311505231736699929)
                      ·
                        rfl

theorem cell23_271820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_271820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271820 prefixEnd_271820 := by exact prefixLift 271820
  have htrace : WordTrace (prefixWord ++ tailWord_271820) baseStart_271820 baseEnd_271820 := by
    simpa [prefixWord, tailWord_271820, baseEnd_271820] using wordTrace_append hprefix tailTrace_271820
  have hstable : (prefixWord ++ tailWord_271820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271820).length < 2 ^ (prefixWord ++ tailWord_271820).sum := by decide
  have hdescent : baseEnd_271820 < baseStart_271820 := by decide
  rcases family_descends (prefixWord ++ tailWord_271820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271829 : List Nat := [1, 3, 2, 3, 1, 1, 2, 1, 3, 1, 5]
def baseStart_271829 : Nat := 118140960795 + 271829 * 2 ^ 59
def prefixEnd_271829 : Nat := 4983230072969 + 3 ^ 40 * 271829 * 2
def baseEnd_271829 : Nat := 139578932831122201487387

theorem tailTrace_271829 : CollatzResearch.WordTrace tailWord_271829 prefixEnd_271829 139578932831122201487387 := by
  unfold tailWord_271829
  simp only [CollatzResearch.WordTrace]
  refine ⟨9914418132217432542250541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6609612088144955028167027 9914418132217432542250541)
  ·
    refine ⟨3717906799581537203343953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9914418132217432542250541 3717906799581537203343953)
    ·
      refine ⟨2788430099686152902507965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3717906799581537203343953 2788430099686152902507965)
      ·
        refine ⟨1045661287382307338440487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2788430099686152902507965 1045661287382307338440487)
        ·
          refine ⟨1568491931073461007660731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1045661287382307338440487 1568491931073461007660731)
          ·
            refine ⟨2352737896610191511491097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1568491931073461007660731 2352737896610191511491097)
            ·
              refine ⟨1764553422457643633618323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2352737896610191511491097 1764553422457643633618323)
              ·
                refine ⟨2646830133686465450427485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1764553422457643633618323 2646830133686465450427485)
                ·
                  refine ⟨992561300132424543910307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2646830133686465450427485 992561300132424543910307)
                  ·
                    refine ⟨1488841950198636815865461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 992561300132424543910307 1488841950198636815865461)
                    ·
                      refine ⟨139578932831122201487387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1488841950198636815865461 139578932831122201487387)
                      ·
                        rfl

theorem cell23_271829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_271829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271829 prefixEnd_271829 := by exact prefixLift 271829
  have htrace : WordTrace (prefixWord ++ tailWord_271829) baseStart_271829 baseEnd_271829 := by
    simpa [prefixWord, tailWord_271829, baseEnd_271829] using wordTrace_append hprefix tailTrace_271829
  have hstable : (prefixWord ++ tailWord_271829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271829).length < 2 ^ (prefixWord ++ tailWord_271829).sum := by decide
  have hdescent : baseEnd_271829 < baseStart_271829 := by decide
  rcases family_descends (prefixWord ++ tailWord_271829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271843 : List Nat := [1, 1, 1, 6, 2, 1, 1, 1, 5, 2, 2]
def baseStart_271843 : Nat := 118140960795 + 271843 * 2 ^ 59
def prefixEnd_271843 : Nat := 4983230072969 + 3 ^ 40 * 271843 * 2
def baseEnd_271843 : Nat := 139586121560285146712323

theorem tailTrace_271843 : CollatzResearch.WordTrace tailWord_271843 prefixEnd_271843 139586121560285146712323 := by
  unfold tailWord_271843
  simp only [CollatzResearch.WordTrace]
  refine ⟨9914928754166712933260183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6609952502777808622173455 9914928754166712933260183)
  ·
    refine ⟨14872393131250069399890275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9914928754166712933260183 14872393131250069399890275)
    ·
      refine ⟨22308589696875104099835413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14872393131250069399890275 22308589696875104099835413)
      ·
        refine ⟨1045715142041020504679785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22308589696875104099835413 1045715142041020504679785)
        ·
          refine ⟨784286356530765378509839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1045715142041020504679785 784286356530765378509839)
          ·
            refine ⟨1176429534796148067764759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 784286356530765378509839 1176429534796148067764759)
            ·
              refine ⟨1764644302194222101647139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1176429534796148067764759 1764644302194222101647139)
              ·
                refine ⟨2646966453291333152470709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1764644302194222101647139 2646966453291333152470709)
                ·
                  refine ⟨248153104996062483044129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2646966453291333152470709 248153104996062483044129)
                  ·
                    refine ⟨186114828747046862283097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 248153104996062483044129 186114828747046862283097)
                    ·
                      refine ⟨139586121560285146712323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 186114828747046862283097 139586121560285146712323)
                      ·
                        rfl

theorem cell23_271843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_271843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271843 prefixEnd_271843 := by exact prefixLift 271843
  have htrace : WordTrace (prefixWord ++ tailWord_271843) baseStart_271843 baseEnd_271843 := by
    simpa [prefixWord, tailWord_271843, baseEnd_271843] using wordTrace_append hprefix tailTrace_271843
  have hstable : (prefixWord ++ tailWord_271843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271843).length < 2 ^ (prefixWord ++ tailWord_271843).sum := by decide
  have hdescent : baseEnd_271843 < baseStart_271843 := by decide
  rcases family_descends (prefixWord ++ tailWord_271843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271859 : List Nat := [1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3]
def baseStart_271859 : Nat := 118140960795 + 271859 * 2 ^ 59
def prefixEnd_271859 : Nat := 4983230072969 + 3 ^ 40 * 271859 * 2
def baseEnd_271859 : Nat := 139594337250757084112249

theorem tailTrace_271859 : CollatzResearch.WordTrace tailWord_271859 prefixEnd_271859 139594337250757084112249 := by
  unfold tailWord_271859
  simp only [CollatzResearch.WordTrace]
  refine ⟨9915512322108747665842631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6610341548072498443895087 9915512322108747665842631)
  ·
    refine ⟨14873268483163121498763947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9915512322108747665842631 14873268483163121498763947)
    ·
      refine ⟨22309902724744682248145921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14873268483163121498763947 22309902724744682248145921)
      ·
        refine ⟨16732427043558511686109441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22309902724744682248145921 16732427043558511686109441)
        ·
          refine ⟨12549320282668883764582081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16732427043558511686109441 12549320282668883764582081)
          ·
            refine ⟨9411990212001662823436561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12549320282668883764582081 9411990212001662823436561)
            ·
              refine ⟨7058992659001247117577421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9411990212001662823436561 7058992659001247117577421)
              ·
                refine ⟨2647122247125467669091533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7058992659001247117577421 2647122247125467669091533)
                ·
                  refine ⟨992670842672050375909325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2647122247125467669091533 992670842672050375909325)
                  ·
                    refine ⟨372251566002018890965997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 992670842672050375909325 372251566002018890965997)
                    ·
                      refine ⟨139594337250757084112249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 372251566002018890965997 139594337250757084112249)
                      ·
                        rfl

theorem cell23_271859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3].length) (baseStart_271859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271859 prefixEnd_271859 := by exact prefixLift 271859
  have htrace : WordTrace (prefixWord ++ tailWord_271859) baseStart_271859 baseEnd_271859 := by
    simpa [prefixWord, tailWord_271859, baseEnd_271859] using wordTrace_append hprefix tailTrace_271859
  have hstable : (prefixWord ++ tailWord_271859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271859).length < 2 ^ (prefixWord ++ tailWord_271859).sum := by decide
  have hdescent : baseEnd_271859 < baseStart_271859 := by decide
  rcases family_descends (prefixWord ++ tailWord_271859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271870 : List Nat := [4, 2, 2, 3, 1, 1, 1, 1, 4, 4]
def baseStart_271870 : Nat := 118140960795 + 271870 * 2 ^ 59
def prefixEnd_271870 : Nat := 4983230072969 + 3 ^ 40 * 271870 * 2
def baseEnd_271870 : Nat := 46533328512652180358233

theorem tailTrace_271870 : CollatzResearch.WordTrace tailWord_271870 prefixEnd_271870 46533328512652180358233 := by
  unfold tailWord_271870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1239489190633612068061633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6610609016712597696328709 1239489190633612068061633)
  ·
    refine ⟨929616892975209051046225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1239489190633612068061633 929616892975209051046225)
    ·
      refine ⟨697212669731406788284669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 929616892975209051046225 697212669731406788284669)
      ·
        refine ⟨261454751149277545606751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 697212669731406788284669 261454751149277545606751)
        ·
          refine ⟨392182126723916318410127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261454751149277545606751 392182126723916318410127)
          ·
            refine ⟨588273190085874477615191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392182126723916318410127 588273190085874477615191)
            ·
              refine ⟨882409785128811716422787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 588273190085874477615191 882409785128811716422787)
              ·
                refine ⟨1323614677693217574634181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 882409785128811716422787 1323614677693217574634181)
                ·
                  refine ⟨248177752067478295243909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1323614677693217574634181 248177752067478295243909)
                  ·
                    refine ⟨46533328512652180358233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 248177752067478295243909 46533328512652180358233)
                    ·
                      rfl

theorem cell23_271870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_271870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271870 prefixEnd_271870 := by exact prefixLift 271870
  have htrace : WordTrace (prefixWord ++ tailWord_271870) baseStart_271870 baseEnd_271870 := by
    simpa [prefixWord, tailWord_271870, baseEnd_271870] using wordTrace_append hprefix tailTrace_271870
  have hstable : (prefixWord ++ tailWord_271870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271870).length < 2 ^ (prefixWord ++ tailWord_271870).sum := by decide
  have hdescent : baseEnd_271870 < baseStart_271870 := by decide
  rcases family_descends (prefixWord ++ tailWord_271870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271893 : List Nat := [1, 3, 2, 1, 3, 4, 1, 1, 1, 3, 3]
def baseStart_271893 : Nat := 118140960795 + 271893 * 2 ^ 59
def prefixEnd_271893 : Nat := 4983230072969 + 3 ^ 40 * 271893 * 2
def baseEnd_271893 : Nat := 139611795593009951087093

theorem tailTrace_271893 : CollatzResearch.WordTrace tailWord_271893 prefixEnd_271893 139611795593009951087093 := by
  unfold tailWord_271893
  simp only [CollatzResearch.WordTrace]
  refine ⟨9916752403985571472580333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6611168269323714315053555 9916752403985571472580333)
  ·
    refine ⟨3718782151494589302217625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9916752403985571472580333 3718782151494589302217625)
    ·
      refine ⟨2789086613620941976663219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3718782151494589302217625 2789086613620941976663219)
      ·
        refine ⟨4183629920431412964994829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2789086613620941976663219 4183629920431412964994829)
        ·
          refine ⟨1568861220161779861873061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4183629920431412964994829 1568861220161779861873061)
          ·
            refine ⟨294161478780333724101199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1568861220161779861873061 294161478780333724101199)
            ·
              refine ⟨441242218170500586151799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294161478780333724101199 441242218170500586151799)
              ·
                refine ⟨661863327255750879227699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 441242218170500586151799 661863327255750879227699)
                ·
                  refine ⟨992794990883626318841549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 661863327255750879227699 992794990883626318841549)
                  ·
                    refine ⟨372298121581359869565581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 992794990883626318841549 372298121581359869565581)
                    ·
                      refine ⟨139611795593009951087093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 372298121581359869565581 139611795593009951087093)
                      ·
                        rfl

theorem cell23_271893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 3, 3].length) (baseStart_271893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271893 prefixEnd_271893 := by exact prefixLift 271893
  have htrace : WordTrace (prefixWord ++ tailWord_271893) baseStart_271893 baseEnd_271893 := by
    simpa [prefixWord, tailWord_271893, baseEnd_271893] using wordTrace_append hprefix tailTrace_271893
  have hstable : (prefixWord ++ tailWord_271893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271893).length < 2 ^ (prefixWord ++ tailWord_271893).sum := by decide
  have hdescent : baseEnd_271893 < baseStart_271893 := by decide
  rcases family_descends (prefixWord ++ tailWord_271893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271903 : List Nat := [1, 1, 2, 4, 1, 1, 3, 4, 1, 3, 2]
def baseStart_271903 : Nat := 118140960795 + 271903 * 2 ^ 59
def prefixEnd_271903 : Nat := 4983230072969 + 3 ^ 40 * 271903 * 2
def baseEnd_271903 : Nat := 139616930399554911962047

theorem tailTrace_271903 : CollatzResearch.WordTrace tailWord_271903 prefixEnd_271903 139616930399554911962047 := by
  unfold tailWord_271903
  simp only [CollatzResearch.WordTrace]
  refine ⟨9917117133949343180444363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6611411422632895453629575 9917117133949343180444363)
  ·
    refine ⟨14875675700924014770666545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9917117133949343180444363 14875675700924014770666545)
    ·
      refine ⟨11156756775693011077999909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14875675700924014770666545 11156756775693011077999909)
      ·
        refine ⟨2091891895442439577124983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11156756775693011077999909 2091891895442439577124983)
        ·
          refine ⟨3137837843163659365687475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2091891895442439577124983 3137837843163659365687475)
          ·
            refine ⟨4706756764745489048531213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3137837843163659365687475 4706756764745489048531213)
            ·
              refine ⟨1765033786779558393199205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4706756764745489048531213 1765033786779558393199205)
              ·
                refine ⟨330943835021167198724851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1765033786779558393199205 330943835021167198724851)
                ·
                  refine ⟨496415752531750798087277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 330943835021167198724851 496415752531750798087277)
                  ·
                    refine ⟨186155907199406549282729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 496415752531750798087277 186155907199406549282729)
                    ·
                      refine ⟨139616930399554911962047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 186155907199406549282729 139616930399554911962047)
                      ·
                        rfl

theorem cell23_271903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_271903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271903 prefixEnd_271903 := by exact prefixLift 271903
  have htrace : WordTrace (prefixWord ++ tailWord_271903) baseStart_271903 baseEnd_271903 := by
    simpa [prefixWord, tailWord_271903, baseEnd_271903] using wordTrace_append hprefix tailTrace_271903
  have hstable : (prefixWord ++ tailWord_271903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271903).length < 2 ^ (prefixWord ++ tailWord_271903).sum := by decide
  have hdescent : baseEnd_271903 < baseStart_271903 := by decide
  rcases family_descends (prefixWord ++ tailWord_271903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271990 : List Nat := [5, 1, 1, 2, 2, 2, 1, 4, 5]
def baseStart_271990 : Nat := 118140960795 + 271990 * 2 ^ 59
def prefixEnd_271990 : Nat := 4983230072969 + 3 ^ 40 * 271990 * 2
def baseEnd_271990 : Nat := 15517955912944007952683

theorem tailTrace_271990 : CollatzResearch.WordTrace tailWord_271990 prefixEnd_271990 15517955912944007952683 := by
  unfold tailWord_271990
  simp only [CollatzResearch.WordTrace]
  refine ⟨620018142789634814928839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6613526856422771359240949 620018142789634814928839)
  ·
    refine ⟨930027214184452222393259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 620018142789634814928839 930027214184452222393259)
    ·
      refine ⟨1395040821276678333589889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 930027214184452222393259 1395040821276678333589889)
      ·
        refine ⟨1046280615957508750192417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1395040821276678333589889 1046280615957508750192417)
        ·
          refine ⟨784710461968131562644313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1046280615957508750192417 784710461968131562644313)
          ·
            refine ⟨588532846476098671983235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 784710461968131562644313 588532846476098671983235)
            ·
              refine ⟨882799269714148007974853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 588532846476098671983235 882799269714148007974853)
              ·
                refine ⟨165524863071402751495285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 882799269714148007974853 165524863071402751495285)
                ·
                  refine ⟨15517955912944007952683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 165524863071402751495285 15517955912944007952683)
                  ·
                    rfl

theorem cell23_271990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_271990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_271990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_271990 prefixEnd_271990 := by exact prefixLift 271990
  have htrace : WordTrace (prefixWord ++ tailWord_271990) baseStart_271990 baseEnd_271990 := by
    simpa [prefixWord, tailWord_271990, baseEnd_271990] using wordTrace_append hprefix tailTrace_271990
  have hstable : (prefixWord ++ tailWord_271990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271990).length < 2 ^ (prefixWord ++ tailWord_271990).sum := by decide
  have hdescent : baseEnd_271990 < baseStart_271990 := by decide
  rcases family_descends (prefixWord ++ tailWord_271990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272019 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 6]
def baseStart_272019 : Nat := 118140960795 + 272019 * 2 ^ 59
def prefixEnd_272019 : Nat := 4983230072969 + 3 ^ 40 * 272019 * 2
def baseEnd_272019 : Nat := 139676494155476458111513

theorem tailTrace_272019 : CollatzResearch.WordTrace tailWord_272019 prefixEnd_272019 139676494155476458111513 := by
  unfold tailWord_272019
  simp only [CollatzResearch.WordTrace]
  refine ⟨9921348001529094991667111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6614232001019396661111407 9921348001529094991667111)
  ·
    refine ⟨14882022002293642487500667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9921348001529094991667111 14882022002293642487500667)
    ·
      refine ⟨22323033003440463731251001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14882022002293642487500667 22323033003440463731251001)
      ·
        refine ⟨16742274752580347798438251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22323033003440463731251001 16742274752580347798438251)
        ·
          refine ⟨25113412128870521697657377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16742274752580347798438251 25113412128870521697657377)
          ·
            refine ⟨18835059096652891273243033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25113412128870521697657377 18835059096652891273243033)
            ·
              refine ⟨14126294322489668454932275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18835059096652891273243033 14126294322489668454932275)
              ·
                refine ⟨21189441483734502682398413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14126294322489668454932275 21189441483734502682398413)
                ·
                  refine ⟨7946040556400438505899405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21189441483734502682398413 7946040556400438505899405)
                  ·
                    refine ⟨2979765208650164439712277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7946040556400438505899405 2979765208650164439712277)
                    ·
                      refine ⟨139676494155476458111513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2979765208650164439712277 139676494155476458111513)
                      ·
                        rfl

theorem cell23_272019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 6].length) (baseStart_272019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272019 prefixEnd_272019 := by exact prefixLift 272019
  have htrace : WordTrace (prefixWord ++ tailWord_272019) baseStart_272019 baseEnd_272019 := by
    simpa [prefixWord, tailWord_272019, baseEnd_272019] using wordTrace_append hprefix tailTrace_272019
  have hstable : (prefixWord ++ tailWord_272019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272019).length < 2 ^ (prefixWord ++ tailWord_272019).sum := by decide
  have hdescent : baseEnd_272019 < baseStart_272019 := by decide
  rcases family_descends (prefixWord ++ tailWord_272019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272023 : List Nat := [1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 4]
def baseStart_272023 : Nat := 118140960795 + 272023 * 2 ^ 59
def prefixEnd_272023 : Nat := 4983230072969 + 3 ^ 40 * 272023 * 2
def baseEnd_272023 : Nat := 139678548078094442461495

theorem tailTrace_272023 : CollatzResearch.WordTrace tailWord_272023 prefixEnd_272023 139678548078094442461495 := by
  unfold tailWord_272023
  simp only [CollatzResearch.WordTrace]
  refine ⟨9921493893514603674812723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6614329262343069116541815 9921493893514603674812723)
  ·
    refine ⟨14882240840271905512219085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9921493893514603674812723 14882240840271905512219085)
    ·
      refine ⟨5580840315101964567082157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14882240840271905512219085 5580840315101964567082157)
      ·
        refine ⟨2092815118163236712655809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5580840315101964567082157 2092815118163236712655809)
        ·
          refine ⟨1569611338622427534491857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2092815118163236712655809 1569611338622427534491857)
          ·
            refine ⟨1177208503966820650868893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1569611338622427534491857 1177208503966820650868893)
            ·
              refine ⟨441453188987557744075835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1177208503966820650868893 441453188987557744075835)
              ·
                refine ⟨662179783481336616113753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 441453188987557744075835 662179783481336616113753)
                ·
                  refine ⟨496634837611002462085315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 662179783481336616113753 496634837611002462085315)
                  ·
                    refine ⟨744952256416503693127973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 496634837611002462085315 744952256416503693127973)
                    ·
                      refine ⟨139678548078094442461495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 744952256416503693127973 139678548078094442461495)
                      ·
                        rfl

theorem cell23_272023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_272023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272023 prefixEnd_272023 := by exact prefixLift 272023
  have htrace : WordTrace (prefixWord ++ tailWord_272023) baseStart_272023 baseEnd_272023 := by
    simpa [prefixWord, tailWord_272023, baseEnd_272023] using wordTrace_append hprefix tailTrace_272023
  have hstable : (prefixWord ++ tailWord_272023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272023).length < 2 ^ (prefixWord ++ tailWord_272023).sum := by decide
  have hdescent : baseEnd_272023 < baseStart_272023 := by decide
  rcases family_descends (prefixWord ++ tailWord_272023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272036 : List Nat := [2, 3, 1, 2, 2, 2, 1, 1, 2, 1, 6]
def baseStart_272036 : Nat := 118140960795 + 272036 * 2 ^ 59
def prefixEnd_272036 : Nat := 4983230072969 + 3 ^ 40 * 272036 * 2
def baseEnd_272036 : Nat := 139685223326602891598935

theorem tailTrace_272036 : CollatzResearch.WordTrace tailWord_272036 prefixEnd_272036 139685223326602891598935 := by
  unfold tailWord_272036
  simp only [CollatzResearch.WordTrace]
  refine ⟨4960984021233753447517981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6614645361645004596690641 4960984021233753447517981)
  ·
    refine ⟨1860369007962657542819243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4960984021233753447517981 1860369007962657542819243)
    ·
      refine ⟨2790553511943986314228865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1860369007962657542819243 2790553511943986314228865)
      ·
        refine ⟨2092915133957989735671649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2790553511943986314228865 2092915133957989735671649)
        ·
          refine ⟨1569686350468492301753737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2092915133957989735671649 1569686350468492301753737)
          ·
            refine ⟨1177264762851369226315303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1569686350468492301753737 1177264762851369226315303)
            ·
              refine ⟨1765897144277053839472955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1177264762851369226315303 1765897144277053839472955)
              ·
                refine ⟨2648845716415580759209433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1765897144277053839472955 2648845716415580759209433)
                ·
                  refine ⟨1986634287311685569407075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2648845716415580759209433 1986634287311685569407075)
                  ·
                    refine ⟨2979951430967528354110613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1986634287311685569407075 2979951430967528354110613)
                    ·
                      refine ⟨139685223326602891598935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2979951430967528354110613 139685223326602891598935)
                      ·
                        rfl

theorem cell23_272036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_272036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272036 prefixEnd_272036 := by exact prefixLift 272036
  have htrace : WordTrace (prefixWord ++ tailWord_272036) baseStart_272036 baseEnd_272036 := by
    simpa [prefixWord, tailWord_272036, baseEnd_272036] using wordTrace_append hprefix tailTrace_272036
  have hstable : (prefixWord ++ tailWord_272036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272036).length < 2 ^ (prefixWord ++ tailWord_272036).sum := by decide
  have hdescent : baseEnd_272036 < baseStart_272036 := by decide
  rcases family_descends (prefixWord ++ tailWord_272036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272050 : List Nat := [3, 2, 1, 1, 1, 2, 4, 4, 1, 4]
def baseStart_272050 : Nat := 118140960795 + 272050 * 2 ^ 59
def prefixEnd_272050 : Nat := 4983230072969 + 3 ^ 40 * 272050 * 2
def baseEnd_272050 : Nat := 46564137351921945607957

theorem tailTrace_272050 : CollatzResearch.WordTrace tailWord_272050 prefixEnd_272050 46564137351921945607957 := by
  unfold tailWord_272050
  simp only [CollatzResearch.WordTrace]
  refine ⟨2480619666104196821511401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6614985776277858190697069 2480619666104196821511401)
  ·
    refine ⟨1860464749578147616133551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2480619666104196821511401 1860464749578147616133551)
    ·
      refine ⟨2790697124367221424200327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1860464749578147616133551 2790697124367221424200327)
      ·
        refine ⟨4186045686550832136300491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2790697124367221424200327 4186045686550832136300491)
        ·
          refine ⟨6279068529826248204450737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4186045686550832136300491 6279068529826248204450737)
          ·
            refine ⟨4709301397369686153338053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6279068529826248204450737 4709301397369686153338053)
            ·
              refine ⟨882994012006816153750885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4709301397369686153338053 882994012006816153750885)
              ·
                refine ⟨165561377251278028828291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 882994012006816153750885 165561377251278028828291)
                ·
                  refine ⟨248342065876917043242437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 165561377251278028828291 248342065876917043242437)
                  ·
                    refine ⟨46564137351921945607957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 248342065876917043242437 46564137351921945607957)
                    ·
                      rfl

theorem cell23_272050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 4, 1, 4].length) (baseStart_272050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272050 prefixEnd_272050 := by exact prefixLift 272050
  have htrace : WordTrace (prefixWord ++ tailWord_272050) baseStart_272050 baseEnd_272050 := by
    simpa [prefixWord, tailWord_272050, baseEnd_272050] using wordTrace_append hprefix tailTrace_272050
  have hstable : (prefixWord ++ tailWord_272050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272050).length < 2 ^ (prefixWord ++ tailWord_272050).sum := by decide
  have hdescent : baseEnd_272050 < baseStart_272050 := by decide
  rcases family_descends (prefixWord ++ tailWord_272050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272063 : List Nat := [1, 1, 2, 2, 2, 3, 5, 1, 6]
def baseStart_272063 : Nat := 118140960795 + 272063 * 2 ^ 59
def prefixEnd_272063 : Nat := 4983230072969 + 3 ^ 40 * 272063 * 2
def baseEnd_272063 : Nat := 15522120811586031773479

theorem tailTrace_272063 : CollatzResearch.WordTrace tailWord_272063 prefixEnd_272063 15522120811586031773479 := by
  unfold tailWord_272063
  simp only [CollatzResearch.WordTrace]
  refine ⟨9922952813369690506268843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6615301875579793670845895 9922952813369690506268843)
  ·
    refine ⟨14884429220054535759403265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9922952813369690506268843 14884429220054535759403265)
    ·
      refine ⟨11163321915040901819552449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14884429220054535759403265 11163321915040901819552449)
      ·
        refine ⟨8372491436280676364664337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11163321915040901819552449 8372491436280676364664337)
        ·
          refine ⟨6279368577210507273498253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8372491436280676364664337 6279368577210507273498253)
          ·
            refine ⟨2354763216453940227561845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6279368577210507273498253 2354763216453940227561845)
            ·
              refine ⟨220759051542556896333923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2354763216453940227561845 220759051542556896333923)
              ·
                refine ⟨331138577313835344500885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220759051542556896333923 331138577313835344500885)
                ·
                  refine ⟨15522120811586031773479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 331138577313835344500885 15522120811586031773479)
                  ·
                    rfl

theorem cell23_272063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 6].length) (baseStart_272063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272063 prefixEnd_272063 := by exact prefixLift 272063
  have htrace : WordTrace (prefixWord ++ tailWord_272063) baseStart_272063 baseEnd_272063 := by
    simpa [prefixWord, tailWord_272063, baseEnd_272063] using wordTrace_append hprefix tailTrace_272063
  have hstable : (prefixWord ++ tailWord_272063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272063).length < 2 ^ (prefixWord ++ tailWord_272063).sum := by decide
  have hdescent : baseEnd_272063 < baseStart_272063 := by decide
  rcases family_descends (prefixWord ++ tailWord_272063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272084 : List Nat := [2, 4, 1, 3, 1, 3, 1, 3, 1, 4]
def baseStart_272084 : Nat := 118140960795 + 272084 * 2 ^ 59
def prefixEnd_272084 : Nat := 4983230072969 + 3 ^ 40 * 272084 * 2
def baseEnd_272084 : Nat := 46569956799339567932905

theorem tailTrace_272084 : CollatzResearch.WordTrace tailWord_272084 prefixEnd_272084 46569956799339567932905 := by
  unfold tailWord_272084
  simp only [CollatzResearch.WordTrace]
  refine ⟨4961859373146805546391653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6615812497529074061855537 4961859373146805546391653)
  ·
    refine ⟨930348632465026039948435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4961859373146805546391653 930348632465026039948435)
    ·
      refine ⟨1395522948697539059922653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 930348632465026039948435 1395522948697539059922653)
      ·
        refine ⟨523321105761577147470995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1395522948697539059922653 523321105761577147470995)
        ·
          refine ⟨784981658642365721206493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 523321105761577147470995 784981658642365721206493)
          ·
            refine ⟨294368121990887145452435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 784981658642365721206493 294368121990887145452435)
            ·
              refine ⟨441552182986330718178653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294368121990887145452435 441552182986330718178653)
              ·
                refine ⟨165582068619874019316995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 441552182986330718178653 165582068619874019316995)
                ·
                  refine ⟨248373102929811028975493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 165582068619874019316995 248373102929811028975493)
                  ·
                    refine ⟨46569956799339567932905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 248373102929811028975493 46569956799339567932905)
                    ·
                      rfl

theorem cell23_272084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_272084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272084 prefixEnd_272084 := by exact prefixLift 272084
  have htrace : WordTrace (prefixWord ++ tailWord_272084) baseStart_272084 baseEnd_272084 := by
    simpa [prefixWord, tailWord_272084, baseEnd_272084] using wordTrace_append hprefix tailTrace_272084
  have hstable : (prefixWord ++ tailWord_272084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272084).length < 2 ^ (prefixWord ++ tailWord_272084).sum := by decide
  have hdescent : baseEnd_272084 < baseStart_272084 := by decide
  rcases family_descends (prefixWord ++ tailWord_272084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272100 : List Nat := [2, 3, 1, 1, 1, 3, 3, 2, 2, 3, 2]
def baseStart_272100 : Nat := 118140960795 + 272100 * 2 ^ 59
def prefixEnd_272100 : Nat := 4983230072969 + 3 ^ 40 * 272100 * 2
def baseEnd_272100 : Nat := 139718086088490641198641

theorem tailTrace_272100 : CollatzResearch.WordTrace tailWord_272100 prefixEnd_272100 139718086088490641198641 := by
  unfold tailWord_272100
  simp only [CollatzResearch.WordTrace]
  refine ⟨4962151157117822912682877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6616201542823763883577169 4962151157117822912682877)
  ·
    refine ⟨1860806683919183592256079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4962151157117822912682877 1860806683919183592256079)
    ·
      refine ⟨2791210025878775388384119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1860806683919183592256079 2791210025878775388384119)
      ·
        refine ⟨4186815038818163082576179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2791210025878775388384119 4186815038818163082576179)
        ·
          refine ⟨6280222558227244623864269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4186815038818163082576179 6280222558227244623864269)
          ·
            refine ⟨2355083459335216733949101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6280222558227244623864269 2355083459335216733949101)
            ·
              refine ⟨883156297250706275230913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2355083459335216733949101 883156297250706275230913)
              ·
                refine ⟨662367222938029706423185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 883156297250706275230913 662367222938029706423185)
                ·
                  refine ⟨496775417203522279817389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 662367222938029706423185 496775417203522279817389)
                  ·
                    refine ⟨186290781451320854931521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 496775417203522279817389 186290781451320854931521)
                    ·
                      refine ⟨139718086088490641198641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 186290781451320854931521 139718086088490641198641)
                      ·
                        rfl

theorem cell23_272100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 2, 3, 2].length) (baseStart_272100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272100 prefixEnd_272100 := by exact prefixLift 272100
  have htrace : WordTrace (prefixWord ++ tailWord_272100) baseStart_272100 baseEnd_272100 := by
    simpa [prefixWord, tailWord_272100, baseEnd_272100] using wordTrace_append hprefix tailTrace_272100
  have hstable : (prefixWord ++ tailWord_272100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272100).length < 2 ^ (prefixWord ++ tailWord_272100).sum := by decide
  have hdescent : baseEnd_272100 < baseStart_272100 := by decide
  rcases family_descends (prefixWord ++ tailWord_272100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272130 : List Nat := [3, 4, 1, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_272130 : Nat := 118140960795 + 272130 * 2 ^ 59
def prefixEnd_272130 : Nat := 4983230072969 + 3 ^ 40 * 272130 * 2
def baseEnd_272130 : Nat := 139733490508125523823503

theorem tailTrace_272130 : CollatzResearch.WordTrace tailWord_272130 prefixEnd_272130 139733490508125523823503 := by
  unfold tailWord_272130
  simp only [CollatzResearch.WordTrace]
  refine ⟨2481349126031740237239461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6616931002751307299305229 2481349126031740237239461)
  ·
    refine ⟨465252961130951294482399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2481349126031740237239461 465252961130951294482399)
    ·
      refine ⟨697879441696426941723599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 465252961130951294482399 697879441696426941723599)
      ·
        refine ⟨1046819162544640412585399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 697879441696426941723599 1046819162544640412585399)
        ·
          refine ⟨1570228743816960618878099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1046819162544640412585399 1570228743816960618878099)
          ·
            refine ⟨2355343115725440928317149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1570228743816960618878099 2355343115725440928317149)
            ·
              refine ⟨883253668397040348118931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2355343115725440928317149 883253668397040348118931)
              ·
                refine ⟨1324880502595560522178397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 883253668397040348118931 1324880502595560522178397)
                ·
                  refine ⟨496830188473335195816899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1324880502595560522178397 496830188473335195816899)
                  ·
                    refine ⟨745245282710002793725349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 496830188473335195816899 745245282710002793725349)
                    ·
                      refine ⟨139733490508125523823503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 745245282710002793725349 139733490508125523823503)
                      ·
                        rfl

theorem cell23_272130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_272130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272130 prefixEnd_272130 := by exact prefixLift 272130
  have htrace : WordTrace (prefixWord ++ tailWord_272130) baseStart_272130 baseEnd_272130 := by
    simpa [prefixWord, tailWord_272130, baseEnd_272130] using wordTrace_append hprefix tailTrace_272130
  have hstable : (prefixWord ++ tailWord_272130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272130).length < 2 ^ (prefixWord ++ tailWord_272130).sum := by decide
  have hdescent : baseEnd_272130 < baseStart_272130 := by decide
  rcases family_descends (prefixWord ++ tailWord_272130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272136 : List Nat := [2, 1, 3, 2, 2, 1, 1, 11]
def baseStart_272136 : Nat := 118140960795 + 272136 * 2 ^ 59
def prefixEnd_272136 : Nat := 4983230072969 + 3 ^ 40 * 272136 * 2
def baseEnd_272136 : Nat := 5175428570076018531425

theorem tailTrace_272136 : CollatzResearch.WordTrace tailWord_272136 prefixEnd_272136 5175428570076018531425 := by
  unfold tailWord_272136
  simp only [CollatzResearch.WordTrace]
  refine ⟨4962807671052611986838131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6617076894736815982450841 4962807671052611986838131)
  ·
    refine ⟨7444211506578917980257197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4962807671052611986838131 7444211506578917980257197)
    ·
      refine ⟨2791579314967094242596449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7444211506578917980257197 2791579314967094242596449)
      ·
        refine ⟨2093684486225320681947337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2791579314967094242596449 2093684486225320681947337)
        ·
          refine ⟨1570263364668990511460503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2093684486225320681947337 1570263364668990511460503)
          ·
            refine ⟨2355395047003485767190755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1570263364668990511460503 2355395047003485767190755)
            ·
              refine ⟨3533092570505228650786133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2355395047003485767190755 3533092570505228650786133)
              ·
                refine ⟨5175428570076018531425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 3533092570505228650786133 5175428570076018531425)
                ·
                  rfl

theorem cell23_272136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 11].length) (baseStart_272136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272136 prefixEnd_272136 := by exact prefixLift 272136
  have htrace : WordTrace (prefixWord ++ tailWord_272136) baseStart_272136 baseEnd_272136 := by
    simpa [prefixWord, tailWord_272136, baseEnd_272136] using wordTrace_append hprefix tailTrace_272136
  have hstable : (prefixWord ++ tailWord_272136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272136).length < 2 ^ (prefixWord ++ tailWord_272136).sum := by decide
  have hdescent : baseEnd_272136 < baseStart_272136 := by decide
  rcases family_descends (prefixWord ++ tailWord_272136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272158 : List Nat := [4, 3, 2, 2, 1, 1, 1, 4, 1, 1, 3]
def baseStart_272158 : Nat := 118140960795 + 272158 * 2 ^ 59
def prefixEnd_272158 : Nat := 4983230072969 + 3 ^ 40 * 272158 * 2
def baseEnd_272158 : Nat := 139747867966451414273375

theorem tailTrace_272158 : CollatzResearch.WordTrace tailWord_272158 prefixEnd_272158 139747867966451414273375 := by
  unfold tailWord_272158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1240802218503190216372141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6617611832017014487318085 1240802218503190216372141)
  ·
    refine ⟨465300831938696331139553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1240802218503190216372141 465300831938696331139553)
    ·
      refine ⟨348975623954022248354665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 465300831938696331139553 348975623954022248354665)
      ·
        refine ⟨261731717965516686265999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 348975623954022248354665 261731717965516686265999)
        ·
          refine ⟨392597576948275029398999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261731717965516686265999 392597576948275029398999)
          ·
            refine ⟨588896365422412544098499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392597576948275029398999 588896365422412544098499)
            ·
              refine ⟨883344548133618816147749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 588896365422412544098499 883344548133618816147749)
              ·
                refine ⟨165627102775053528027703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 883344548133618816147749 165627102775053528027703)
                ·
                  refine ⟨248440654162580292041555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 165627102775053528027703 248440654162580292041555)
                  ·
                    refine ⟨372660981243870438062333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 248440654162580292041555 372660981243870438062333)
                    ·
                      refine ⟨139747867966451414273375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 372660981243870438062333 139747867966451414273375)
                      ·
                        rfl

theorem cell23_272158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_272158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272158 prefixEnd_272158 := by exact prefixLift 272158
  have htrace : WordTrace (prefixWord ++ tailWord_272158) baseStart_272158 baseEnd_272158 := by
    simpa [prefixWord, tailWord_272158, baseEnd_272158] using wordTrace_append hprefix tailTrace_272158
  have hstable : (prefixWord ++ tailWord_272158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272158).length < 2 ^ (prefixWord ++ tailWord_272158).sum := by decide
  have hdescent : baseEnd_272158 < baseStart_272158 := by decide
  rcases family_descends (prefixWord ++ tailWord_272158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272176 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 5]
def baseStart_272176 : Nat := 118140960795 + 272176 * 2 ^ 59
def prefixEnd_272176 : Nat := 4983230072969 + 3 ^ 40 * 272176 * 2
def baseEnd_272176 : Nat := 139757110618232343848291

theorem tailTrace_272176 : CollatzResearch.WordTrace tailWord_272176 prefixEnd_272176 139757110618232343848291 := by
  unfold tailWord_272176
  simp only [CollatzResearch.WordTrace]
  refine ⟨4963537130980155402566191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6618049507973540536754921 4963537130980155402566191)
  ·
    refine ⟨7445305696470233103849287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4963537130980155402566191 7445305696470233103849287)
    ·
      refine ⟨11167958544705349655773931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7445305696470233103849287 11167958544705349655773931)
      ·
        refine ⟨16751937817058024483660897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11167958544705349655773931 16751937817058024483660897)
        ·
          refine ⟨12563953362793518362745673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16751937817058024483660897 12563953362793518362745673)
          ·
            refine ⟨9422965022095138772059255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12563953362793518362745673 9422965022095138772059255)
            ·
              refine ⟨14134447533142708158088883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9422965022095138772059255 14134447533142708158088883)
              ·
                refine ⟨21201671299714062237133325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14134447533142708158088883 21201671299714062237133325)
                ·
                  refine ⟨7950626737392773338924997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21201671299714062237133325 7950626737392773338924997)
                  ·
                    refine ⟨1490742513261145001048437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7950626737392773338924997 1490742513261145001048437)
                    ·
                      refine ⟨139757110618232343848291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1490742513261145001048437 139757110618232343848291)
                      ·
                        rfl

theorem cell23_272176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 5].length) (baseStart_272176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272176 prefixEnd_272176 := by exact prefixLift 272176
  have htrace : WordTrace (prefixWord ++ tailWord_272176) baseStart_272176 baseEnd_272176 := by
    simpa [prefixWord, tailWord_272176, baseEnd_272176] using wordTrace_append hprefix tailTrace_272176
  have hstable : (prefixWord ++ tailWord_272176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272176).length < 2 ^ (prefixWord ++ tailWord_272176).sum := by decide
  have hdescent : baseEnd_272176 < baseStart_272176 := by decide
  rcases family_descends (prefixWord ++ tailWord_272176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272198 : List Nat := [6, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2]
def baseStart_272198 : Nat := 118140960795 + 272198 * 2 ^ 59
def prefixEnd_272198 : Nat := 4983230072969 + 3 ^ 40 * 272198 * 2
def baseEnd_272198 : Nat := 139768407192631257773191

theorem tailTrace_272198 : CollatzResearch.WordTrace tailWord_272198 prefixEnd_272198 139768407192631257773191 := by
  unfold tailWord_272198
  simp only [CollatzResearch.WordTrace]
  refine ⟨310246145871269017576039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6618584445253739041622165 310246145871269017576039)
  ·
    refine ⟨465369218806903526364059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 310246145871269017576039 465369218806903526364059)
    ·
      refine ⟨698053828210355289546089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 465369218806903526364059 698053828210355289546089)
      ·
        refine ⟨523540371157766467159567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 698053828210355289546089 523540371157766467159567)
        ·
          refine ⟨785310556736649700739351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 523540371157766467159567 785310556736649700739351)
          ·
            refine ⟨1177965835104974551109027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 785310556736649700739351 1177965835104974551109027)
            ·
              refine ⟨1766948752657461826663541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1177965835104974551109027 1766948752657461826663541)
              ·
                refine ⟨165651445561637046249707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1766948752657461826663541 165651445561637046249707)
                ·
                  refine ⟨248477168342455569374561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 165651445561637046249707 248477168342455569374561)
                  ·
                    refine ⟨186357876256841677030921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 248477168342455569374561 186357876256841677030921)
                    ·
                      refine ⟨139768407192631257773191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 186357876256841677030921 139768407192631257773191)
                      ·
                        rfl

theorem cell23_272198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_272198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272198 prefixEnd_272198 := by exact prefixLift 272198
  have htrace : WordTrace (prefixWord ++ tailWord_272198) baseStart_272198 baseEnd_272198 := by
    simpa [prefixWord, tailWord_272198, baseEnd_272198] using wordTrace_append hprefix tailTrace_272198
  have hstable : (prefixWord ++ tailWord_272198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272198).length < 2 ^ (prefixWord ++ tailWord_272198).sum := by decide
  have hdescent : baseEnd_272198 < baseStart_272198 := by decide
  rcases family_descends (prefixWord ++ tailWord_272198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272213 : List Nat := [1, 3, 2, 2, 2, 2, 1, 2, 2, 6]
def baseStart_272213 : Nat := 118140960795 + 272213 * 2 ^ 59
def prefixEnd_272213 : Nat := 4983230072969 + 3 ^ 40 * 272213 * 2
def baseEnd_272213 : Nat := 46592036467482899695207

theorem tailTrace_272213 : CollatzResearch.WordTrace tailWord_272213 prefixEnd_272213 46592036467482899695207 := by
  unfold tailWord_272213
  simp only [CollatzResearch.WordTrace]
  refine ⟨9928423762826266124229293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6618949175217510749486195 9928423762826266124229293)
  ·
    refine ⟨3723158911059849796585985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9928423762826266124229293 3723158911059849796585985)
    ·
      refine ⟨2792369183294887347439489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3723158911059849796585985 2792369183294887347439489)
      ·
        refine ⟨2094276887471165510579617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2792369183294887347439489 2094276887471165510579617)
        ·
          refine ⟨1570707665603374132934713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2094276887471165510579617 1570707665603374132934713)
          ·
            refine ⟨1178030749202530599701035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1570707665603374132934713 1178030749202530599701035)
            ·
              refine ⟨1767046123803795899551553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1178030749202530599701035 1767046123803795899551553)
              ·
                refine ⟨1325284592852846924663665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1767046123803795899551553 1325284592852846924663665)
                ·
                  refine ⟨993963444639635193497749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1325284592852846924663665 993963444639635193497749)
                  ·
                    refine ⟨46592036467482899695207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 993963444639635193497749 46592036467482899695207)
                    ·
                      rfl

theorem cell23_272213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_272213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272213 prefixEnd_272213 := by exact prefixLift 272213
  have htrace : WordTrace (prefixWord ++ tailWord_272213) baseStart_272213 baseEnd_272213 := by
    simpa [prefixWord, tailWord_272213, baseEnd_272213] using wordTrace_append hprefix tailTrace_272213
  have hstable : (prefixWord ++ tailWord_272213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272213).length < 2 ^ (prefixWord ++ tailWord_272213).sum := by decide
  have hdescent : baseEnd_272213 < baseStart_272213 := by decide
  rcases family_descends (prefixWord ++ tailWord_272213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272237 : List Nat := [1, 5, 1, 1, 1, 1, 5, 1, 1, 4, 2]
def baseStart_272237 : Nat := 118140960795 + 272237 * 2 ^ 59
def prefixEnd_272237 : Nat := 4983230072969 + 3 ^ 40 * 272237 * 2
def baseEnd_272237 : Nat := 139788432938156605185511

theorem tailTrace_272237 : CollatzResearch.WordTrace tailWord_272237 prefixEnd_272237 139788432938156605185511 := by
  unfold tailWord_272237
  simp only [CollatzResearch.WordTrace]
  refine ⟨9929299114739318223102965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6619532743159545482068643 9929299114739318223102965)
  ·
    refine ⟨930871792006811083415903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9929299114739318223102965 930871792006811083415903)
    ·
      refine ⟨1396307688010216625123855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 930871792006811083415903 1396307688010216625123855)
      ·
        refine ⟨2094461532015324937685783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1396307688010216625123855 2094461532015324937685783)
        ·
          refine ⟨3141692298022987406528675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2094461532015324937685783 3141692298022987406528675)
          ·
            refine ⟨4712538447034481109793013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3141692298022987406528675 4712538447034481109793013)
            ·
              refine ⟨441800479409482604043095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4712538447034481109793013 441800479409482604043095)
              ·
                refine ⟨662700719114223906064643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 441800479409482604043095 662700719114223906064643)
                ·
                  refine ⟨994051078671335859096965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 662700719114223906064643 994051078671335859096965)
                  ·
                    refine ⟨186384577250875473580681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 994051078671335859096965 186384577250875473580681)
                    ·
                      refine ⟨139788432938156605185511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 186384577250875473580681 139788432938156605185511)
                      ·
                        rfl

theorem cell23_272237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_272237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272237 prefixEnd_272237 := by exact prefixLift 272237
  have htrace : WordTrace (prefixWord ++ tailWord_272237) baseStart_272237 baseEnd_272237 := by
    simpa [prefixWord, tailWord_272237, baseEnd_272237] using wordTrace_append hprefix tailTrace_272237
  have hstable : (prefixWord ++ tailWord_272237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272237).length < 2 ^ (prefixWord ++ tailWord_272237).sum := by decide
  have hdescent : baseEnd_272237 < baseStart_272237 := by decide
  rcases family_descends (prefixWord ++ tailWord_272237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272257 : List Nat := [1, 2, 4, 4, 1, 1, 1, 1, 2, 1, 5]
def baseStart_272257 : Nat := 118140960795 + 272257 * 2 ^ 59
def prefixEnd_272257 : Nat := 4983230072969 + 3 ^ 40 * 272257 * 2
def baseEnd_272257 : Nat := 139798702551246526935419

theorem tailTrace_272257 : CollatzResearch.WordTrace tailWord_272257 prefixEnd_272257 139798702551246526935419 := by
  unfold tailWord_272257
  simp only [CollatzResearch.WordTrace]
  refine ⟨9930028574666861638831025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6620019049777907759220683 9930028574666861638831025)
  ·
    refine ⟨7447521431000146229123269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9930028574666861638831025 7447521431000146229123269)
    ·
      refine ⟨1396410268312527417960613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7447521431000146229123269 1396410268312527417960613)
      ·
        refine ⟨261826925308598890867615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1396410268312527417960613 261826925308598890867615)
        ·
          refine ⟨392740387962898336301423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261826925308598890867615 392740387962898336301423)
          ·
            refine ⟨589110581944347504452135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392740387962898336301423 589110581944347504452135)
            ·
              refine ⟨883665872916521256678203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 589110581944347504452135 883665872916521256678203)
              ·
                refine ⟨1325498809374781885017305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 883665872916521256678203 1325498809374781885017305)
                ·
                  refine ⟨994124107031086413762979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1325498809374781885017305 994124107031086413762979)
                  ·
                    refine ⟨1491186160546629620644469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 994124107031086413762979 1491186160546629620644469)
                    ·
                      refine ⟨139798702551246526935419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1491186160546629620644469 139798702551246526935419)
                      ·
                        rfl

theorem cell23_272257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_272257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272257 prefixEnd_272257 := by exact prefixLift 272257
  have htrace : WordTrace (prefixWord ++ tailWord_272257) baseStart_272257 baseEnd_272257 := by
    simpa [prefixWord, tailWord_272257, baseEnd_272257] using wordTrace_append hprefix tailTrace_272257
  have hstable : (prefixWord ++ tailWord_272257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272257).length < 2 ^ (prefixWord ++ tailWord_272257).sum := by decide
  have hdescent : baseEnd_272257 < baseStart_272257 := by decide
  rcases family_descends (prefixWord ++ tailWord_272257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272273 : List Nat := [1, 2, 2, 1, 1, 1, 5, 1, 4, 5]
def baseStart_272273 : Nat := 118140960795 + 272273 * 2 ^ 59
def prefixEnd_272273 : Nat := 4983230072969 + 3 ^ 40 * 272273 * 2
def baseEnd_272273 : Nat := 46602306080572821445115

theorem tailTrace_272273 : CollatzResearch.WordTrace tailWord_272273 prefixEnd_272273 46602306080572821445115 := by
  unfold tailWord_272273
  simp only [CollatzResearch.WordTrace]
  refine ⟨9930612142608896371413473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6620408095072597580942315 9930612142608896371413473)
  ·
    refine ⟨7447959106956672278560105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9930612142608896371413473 7447959106956672278560105)
    ·
      refine ⟨5585969330217504208920079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7447959106956672278560105 5585969330217504208920079)
      ·
        refine ⟨8378953995326256313380119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5585969330217504208920079 8378953995326256313380119)
        ·
          refine ⟨12568430992989384470070179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8378953995326256313380119 12568430992989384470070179)
          ·
            refine ⟨18852646489484076705105269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12568430992989384470070179 18852646489484076705105269)
            ·
              refine ⟨1767435608389132191103619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18852646489484076705105269 1767435608389132191103619)
              ·
                refine ⟨2651153412583698286655429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1767435608389132191103619 2651153412583698286655429)
                ·
                  refine ⟨497091264859443428747893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2651153412583698286655429 497091264859443428747893)
                  ·
                    refine ⟨46602306080572821445115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 497091264859443428747893 46602306080572821445115)
                    ·
                      rfl

theorem cell23_272273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 5].length) (baseStart_272273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272273 prefixEnd_272273 := by exact prefixLift 272273
  have htrace : WordTrace (prefixWord ++ tailWord_272273) baseStart_272273 baseEnd_272273 := by
    simpa [prefixWord, tailWord_272273, baseEnd_272273] using wordTrace_append hprefix tailTrace_272273
  have hstable : (prefixWord ++ tailWord_272273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272273).length < 2 ^ (prefixWord ++ tailWord_272273).sum := by decide
  have hdescent : baseEnd_272273 < baseStart_272273 := by decide
  rcases family_descends (prefixWord ++ tailWord_272273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272277 : List Nat := [1, 3, 2, 1, 1, 3, 5, 2, 5]
def baseStart_272277 : Nat := 118140960795 + 272277 * 2 ^ 59
def prefixEnd_272277 : Nat := 4983230072969 + 3 ^ 40 * 272277 * 2
def baseEnd_272277 : Nat := 15534330240481827631703

theorem tailTrace_272277 : CollatzResearch.WordTrace tailWord_272277 prefixEnd_272277 15534330240481827631703 := by
  unfold tailWord_272277
  simp only [CollatzResearch.WordTrace]
  refine ⟨9930758034594405054559085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6620505356396270036372723 9930758034594405054559085)
  ·
    refine ⟨3724034262972901895459657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9930758034594405054559085 3724034262972901895459657)
    ·
      refine ⟨2793025697229676421594743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3724034262972901895459657 2793025697229676421594743)
      ·
        refine ⟨4189538545844514632392115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2793025697229676421594743 4189538545844514632392115)
        ·
          refine ⟨6284307818766771948588173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4189538545844514632392115 6284307818766771948588173)
          ·
            refine ⟨2356615432037539480720565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6284307818766771948588173 2356615432037539480720565)
            ·
              refine ⟨220932696753519326317553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2356615432037539480720565 220932696753519326317553)
              ·
                refine ⟨165699522565139494738165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 220932696753519326317553 165699522565139494738165)
                ·
                  refine ⟨15534330240481827631703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 165699522565139494738165 15534330240481827631703)
                  ·
                    rfl

theorem cell23_272277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 2, 5].length) (baseStart_272277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272277 prefixEnd_272277 := by exact prefixLift 272277
  have htrace : WordTrace (prefixWord ++ tailWord_272277) baseStart_272277 baseEnd_272277 := by
    simpa [prefixWord, tailWord_272277, baseEnd_272277] using wordTrace_append hprefix tailTrace_272277
  have hstable : (prefixWord ++ tailWord_272277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272277).length < 2 ^ (prefixWord ++ tailWord_272277).sum := by decide
  have hdescent : baseEnd_272277 < baseStart_272277 := by decide
  rcases family_descends (prefixWord ++ tailWord_272277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272293 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 3, 3, 4]
def baseStart_272293 : Nat := 118140960795 + 272293 * 2 ^ 59
def prefixEnd_272293 : Nat := 4983230072969 + 3 ^ 40 * 272293 * 2
def baseEnd_272293 : Nat := 139817187854808386085253

theorem tailTrace_272293 : CollatzResearch.WordTrace tailWord_272293 prefixEnd_272293 139817187854808386085253 := by
  unfold tailWord_272293
  simp only [CollatzResearch.WordTrace]
  refine ⟨9931341602536439787141533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6620894401690959858094355 9931341602536439787141533)
  ·
    refine ⟨3724253100951164920178075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9931341602536439787141533 3724253100951164920178075)
    ·
      refine ⟨5586379651426747380267113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3724253100951164920178075 5586379651426747380267113)
      ·
        refine ⟨4189784738570060535200335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5586379651426747380267113 4189784738570060535200335)
        ·
          refine ⟨6284677107855090802800503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4189784738570060535200335 6284677107855090802800503)
          ·
            refine ⟨9427015661782636204200755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6284677107855090802800503 9427015661782636204200755)
            ·
              refine ⟨14140523492673954306301133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9427015661782636204200755 14140523492673954306301133)
              ·
                refine ⟨5302696309752732864862925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14140523492673954306301133 5302696309752732864862925)
                ·
                  refine ⟨1988511116157274824323597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5302696309752732864862925 1988511116157274824323597)
                  ·
                    refine ⟨745691668558978059121349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1988511116157274824323597 745691668558978059121349)
                    ·
                      refine ⟨139817187854808386085253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 745691668558978059121349 139817187854808386085253)
                      ·
                        rfl

theorem cell23_272293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_272293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272293 prefixEnd_272293 := by exact prefixLift 272293
  have htrace : WordTrace (prefixWord ++ tailWord_272293) baseStart_272293 baseEnd_272293 := by
    simpa [prefixWord, tailWord_272293, baseEnd_272293] using wordTrace_append hprefix tailTrace_272293
  have hstable : (prefixWord ++ tailWord_272293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272293).length < 2 ^ (prefixWord ++ tailWord_272293).sum := by decide
  have hdescent : baseEnd_272293 < baseStart_272293 := by decide
  rcases family_descends (prefixWord ++ tailWord_272293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272387 : List Nat := [1, 1, 1, 3, 2, 1, 1, 6, 2, 3, 2]
def baseStart_272387 : Nat := 118140960795 + 272387 * 2 ^ 59
def prefixEnd_272387 : Nat := 4983230072969 + 3 ^ 40 * 272387 * 2
def baseEnd_272387 : Nat := 139865455036331018309821

theorem tailTrace_272387 : CollatzResearch.WordTrace tailWord_272387 prefixEnd_272387 139865455036331018309821 := by
  unfold tailWord_272387
  simp only [CollatzResearch.WordTrace]
  refine ⟨9934770064195893841063415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6623180042797262560708943 9934770064195893841063415)
  ·
    refine ⟨14902155096293840761595123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9934770064195893841063415 14902155096293840761595123)
    ·
      refine ⟨22353232644440761142392685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14902155096293840761595123 22353232644440761142392685)
      ·
        refine ⟨8382462241665285428397257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22353232644440761142392685 8382462241665285428397257)
        ·
          refine ⟨6286846681248964071297943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8382462241665285428397257 6286846681248964071297943)
          ·
            refine ⟨9430270021873446106946915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6286846681248964071297943 9430270021873446106946915)
            ·
              refine ⟨14145405032810169160420373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9430270021873446106946915 14145405032810169160420373)
              ·
                refine ⟨663065860912976679394705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14145405032810169160420373 663065860912976679394705)
                ·
                  refine ⟨497299395684732509546029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 663065860912976679394705 497299395684732509546029)
                  ·
                    refine ⟨186487273381774691079761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 497299395684732509546029 186487273381774691079761)
                    ·
                      refine ⟨139865455036331018309821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 186487273381774691079761 139865455036331018309821)
                      ·
                        rfl

theorem cell23_272387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 3, 2].length) (baseStart_272387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272387 prefixEnd_272387 := by exact prefixLift 272387
  have htrace : WordTrace (prefixWord ++ tailWord_272387) baseStart_272387 baseEnd_272387 := by
    simpa [prefixWord, tailWord_272387, baseEnd_272387] using wordTrace_append hprefix tailTrace_272387
  have hstable : (prefixWord ++ tailWord_272387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272387).length < 2 ^ (prefixWord ++ tailWord_272387).sum := by decide
  have hdescent : baseEnd_272387 < baseStart_272387 := by decide
  rcases family_descends (prefixWord ++ tailWord_272387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272393 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 2, 10]
def baseStart_272393 : Nat := 118140960795 + 272393 * 2 ^ 59
def prefixEnd_272393 : Nat := 4983230072969 + 3 ^ 40 * 272393 * 2
def baseEnd_272393 : Nat := 46622845306752664944931

theorem tailTrace_272393 : CollatzResearch.WordTrace tailWord_272393 prefixEnd_272393 46622845306752664944931 := by
  unfold tailWord_272393
  simp only [CollatzResearch.WordTrace]
  refine ⟨9934988902174156865781833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6623325934782771243854555 9934988902174156865781833)
  ·
    refine ⟨7451241676630617649336375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9934988902174156865781833 7451241676630617649336375)
    ·
      refine ⟨11176862514945926474004563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7451241676630617649336375 11176862514945926474004563)
      ·
        refine ⟨16765293772418889711006845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11176862514945926474004563 16765293772418889711006845)
        ·
          refine ⟨6286985164657083641627567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16765293772418889711006845 6286985164657083641627567)
          ·
            refine ⟨9430477746985625462441351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6286985164657083641627567 9430477746985625462441351)
            ·
              refine ⟨14145716620478438193662027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9430477746985625462441351 14145716620478438193662027)
              ·
                refine ⟨21218574930717657290493041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14145716620478438193662027 21218574930717657290493041)
                ·
                  refine ⟨15913931198038242967869781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21218574930717657290493041 15913931198038242967869781)
                  ·
                    refine ⟨46622845306752664944931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 15913931198038242967869781 46622845306752664944931)
                    ·
                      rfl

theorem cell23_272393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 10].length) (baseStart_272393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272393 prefixEnd_272393 := by exact prefixLift 272393
  have htrace : WordTrace (prefixWord ++ tailWord_272393) baseStart_272393 baseEnd_272393 := by
    simpa [prefixWord, tailWord_272393, baseEnd_272393] using wordTrace_append hprefix tailTrace_272393
  have hstable : (prefixWord ++ tailWord_272393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272393).length < 2 ^ (prefixWord ++ tailWord_272393).sum := by decide
  have hdescent : baseEnd_272393 < baseStart_272393 := by decide
  rcases family_descends (prefixWord ++ tailWord_272393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272454 : List Nat := [6, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_272454 : Nat := 118140960795 + 272454 * 2 ^ 59
def prefixEnd_272454 : Nat := 4983230072969 + 3 ^ 40 * 272454 * 2
def baseEnd_272454 : Nat := 139899858240182256172013

theorem tailTrace_272454 : CollatzResearch.WordTrace tailWord_272454 prefixEnd_272454 139899858240182256172013 := by
  unfold tailWord_272454
  simp only [CollatzResearch.WordTrace]
  refine ⟨310537929842286383867263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6624809169968776189168277 310537929842286383867263)
  ·
    refine ⟨465806894763429575800895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 310537929842286383867263 465806894763429575800895)
    ·
      refine ⟨698710342145144363701343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 465806894763429575800895 698710342145144363701343)
      ·
        refine ⟨1048065513217716545552015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 698710342145144363701343 1048065513217716545552015)
        ·
          refine ⟨1572098269826574818328023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1048065513217716545552015 1572098269826574818328023)
          ·
            refine ⟨2358147404739862227492035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1572098269826574818328023 2358147404739862227492035)
            ·
              refine ⟨3537221107109793341238053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2358147404739862227492035 3537221107109793341238053)
              ·
                refine ⟨663228957583086251482135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3537221107109793341238053 663228957583086251482135)
                ·
                  refine ⟨994843436374629377223203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 663228957583086251482135 994843436374629377223203)
                  ·
                    refine ⟨1492265154561944065834805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 994843436374629377223203 1492265154561944065834805)
                    ·
                      refine ⟨139899858240182256172013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1492265154561944065834805 139899858240182256172013)
                      ·
                        rfl

theorem cell23_272454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_272454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272454 prefixEnd_272454 := by exact prefixLift 272454
  have htrace : WordTrace (prefixWord ++ tailWord_272454) baseStart_272454 baseEnd_272454 := by
    simpa [prefixWord, tailWord_272454, baseEnd_272454] using wordTrace_append hprefix tailTrace_272454
  have hstable : (prefixWord ++ tailWord_272454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272454).length < 2 ^ (prefixWord ++ tailWord_272454).sum := by decide
  have hdescent : baseEnd_272454 < baseStart_272454 := by decide
  rcases family_descends (prefixWord ++ tailWord_272454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272502 : List Nat := [5, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2]
def baseStart_272502 : Nat := 118140960795 + 272502 * 2 ^ 59
def prefixEnd_272502 : Nat := 4983230072969 + 3 ^ 40 * 272502 * 2
def baseEnd_272502 : Nat := 139924505311598068371793

theorem tailTrace_272502 : CollatzResearch.WordTrace tailWord_272502 prefixEnd_272502 139924505311598068371793 := by
  unfold tailWord_272502
  simp only [CollatzResearch.WordTrace]
  refine ⟨621185278673704280093735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6625976305852845654333173 621185278673704280093735)
  ·
    refine ⟨931777918010556420140603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 621185278673704280093735 931777918010556420140603)
    ·
      refine ⟨1397666877015834630210905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 931777918010556420140603 1397666877015834630210905)
      ·
        refine ⟨1048250157761875972658179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1397666877015834630210905 1048250157761875972658179)
        ·
          refine ⟨1572375236642813958987269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1048250157761875972658179 1572375236642813958987269)
          ·
            refine ⟨294820356870527617310113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1572375236642813958987269 294820356870527617310113)
            ·
              refine ⟨221115267652895712982585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 294820356870527617310113 221115267652895712982585)
              ·
                refine ⟨165836450739671784736939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221115267652895712982585 165836450739671784736939)
                ·
                  refine ⟨248754676109507677105409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 165836450739671784736939 248754676109507677105409)
                  ·
                    refine ⟨186566007082130757829057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 248754676109507677105409 186566007082130757829057)
                    ·
                      refine ⟨139924505311598068371793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 186566007082130757829057 139924505311598068371793)
                      ·
                        rfl

theorem cell23_272502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_272502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272502 prefixEnd_272502 := by exact prefixLift 272502
  have htrace : WordTrace (prefixWord ++ tailWord_272502) baseStart_272502 baseEnd_272502 := by
    simpa [prefixWord, tailWord_272502, baseEnd_272502] using wordTrace_append hprefix tailTrace_272502
  have hstable : (prefixWord ++ tailWord_272502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272502).length < 2 ^ (prefixWord ++ tailWord_272502).sum := by decide
  have hdescent : baseEnd_272502 < baseStart_272502 := by decide
  rcases family_descends (prefixWord ++ tailWord_272502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272517 : List Nat := [1, 3, 1, 1, 5, 2, 1, 1, 2, 6]
def baseStart_272517 : Nat := 118140960795 + 272517 * 2 ^ 59
def prefixEnd_272517 : Nat := 4983230072969 + 3 ^ 40 * 272517 * 2
def baseEnd_272517 : Nat := 46644069173805169894741

theorem tailTrace_272517 : CollatzResearch.WordTrace tailWord_272517 prefixEnd_272517 46644069173805169894741 := by
  unfold tailWord_272517
  simp only [CollatzResearch.WordTrace]
  refine ⟨9939511553724926043295805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6626341035816617362197203 9939511553724926043295805)
  ·
    refine ⟨3727316832646847266235927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9939511553724926043295805 3727316832646847266235927)
    ·
      refine ⟨5590975248970270899353891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3727316832646847266235927 5590975248970270899353891)
      ·
        refine ⟨8386462873455406349030837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5590975248970270899353891 8386462873455406349030837)
        ·
          refine ⟨786230894386444345221641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8386462873455406349030837 786230894386444345221641)
          ·
            refine ⟨589673170789833258916231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 786230894386444345221641 589673170789833258916231)
            ·
              refine ⟨884509756184749888374347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 589673170789833258916231 884509756184749888374347)
              ·
                refine ⟨1326764634277124832561521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 884509756184749888374347 1326764634277124832561521)
                ·
                  refine ⟨995073475707843624421141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1326764634277124832561521 995073475707843624421141)
                  ·
                    refine ⟨46644069173805169894741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 995073475707843624421141 46644069173805169894741)
                    ·
                      rfl

theorem cell23_272517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 6].length) (baseStart_272517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272517 prefixEnd_272517 := by exact prefixLift 272517
  have htrace : WordTrace (prefixWord ++ tailWord_272517) baseStart_272517 baseEnd_272517 := by
    simpa [prefixWord, tailWord_272517, baseEnd_272517] using wordTrace_append hprefix tailTrace_272517
  have hstable : (prefixWord ++ tailWord_272517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272517).length < 2 ^ (prefixWord ++ tailWord_272517).sum := by decide
  have hdescent : baseEnd_272517 < baseStart_272517 := by decide
  rcases family_descends (prefixWord ++ tailWord_272517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272524 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 8, 2, 2]
def baseStart_272524 : Nat := 118140960795 + 272524 * 2 ^ 59
def prefixEnd_272524 : Nat := 4983230072969 + 3 ^ 40 * 272524 * 2
def baseEnd_272524 : Nat := 139935801885996982296691

theorem tailTrace_272524 : CollatzResearch.WordTrace tailWord_272524 prefixEnd_272524 139935801885996982296691 := by
  unfold tailWord_272524
  simp only [CollatzResearch.WordTrace]
  refine ⟨4969883432349783119400313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6626511243133044159200417 4969883432349783119400313)
  ·
    refine ⟨3727412574262337339550235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4969883432349783119400313 3727412574262337339550235)
    ·
      refine ⟨5591118861393506009325353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3727412574262337339550235 5591118861393506009325353)
      ·
        refine ⟨4193339146045129506994015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5591118861393506009325353 4193339146045129506994015)
        ·
          refine ⟨6290008719067694260491023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4193339146045129506994015 6290008719067694260491023)
          ·
            refine ⟨9435013078601541390736535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6290008719067694260491023 9435013078601541390736535)
            ·
              refine ⟨14152519617902312086104803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9435013078601541390736535 14152519617902312086104803)
              ·
                refine ⟨21228779426853468129157205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14152519617902312086104803 21228779426853468129157205)
                ·
                  refine ⟨248774758908439079638561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21228779426853468129157205 248774758908439079638561)
                  ·
                    refine ⟨186581069181329309728921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 248774758908439079638561 186581069181329309728921)
                    ·
                      refine ⟨139935801885996982296691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 186581069181329309728921 139935801885996982296691)
                      ·
                        rfl

theorem cell23_272524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 8, 2, 2].length) (baseStart_272524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272524 prefixEnd_272524 := by exact prefixLift 272524
  have htrace : WordTrace (prefixWord ++ tailWord_272524) baseStart_272524 baseEnd_272524 := by
    simpa [prefixWord, tailWord_272524, baseEnd_272524] using wordTrace_append hprefix tailTrace_272524
  have hstable : (prefixWord ++ tailWord_272524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272524).length < 2 ^ (prefixWord ++ tailWord_272524).sum := by decide
  have hdescent : baseEnd_272524 < baseStart_272524 := by decide
  rcases family_descends (prefixWord ++ tailWord_272524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272560 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 5, 7]
def baseStart_272560 : Nat := 118140960795 + 272560 * 2 ^ 59
def prefixEnd_272560 : Nat := 4983230072969 + 3 ^ 40 * 272560 * 2
def baseEnd_272560 : Nat := 46651429063186280482175

theorem tailTrace_272560 : CollatzResearch.WordTrace tailWord_272560 prefixEnd_272560 46651429063186280482175 := by
  unfold tailWord_272560
  simp only [CollatzResearch.WordTrace]
  refine ⟨4970539946284572193555567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6627386595046096258074089 4970539946284572193555567)
  ·
    refine ⟨7455809919426858290333351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4970539946284572193555567 7455809919426858290333351)
    ·
      refine ⟨11183714879140287435500027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7455809919426858290333351 11183714879140287435500027)
      ·
        refine ⟨16775572318710431153250041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11183714879140287435500027 16775572318710431153250041)
        ·
          refine ⟨12581679239032823364937531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16775572318710431153250041 12581679239032823364937531)
          ·
            refine ⟨18872518858549235047406297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12581679239032823364937531 18872518858549235047406297)
            ·
              refine ⟨14154389143911926285554723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18872518858549235047406297 14154389143911926285554723)
              ·
                refine ⟨21231583715867889428332085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14154389143911926285554723 21231583715867889428332085)
                ·
                  refine ⟨1990460973362614633906133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21231583715867889428332085 1990460973362614633906133)
                  ·
                    refine ⟨46651429063186280482175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1990460973362614633906133 46651429063186280482175)
                    ·
                      rfl

theorem cell23_272560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 5, 7].length) (baseStart_272560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272560 prefixEnd_272560 := by exact prefixLift 272560
  have htrace : WordTrace (prefixWord ++ tailWord_272560) baseStart_272560 baseEnd_272560 := by
    simpa [prefixWord, tailWord_272560, baseEnd_272560] using wordTrace_append hprefix tailTrace_272560
  have hstable : (prefixWord ++ tailWord_272560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272560).length < 2 ^ (prefixWord ++ tailWord_272560).sum := by decide
  have hdescent : baseEnd_272560 < baseStart_272560 := by decide
  rcases family_descends (prefixWord ++ tailWord_272560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272598 : List Nat := [5, 2, 1, 2, 1, 1, 3, 3, 5]
def baseStart_272598 : Nat := 118140960795 + 272598 * 2 ^ 59
def prefixEnd_272598 : Nat := 4983230072969 + 3 ^ 40 * 272598 * 2
def baseEnd_272598 : Nat := 15552644383825521419039

theorem tailTrace_272598 : CollatzResearch.WordTrace tailWord_272598 prefixEnd_272598 15552644383825521419039 := by
  unfold tailWord_272598
  simp only [CollatzResearch.WordTrace]
  refine ⟨621404116651967304812153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6628310577620984584662965 621404116651967304812153)
  ·
    refine ⟨466053087488975478609115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 621404116651967304812153 466053087488975478609115)
    ·
      refine ⟨699079631233463217913673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 466053087488975478609115 699079631233463217913673)
      ·
        refine ⟨524309723425097413435255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 699079631233463217913673 524309723425097413435255)
        ·
          refine ⟨786464585137646120152883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 524309723425097413435255 786464585137646120152883)
          ·
            refine ⟨1179696877706469180229325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 786464585137646120152883 1179696877706469180229325)
            ·
              refine ⟨442386329139925942585997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1179696877706469180229325 442386329139925942585997)
              ·
                refine ⟨165894873427472228469749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 442386329139925942585997 165894873427472228469749)
                ·
                  refine ⟨15552644383825521419039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 165894873427472228469749 15552644383825521419039)
                  ·
                    rfl

theorem cell23_272598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_272598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272598 prefixEnd_272598 := by exact prefixLift 272598
  have htrace : WordTrace (prefixWord ++ tailWord_272598) baseStart_272598 baseEnd_272598 := by
    simpa [prefixWord, tailWord_272598, baseEnd_272598] using wordTrace_append hprefix tailTrace_272598
  have hstable : (prefixWord ++ tailWord_272598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272598).length < 2 ^ (prefixWord ++ tailWord_272598).sum := by decide
  have hdescent : baseEnd_272598 < baseStart_272598 := by decide
  rcases family_descends (prefixWord ++ tailWord_272598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272611 : List Nat := [1, 1, 1, 8, 1, 1, 1, 2, 2, 5]
def baseStart_272611 : Nat := 118140960795 + 272611 * 2 ^ 59
def prefixEnd_272611 : Nat := 4983230072969 + 3 ^ 40 * 272611 * 2
def baseEnd_272611 : Nat := 46660158234312713969597

theorem tailTrace_272611 : CollatzResearch.WordTrace tailWord_272611 prefixEnd_272611 46660158234312713969597 := by
  unfold tailWord_272611
  simp only [CollatzResearch.WordTrace]
  refine ⟨9942940015384380097217687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6628626676922920064811791 9942940015384380097217687)
  ·
    refine ⟨14914410023076570145826531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9942940015384380097217687 14914410023076570145826531)
    ·
      refine ⟨22371615034614855218739797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14914410023076570145826531 22371615034614855218739797)
      ·
        refine ⟨262167363686892834594607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 22371615034614855218739797 262167363686892834594607)
        ·
          refine ⟨393251045530339251891911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262167363686892834594607 393251045530339251891911)
          ·
            refine ⟨589876568295508877837867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 393251045530339251891911 589876568295508877837867)
            ·
              refine ⟨884814852443263316756801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 589876568295508877837867 884814852443263316756801)
              ·
                refine ⟨663611139332447487567601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 884814852443263316756801 663611139332447487567601)
                ·
                  refine ⟨497708354499335615675701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 663611139332447487567601 497708354499335615675701)
                  ·
                    refine ⟨46660158234312713969597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 497708354499335615675701 46660158234312713969597)
                    ·
                      rfl

theorem cell23_272611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 5].length) (baseStart_272611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272611 prefixEnd_272611 := by exact prefixLift 272611
  have htrace : WordTrace (prefixWord ++ tailWord_272611) baseStart_272611 baseEnd_272611 := by
    simpa [prefixWord, tailWord_272611, baseEnd_272611] using wordTrace_append hprefix tailTrace_272611
  have hstable : (prefixWord ++ tailWord_272611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272611).length < 2 ^ (prefixWord ++ tailWord_272611).sum := by decide
  have hdescent : baseEnd_272611 < baseStart_272611 := by decide
  rcases family_descends (prefixWord ++ tailWord_272611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272704 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 1, 8, 2]
def baseStart_272704 : Nat := 118140960795 + 272704 * 2 ^ 59
def prefixEnd_272704 : Nat := 4983230072969 + 3 ^ 40 * 272704 * 2
def baseEnd_272704 : Nat := 140028228403806278045863

theorem tailTrace_272704 : CollatzResearch.WordTrace tailWord_272704 prefixEnd_272704 140028228403806278045863 := by
  unfold tailWord_272704
  simp only [CollatzResearch.WordTrace]
  refine ⟨4973166002023728490176583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6630888002698304653568777 4973166002023728490176583)
  ·
    refine ⟨7459749003035592735264875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4973166002023728490176583 7459749003035592735264875)
    ·
      refine ⟨11189623504553389102897313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7459749003035592735264875 11189623504553389102897313)
      ·
        refine ⟨8392217628415041827172985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11189623504553389102897313 8392217628415041827172985)
        ·
          refine ⟨6294163221311281370379739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8392217628415041827172985 6294163221311281370379739)
          ·
            refine ⟨9441244831966922055569609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6294163221311281370379739 9441244831966922055569609)
            ·
              refine ⟨7080933623975191541677207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9441244831966922055569609 7080933623975191541677207)
              ·
                refine ⟨10621400435962787312515811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7080933623975191541677207 10621400435962787312515811)
                ·
                  refine ⟨15932100653944180968773717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10621400435962787312515811 15932100653944180968773717)
                  ·
                    refine ⟨186704304538408370727817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15932100653944180968773717 186704304538408370727817)
                    ·
                      refine ⟨140028228403806278045863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 186704304538408370727817 140028228403806278045863)
                      ·
                        rfl

theorem cell23_272704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 8, 2].length) (baseStart_272704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272704 prefixEnd_272704 := by exact prefixLift 272704
  have htrace : WordTrace (prefixWord ++ tailWord_272704) baseStart_272704 baseEnd_272704 := by
    simpa [prefixWord, tailWord_272704, baseEnd_272704] using wordTrace_append hprefix tailTrace_272704
  have hstable : (prefixWord ++ tailWord_272704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272704).length < 2 ^ (prefixWord ++ tailWord_272704).sum := by decide
  have hdescent : baseEnd_272704 < baseStart_272704 := by decide
  rcases family_descends (prefixWord ++ tailWord_272704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272721 : List Nat := [1, 2, 2, 1, 4, 3, 1, 3, 1, 1, 4]
def baseStart_272721 : Nat := 118140960795 + 272721 * 2 ^ 59
def prefixEnd_272721 : Nat := 4983230072969 + 3 ^ 40 * 272721 * 2
def baseEnd_272721 : Nat := 140036957574932711533285

theorem tailTrace_272721 : CollatzResearch.WordTrace tailWord_272721 prefixEnd_272721 140036957574932711533285 := by
  unfold tailWord_272721
  simp only [CollatzResearch.WordTrace]
  refine ⟨9946952044985868883722017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6631301363323912589148011 9946952044985868883722017)
  ·
    refine ⟨7460214033739401662791513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9946952044985868883722017 7460214033739401662791513)
    ·
      refine ⟨5595160525304551247093635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7460214033739401662791513 5595160525304551247093635)
      ·
        refine ⟨8392740787956826870640453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5595160525304551247093635 8392740787956826870640453)
        ·
          refine ⟨1573638897741905038245085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8392740787956826870640453 1573638897741905038245085)
          ·
            refine ⟨590114586653214389341907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1573638897741905038245085 590114586653214389341907)
            ·
              refine ⟨885171879979821584012861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 590114586653214389341907 885171879979821584012861)
              ·
                refine ⟨331939454992433094004823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 885171879979821584012861 331939454992433094004823)
                ·
                  refine ⟨497909182488649641007235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 331939454992433094004823 497909182488649641007235)
                  ·
                    refine ⟨746863773732974461510853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 497909182488649641007235 746863773732974461510853)
                    ·
                      refine ⟨140036957574932711533285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 746863773732974461510853 140036957574932711533285)
                      ·
                        rfl

theorem cell23_272721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 1, 4].length) (baseStart_272721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272721 prefixEnd_272721 := by exact prefixLift 272721
  have htrace : WordTrace (prefixWord ++ tailWord_272721) baseStart_272721 baseEnd_272721 := by
    simpa [prefixWord, tailWord_272721, baseEnd_272721] using wordTrace_append hprefix tailTrace_272721
  have hstable : (prefixWord ++ tailWord_272721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272721).length < 2 ^ (prefixWord ++ tailWord_272721).sum := by decide
  have hdescent : baseEnd_272721 < baseStart_272721 := by decide
  rcases family_descends (prefixWord ++ tailWord_272721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272727 : List Nat := [1, 1, 3, 2, 3, 1, 12]
def baseStart_272727 : Nat := 118140960795 + 272727 * 2 ^ 59
def prefixEnd_272727 : Nat := 4983230072969 + 3 ^ 40 * 272727 * 2
def baseEnd_272727 : Nat := 1728889363689625778497

theorem tailTrace_272727 : CollatzResearch.WordTrace tailWord_272727 prefixEnd_272727 1728889363689625778497 := by
  unfold tailWord_272727
  simp only [CollatzResearch.WordTrace]
  refine ⟨9947170882964131908440435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6631447255309421272293623 9947170882964131908440435)
  ·
    refine ⟨14920756324446197862660653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9947170882964131908440435 14920756324446197862660653)
    ·
      refine ⟨5595283621667324198497745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14920756324446197862660653 5595283621667324198497745)
      ·
        refine ⟨4196462716250493148873309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5595283621667324198497745 4196462716250493148873309)
        ·
          refine ⟨1573673518593934930827491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4196462716250493148873309 1573673518593934930827491)
          ·
            refine ⟨2360510277890902396241237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1573673518593934930827491 2360510277890902396241237)
            ·
              refine ⟨1728889363689625778497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 2360510277890902396241237 1728889363689625778497)
              ·
                rfl

theorem cell23_272727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 12].length) (baseStart_272727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272727 prefixEnd_272727 := by exact prefixLift 272727
  have htrace : WordTrace (prefixWord ++ tailWord_272727) baseStart_272727 baseEnd_272727 := by
    simpa [prefixWord, tailWord_272727, baseEnd_272727] using wordTrace_append hprefix tailTrace_272727
  have hstable : (prefixWord ++ tailWord_272727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272727).length < 2 ^ (prefixWord ++ tailWord_272727).sum := by decide
  have hdescent : baseEnd_272727 < baseStart_272727 := by decide
  rcases family_descends (prefixWord ++ tailWord_272727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272737 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 1, 4, 7]
def baseStart_272737 : Nat := 118140960795 + 272737 * 2 ^ 59
def prefixEnd_272737 : Nat := 4983230072969 + 3 ^ 40 * 272737 * 2
def baseEnd_272737 : Nat := 140045173265404648933211

theorem tailTrace_272737 : CollatzResearch.WordTrace tailWord_272737 prefixEnd_272737 140045173265404648933211 := by
  unfold tailWord_272737
  simp only [CollatzResearch.WordTrace]
  refine ⟨9947535612927903616304465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6631690408618602410869643 9947535612927903616304465)
  ·
    refine ⟨7460651709695927712228349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9947535612927903616304465 7460651709695927712228349)
    ·
      refine ⟨2797744391135972892085631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7460651709695927712228349 2797744391135972892085631)
      ·
        refine ⟨4196616586703959338128447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2797744391135972892085631 4196616586703959338128447)
        ·
          refine ⟨6294924880055939007192671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4196616586703959338128447 6294924880055939007192671)
          ·
            refine ⟨9442387320083908510789007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6294924880055939007192671 9442387320083908510789007)
            ·
              refine ⟨14163580980125862766183511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9442387320083908510789007 14163580980125862766183511)
              ·
                refine ⟨21245371470188794149275267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14163580980125862766183511 21245371470188794149275267)
                ·
                  refine ⟨31868057205283191223912901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21245371470188794149275267 31868057205283191223912901)
                  ·
                    refine ⟨5975260725990598354483669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31868057205283191223912901 5975260725990598354483669)
                    ·
                      refine ⟨140045173265404648933211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 5975260725990598354483669 140045173265404648933211)
                      ·
                        rfl

theorem cell23_272737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_272737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272737 prefixEnd_272737 := by exact prefixLift 272737
  have htrace : WordTrace (prefixWord ++ tailWord_272737) baseStart_272737 baseEnd_272737 := by
    simpa [prefixWord, tailWord_272737, baseEnd_272737] using wordTrace_append hprefix tailTrace_272737
  have hstable : (prefixWord ++ tailWord_272737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272737).length < 2 ^ (prefixWord ++ tailWord_272737).sum := by decide
  have hdescent : baseEnd_272737 < baseStart_272737 := by decide
  rcases family_descends (prefixWord ++ tailWord_272737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272747 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 6]
def baseStart_272747 : Nat := 118140960795 + 272747 * 2 ^ 59
def prefixEnd_272747 : Nat := 4983230072969 + 3 ^ 40 * 272747 * 2
def baseEnd_272747 : Nat := 140050308071949609808165

theorem tailTrace_272747 : CollatzResearch.WordTrace tailWord_272747 prefixEnd_272747 140050308071949609808165 := by
  unfold tailWord_272747
  simp only [CollatzResearch.WordTrace]
  refine ⟨9947900342891675324168495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6631933561927783549445663 9947900342891675324168495)
  ·
    refine ⟨14921850514337512986252743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9947900342891675324168495 14921850514337512986252743)
    ·
      refine ⟨22382775771506269479379115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14921850514337512986252743 22382775771506269479379115)
      ·
        refine ⟨33574163657259404219068673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22382775771506269479379115 33574163657259404219068673)
        ·
          refine ⟨25180622742944553164301505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33574163657259404219068673 25180622742944553164301505)
          ·
            refine ⟨18885467057208414873226129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25180622742944553164301505 18885467057208414873226129)
            ·
              refine ⟨14164100292906311154919597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18885467057208414873226129 14164100292906311154919597)
              ·
                refine ⟨5311537609839866683094849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14164100292906311154919597 5311537609839866683094849)
                ·
                  refine ⟨3983653207379900012321137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5311537609839866683094849 3983653207379900012321137)
                  ·
                    refine ⟨2987739905534925009240853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3983653207379900012321137 2987739905534925009240853)
                    ·
                      refine ⟨140050308071949609808165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2987739905534925009240853 140050308071949609808165)
                      ·
                        rfl

theorem cell23_272747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 6].length) (baseStart_272747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272747 prefixEnd_272747 := by exact prefixLift 272747
  have htrace : WordTrace (prefixWord ++ tailWord_272747) baseStart_272747 baseEnd_272747 := by
    simpa [prefixWord, tailWord_272747, baseEnd_272747] using wordTrace_append hprefix tailTrace_272747
  have hstable : (prefixWord ++ tailWord_272747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272747).length < 2 ^ (prefixWord ++ tailWord_272747).sum := by decide
  have hdescent : baseEnd_272747 < baseStart_272747 := by decide
  rcases family_descends (prefixWord ++ tailWord_272747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272748 : List Nat := [2, 2, 1, 1, 7, 1, 1, 1, 1, 6]
def baseStart_272748 : Nat := 118140960795 + 272748 * 2 ^ 59
def prefixEnd_272748 : Nat := 4983230072969 + 3 ^ 40 * 272748 * 2
def baseEnd_272748 : Nat := 46683607184201368631887

theorem tailTrace_272748 : CollatzResearch.WordTrace tailWord_272748 prefixEnd_272748 46683607184201368631887 := by
  unfold tailWord_272748
  simp only [CollatzResearch.WordTrace]
  refine ⟨4973968407944026247477449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6631957877258701663303265 4973968407944026247477449)
  ·
    refine ⟨3730476305958019685608087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4973968407944026247477449 3730476305958019685608087)
    ·
      refine ⟨5595714458937029528412131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3730476305958019685608087 5595714458937029528412131)
      ·
        refine ⟨8393571688405544292618197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5595714458937029528412131 8393571688405544292618197)
        ·
          refine ⟨196724336447004944358239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 8393571688405544292618197 196724336447004944358239)
          ·
            refine ⟨295086504670507416537359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196724336447004944358239 295086504670507416537359)
            ·
              refine ⟨442629757005761124806039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295086504670507416537359 442629757005761124806039)
              ·
                refine ⟨663944635508641687209059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 442629757005761124806039 663944635508641687209059)
                ·
                  refine ⟨995916953262962530813589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 663944635508641687209059 995916953262962530813589)
                  ·
                    refine ⟨46683607184201368631887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 995916953262962530813589 46683607184201368631887)
                    ·
                      rfl

theorem cell23_272748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 1, 6].length) (baseStart_272748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272748 prefixEnd_272748 := by exact prefixLift 272748
  have htrace : WordTrace (prefixWord ++ tailWord_272748) baseStart_272748 baseEnd_272748 := by
    simpa [prefixWord, tailWord_272748, baseEnd_272748] using wordTrace_append hprefix tailTrace_272748
  have hstable : (prefixWord ++ tailWord_272748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272748).length < 2 ^ (prefixWord ++ tailWord_272748).sum := by decide
  have hdescent : baseEnd_272748 < baseStart_272748 := by decide
  rcases family_descends (prefixWord ++ tailWord_272748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272778 : List Nat := [3, 1, 2, 5, 2, 1, 9]
def baseStart_272778 : Nat := 118140960795 + 272778 * 2 ^ 59
def prefixEnd_272778 : Nat := 4983230072969 + 3 ^ 40 * 272778 * 2
def baseEnd_272778 : Nat := 1729212666323938129883

theorem tailTrace_272778 : CollatzResearch.WordTrace tailWord_272778 prefixEnd_272778 1729212666323938129883 := by
  unfold tailWord_272778
  simp only [CollatzResearch.WordTrace]
  refine ⟨2487257751444841904636747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6632687337186245079031325 2487257751444841904636747)
  ·
    refine ⟨3730886627167262856955121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2487257751444841904636747 3730886627167262856955121)
    ·
      refine ⟨2798164970375447142716341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3730886627167262856955121 2798164970375447142716341)
      ·
        refine ⟨262327965972698169629657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2798164970375447142716341 262327965972698169629657)
        ·
          refine ⟨196745974479523627222243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 262327965972698169629657 196745974479523627222243)
          ·
            refine ⟨295118961719285440833365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196745974479523627222243 295118961719285440833365)
            ·
              refine ⟨1729212666323938129883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 295118961719285440833365 1729212666323938129883)
              ·
                rfl

theorem cell23_272778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 9].length) (baseStart_272778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272778 prefixEnd_272778 := by exact prefixLift 272778
  have htrace : WordTrace (prefixWord ++ tailWord_272778) baseStart_272778 baseEnd_272778 := by
    simpa [prefixWord, tailWord_272778, baseEnd_272778] using wordTrace_append hprefix tailTrace_272778
  have hstable : (prefixWord ++ tailWord_272778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272778).length < 2 ^ (prefixWord ++ tailWord_272778).sum := by decide
  have hdescent : baseEnd_272778 < baseStart_272778 := by decide
  rcases family_descends (prefixWord ++ tailWord_272778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272804 : List Nat := [2, 3, 1, 2, 1, 1, 2, 3, 2, 6]
def baseStart_272804 : Nat := 118140960795 + 272804 * 2 ^ 59
def prefixEnd_272804 : Nat := 4983230072969 + 3 ^ 40 * 272804 * 2
def baseEnd_272804 : Nat := 46693192156418628931801

theorem tailTrace_272804 : CollatzResearch.WordTrace tailWord_272804 prefixEnd_272804 46693192156418628931801 := by
  unfold tailWord_272804
  simp only [CollatzResearch.WordTrace]
  refine ⟨4974989651842587029496733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6633319535790116039328977 4974989651842587029496733)
  ·
    refine ⟨1865621119440970136061275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4974989651842587029496733 1865621119440970136061275)
    ·
      refine ⟨2798431679161455204091913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1865621119440970136061275 2798431679161455204091913)
      ·
        refine ⟨2098823759371091403068935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2798431679161455204091913 2098823759371091403068935)
        ·
          refine ⟨3148235639056637104603403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2098823759371091403068935 3148235639056637104603403)
          ·
            refine ⟨4722353458584955656905105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3148235639056637104603403 4722353458584955656905105)
            ·
              refine ⟨3541765093938716742678829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4722353458584955656905105 3541765093938716742678829)
              ·
                refine ⟨1328161910227018778504561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3541765093938716742678829 1328161910227018778504561)
                ·
                  refine ⟨996121432670264083878421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1328161910227018778504561 996121432670264083878421)
                  ·
                    refine ⟨46693192156418628931801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 996121432670264083878421 46693192156418628931801)
                    ·
                      rfl

theorem cell23_272804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_272804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272804 prefixEnd_272804 := by exact prefixLift 272804
  have htrace : WordTrace (prefixWord ++ tailWord_272804) baseStart_272804 baseEnd_272804 := by
    simpa [prefixWord, tailWord_272804, baseEnd_272804] using wordTrace_append hprefix tailTrace_272804
  have hstable : (prefixWord ++ tailWord_272804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272804).length < 2 ^ (prefixWord ++ tailWord_272804).sum := by decide
  have hdescent : baseEnd_272804 < baseStart_272804 := by decide
  rcases family_descends (prefixWord ++ tailWord_272804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272824 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 4, 2, 4]
def baseStart_272824 : Nat := 118140960795 + 272824 * 2 ^ 59
def prefixEnd_272824 : Nat := 4983230072969 + 3 ^ 40 * 272824 * 2
def baseEnd_272824 : Nat := 140089846082345808545311

theorem tailTrace_272824 : CollatzResearch.WordTrace tailWord_272824 prefixEnd_272824 140089846082345808545311 := by
  unfold tailWord_272824
  simp only [CollatzResearch.WordTrace]
  refine ⟨4975354381806358737360763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6633805842408478316481017 4975354381806358737360763)
  ·
    refine ⟨7463031572709538106041145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4975354381806358737360763 7463031572709538106041145)
    ·
      refine ⟨5597273679532153579530859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7463031572709538106041145 5597273679532153579530859)
      ·
        refine ⟨8395910519298230369296289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5597273679532153579530859 8395910519298230369296289)
        ·
          refine ⟨6296932889473672776972217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8395910519298230369296289 6296932889473672776972217)
          ·
            refine ⟨4722699667105254582729163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6296932889473672776972217 4722699667105254582729163)
            ·
              refine ⟨7084049500657881874093745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4722699667105254582729163 7084049500657881874093745)
              ·
                refine ⟨5313037125493411405570309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7084049500657881874093745 5313037125493411405570309)
                ·
                  refine ⟨996194461030014638544433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5313037125493411405570309 996194461030014638544433)
                  ·
                    refine ⟨747145845772510978908325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 996194461030014638544433 747145845772510978908325)
                    ·
                      refine ⟨140089846082345808545311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 747145845772510978908325 140089846082345808545311)
                      ·
                        rfl

theorem cell23_272824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_272824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272824 prefixEnd_272824 := by exact prefixLift 272824
  have htrace : WordTrace (prefixWord ++ tailWord_272824) baseStart_272824 baseEnd_272824 := by
    simpa [prefixWord, tailWord_272824, baseEnd_272824] using wordTrace_append hprefix tailTrace_272824
  have hstable : (prefixWord ++ tailWord_272824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272824).length < 2 ^ (prefixWord ++ tailWord_272824).sum := by decide
  have hdescent : baseEnd_272824 < baseStart_272824 := by decide
  rcases family_descends (prefixWord ++ tailWord_272824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272828 : List Nat := [2, 2, 2, 4, 1, 1, 1, 1, 3, 4, 2]
def baseStart_272828 : Nat := 118140960795 + 272828 * 2 ^ 59
def prefixEnd_272828 : Nat := 4983230072969 + 3 ^ 40 * 272828 * 2
def baseEnd_272828 : Nat := 140091900004963792895293

theorem tailTrace_272828 : CollatzResearch.WordTrace tailWord_272828 prefixEnd_272828 140091900004963792895293 := by
  unfold tailWord_272828
  simp only [CollatzResearch.WordTrace]
  refine ⟨4975427327799113078933569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6633903103732150771911425 4975427327799113078933569)
  ·
    refine ⟨3731570495849334809200177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4975427327799113078933569 3731570495849334809200177)
    ·
      refine ⟨2798677871887001106900133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3731570495849334809200177 2798677871887001106900133)
      ·
        refine ⟨524752100978812707543775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2798677871887001106900133 524752100978812707543775)
        ·
          refine ⟨787128151468219061315663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 524752100978812707543775 787128151468219061315663)
          ·
            refine ⟨1180692227202328591973495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 787128151468219061315663 1180692227202328591973495)
            ·
              refine ⟨1771038340803492887960243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1180692227202328591973495 1771038340803492887960243)
              ·
                refine ⟨2656557511205239331940365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1771038340803492887960243 2656557511205239331940365)
                ·
                  refine ⟨996209066701964749477637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2656557511205239331940365 996209066701964749477637)
                  ·
                    refine ⟨186789200006618390527057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 996209066701964749477637 186789200006618390527057)
                    ·
                      refine ⟨140091900004963792895293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 186789200006618390527057 140091900004963792895293)
                      ·
                        rfl

theorem cell23_272828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_272828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272828 prefixEnd_272828 := by exact prefixLift 272828
  have htrace : WordTrace (prefixWord ++ tailWord_272828) baseStart_272828 baseEnd_272828 := by
    simpa [prefixWord, tailWord_272828, baseEnd_272828] using wordTrace_append hprefix tailTrace_272828
  have hstable : (prefixWord ++ tailWord_272828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272828).length < 2 ^ (prefixWord ++ tailWord_272828).sum := by decide
  have hdescent : baseEnd_272828 < baseStart_272828 := by decide
  rcases family_descends (prefixWord ++ tailWord_272828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272864 : List Nat := [2, 1, 1, 3, 1, 1, 4, 2, 1, 7]
def baseStart_272864 : Nat := 118140960795 + 272864 * 2 ^ 59
def prefixEnd_272864 : Nat := 4983230072969 + 3 ^ 40 * 272864 * 2
def baseEnd_272864 : Nat := 46703461769508550681709

theorem tailTrace_272864 : CollatzResearch.WordTrace tailWord_272864 prefixEnd_272864 46703461769508550681709 := by
  unfold tailWord_272864
  simp only [CollatzResearch.WordTrace]
  refine ⟨4976083841733902153088823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6634778455645202870785097 4976083841733902153088823)
  ·
    refine ⟨7464125762600853229633235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4976083841733902153088823 7464125762600853229633235)
    ·
      refine ⟨11196188643901279844449853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7464125762600853229633235 11196188643901279844449853)
      ·
        refine ⟨4198570741462979941668695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11196188643901279844449853 4198570741462979941668695)
        ·
          refine ⟨6297856112194469912503043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4198570741462979941668695 6297856112194469912503043)
          ·
            refine ⟨9446784168291704868754565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6297856112194469912503043 9446784168291704868754565)
            ·
              refine ⟨1771272031554694662891481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9446784168291704868754565 1771272031554694662891481)
              ·
                refine ⟨1328454023666020997168611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1771272031554694662891481 1328454023666020997168611)
                ·
                  refine ⟨1992681035499031495752917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1328454023666020997168611 1992681035499031495752917)
                  ·
                    refine ⟨46703461769508550681709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1992681035499031495752917 46703461769508550681709)
                    ·
                      rfl

theorem cell23_272864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 1, 7].length) (baseStart_272864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_272864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_272864 prefixEnd_272864 := by exact prefixLift 272864
  have htrace : WordTrace (prefixWord ++ tailWord_272864) baseStart_272864 baseEnd_272864 := by
    simpa [prefixWord, tailWord_272864, baseEnd_272864] using wordTrace_append hprefix tailTrace_272864
  have hstable : (prefixWord ++ tailWord_272864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272864).length < 2 ^ (prefixWord ++ tailWord_272864).sum := by decide
  have hdescent : baseEnd_272864 < baseStart_272864 := by decide
  rcases family_descends (prefixWord ++ tailWord_272864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
