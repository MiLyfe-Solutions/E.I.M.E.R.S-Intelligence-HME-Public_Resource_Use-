import V185TrunkScan22Chunk437

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3905333 : List Nat := [1, 3, 3, 1, 4, 1, 2, 1, 1, 5]
def baseStart_3905333 : Nat := 118140960795 + 3905333 * 2 ^ 59
def prefixEnd_3905333 : Nat := 4983230072969 + 3 ^ 40 * 3905333 * 2
def baseEnd_3905333 : Nat := 1336875296576849400251471

theorem tailTrace_3905333 : CollatzResearch.WordTrace tailWord_3905333 prefixEnd_3905333 1336875296576849400251471 := by
  unfold tailWord_3905333
  simp only [CollatzResearch.WordTrace]
  refine ⟨142439196360652993620696653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94959464240435329080464435 142439196360652993620696653)
  ·
    refine ⟨53414698635244872607761245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142439196360652993620696653 53414698635244872607761245)
    ·
      refine ⟨20030511988216827227910467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53414698635244872607761245 20030511988216827227910467)
      ·
        refine ⟨30045767982325240841865701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20030511988216827227910467 30045767982325240841865701)
        ·
          refine ⟨5633581496685982657849819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30045767982325240841865701 5633581496685982657849819)
          ·
            refine ⟨8450372245028973986774729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5633581496685982657849819 8450372245028973986774729)
            ·
              refine ⟨6337779183771730490081047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8450372245028973986774729 6337779183771730490081047)
              ·
                refine ⟨9506668775657595735121571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6337779183771730490081047 9506668775657595735121571)
                ·
                  refine ⟨14260003163486393602682357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9506668775657595735121571 14260003163486393602682357)
                  ·
                    refine ⟨1336875296576849400251471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14260003163486393602682357 1336875296576849400251471)
                    ·
                      rfl

theorem cell22_3905333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_3905333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3905333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3905333 prefixEnd_3905333 := by exact prefixLift 3905333
  have htrace : WordTrace (prefixWord ++ tailWord_3905333) baseStart_3905333 baseEnd_3905333 := by
    simpa [prefixWord, tailWord_3905333, baseEnd_3905333] using wordTrace_append hprefix tailTrace_3905333
  have hstable : (prefixWord ++ tailWord_3905333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905333).length < 2 ^ (prefixWord ++ tailWord_3905333).sum := by decide
  have hdescent : baseEnd_3905333 < baseStart_3905333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905350 : List Nat := [6, 1, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_3905350 : Nat := 118140960795 + 3905350 * 2 ^ 59
def prefixEnd_3905350 : Nat := 4983230072969 + 3 ^ 40 * 3905350 * 2
def baseEnd_3905350 : Nat := 1336881116024267022576419

theorem tailTrace_3905350 : CollatzResearch.WordTrace tailWord_3905350 prefixEnd_3905350 1336881116024267022576419 := by
  unfold tailWord_3905350
  simp only [CollatzResearch.WordTrace]
  refine ⟨4451244262549731422627047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 94959877601060937016043669 4451244262549731422627047)
  ·
    refine ⟨6676866393824597133940571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4451244262549731422627047 6676866393824597133940571)
    ·
      refine ⟨10015299590736895700910857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6676866393824597133940571 10015299590736895700910857)
      ·
        refine ⟨7511474693052671775683143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10015299590736895700910857 7511474693052671775683143)
        ·
          refine ⟨11267212039579007663524715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7511474693052671775683143 11267212039579007663524715)
          ·
            refine ⟨16900818059368511495287073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11267212039579007663524715 16900818059368511495287073)
            ·
              refine ⟨12675613544526383621465305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16900818059368511495287073 12675613544526383621465305)
              ·
                refine ⟨9506710158394787716098979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12675613544526383621465305 9506710158394787716098979)
                ·
                  refine ⟨14260065237592181574148469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9506710158394787716098979 14260065237592181574148469)
                  ·
                    refine ⟨1336881116024267022576419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14260065237592181574148469 1336881116024267022576419)
                    ·
                      rfl

theorem cell22_3905350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_3905350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3905350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3905350 prefixEnd_3905350 := by exact prefixLift 3905350
  have htrace : WordTrace (prefixWord ++ tailWord_3905350) baseStart_3905350 baseEnd_3905350 := by
    simpa [prefixWord, tailWord_3905350, baseEnd_3905350] using wordTrace_append hprefix tailTrace_3905350
  have hstable : (prefixWord ++ tailWord_3905350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905350).length < 2 ^ (prefixWord ++ tailWord_3905350).sum := by decide
  have hdescent : baseEnd_3905350 < baseStart_3905350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905367 : List Nat := [1, 1, 3, 2, 6, 1, 1, 2, 2, 3]
def baseStart_3905367 : Nat := 118140960795 + 3905367 * 2 ^ 59
def prefixEnd_3905367 : Nat := 4983230072969 + 3 ^ 40 * 3905367 * 2
def baseEnd_3905367 : Nat := 1336886935471684644901367

theorem tailTrace_3905367 : CollatzResearch.WordTrace tailWord_3905367 prefixEnd_3905367 1336886935471684644901367 := by
  unfold tailWord_3905367
  simp only [CollatzResearch.WordTrace]
  refine ⟨142440436442529817427434355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94960290961686544951622903 142440436442529817427434355)
  ·
    refine ⟨213660654663794726141151533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142440436442529817427434355 213660654663794726141151533)
    ·
      refine ⟨80122745498923022302931825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213660654663794726141151533 80122745498923022302931825)
      ·
        refine ⟨60092059124192266727198869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80122745498923022302931825 60092059124192266727198869)
        ·
          refine ⟨2816815271446512502837447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 60092059124192266727198869 2816815271446512502837447)
          ·
            refine ⟨4225222907169768754256171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2816815271446512502837447 4225222907169768754256171)
            ·
              refine ⟨6337834360754653131384257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4225222907169768754256171 6337834360754653131384257)
              ·
                refine ⟨4753375770565989848538193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6337834360754653131384257 4753375770565989848538193)
                ·
                  refine ⟨3565031827924492386403645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4753375770565989848538193 3565031827924492386403645)
                  ·
                    refine ⟨1336886935471684644901367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3565031827924492386403645 1336886935471684644901367)
                    ·
                      rfl

theorem cell22_3905367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 2, 3].length) (baseStart_3905367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3905367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3905367 prefixEnd_3905367 := by exact prefixLift 3905367
  have htrace : WordTrace (prefixWord ++ tailWord_3905367) baseStart_3905367 baseEnd_3905367 := by
    simpa [prefixWord, tailWord_3905367, baseEnd_3905367] using wordTrace_append hprefix tailTrace_3905367
  have hstable : (prefixWord ++ tailWord_3905367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905367).length < 2 ^ (prefixWord ++ tailWord_3905367).sum := by decide
  have hdescent : baseEnd_3905367 < baseStart_3905367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905442 : List Nat := [3, 3, 1, 2, 3, 2, 2, 1, 5]
def baseStart_3905442 : Nat := 118140960795 + 3905442 * 2 ^ 59
def prefixEnd_3905442 : Nat := 4983230072969 + 3 ^ 40 * 3905442 * 2
def baseEnd_3905442 : Nat := 445637536501469816425379

theorem tailTrace_3905442 : CollatzResearch.WordTrace tailWord_3905442 prefixEnd_3905442 445637536501469816425379 := by
  unfold tailWord_3905442
  simp only [CollatzResearch.WordTrace]
  refine ⟨35610792979314526309103645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94962114611505403490943053 35610792979314526309103645)
  ·
    refine ⟨13354047367242947365913867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35610792979314526309103645 13354047367242947365913867)
    ·
      refine ⟨20031071050864421048870801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13354047367242947365913867 20031071050864421048870801)
      ·
        refine ⟨15023303288148315786653101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20031071050864421048870801 15023303288148315786653101)
        ·
          refine ⟨5633738733055618419994913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15023303288148315786653101 5633738733055618419994913)
          ·
            refine ⟨4225304049791713814996185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5633738733055618419994913 4225304049791713814996185)
            ·
              refine ⟨3168978037343785361247139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4225304049791713814996185 3168978037343785361247139)
              ·
                refine ⟨4753467056015678041870709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3168978037343785361247139 4753467056015678041870709)
                ·
                  refine ⟨445637536501469816425379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4753467056015678041870709 445637536501469816425379)
                  ·
                    rfl

theorem cell22_3905442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_3905442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3905442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3905442 prefixEnd_3905442 := by exact prefixLift 3905442
  have htrace : WordTrace (prefixWord ++ tailWord_3905442) baseStart_3905442 baseEnd_3905442 := by
    simpa [prefixWord, tailWord_3905442, baseEnd_3905442] using wordTrace_append hprefix tailTrace_3905442
  have hstable : (prefixWord ++ tailWord_3905442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905442).length < 2 ^ (prefixWord ++ tailWord_3905442).sum := by decide
  have hdescent : baseEnd_3905442 < baseStart_3905442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905543 : List Nat := [1, 1, 4, 3, 1, 3, 1, 1, 7]
def baseStart_3905543 : Nat := 118140960795 + 3905543 * 2 ^ 59
def prefixEnd_3905543 : Nat := 4983230072969 + 3 ^ 40 * 3905543 * 2
def baseEnd_3905543 : Nat := 445649061289492950833609

theorem tailTrace_3905543 : CollatzResearch.WordTrace tailWord_3905543 prefixEnd_3905543 445649061289492950833609 := by
  unfold tailWord_3905543
  simp only [CollatzResearch.WordTrace]
  refine ⟨142446855689892199485841283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94964570459928132990560855 142446855689892199485841283)
  ·
    refine ⟨213670283534838299228761925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142446855689892199485841283 213670283534838299228761925)
    ·
      refine ⟨40063178162782181105392861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213670283534838299228761925 40063178162782181105392861)
      ·
        refine ⟨15023691811043317914522323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40063178162782181105392861 15023691811043317914522323)
        ·
          refine ⟨22535537716564976871783485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15023691811043317914522323 22535537716564976871783485)
          ·
            refine ⟨8450826643711866326918807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22535537716564976871783485 8450826643711866326918807)
            ·
              refine ⟨12676239965567799490378211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8450826643711866326918807 12676239965567799490378211)
              ·
                refine ⟨19014359948351699235567317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12676239965567799490378211 19014359948351699235567317)
                ·
                  refine ⟨445649061289492950833609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19014359948351699235567317 445649061289492950833609)
                  ·
                    rfl

theorem cell22_3905543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 7].length) (baseStart_3905543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3905543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3905543 prefixEnd_3905543 := by exact prefixLift 3905543
  have htrace : WordTrace (prefixWord ++ tailWord_3905543) baseStart_3905543 baseEnd_3905543 := by
    simpa [prefixWord, tailWord_3905543, baseEnd_3905543] using wordTrace_append hprefix tailTrace_3905543
  have hstable : (prefixWord ++ tailWord_3905543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905543).length < 2 ^ (prefixWord ++ tailWord_3905543).sum := by decide
  have hdescent : baseEnd_3905543 < baseStart_3905543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905560 : List Nat := [2, 1, 2, 3, 2, 1, 5, 1, 5]
def baseStart_3905560 : Nat := 118140960795 + 3905560 * 2 ^ 59
def prefixEnd_3905560 : Nat := 4983230072969 + 3 ^ 40 * 3905560 * 2
def baseEnd_3905560 : Nat := 445651001105298824941925

theorem tailTrace_3905560 : CollatzResearch.WordTrace tailWord_3905560 prefixEnd_3905560 445651001105298824941925 := by
  unfold tailWord_3905560
  simp only [CollatzResearch.WordTrace]
  refine ⟨71223737865415305694605067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94964983820553740926140089 71223737865415305694605067)
  ·
    refine ⟨106835606798122958541907601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71223737865415305694605067 106835606798122958541907601)
    ·
      refine ⟨80126705098592218906430701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106835606798122958541907601 80126705098592218906430701)
      ·
        refine ⟨30047514411972082089911513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80126705098592218906430701 30047514411972082089911513)
        ·
          refine ⟨22535635808979061567433635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30047514411972082089911513 22535635808979061567433635)
          ·
            refine ⟨33803453713468592351150453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22535635808979061567433635 33803453713468592351150453)
            ·
              refine ⟨3169073785637680532920355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33803453713468592351150453 3169073785637680532920355)
              ·
                refine ⟨4753610678456520799380533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3169073785637680532920355 4753610678456520799380533)
                ·
                  refine ⟨445651001105298824941925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4753610678456520799380533 445651001105298824941925)
                  ·
                    rfl

theorem cell22_3905560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 5].length) (baseStart_3905560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3905560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3905560 prefixEnd_3905560 := by exact prefixLift 3905560
  have htrace : WordTrace (prefixWord ++ tailWord_3905560) baseStart_3905560 baseEnd_3905560 := by
    simpa [prefixWord, tailWord_3905560, baseEnd_3905560] using wordTrace_append hprefix tailTrace_3905560
  have hstable : (prefixWord ++ tailWord_3905560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905560).length < 2 ^ (prefixWord ++ tailWord_3905560).sum := by decide
  have hdescent : baseEnd_3905560 < baseStart_3905560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905654 : List Nat := [5, 1, 1, 2, 1, 3, 2, 2, 2, 3]
def baseStart_3905654 : Nat := 118140960795 + 3905654 * 2 ^ 59
def prefixEnd_3905654 : Nat := 4983230072969 + 3 ^ 40 * 3905654 * 2
def baseEnd_3905654 : Nat := 1336985181436911562975487

theorem tailTrace_3905654 : CollatzResearch.WordTrace tailWord_3905654 prefixEnd_3905654 1336985181436911562975487 := by
  unfold tailWord_3905654
  simp only [CollatzResearch.WordTrace]
  refine ⟨8903181512030629090195751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94967269461660043628754677 8903181512030629090195751)
  ·
    refine ⟨13354772268045943635293627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8903181512030629090195751 13354772268045943635293627)
    ·
      refine ⟨20032158402068915452940441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13354772268045943635293627 20032158402068915452940441)
      ·
        refine ⟨15024118801551686589705331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20032158402068915452940441 15024118801551686589705331)
        ·
          refine ⟨22536178202327529884557997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15024118801551686589705331 22536178202327529884557997)
          ·
            refine ⟨8451066825872823706709249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22536178202327529884557997 8451066825872823706709249)
            ·
              refine ⟨6338300119404617780031937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8451066825872823706709249 6338300119404617780031937)
              ·
                refine ⟨4753725089553463335023953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6338300119404617780031937 4753725089553463335023953)
                ·
                  refine ⟨3565293817165097501267965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4753725089553463335023953 3565293817165097501267965)
                  ·
                    refine ⟨1336985181436911562975487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3565293817165097501267965 1336985181436911562975487)
                    ·
                      rfl

theorem cell22_3905654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_3905654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3905654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3905654 prefixEnd_3905654 := by exact prefixLift 3905654
  have htrace : WordTrace (prefixWord ++ tailWord_3905654) baseStart_3905654 baseEnd_3905654 := by
    simpa [prefixWord, tailWord_3905654, baseEnd_3905654] using wordTrace_append hprefix tailTrace_3905654
  have hstable : (prefixWord ++ tailWord_3905654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905654).length < 2 ^ (prefixWord ++ tailWord_3905654).sum := by decide
  have hdescent : baseEnd_3905654 < baseStart_3905654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905682 : List Nat := [3, 2, 3, 1, 1, 1, 3, 2, 3, 3]
def baseStart_3905682 : Nat := 118140960795 + 3905682 * 2 ^ 59
def prefixEnd_3905682 : Nat := 4983230072969 + 3 ^ 40 * 3905682 * 2
def baseEnd_3905682 : Nat := 1336994766409128823275401

theorem tailTrace_3905682 : CollatzResearch.WordTrace tailWord_3905682 prefixEnd_3905682 1336994766409128823275401 := by
  unfold tailWord_3905682
  simp only [CollatzResearch.WordTrace]
  refine ⟨35612981359097156556287825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94967950290925750816767533 35612981359097156556287825)
  ·
    refine ⟨26709736019322867417215869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35612981359097156556287825 26709736019322867417215869)
    ·
      refine ⟨10016151007246075281455951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26709736019322867417215869 10016151007246075281455951)
      ·
        refine ⟨15024226510869112922183927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10016151007246075281455951 15024226510869112922183927)
        ·
          refine ⟨22536339766303669383275891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15024226510869112922183927 22536339766303669383275891)
          ·
            refine ⟨33804509649455504074913837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22536339766303669383275891 33804509649455504074913837)
            ·
              refine ⟨12676691118545814028092689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33804509649455504074913837 12676691118545814028092689)
              ·
                refine ⟨9507518338909360521069517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12676691118545814028092689 9507518338909360521069517)
                ·
                  refine ⟨3565319377091010195401069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9507518338909360521069517 3565319377091010195401069)
                  ·
                    refine ⟨1336994766409128823275401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3565319377091010195401069 1336994766409128823275401)
                    ·
                      rfl

theorem cell22_3905682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_3905682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3905682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3905682 prefixEnd_3905682 := by exact prefixLift 3905682
  have htrace : WordTrace (prefixWord ++ tailWord_3905682) baseStart_3905682 baseEnd_3905682 := by
    simpa [prefixWord, tailWord_3905682, baseEnd_3905682] using wordTrace_append hprefix tailTrace_3905682
  have hstable : (prefixWord ++ tailWord_3905682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905682).length < 2 ^ (prefixWord ++ tailWord_3905682).sum := by decide
  have hdescent : baseEnd_3905682 < baseStart_3905682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905684 : List Nat := [2, 4, 2, 3, 1, 1, 3, 6]
def baseStart_3905684 : Nat := 118140960795 + 3905684 * 2 ^ 59
def prefixEnd_3905684 : Nat := 4983230072969 + 3 ^ 40 * 3905684 * 2
def baseEnd_3905684 : Nat := 148555050116666831636155

theorem tailTrace_3905684 : CollatzResearch.WordTrace tailWord_3905684 prefixEnd_3905684 148555050116666831636155 := by
  unfold tailWord_3905684
  simp only [CollatzResearch.WordTrace]
  refine ⟨71225999191190690283362053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94967998921587587044482737 71225999191190690283362053)
  ·
    refine ⟨13354874848348254428130385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71225999191190690283362053 13354874848348254428130385)
    ·
      refine ⟨10016156136261190821097789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13354874848348254428130385 10016156136261190821097789)
      ·
        refine ⟨3756058551097946557911671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10016156136261190821097789 3756058551097946557911671)
        ·
          refine ⟨5634087826646919836867507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3756058551097946557911671 5634087826646919836867507)
          ·
            refine ⟨8451131739970379755301261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5634087826646919836867507 8451131739970379755301261)
            ·
              refine ⟨3169174402488892408237973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8451131739970379755301261 3169174402488892408237973)
              ·
                refine ⟨148555050116666831636155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3169174402488892408237973 148555050116666831636155)
                ·
                  rfl

theorem cell22_3905684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 6].length) (baseStart_3905684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3905684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3905684 prefixEnd_3905684 := by exact prefixLift 3905684
  have htrace : WordTrace (prefixWord ++ tailWord_3905684) baseStart_3905684 baseEnd_3905684 := by
    simpa [prefixWord, tailWord_3905684, baseEnd_3905684] using wordTrace_append hprefix tailTrace_3905684
  have hstable : (prefixWord ++ tailWord_3905684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905684).length < 2 ^ (prefixWord ++ tailWord_3905684).sum := by decide
  have hdescent : baseEnd_3905684 < baseStart_3905684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905742 : List Nat := [4, 1, 1, 1, 4, 1, 1, 4, 1, 4]
def baseStart_3905742 : Nat := 118140960795 + 3905742 * 2 ^ 59
def prefixEnd_3905742 : Nat := 4983230072969 + 3 ^ 40 * 3905742 * 2
def baseEnd_3905742 : Nat := 1337015305635308666775217

theorem tailTrace_3905742 : CollatzResearch.WordTrace tailWord_3905742 prefixEnd_3905742 1337015305635308666775217 := by
  unfold tailWord_3905742
  simp only [CollatzResearch.WordTrace]
  refine ⟨17806764227021407059041935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94969409210780837648223653 17806764227021407059041935)
  ·
    refine ⟨26710146340532110588562903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17806764227021407059041935 26710146340532110588562903)
    ·
      refine ⟨40065219510798165882844355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26710146340532110588562903 40065219510798165882844355)
      ·
        refine ⟨60097829266197248824266533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40065219510798165882844355 60097829266197248824266533)
        ·
          refine ⟨11268342987411984154549975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60097829266197248824266533 11268342987411984154549975)
          ·
            refine ⟨16902514481117976231824963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11268342987411984154549975 16902514481117976231824963)
            ·
              refine ⟨25353771721676964347737445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16902514481117976231824963 25353771721676964347737445)
              ·
                refine ⟨4753832197814430815200771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25353771721676964347737445 4753832197814430815200771)
                ·
                  refine ⟨7130748296721646222801157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4753832197814430815200771 7130748296721646222801157)
                  ·
                    refine ⟨1337015305635308666775217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7130748296721646222801157 1337015305635308666775217)
                    ·
                      rfl

theorem cell22_3905742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_3905742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3905742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3905742 prefixEnd_3905742 := by exact prefixLift 3905742
  have htrace : WordTrace (prefixWord ++ tailWord_3905742) baseStart_3905742 baseEnd_3905742 := by
    simpa [prefixWord, tailWord_3905742, baseEnd_3905742] using wordTrace_append hprefix tailTrace_3905742
  have hstable : (prefixWord ++ tailWord_3905742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905742).length < 2 ^ (prefixWord ++ tailWord_3905742).sum := by decide
  have hdescent : baseEnd_3905742 < baseStart_3905742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905755 : List Nat := [1, 1, 1, 1, 1, 1, 1, 8, 4, 3]
def baseStart_3905755 : Nat := 118140960795 + 3905755 * 2 ^ 59
def prefixEnd_3905755 : Nat := 4983230072969 + 3 ^ 40 * 3905755 * 2
def baseEnd_3905755 : Nat := 1337019755800980966200177

theorem tailTrace_3905755 : CollatzResearch.WordTrace tailWord_3905755 prefixEnd_3905755 1337019755800980966200177 := by
  unfold tailWord_3905755
  simp only [CollatzResearch.WordTrace]
  refine ⟨142454587965124159692558719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94969725310082773128372479 142454587965124159692558719)
  ·
    refine ⟨213681881947686239538838079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142454587965124159692558719 213681881947686239538838079)
    ·
      refine ⟨320522822921529359308257119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213681881947686239538838079 320522822921529359308257119)
      ·
        refine ⟨480784234382294038962385679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320522822921529359308257119 480784234382294038962385679)
        ·
          refine ⟨721176351573441058443578519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480784234382294038962385679 721176351573441058443578519)
          ·
            refine ⟨1081764527360161587665367779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 721176351573441058443578519 1081764527360161587665367779)
            ·
              refine ⟨1622646791040242381498051669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1081764527360161587665367779 1622646791040242381498051669)
              ·
                refine ⟨19015392082502840408180293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1622646791040242381498051669 19015392082502840408180293)
                ·
                  refine ⟨3565386015469282576533805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19015392082502840408180293 3565386015469282576533805)
                  ·
                    refine ⟨1337019755800980966200177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3565386015469282576533805 1337019755800980966200177)
                    ·
                      rfl

theorem cell22_3905755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 4, 3].length) (baseStart_3905755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3905755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3905755 prefixEnd_3905755 := by exact prefixLift 3905755
  have htrace : WordTrace (prefixWord ++ tailWord_3905755) baseStart_3905755 baseEnd_3905755 := by
    simpa [prefixWord, tailWord_3905755, baseEnd_3905755] using wordTrace_append hprefix tailTrace_3905755
  have hstable : (prefixWord ++ tailWord_3905755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905755).length < 2 ^ (prefixWord ++ tailWord_3905755).sum := by decide
  have hdescent : baseEnd_3905755 < baseStart_3905755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905772 : List Nat := [2, 2, 1, 1, 2, 3, 2, 4, 2, 3]
def baseStart_3905772 : Nat := 118140960795 + 3905772 * 2 ^ 59
def prefixEnd_3905772 : Nat := 4983230072969 + 3 ^ 40 * 3905772 * 2
def baseEnd_3905772 : Nat := 1337025575248398588525125

theorem tailTrace_3905772 : CollatzResearch.WordTrace tailWord_3905772 prefixEnd_3905772 1337025575248398588525125 := by
  unfold tailWord_3905772
  simp only [CollatzResearch.WordTrace]
  refine ⟨71227604003031285797963785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94970138670708381063951713 71227604003031285797963785)
  ·
    refine ⟨53420703002273464348472839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71227604003031285797963785 53420703002273464348472839)
    ·
      refine ⟨80131054503410196522709259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53420703002273464348472839 80131054503410196522709259)
      ·
        refine ⟨120196581755115294784063889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80131054503410196522709259 120196581755115294784063889)
        ·
          refine ⟨90147436316336471088047917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120196581755115294784063889 90147436316336471088047917)
          ·
            refine ⟨33805288618626176658017969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90147436316336471088047917 33805288618626176658017969)
            ·
              refine ⟨25353966463969632493513477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33805288618626176658017969 25353966463969632493513477)
              ·
                refine ⟨4753868711994306092533777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25353966463969632493513477 4753868711994306092533777)
                ·
                  refine ⟨3565401533995729569400333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4753868711994306092533777 3565401533995729569400333)
                  ·
                    refine ⟨1337025575248398588525125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3565401533995729569400333 1337025575248398588525125)
                    ·
                      rfl

theorem cell22_3905772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 3].length) (baseStart_3905772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3905772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3905772 prefixEnd_3905772 := by exact prefixLift 3905772
  have htrace : WordTrace (prefixWord ++ tailWord_3905772) baseStart_3905772 baseEnd_3905772 := by
    simpa [prefixWord, tailWord_3905772, baseEnd_3905772] using wordTrace_append hprefix tailTrace_3905772
  have hstable : (prefixWord ++ tailWord_3905772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905772).length < 2 ^ (prefixWord ++ tailWord_3905772).sum := by decide
  have hdescent : baseEnd_3905772 < baseStart_3905772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905892 : List Nat := [2, 3, 1, 1, 3, 1, 4, 1, 6]
def baseStart_3905892 : Nat := 118140960795 + 3905892 * 2 ^ 59
def prefixEnd_3905892 : Nat := 4983230072969 + 3 ^ 40 * 3905892 * 2
def baseEnd_3905892 : Nat := 445688884566919425174919

theorem tailTrace_3905892 : CollatzResearch.WordTrace tailWord_3905892 prefixEnd_3905892 445688884566919425174919 := by
  unfold tailWord_3905892
  simp only [CollatzResearch.WordTrace]
  refine ⟨71229792382813916045147965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94973056510418554726863953 71229792382813916045147965)
  ·
    refine ⟨26711172143555218516930487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71229792382813916045147965 26711172143555218516930487)
    ·
      refine ⟨40066758215332827775395731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26711172143555218516930487 40066758215332827775395731)
      ·
        refine ⟨60100137322999241663093597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40066758215332827775395731 60100137322999241663093597)
        ·
          refine ⟨22537551496124715623660099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60100137322999241663093597 22537551496124715623660099)
          ·
            refine ⟨33806327244187073435490149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22537551496124715623660099 33806327244187073435490149)
            ·
              refine ⟨6338686358285076269154403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33806327244187073435490149 6338686358285076269154403)
              ·
                refine ⟨9508029537427614403731605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6338686358285076269154403 9508029537427614403731605)
                ·
                  refine ⟨445688884566919425174919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9508029537427614403731605 445688884566919425174919)
                  ·
                    rfl

theorem cell22_3905892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_3905892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3905892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3905892 prefixEnd_3905892 := by exact prefixLift 3905892
  have htrace : WordTrace (prefixWord ++ tailWord_3905892) baseStart_3905892 baseEnd_3905892 := by
    simpa [prefixWord, tailWord_3905892, baseEnd_3905892] using wordTrace_append hprefix tailTrace_3905892
  have hstable : (prefixWord ++ tailWord_3905892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905892).length < 2 ^ (prefixWord ++ tailWord_3905892).sum := by decide
  have hdescent : baseEnd_3905892 < baseStart_3905892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905962 : List Nat := [3, 1, 6, 1, 2, 1, 1, 2, 1, 4]
def baseStart_3905962 : Nat := 118140960795 + 3905962 * 2 ^ 59
def prefixEnd_3905962 : Nat := 4983230072969 + 3 ^ 40 * 3905962 * 2
def baseEnd_3905962 : Nat := 1337090616131301426274543

theorem tailTrace_3905962 : CollatzResearch.WordTrace tailWord_3905962 prefixEnd_3905962 1337090616131301426274543 := by
  unfold tailWord_3905962
  simp only [CollatzResearch.WordTrace]
  refine ⟨35615534468843558511336035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94974758583582822696896093 35615534468843558511336035)
  ·
    refine ⟨53423301703265337767004053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35615534468843558511336035 53423301703265337767004053)
    ·
      refine ⟨2504217267340562707828315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53423301703265337767004053 2504217267340562707828315)
      ·
        refine ⟨3756325901010844061742473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2504217267340562707828315 3756325901010844061742473)
        ·
          refine ⟨2817244425758133046306855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3756325901010844061742473 2817244425758133046306855)
          ·
            refine ⟨4225866638637199569460283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2817244425758133046306855 4225866638637199569460283)
            ·
              refine ⟨6338799957955799354190425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4225866638637199569460283 6338799957955799354190425)
              ·
                refine ⟨4754099968466849515642819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6338799957955799354190425 4754099968466849515642819)
                ·
                  refine ⟨7131149952700274273464229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4754099968466849515642819 7131149952700274273464229)
                  ·
                    refine ⟨1337090616131301426274543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7131149952700274273464229 1337090616131301426274543)
                    ·
                      rfl

theorem cell22_3905962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_3905962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3905962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3905962 prefixEnd_3905962 := by exact prefixLift 3905962
  have htrace : WordTrace (prefixWord ++ tailWord_3905962) baseStart_3905962 baseEnd_3905962 := by
    simpa [prefixWord, tailWord_3905962, baseEnd_3905962] using wordTrace_append hprefix tailTrace_3905962
  have hstable : (prefixWord ++ tailWord_3905962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905962).length < 2 ^ (prefixWord ++ tailWord_3905962).sum := by decide
  have hdescent : baseEnd_3905962 < baseStart_3905962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3905982 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 9]
def baseStart_3905982 : Nat := 118140960795 + 3905982 * 2 ^ 59
def prefixEnd_3905982 : Nat := 4983230072969 + 3 ^ 40 * 3905982 * 2
def baseEnd_3905982 : Nat := 445699154180009346924827

theorem tailTrace_3905982 : CollatzResearch.WordTrace tailWord_3905982 prefixEnd_3905982 445699154180009346924827 := by
  unfold tailWord_3905982
  simp only [CollatzResearch.WordTrace]
  refine ⟨17807858416912722182634025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94975244890201184974048133 17807858416912722182634025)
  ·
    refine ⟨13355893812684541636975519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17807858416912722182634025 13355893812684541636975519)
    ·
      refine ⟨20033840719026812455463279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13355893812684541636975519 20033840719026812455463279)
      ·
        refine ⟨30050761078540218683194919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20033840719026812455463279 30050761078540218683194919)
        ·
          refine ⟨45076141617810328024792379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30050761078540218683194919 45076141617810328024792379)
          ·
            refine ⟨67614212426715492037188569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45076141617810328024792379 67614212426715492037188569)
            ·
              refine ⟨50710659320036619027891427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67614212426715492037188569 50710659320036619027891427)
              ·
                refine ⟨76065988980054928541837141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50710659320036619027891427 76065988980054928541837141)
                ·
                  refine ⟨445699154180009346924827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 76065988980054928541837141 445699154180009346924827)
                  ·
                    rfl

theorem cell22_3905982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_3905982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3905982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3905982 prefixEnd_3905982 := by exact prefixLift 3905982
  have htrace : WordTrace (prefixWord ++ tailWord_3905982) baseStart_3905982 baseEnd_3905982 := by
    simpa [prefixWord, tailWord_3905982, baseEnd_3905982] using wordTrace_append hprefix tailTrace_3905982
  have hstable : (prefixWord ++ tailWord_3905982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3905982).length < 2 ^ (prefixWord ++ tailWord_3905982).sum := by decide
  have hdescent : baseEnd_3905982 < baseStart_3905982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3905982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906027 : List Nat := [1, 1, 1, 1, 2, 3, 5, 2, 6]
def baseStart_3906027 : Nat := 118140960795 + 3906027 * 2 ^ 59
def prefixEnd_3906027 : Nat := 4983230072969 + 3 ^ 40 * 3906027 * 2
def baseEnd_3906027 : Nat := 445704288986554307799781

theorem tailTrace_3906027 : CollatzResearch.WordTrace tailWord_3906027 prefixEnd_3906027 445704288986554307799781 := by
  unfold tailWord_3906027
  simp only [CollatzResearch.WordTrace]
  refine ⟨142464508620138750146460335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94976339080092500097640223 142464508620138750146460335)
  ·
    refine ⟨213696762930208125219690503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142464508620138750146460335 213696762930208125219690503)
    ·
      refine ⟨320545144395312187829535755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213696762930208125219690503 320545144395312187829535755)
      ·
        refine ⟨480817716592968281744303633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320545144395312187829535755 480817716592968281744303633)
        ·
          refine ⟨360613287444726211308227725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480817716592968281744303633 360613287444726211308227725)
          ·
            refine ⟨135229982791772329240585397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360613287444726211308227725 135229982791772329240585397)
            ·
              refine ⟨12677810886728655866304881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135229982791772329240585397 12677810886728655866304881)
              ·
                refine ⟨9508358165046491899728661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12677810886728655866304881 9508358165046491899728661)
                ·
                  refine ⟨445704288986554307799781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9508358165046491899728661 445704288986554307799781)
                  ·
                    rfl

theorem cell22_3906027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 6].length) (baseStart_3906027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3906027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3906027 prefixEnd_3906027 := by exact prefixLift 3906027
  have htrace : WordTrace (prefixWord ++ tailWord_3906027) baseStart_3906027 baseEnd_3906027 := by
    simpa [prefixWord, tailWord_3906027, baseEnd_3906027] using wordTrace_append hprefix tailTrace_3906027
  have hstable : (prefixWord ++ tailWord_3906027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906027).length < 2 ^ (prefixWord ++ tailWord_3906027).sum := by decide
  have hdescent : baseEnd_3906027 < baseStart_3906027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906042 : List Nat := [3, 1, 1, 1, 1, 2, 2, 3, 3, 5]
def baseStart_3906042 : Nat := 118140960795 + 3906042 * 2 ^ 59
def prefixEnd_3906042 : Nat := 4983230072969 + 3 ^ 40 * 3906042 * 2
def baseEnd_3906042 : Nat := 1337118001766207884274297

theorem tailTrace_3906042 : CollatzResearch.WordTrace tailWord_3906042 prefixEnd_3906042 1337118001766207884274297 := by
  unfold tailWord_3906042
  simp only [CollatzResearch.WordTrace]
  refine ⟨35616263928771101927064095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94976703810056271805504253 35616263928771101927064095)
  ·
    refine ⟨53424395893156652890596143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35616263928771101927064095 53424395893156652890596143)
    ·
      refine ⟨80136593839734979335894215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53424395893156652890596143 80136593839734979335894215)
      ·
        refine ⟨120204890759602469003841323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80136593839734979335894215 120204890759602469003841323)
        ·
          refine ⟨180307336139403703505761985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120204890759602469003841323 180307336139403703505761985)
          ·
            refine ⟨135230502104552777629321489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180307336139403703505761985 135230502104552777629321489)
            ·
              refine ⟨101422876578414583221991117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135230502104552777629321489 101422876578414583221991117)
              ·
                refine ⟨38033578716905468708246669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101422876578414583221991117 38033578716905468708246669)
                ·
                  refine ⟨14262592018839550765592501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38033578716905468708246669 14262592018839550765592501)
                  ·
                    refine ⟨1337118001766207884274297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14262592018839550765592501 1337118001766207884274297)
                    ·
                      rfl

theorem cell22_3906042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_3906042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3906042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3906042 prefixEnd_3906042 := by exact prefixLift 3906042
  have htrace : WordTrace (prefixWord ++ tailWord_3906042) baseStart_3906042 baseEnd_3906042 := by
    simpa [prefixWord, tailWord_3906042, baseEnd_3906042] using wordTrace_append hprefix tailTrace_3906042
  have hstable : (prefixWord ++ tailWord_3906042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906042).length < 2 ^ (prefixWord ++ tailWord_3906042).sum := by decide
  have hdescent : baseEnd_3906042 < baseStart_3906042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906050 : List Nat := [3, 4, 1, 2, 3, 1, 1, 2, 5]
def baseStart_3906050 : Nat := 118140960795 + 3906050 * 2 ^ 59
def prefixEnd_3906050 : Nat := 4983230072969 + 3 ^ 40 * 3906050 * 2
def baseEnd_3906050 : Nat := 445706913443232843358091

theorem tailTrace_3906050 : CollatzResearch.WordTrace tailWord_3906050 prefixEnd_3906050 445706913443232843358091 := by
  unfold tailWord_3906050
  simp only [CollatzResearch.WordTrace]
  refine ⟨35616336874763856268636901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94976898332703616716365069 35616336874763856268636901)
  ·
    refine ⟨6678063164018223050369419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35616336874763856268636901 6678063164018223050369419)
    ·
      refine ⟨10017094746027334575554129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6678063164018223050369419 10017094746027334575554129)
      ·
        refine ⟨7512821059520500931665597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10017094746027334575554129 7512821059520500931665597)
        ·
          refine ⟨2817307897320187849374599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7512821059520500931665597 2817307897320187849374599)
          ·
            refine ⟨4225961845980281774061899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2817307897320187849374599 4225961845980281774061899)
            ·
              refine ⟨6338942768970422661092849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4225961845980281774061899 6338942768970422661092849)
              ·
                refine ⟨4754207076727816995819637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6338942768970422661092849 4754207076727816995819637)
                ·
                  refine ⟨445706913443232843358091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4754207076727816995819637 445706913443232843358091)
                  ·
                    rfl

theorem cell22_3906050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_3906050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3906050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3906050 prefixEnd_3906050 := by exact prefixLift 3906050
  have htrace : WordTrace (prefixWord ++ tailWord_3906050) baseStart_3906050 baseEnd_3906050 := by
    simpa [prefixWord, tailWord_3906050, baseEnd_3906050] using wordTrace_append hprefix tailTrace_3906050
  have hstable : (prefixWord ++ tailWord_3906050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906050).length < 2 ^ (prefixWord ++ tailWord_3906050).sum := by decide
  have hdescent : baseEnd_3906050 < baseStart_3906050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906076 : List Nat := [2, 2, 3, 1, 2, 4, 1, 1, 1, 5]
def baseStart_3906076 : Nat := 118140960795 + 3906076 * 2 ^ 59
def prefixEnd_3906076 : Nat := 4983230072969 + 3 ^ 40 * 3906076 * 2
def baseEnd_3906076 : Nat := 1337129640661043128924193

theorem tailTrace_3906076 : CollatzResearch.WordTrace tailWord_3906076 prefixEnd_3906076 1337129640661043128924193 := by
  unfold tailWord_3906076
  simp only [CollatzResearch.WordTrace]
  refine ⟨71233147898480615757497041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94977530531307487676662721 71233147898480615757497041)
  ·
    refine ⟨53424860923860461818122781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71233147898480615757497041 53424860923860461818122781)
    ·
      refine ⟨20034322846447673181796043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53424860923860461818122781 20034322846447673181796043)
      ·
        refine ⟨30051484269671509772694065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20034322846447673181796043 30051484269671509772694065)
        ·
          refine ⟨22538613202253632329520549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30051484269671509772694065 22538613202253632329520549)
          ·
            refine ⟨4225989975422556061785103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22538613202253632329520549 4225989975422556061785103)
            ·
              refine ⟨6338984963133834092677655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4225989975422556061785103 6338984963133834092677655)
              ·
                refine ⟨9508477444700751139016483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6338984963133834092677655 9508477444700751139016483)
                ·
                  refine ⟨14262716167051126708524725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9508477444700751139016483 14262716167051126708524725)
                  ·
                    refine ⟨1337129640661043128924193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14262716167051126708524725 1337129640661043128924193)
                    ·
                      rfl

theorem cell22_3906076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_3906076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3906076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3906076 prefixEnd_3906076 := by exact prefixLift 3906076
  have htrace : WordTrace (prefixWord ++ tailWord_3906076) baseStart_3906076 baseEnd_3906076 := by
    simpa [prefixWord, tailWord_3906076, baseEnd_3906076] using wordTrace_append hprefix tailTrace_3906076
  have hstable : (prefixWord ++ tailWord_3906076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906076).length < 2 ^ (prefixWord ++ tailWord_3906076).sum := by decide
  have hdescent : baseEnd_3906076 < baseStart_3906076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906142 : List Nat := [4, 4, 1, 2, 1, 1, 2, 1, 2, 4]
def baseStart_3906142 : Nat := 118140960795 + 3906142 * 2 ^ 59
def prefixEnd_3906142 : Nat := 4983230072969 + 3 ^ 40 * 3906142 * 2
def baseEnd_3906142 : Nat := 1337152233809840956773991

theorem tailTrace_3906142 : CollatzResearch.WordTrace tailWord_3906142 prefixEnd_3906142 1337152233809840956773991 := by
  unfold tailWord_3906142
  simp only [CollatzResearch.WordTrace]
  refine ⟨17808587876840265598362085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94979135343148083191264453 17808587876840265598362085)
  ·
    refine ⟨3339110226907549799692891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17808587876840265598362085 3339110226907549799692891)
    ·
      refine ⟨5008665340361324699539337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3339110226907549799692891 5008665340361324699539337)
      ·
        refine ⟨3756499005270993524654503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5008665340361324699539337 3756499005270993524654503)
        ·
          refine ⟨5634748507906490286981755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3756499005270993524654503 5634748507906490286981755)
          ·
            refine ⟨8452122761859735430472633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5634748507906490286981755 8452122761859735430472633)
            ·
              refine ⟨6339092071394801572854475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8452122761859735430472633 6339092071394801572854475)
              ·
                refine ⟨9508638107092202359281713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6339092071394801572854475 9508638107092202359281713)
                ·
                  refine ⟨7131478580319151769461285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9508638107092202359281713 7131478580319151769461285)
                  ·
                    refine ⟨1337152233809840956773991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7131478580319151769461285 1337152233809840956773991)
                    ·
                      rfl

theorem cell22_3906142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_3906142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3906142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3906142 prefixEnd_3906142 := by exact prefixLift 3906142
  have htrace : WordTrace (prefixWord ++ tailWord_3906142) baseStart_3906142 baseEnd_3906142 := by
    simpa [prefixWord, tailWord_3906142, baseEnd_3906142] using wordTrace_append hprefix tailTrace_3906142
  have hstable : (prefixWord ++ tailWord_3906142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906142).length < 2 ^ (prefixWord ++ tailWord_3906142).sum := by decide
  have hdescent : baseEnd_3906142 < baseStart_3906142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906196 : List Nat := [2, 4, 2, 2, 1, 1, 1, 1, 8]
def baseStart_3906196 : Nat := 118140960795 + 3906196 * 2 ^ 59
def prefixEnd_3906196 : Nat := 4983230072969 + 3 ^ 40 * 3906196 * 2
def baseEnd_3906196 : Nat := 445723573037800938641275

theorem tailTrace_3906196 : CollatzResearch.WordTrace tailWord_3906196 prefixEnd_3906196 445723573037800938641275 := by
  unfold tailWord_3906196
  simp only [CollatzResearch.WordTrace]
  refine ⟨71235336278263246004681221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94980448371017661339574961 71235336278263246004681221)
  ·
    refine ⟨13356625552174358625877729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71235336278263246004681221 13356625552174358625877729)
    ·
      refine ⟨10017469164130768969408297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13356625552174358625877729 10017469164130768969408297)
      ·
        refine ⟨7513101873098076727056223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10017469164130768969408297 7513101873098076727056223)
        ·
          refine ⟨11269652809647115090584335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7513101873098076727056223 11269652809647115090584335)
          ·
            refine ⟨16904479214470672635876503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11269652809647115090584335 16904479214470672635876503)
            ·
              refine ⟨25356718821706008953814755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16904479214470672635876503 25356718821706008953814755)
              ·
                refine ⟨38035078232559013430722133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25356718821706008953814755 38035078232559013430722133)
                ·
                  refine ⟨445723573037800938641275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38035078232559013430722133 445723573037800938641275)
                  ·
                    rfl

theorem cell22_3906196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_3906196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3906196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3906196 prefixEnd_3906196 := by exact prefixLift 3906196
  have htrace : WordTrace (prefixWord ++ tailWord_3906196) baseStart_3906196 baseEnd_3906196 := by
    simpa [prefixWord, tailWord_3906196, baseEnd_3906196] using wordTrace_append hprefix tailTrace_3906196
  have hstable : (prefixWord ++ tailWord_3906196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906196).length < 2 ^ (prefixWord ++ tailWord_3906196).sum := by decide
  have hdescent : baseEnd_3906196 < baseStart_3906196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906215 : List Nat := [1, 1, 6, 3, 1, 1, 1, 3, 1, 4]
def baseStart_3906215 : Nat := 118140960795 + 3906215 * 2 ^ 59
def prefixEnd_3906215 : Nat := 4983230072969 + 3 ^ 40 * 3906215 * 2
def baseEnd_3906215 : Nat := 1337177223201693099698767

theorem tailTrace_3906215 : CollatzResearch.WordTrace tailWord_3906215 prefixEnd_3906215 1337177223201693099698767 := by
  unfold tailWord_3906215
  simp only [CollatzResearch.WordTrace]
  refine ⟨142471365543457658254304099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94980910362305105502869399 142471365543457658254304099)
  ·
    refine ⟨213707048315186487381456149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142471365543457658254304099 213707048315186487381456149)
    ·
      refine ⟨10017517889774366596005757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 213707048315186487381456149 10017517889774366596005757)
      ·
        refine ⟨3756569208665387473502159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10017517889774366596005757 3756569208665387473502159)
        ·
          refine ⟨5634853812998081210253239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3756569208665387473502159 5634853812998081210253239)
          ·
            refine ⟨8452280719497121815379859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5634853812998081210253239 8452280719497121815379859)
            ·
              refine ⟨12678421079245682723069789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8452280719497121815379859 12678421079245682723069789)
              ·
                refine ⟨4754407904717131021151171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12678421079245682723069789 4754407904717131021151171)
                ·
                  refine ⟨7131611857075696531726757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4754407904717131021151171 7131611857075696531726757)
                  ·
                    refine ⟨1337177223201693099698767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7131611857075696531726757 1337177223201693099698767)
                    ·
                      rfl

theorem cell22_3906215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_3906215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3906215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3906215 prefixEnd_3906215 := by exact prefixLift 3906215
  have htrace : WordTrace (prefixWord ++ tailWord_3906215) baseStart_3906215 baseEnd_3906215 := by
    simpa [prefixWord, tailWord_3906215, baseEnd_3906215] using wordTrace_append hprefix tailTrace_3906215
  have hstable : (prefixWord ++ tailWord_3906215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906215).length < 2 ^ (prefixWord ++ tailWord_3906215).sum := by decide
  have hdescent : baseEnd_3906215 < baseStart_3906215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906230 : List Nat := [5, 1, 3, 1, 2, 1, 2, 1, 6]
def baseStart_3906230 : Nat := 118140960795 + 3906230 * 2 ^ 59
def prefixEnd_3906230 : Nat := 4983230072969 + 3 ^ 40 * 3906230 * 2
def baseEnd_3906230 : Nat := 445727452669412686857907

theorem tailTrace_3906230 : CollatzResearch.WordTrace tailWord_3906230 prefixEnd_3906230 445727452669412686857907 := by
  unfold tailWord_3906230
  simp only [CollatzResearch.WordTrace]
  refine ⟨8904494539900207238506259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94981275092268877210733429 8904494539900207238506259)
  ·
    refine ⟨13356741809850310857759389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8904494539900207238506259 13356741809850310857759389)
    ·
      refine ⟨5008778178693866571659771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13356741809850310857759389 5008778178693866571659771)
      ·
        refine ⟨7513167268040799857489657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5008778178693866571659771 7513167268040799857489657)
        ·
          refine ⟨5634875451030599893117243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7513167268040799857489657 5634875451030599893117243)
          ·
            refine ⟨8452313176545899839675865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5634875451030599893117243 8452313176545899839675865)
            ·
              refine ⟨6339234882409424879756899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8452313176545899839675865 6339234882409424879756899)
              ·
                refine ⟨9508852323614137319635349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6339234882409424879756899 9508852323614137319635349)
                ·
                  refine ⟨445727452669412686857907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9508852323614137319635349 445727452669412686857907)
                  ·
                    rfl

theorem cell22_3906230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_3906230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3906230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3906230 prefixEnd_3906230 := by exact prefixLift 3906230
  have htrace : WordTrace (prefixWord ++ tailWord_3906230) baseStart_3906230 baseEnd_3906230 := by
    simpa [prefixWord, tailWord_3906230, baseEnd_3906230] using wordTrace_append hprefix tailTrace_3906230
  have hstable : (prefixWord ++ tailWord_3906230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906230).length < 2 ^ (prefixWord ++ tailWord_3906230).sum := by decide
  have hdescent : baseEnd_3906230 < baseStart_3906230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906286 : List Nat := [4, 1, 2, 1, 1, 3, 2, 1, 7]
def baseStart_3906286 : Nat := 118140960795 + 3906286 * 2 ^ 59
def prefixEnd_3906286 : Nat := 4983230072969 + 3 ^ 40 * 3906286 * 2
def baseEnd_3906286 : Nat := 445733842650890860391183

theorem tailTrace_3906286 : CollatzResearch.WordTrace tailWord_3906286 prefixEnd_3906286 445733842650890860391183 := by
  unfold tailWord_3906286
  simp only [CollatzResearch.WordTrace]
  refine ⟨17809244390775054672517339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94982636750800291586759141 17809244390775054672517339)
  ·
    refine ⟨26713866586162582008776009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17809244390775054672517339 26713866586162582008776009)
    ·
      refine ⟨20035399939621936506582007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26713866586162582008776009 20035399939621936506582007)
      ·
        refine ⟨30053099909432904759873011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20035399939621936506582007 30053099909432904759873011)
        ·
          refine ⟨45079649864149357139809517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30053099909432904759873011 45079649864149357139809517)
          ·
            refine ⟨16904868699056008927428569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45079649864149357139809517 16904868699056008927428569)
            ·
              refine ⟨12678651524292006695571427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16904868699056008927428569 12678651524292006695571427)
              ·
                refine ⟨19017977286438010043357141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12678651524292006695571427 19017977286438010043357141)
                ·
                  refine ⟨445733842650890860391183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19017977286438010043357141 445733842650890860391183)
                  ·
                    rfl

theorem cell22_3906286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_3906286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3906286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3906286 prefixEnd_3906286 := by exact prefixLift 3906286
  have htrace : WordTrace (prefixWord ++ tailWord_3906286) baseStart_3906286 baseEnd_3906286 := by
    simpa [prefixWord, tailWord_3906286, baseEnd_3906286] using wordTrace_append hprefix tailTrace_3906286
  have hstable : (prefixWord ++ tailWord_3906286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906286).length < 2 ^ (prefixWord ++ tailWord_3906286).sum := by decide
  have hdescent : baseEnd_3906286 < baseStart_3906286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906290 : List Nat := [3, 2, 1, 3, 1, 4, 1, 1, 3, 3]
def baseStart_3906290 : Nat := 118140960795 + 3906290 * 2 ^ 59
def prefixEnd_3906290 : Nat := 4983230072969 + 3 ^ 40 * 3906290 * 2
def baseEnd_3906290 : Nat := 1337202897234417904073537

theorem tailTrace_3906290 : CollatzResearch.WordTrace tailWord_3906290 prefixEnd_3906290 1337202897234417904073537 := by
  unfold tailWord_3906290
  simp only [CollatzResearch.WordTrace]
  refine ⟨35618525254546486515821081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94982734012123964042189549 35618525254546486515821081)
  ·
    refine ⟨26713893940909864886865811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35618525254546486515821081 26713893940909864886865811)
    ·
      refine ⟨40070840911364797330298717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26713893940909864886865811 40070840911364797330298717)
      ·
        refine ⟨15026565341761798998862019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40070840911364797330298717 15026565341761798998862019)
        ·
          refine ⟨22539848012642698498293029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15026565341761798998862019 22539848012642698498293029)
          ·
            refine ⟨4226221502370505968429943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22539848012642698498293029 4226221502370505968429943)
            ·
              refine ⟨6339332253555758952644915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4226221502370505968429943 6339332253555758952644915)
              ·
                refine ⟨9508998380333638428967373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6339332253555758952644915 9508998380333638428967373)
                ·
                  refine ⟨3565874392625114410862765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9508998380333638428967373 3565874392625114410862765)
                  ·
                    refine ⟨1337202897234417904073537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3565874392625114410862765 1337202897234417904073537)
                    ·
                      rfl

theorem cell22_3906290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_3906290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3906290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3906290 prefixEnd_3906290 := by exact prefixLift 3906290
  have htrace : WordTrace (prefixWord ++ tailWord_3906290) baseStart_3906290 baseEnd_3906290 := by
    simpa [prefixWord, tailWord_3906290, baseEnd_3906290] using wordTrace_append hprefix tailTrace_3906290
  have hstable : (prefixWord ++ tailWord_3906290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906290).length < 2 ^ (prefixWord ++ tailWord_3906290).sum := by decide
  have hdescent : baseEnd_3906290 < baseStart_3906290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906348 : List Nat := [2, 2, 1, 1, 1, 4, 3, 4, 4]
def baseStart_3906348 : Nat := 118140960795 + 3906348 * 2 ^ 59
def prefixEnd_3906348 : Nat := 4983230072969 + 3 ^ 40 * 3906348 * 2
def baseEnd_3906348 : Nat := 445740917273241695374453

theorem tailTrace_3906348 : CollatzResearch.WordTrace tailWord_3906348 prefixEnd_3906348 445740917273241695374453 := by
  unfold tailWord_3906348
  simp only [CollatzResearch.WordTrace]
  refine ⟨71238108225987910984447849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94984144301317214645930465 71238108225987910984447849)
  ·
    refine ⟨53428581169490933238335887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71238108225987910984447849 53428581169490933238335887)
    ·
      refine ⟨80142871754236399857503831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53428581169490933238335887 80142871754236399857503831)
      ·
        refine ⟨120214307631354599786255747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80142871754236399857503831 120214307631354599786255747)
        ·
          refine ⟨180321461447031899679383621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120214307631354599786255747 180321461447031899679383621)
          ·
            refine ⟨33810274021318481189884429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180321461447031899679383621 33810274021318481189884429)
            ·
              refine ⟨12678852757994430446206661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33810274021318481189884429 12678852757994430446206661)
              ·
                refine ⟨2377284892123955708663749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12678852757994430446206661 2377284892123955708663749)
                ·
                  refine ⟨445740917273241695374453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2377284892123955708663749 445740917273241695374453)
                  ·
                    rfl

theorem cell22_3906348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 4, 4].length) (baseStart_3906348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3906348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3906348 prefixEnd_3906348 := by exact prefixLift 3906348
  have htrace : WordTrace (prefixWord ++ tailWord_3906348) baseStart_3906348 baseEnd_3906348 := by
    simpa [prefixWord, tailWord_3906348, baseEnd_3906348] using wordTrace_append hprefix tailTrace_3906348
  have hstable : (prefixWord ++ tailWord_3906348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906348).length < 2 ^ (prefixWord ++ tailWord_3906348).sum := by decide
  have hdescent : baseEnd_3906348 < baseStart_3906348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906414 : List Nat := [4, 1, 2, 3, 2, 1, 3, 1, 2, 3]
def baseStart_3906414 : Nat := 118140960795 + 3906414 * 2 ^ 59
def prefixEnd_3906414 : Nat := 4983230072969 + 3 ^ 40 * 3906414 * 2
def baseEnd_3906414 : Nat := 1337245344968522913973157

theorem tailTrace_3906414 : CollatzResearch.WordTrace tailWord_3906414 prefixEnd_3906414 1337245344968522913973157 := by
  unfold tailWord_3906414
  simp only [CollatzResearch.WordTrace]
  refine ⟨17809827958717089405099787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94985749113157810160532197 17809827958717089405099787)
  ·
    refine ⟨26714741938075634107649681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17809827958717089405099787 26714741938075634107649681)
    ·
      refine ⟨20036056453556725580737261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26714741938075634107649681 20036056453556725580737261)
      ·
        refine ⟨7513521170083772092776473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20036056453556725580737261 7513521170083772092776473)
        ·
          refine ⟨5635140877562829069582355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7513521170083772092776473 5635140877562829069582355)
          ·
            refine ⟨8452711316344243604373533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5635140877562829069582355 8452711316344243604373533)
            ·
              refine ⟨3169766743629091351640075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8452711316344243604373533 3169766743629091351640075)
              ·
                refine ⟨4754650115443637027460113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3169766743629091351640075 4754650115443637027460113)
                ·
                  refine ⟨3565987586582727770595085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4754650115443637027460113 3565987586582727770595085)
                  ·
                    refine ⟨1337245344968522913973157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3565987586582727770595085 1337245344968522913973157)
                    ·
                      rfl

theorem cell22_3906414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_3906414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3906414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3906414 prefixEnd_3906414 := by exact prefixLift 3906414
  have htrace : WordTrace (prefixWord ++ tailWord_3906414) baseStart_3906414 baseEnd_3906414 := by
    simpa [prefixWord, tailWord_3906414, baseEnd_3906414] using wordTrace_append hprefix tailTrace_3906414
  have hstable : (prefixWord ++ tailWord_3906414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906414).length < 2 ^ (prefixWord ++ tailWord_3906414).sum := by decide
  have hdescent : baseEnd_3906414 < baseStart_3906414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906468 : List Nat := [2, 3, 1, 2, 1, 2, 2, 2, 3, 4]
def baseStart_3906468 : Nat := 118140960795 + 3906468 * 2 ^ 59
def prefixEnd_3906468 : Nat := 4983230072969 + 3 ^ 40 * 3906468 * 2
def baseEnd_3906468 : Nat := 1337263830272084773122991

theorem tailTrace_3906468 : CollatzResearch.WordTrace tailWord_3906468 prefixEnd_3906468 1337263830272084773122991 := by
  unfold tailWord_3906468
  simp only [CollatzResearch.WordTrace]
  refine ⟨71240296605770541231632029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94987062141027388308842705 71240296605770541231632029)
  ·
    refine ⟨26715111227163952961862011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71240296605770541231632029 26715111227163952961862011)
    ·
      refine ⟨40072666840745929442793017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26715111227163952961862011 40072666840745929442793017)
      ·
        refine ⟨30054500130559447082094763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40072666840745929442793017 30054500130559447082094763)
        ·
          refine ⟨45081750195839170623142145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30054500130559447082094763 45081750195839170623142145)
          ·
            refine ⟨33811312646879377967356609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45081750195839170623142145 33811312646879377967356609)
            ·
              refine ⟨25358484485159533475517457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33811312646879377967356609 25358484485159533475517457)
              ·
                refine ⟨19018863363869650106638093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25358484485159533475517457 19018863363869650106638093)
                ·
                  refine ⟨7132073761451118789989285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19018863363869650106638093 7132073761451118789989285)
                  ·
                    refine ⟨1337263830272084773122991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7132073761451118789989285 1337263830272084773122991)
                    ·
                      rfl

theorem cell22_3906468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_3906468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3906468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3906468 prefixEnd_3906468 := by exact prefixLift 3906468
  have htrace : WordTrace (prefixWord ++ tailWord_3906468) baseStart_3906468 baseEnd_3906468 := by
    simpa [prefixWord, tailWord_3906468, baseEnd_3906468] using wordTrace_append hprefix tailTrace_3906468
  have hstable : (prefixWord ++ tailWord_3906468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906468).length < 2 ^ (prefixWord ++ tailWord_3906468).sum := by decide
  have hdescent : baseEnd_3906468 < baseStart_3906468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906511 : List Nat := [1, 1, 2, 1, 1, 16]
def baseStart_3906511 : Nat := 118140960795 + 3906511 * 2 ^ 59
def prefixEnd_3906511 : Nat := 4983230072969 + 3 ^ 40 * 3906511 * 2
def baseEnd_3906511 : Nat := 16509611729022802398739

theorem tailTrace_3906511 : CollatzResearch.WordTrace tailWord_3906511 prefixEnd_3906511 16509611729022802398739 := by
  unfold tailWord_3906511
  simp only [CollatzResearch.WordTrace]
  refine ⟨142482161550385300807079387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94988107700256867204719591 142482161550385300807079387)
  ·
    refine ⟨213723242325577951210619081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142482161550385300807079387 213723242325577951210619081)
    ·
      refine ⟨160292431744183463407964311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213723242325577951210619081 160292431744183463407964311)
      ·
        refine ⟨240438647616275195111946467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160292431744183463407964311 240438647616275195111946467)
        ·
          refine ⟨360657971424412792667919701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240438647616275195111946467 360657971424412792667919701)
          ·
            refine ⟨16509611729022802398739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 16 360657971424412792667919701 16509611729022802398739)
            ·
              rfl

theorem cell22_3906511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 16].length) (baseStart_3906511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3906511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3906511 prefixEnd_3906511 := by exact prefixLift 3906511
  have htrace : WordTrace (prefixWord ++ tailWord_3906511) baseStart_3906511 baseEnd_3906511 := by
    simpa [prefixWord, tailWord_3906511, baseEnd_3906511] using wordTrace_append hprefix tailTrace_3906511
  have hstable : (prefixWord ++ tailWord_3906511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906511).length < 2 ^ (prefixWord ++ tailWord_3906511).sum := by decide
  have hdescent : baseEnd_3906511 < baseStart_3906511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906513 : List Nat := [1, 2, 2, 1, 2, 1, 3, 4, 2, 4]
def baseStart_3906513 : Nat := 118140960795 + 3906513 * 2 ^ 59
def prefixEnd_3906513 : Nat := 4983230072969 + 3 ^ 40 * 3906513 * 2
def baseEnd_3906513 : Nat := 1337279234691719655747853

theorem tailTrace_3906513 : CollatzResearch.WordTrace tailWord_3906513 prefixEnd_3906513 1337279234691719655747853 := by
  unfold tailWord_3906513
  simp only [CollatzResearch.WordTrace]
  refine ⟨142482234496378055148652193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94988156330918703432434795 142482234496378055148652193)
  ·
    refine ⟨106861675872283541361489145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142482234496378055148652193 106861675872283541361489145)
    ·
      refine ⟨80146256904212656021116859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106861675872283541361489145 80146256904212656021116859)
      ·
        refine ⟨120219385356318984031675289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80146256904212656021116859 120219385356318984031675289)
        ·
          refine ⟨90164539017239238023756467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120219385356318984031675289 90164539017239238023756467)
          ·
            refine ⟨135246808525858857035634701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90164539017239238023756467 135246808525858857035634701)
            ·
              refine ⟨50717553197197071388363013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135246808525858857035634701 50717553197197071388363013)
              ·
                refine ⟨9509541224474450885318065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50717553197197071388363013 9509541224474450885318065)
                ·
                  refine ⟨7132155918355838163988549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9509541224474450885318065 7132155918355838163988549)
                  ·
                    refine ⟨1337279234691719655747853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7132155918355838163988549 1337279234691719655747853)
                    ·
                      rfl

theorem cell22_3906513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_3906513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3906513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3906513 prefixEnd_3906513 := by exact prefixLift 3906513
  have htrace : WordTrace (prefixWord ++ tailWord_3906513) baseStart_3906513 baseEnd_3906513 := by
    simpa [prefixWord, tailWord_3906513, baseEnd_3906513] using wordTrace_append hprefix tailTrace_3906513
  have hstable : (prefixWord ++ tailWord_3906513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906513).length < 2 ^ (prefixWord ++ tailWord_3906513).sum := by decide
  have hdescent : baseEnd_3906513 < baseStart_3906513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906517 : List Nat := [1, 3, 2, 3, 3, 1, 1, 4, 4]
def baseStart_3906517 : Nat := 118140960795 + 3906517 * 2 ^ 59
def prefixEnd_3906517 : Nat := 4983230072969 + 3 ^ 40 * 3906517 * 2
def baseEnd_3906517 : Nat := 445760201324488326215947

theorem tailTrace_3906517 : CollatzResearch.WordTrace tailWord_3906517 prefixEnd_3906517 445760201324488326215947 := by
  unfold tailWord_3906517
  simp only [CollatzResearch.WordTrace]
  refine ⟨142482380388363563831797805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94988253592242375887865203 142482380388363563831797805)
  ·
    refine ⟨53430892645636336436924177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142482380388363563831797805 53430892645636336436924177)
    ·
      refine ⟨40073169484227252327693133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53430892645636336436924177 40073169484227252327693133)
      ·
        refine ⟨15027438556585219622884925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40073169484227252327693133 15027438556585219622884925)
        ·
          refine ⟨5635289458719457358581847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15027438556585219622884925 5635289458719457358581847)
          ·
            refine ⟨8452934188079186037872771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5635289458719457358581847 8452934188079186037872771)
            ·
              refine ⟨12679401282118779056809157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8452934188079186037872771 12679401282118779056809157)
              ·
                refine ⟨2377387740397271073151717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12679401282118779056809157 2377387740397271073151717)
                ·
                  refine ⟨445760201324488326215947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2377387740397271073151717 445760201324488326215947)
                  ·
                    rfl

theorem cell22_3906517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 4, 4].length) (baseStart_3906517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3906517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3906517 prefixEnd_3906517 := by exact prefixLift 3906517
  have htrace : WordTrace (prefixWord ++ tailWord_3906517) baseStart_3906517 baseEnd_3906517 := by
    simpa [prefixWord, tailWord_3906517, baseEnd_3906517] using wordTrace_append hprefix tailTrace_3906517
  have hstable : (prefixWord ++ tailWord_3906517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906517).length < 2 ^ (prefixWord ++ tailWord_3906517).sum := by decide
  have hdescent : baseEnd_3906517 < baseStart_3906517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906545 : List Nat := [1, 2, 2, 2, 4, 2, 3, 6]
def baseStart_3906545 : Nat := 118140960795 + 3906545 * 2 ^ 59
def prefixEnd_3906545 : Nat := 4983230072969 + 3 ^ 40 * 3906545 * 2
def baseEnd_3906545 : Nat := 148587798771742470994195

theorem tailTrace_3906545 : CollatzResearch.WordTrace tailWord_3906545 prefixEnd_3906545 148587798771742470994195 := by
  unfold tailWord_3906545
  simp only [CollatzResearch.WordTrace]
  refine ⟨142483401632262124613817089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94988934421508083075878059 142483401632262124613817089)
  ·
    refine ⟨106862551224196593460362817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142483401632262124613817089 106862551224196593460362817)
    ·
      refine ⟨80146913418147445095272113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106862551224196593460362817 80146913418147445095272113)
      ·
        refine ⟨60110185063610583821454085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80146913418147445095272113 60110185063610583821454085)
        ·
          refine ⟨11270659699426984466522641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60110185063610583821454085 11270659699426984466522641)
          ·
            refine ⟨8452994774570238349891981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11270659699426984466522641 8452994774570238349891981)
            ·
              refine ⟨3169873040463839381209493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8452994774570238349891981 3169873040463839381209493)
              ·
                refine ⟨148587798771742470994195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3169873040463839381209493 148587798771742470994195)
                ·
                  rfl

theorem cell22_3906545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 6].length) (baseStart_3906545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3906545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3906545 prefixEnd_3906545 := by exact prefixLift 3906545
  have htrace : WordTrace (prefixWord ++ tailWord_3906545) baseStart_3906545 baseEnd_3906545 := by
    simpa [prefixWord, tailWord_3906545, baseEnd_3906545] using wordTrace_append hprefix tailTrace_3906545
  have hstable : (prefixWord ++ tailWord_3906545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906545).length < 2 ^ (prefixWord ++ tailWord_3906545).sum := by decide
  have hdescent : baseEnd_3906545 < baseStart_3906545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906562 : List Nat := [3, 4, 1, 3, 1, 1, 9]
def baseStart_3906562 : Nat := 118140960795 + 3906562 * 2 ^ 59
def prefixEnd_3906562 : Nat := 4983230072969 + 3 ^ 40 * 3906562 * 2
def baseEnd_3906562 : Nat := 49529481792337031898989

theorem tailTrace_3906562 : CollatzResearch.WordTrace tailWord_3906562 prefixEnd_3906562 49529481792337031898989 := by
  unfold tailWord_3906562
  simp only [CollatzResearch.WordTrace]
  refine ⟨35621005418300134129296485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94989347782133691011457293 35621005418300134129296485)
  ·
    refine ⟨6678938515931275149243091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35621005418300134129296485 6678938515931275149243091)
    ·
      refine ⟨10018407773896912723864637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6678938515931275149243091 10018407773896912723864637)
      ·
        refine ⟨3756902915211342271449239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10018407773896912723864637 3756902915211342271449239)
        ·
          refine ⟨5635354372817013407173859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3756902915211342271449239 5635354372817013407173859)
          ·
            refine ⟨8453031559225520110760789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5635354372817013407173859 8453031559225520110760789)
            ·
              refine ⟨49529481792337031898989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8453031559225520110760789 49529481792337031898989)
              ·
                rfl

theorem cell22_3906562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 9].length) (baseStart_3906562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3906562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3906562 prefixEnd_3906562 := by exact prefixLift 3906562
  have htrace : WordTrace (prefixWord ++ tailWord_3906562) baseStart_3906562 baseEnd_3906562 := by
    simpa [prefixWord, tailWord_3906562, baseEnd_3906562] using wordTrace_append hprefix tailTrace_3906562
  have hstable : (prefixWord ++ tailWord_3906562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906562).length < 2 ^ (prefixWord ++ tailWord_3906562).sum := by decide
  have hdescent : baseEnd_3906562 < baseStart_3906562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906618 : List Nat := [3, 1, 1, 1, 3, 1, 2, 2, 8]
def baseStart_3906618 : Nat := 118140960795 + 3906618 * 2 ^ 59
def prefixEnd_3906618 : Nat := 4983230072969 + 3 ^ 40 * 3906618 * 2
def baseEnd_3906618 : Nat := 445771726112511460624177

theorem tailTrace_3906618 : CollatzResearch.WordTrace tailWord_3906618 prefixEnd_3906618 445771726112511460624177 := by
  unfold tailWord_3906618
  simp only [CollatzResearch.WordTrace]
  refine ⟨35621516040249414520306127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94990709440665105387483005 35621516040249414520306127)
  ·
    refine ⟨53432274060374121780459191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35621516040249414520306127 53432274060374121780459191)
    ·
      refine ⟨80148411090561182670688787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53432274060374121780459191 80148411090561182670688787)
      ·
        refine ⟨120222616635841774006033181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80148411090561182670688787 120222616635841774006033181)
        ·
          refine ⟨45083481238440665252262443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120222616635841774006033181 45083481238440665252262443)
          ·
            refine ⟨67625221857660997878393665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45083481238440665252262443 67625221857660997878393665)
            ·
              refine ⟨50718916393245748408795249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67625221857660997878393665 50718916393245748408795249)
              ·
                refine ⟨38039187294934311306596437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50718916393245748408795249 38039187294934311306596437)
                ·
                  refine ⟨445771726112511460624177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38039187294934311306596437 445771726112511460624177)
                  ·
                    rfl

theorem cell22_3906618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 8].length) (baseStart_3906618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3906618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3906618 prefixEnd_3906618 := by exact prefixLift 3906618
  have htrace : WordTrace (prefixWord ++ tailWord_3906618) baseStart_3906618 baseEnd_3906618 := by
    simpa [prefixWord, tailWord_3906618, baseEnd_3906618] using wordTrace_append hprefix tailTrace_3906618
  have hstable : (prefixWord ++ tailWord_3906618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906618).length < 2 ^ (prefixWord ++ tailWord_3906618).sum := by decide
  have hdescent : baseEnd_3906618 < baseStart_3906618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906633 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 5, 5]
def baseStart_3906633 : Nat := 118140960795 + 3906633 * 2 ^ 59
def prefixEnd_3906633 : Nat := 4983230072969 + 3 ^ 40 * 3906633 * 2
def baseEnd_3906633 : Nat := 1337320313144079342747485

theorem tailTrace_3906633 : CollatzResearch.WordTrace tailWord_3906633 prefixEnd_3906633 1337320313144079342747485 := by
  unfold tailWord_3906633
  simp only [CollatzResearch.WordTrace]
  refine ⟨142486611255943315643020553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94991074170628877095347035 142486611255943315643020553)
  ·
    refine ⟨106864958441957486732265415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142486611255943315643020553 106864958441957486732265415)
    ·
      refine ⟨160297437662936230098398123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106864958441957486732265415 160297437662936230098398123)
      ·
        refine ⟨240446156494404345147597185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160297437662936230098398123 240446156494404345147597185)
        ·
          refine ⟨180334617370803258860697889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240446156494404345147597185 180334617370803258860697889)
          ·
            refine ⟨135250963028102444145523417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180334617370803258860697889 135250963028102444145523417)
            ·
              refine ⟨101438222271076833109142563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135250963028102444145523417 101438222271076833109142563)
              ·
                refine ⟨152157333406615249663713845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101438222271076833109142563 152157333406615249663713845)
                ·
                  refine ⟨14264750006870179655973173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 152157333406615249663713845 14264750006870179655973173)
                  ·
                    refine ⟨1337320313144079342747485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14264750006870179655973173 1337320313144079342747485)
                    ·
                      rfl

theorem cell22_3906633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 5].length) (baseStart_3906633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3906633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3906633 prefixEnd_3906633 := by exact prefixLift 3906633
  have htrace : WordTrace (prefixWord ++ tailWord_3906633) baseStart_3906633 baseEnd_3906633 := by
    simpa [prefixWord, tailWord_3906633, baseEnd_3906633] using wordTrace_append hprefix tailTrace_3906633
  have hstable : (prefixWord ++ tailWord_3906633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906633).length < 2 ^ (prefixWord ++ tailWord_3906633).sum := by decide
  have hdescent : baseEnd_3906633 < baseStart_3906633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906650 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 6, 3]
def baseStart_3906650 : Nat := 118140960795 + 3906650 * 2 ^ 59
def prefixEnd_3906650 : Nat := 4983230072969 + 3 ^ 40 * 3906650 * 2
def baseEnd_3906650 : Nat := 1337326132591496965072433

theorem tailTrace_3906650 : CollatzResearch.WordTrace tailWord_3906650 prefixEnd_3906650 1337326132591496965072433 := by
  unfold tailWord_3906650
  simp only [CollatzResearch.WordTrace]
  refine ⟨35621807824220431886597351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94991487531254485030926269 35621807824220431886597351)
  ·
    refine ⟨53432711736330647829896027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35621807824220431886597351 53432711736330647829896027)
    ·
      refine ⟨80149067604495971744844041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53432711736330647829896027 80149067604495971744844041)
      ·
        refine ⟨60111800703371978808633031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80149067604495971744844041 60111800703371978808633031)
        ·
          refine ⟨90167701055057968212949547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60111800703371978808633031 90167701055057968212949547)
          ·
            refine ⟨135251551582586952319424321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90167701055057968212949547 135251551582586952319424321)
            ·
              refine ⟨101438663686940214239568241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135251551582586952319424321 101438663686940214239568241)
              ·
                refine ⟨76078997765205160679676181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101438663686940214239568241 76078997765205160679676181)
                ·
                  refine ⟨3566203020243991906859821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 76078997765205160679676181 3566203020243991906859821)
                  ·
                    refine ⟨1337326132591496965072433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3566203020243991906859821 1337326132591496965072433)
                    ·
                      rfl

theorem cell22_3906650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 6, 3].length) (baseStart_3906650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3906650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3906650 prefixEnd_3906650 := by exact prefixLift 3906650
  have htrace : WordTrace (prefixWord ++ tailWord_3906650) baseStart_3906650 baseEnd_3906650 := by
    simpa [prefixWord, tailWord_3906650, baseEnd_3906650] using wordTrace_append hprefix tailTrace_3906650
  have hstable : (prefixWord ++ tailWord_3906650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906650).length < 2 ^ (prefixWord ++ tailWord_3906650).sum := by decide
  have hdescent : baseEnd_3906650 < baseStart_3906650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906665 : List Nat := [1, 2, 1, 1, 1, 6, 1, 3, 2, 4]
def baseStart_3906665 : Nat := 118140960795 + 3906665 * 2 ^ 59
def prefixEnd_3906665 : Nat := 4983230072969 + 3 ^ 40 * 3906665 * 2
def baseEnd_3906665 : Nat := 1337331267398041925947387

theorem tailTrace_3906665 : CollatzResearch.WordTrace tailWord_3906665 prefixEnd_3906665 1337331267398041925947387 := by
  unfold tailWord_3906665
  simp only [CollatzResearch.WordTrace]
  refine ⟨142487778391827385108185449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94991852261218256738790299 142487778391827385108185449)
  ·
    refine ⟨106865833793870538831139087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142487778391827385108185449 106865833793870538831139087)
    ·
      refine ⟨160298750690805808246708631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106865833793870538831139087 160298750690805808246708631)
      ·
        refine ⟨240448126036208712370062947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160298750690805808246708631 240448126036208712370062947)
        ·
          refine ⟨360672189054313068555094421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240448126036208712370062947 360672189054313068555094421)
          ·
            refine ⟨16906508861920925088520051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 360672189054313068555094421 16906508861920925088520051)
            ·
              refine ⟨25359763292881387632780077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16906508861920925088520051 25359763292881387632780077)
              ·
                refine ⟨9509911234830520362292529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25359763292881387632780077 9509911234830520362292529)
                ·
                  refine ⟨7132433426122890271719397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9509911234830520362292529 7132433426122890271719397)
                  ·
                    refine ⟨1337331267398041925947387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7132433426122890271719397 1337331267398041925947387)
                    ·
                      rfl

theorem cell22_3906665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 4].length) (baseStart_3906665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3906665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3906665 prefixEnd_3906665 := by exact prefixLift 3906665
  have htrace : WordTrace (prefixWord ++ tailWord_3906665) baseStart_3906665 baseEnd_3906665 := by
    simpa [prefixWord, tailWord_3906665, baseEnd_3906665] using wordTrace_append hprefix tailTrace_3906665
  have hstable : (prefixWord ++ tailWord_3906665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906665).length < 2 ^ (prefixWord ++ tailWord_3906665).sum := by decide
  have hdescent : baseEnd_3906665 < baseStart_3906665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906712 : List Nat := [2, 1, 2, 4, 2, 1, 1, 1, 5, 3]
def baseStart_3906712 : Nat := 118140960795 + 3906712 * 2 ^ 59
def prefixEnd_3906712 : Nat := 4983230072969 + 3 ^ 40 * 3906712 * 2
def baseEnd_3906712 : Nat := 1337347356458549470022243

theorem tailTrace_3906712 : CollatzResearch.WordTrace tailWord_3906712 prefixEnd_3906712 1337347356458549470022243 := by
  unfold tailWord_3906712
  simp only [CollatzResearch.WordTrace]
  refine ⟨71244746311328556067573195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94992995081771408090097593 71244746311328556067573195)
  ·
    refine ⟨106867119466992834101359793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71244746311328556067573195 106867119466992834101359793)
    ·
      refine ⟨80150339600244625576019845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106867119466992834101359793 80150339600244625576019845)
      ·
        refine ⟨15028188675045867295503721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80150339600244625576019845 15028188675045867295503721)
        ·
          refine ⟨11271141506284400471627791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15028188675045867295503721 11271141506284400471627791)
          ·
            refine ⟨16906712259426600707441687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11271141506284400471627791 16906712259426600707441687)
            ·
              refine ⟨25360068389139901061162531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16906712259426600707441687 25360068389139901061162531)
              ·
                refine ⟨38040102583709851591743797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25360068389139901061162531 38040102583709851591743797)
                ·
                  refine ⟨3566259617222798586725981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38040102583709851591743797 3566259617222798586725981)
                  ·
                    refine ⟨1337347356458549470022243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3566259617222798586725981 1337347356458549470022243)
                    ·
                      rfl

theorem cell22_3906712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 5, 3].length) (baseStart_3906712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3906712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3906712 prefixEnd_3906712 := by exact prefixLift 3906712
  have htrace : WordTrace (prefixWord ++ tailWord_3906712) baseStart_3906712 baseEnd_3906712 := by
    simpa [prefixWord, tailWord_3906712, baseEnd_3906712] using wordTrace_append hprefix tailTrace_3906712
  have hstable : (prefixWord ++ tailWord_3906712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906712).length < 2 ^ (prefixWord ++ tailWord_3906712).sum := by decide
  have hdescent : baseEnd_3906712 < baseStart_3906712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906755 : List Nat := [1, 1, 1, 3, 1, 1, 1, 6, 3, 4]
def baseStart_3906755 : Nat := 118140960795 + 3906755 * 2 ^ 59
def prefixEnd_3906755 : Nat := 4983230072969 + 3 ^ 40 * 3906755 * 2
def baseEnd_3906755 : Nat := 1337362076237311691197111

theorem tailTrace_3906755 : CollatzResearch.WordTrace tailWord_3906755 prefixEnd_3906755 1337362076237311691197111 := by
  unfold tailWord_3906755
  simp only [CollatzResearch.WordTrace]
  refine ⟨142491060961501330478961719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94994040641000886985974479 142491060961501330478961719)
  ·
    refine ⟨213736591442251995718442579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142491060961501330478961719 213736591442251995718442579)
    ·
      refine ⟨320604887163377993577663869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213736591442251995718442579 320604887163377993577663869)
      ·
        refine ⟨120226832686266747591623951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320604887163377993577663869 120226832686266747591623951)
        ·
          refine ⟨180340249029400121387435927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120226832686266747591623951 180340249029400121387435927)
          ·
            refine ⟨270510373544100182081153891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180340249029400121387435927 270510373544100182081153891)
            ·
              refine ⟨405765560316150273121730837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270510373544100182081153891 405765560316150273121730837)
              ·
                refine ⟨19020260639819544052581133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 405765560316150273121730837 19020260639819544052581133)
                ·
                  refine ⟨7132597739932329019717925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19020260639819544052581133 7132597739932329019717925)
                  ·
                    refine ⟨1337362076237311691197111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7132597739932329019717925 1337362076237311691197111)
                    ·
                      rfl

theorem cell22_3906755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 4].length) (baseStart_3906755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3906755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3906755 prefixEnd_3906755 := by exact prefixLift 3906755
  have htrace : WordTrace (prefixWord ++ tailWord_3906755) baseStart_3906755 baseEnd_3906755 := by
    simpa [prefixWord, tailWord_3906755, baseEnd_3906755] using wordTrace_append hprefix tailTrace_3906755
  have hstable : (prefixWord ++ tailWord_3906755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906755).length < 2 ^ (prefixWord ++ tailWord_3906755).sum := by decide
  have hdescent : baseEnd_3906755 < baseStart_3906755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906815 : List Nat := [1, 1, 2, 2, 1, 5, 1, 9]
def baseStart_3906815 : Nat := 118140960795 + 3906815 * 2 ^ 59
def prefixEnd_3906815 : Nat := 4983230072969 + 3 ^ 40 * 3906815 * 2
def baseEnd_3906815 : Nat := 148598068384832392744103

theorem tailTrace_3906815 : CollatzResearch.WordTrace tailWord_3906815 prefixEnd_3906815 148598068384832392744103 := by
  unfold tailWord_3906815
  simp only [CollatzResearch.WordTrace]
  refine ⟨142493249341283960726145899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94995499560855973817430599 142493249341283960726145899)
  ·
    refine ⟨213739874011925941089218849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142493249341283960726145899 213739874011925941089218849)
    ·
      refine ⟨160304905508944455816914137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213739874011925941089218849 160304905508944455816914137)
      ·
        refine ⟨120228679131708341862685603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160304905508944455816914137 120228679131708341862685603)
        ·
          refine ⟨180343018697562512794028405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120228679131708341862685603 180343018697562512794028405)
          ·
            refine ⟨16907158002896485574440163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 180343018697562512794028405 16907158002896485574440163)
            ·
              refine ⟨25360737004344728361660245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16907158002896485574440163 25360737004344728361660245)
              ·
                refine ⟨148598068384832392744103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25360737004344728361660245 148598068384832392744103)
                ·
                  rfl

theorem cell22_3906815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 9].length) (baseStart_3906815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3906815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3906815 prefixEnd_3906815 := by exact prefixLift 3906815
  have htrace : WordTrace (prefixWord ++ tailWord_3906815) baseStart_3906815 baseEnd_3906815 := by
    simpa [prefixWord, tailWord_3906815, baseEnd_3906815] using wordTrace_append hprefix tailTrace_3906815
  have hstable : (prefixWord ++ tailWord_3906815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906815).length < 2 ^ (prefixWord ++ tailWord_3906815).sum := by decide
  have hdescent : baseEnd_3906815 < baseStart_3906815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906819 : List Nat := [1, 1, 1, 3, 2, 5, 1, 3, 2, 3]
def baseStart_3906819 : Nat := 118140960795 + 3906819 * 2 ^ 59
def prefixEnd_3906819 : Nat := 4983230072969 + 3 ^ 40 * 3906819 * 2
def baseEnd_3906819 : Nat := 1337383984745236857596915

theorem tailTrace_3906819 : CollatzResearch.WordTrace tailWord_3906819 prefixEnd_3906819 1337383984745236857596915 := by
  unfold tailWord_3906819
  simp only [CollatzResearch.WordTrace]
  refine ⟨142493395233269469409291511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94995596822179646272861007 142493395233269469409291511)
  ·
    refine ⟨213740092849904204113937267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142493395233269469409291511 213740092849904204113937267)
    ·
      refine ⟨320610139274856306170905901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213740092849904204113937267 320610139274856306170905901)
      ·
        refine ⟨120228802228071114814089713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320610139274856306170905901 120228802228071114814089713)
        ·
          refine ⟨90171601671053336110567285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120228802228071114814089713 90171601671053336110567285)
          ·
            refine ⟨8453587656661250260365683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90171601671053336110567285 8453587656661250260365683)
            ·
              refine ⟨12680381484991875390548525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8453587656661250260365683 12680381484991875390548525)
              ·
                refine ⟨4755143056871953271455697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12680381484991875390548525 4755143056871953271455697)
                ·
                  refine ⟨3566357292653964953591773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4755143056871953271455697 3566357292653964953591773)
                  ·
                    refine ⟨1337383984745236857596915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3566357292653964953591773 1337383984745236857596915)
                    ·
                      rfl

theorem cell22_3906819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 3, 2, 3].length) (baseStart_3906819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3906819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3906819 prefixEnd_3906819 := by exact prefixLift 3906819
  have htrace : WordTrace (prefixWord ++ tailWord_3906819) baseStart_3906819 baseEnd_3906819 := by
    simpa [prefixWord, tailWord_3906819, baseEnd_3906819] using wordTrace_append hprefix tailTrace_3906819
  have hstable : (prefixWord ++ tailWord_3906819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906819).length < 2 ^ (prefixWord ++ tailWord_3906819).sum := by decide
  have hdescent : baseEnd_3906819 < baseStart_3906819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906881 : List Nat := [1, 2, 5, 2, 1, 2, 1, 2, 3, 3]
def baseStart_3906881 : Nat := 118140960795 + 3906881 * 2 ^ 59
def prefixEnd_3906881 : Nat := 4983230072969 + 3 ^ 40 * 3906881 * 2
def baseEnd_3906881 : Nat := 1337405208612289362546725

theorem tailTrace_3906881 : CollatzResearch.WordTrace tailWord_3906881 prefixEnd_3906881 1337405208612289362546725 := by
  unfold tailWord_3906881
  simp only [CollatzResearch.WordTrace]
  refine ⟨142495656559044853998048497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94997104372696569332032331 142495656559044853998048497)
  ·
    refine ⟨106871742419283640498536373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142495656559044853998048497 106871742419283640498536373)
    ·
      refine ⟨10019225851807841296737785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106871742419283640498536373 10019225851807841296737785)
      ·
        refine ⟨7514419388855880972553339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10019225851807841296737785 7514419388855880972553339)
        ·
          refine ⟨11271629083283821458830009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7514419388855880972553339 11271629083283821458830009)
          ·
            refine ⟨8453721812462866094122507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11271629083283821458830009 8453721812462866094122507)
            ·
              refine ⟨12680582718694299141183761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8453721812462866094122507 12680582718694299141183761)
              ·
                refine ⟨9510437039020724355887821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12680582718694299141183761 9510437039020724355887821)
                ·
                  refine ⟨3566413889632771633457933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9510437039020724355887821 3566413889632771633457933)
                  ·
                    refine ⟨1337405208612289362546725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3566413889632771633457933 1337405208612289362546725)
                    ·
                      rfl

theorem cell22_3906881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_3906881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3906881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3906881 prefixEnd_3906881 := by exact prefixLift 3906881
  have htrace : WordTrace (prefixWord ++ tailWord_3906881) baseStart_3906881 baseEnd_3906881 := by
    simpa [prefixWord, tailWord_3906881, baseEnd_3906881] using wordTrace_append hprefix tailTrace_3906881
  have hstable : (prefixWord ++ tailWord_3906881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906881).length < 2 ^ (prefixWord ++ tailWord_3906881).sum := by decide
  have hdescent : baseEnd_3906881 < baseStart_3906881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906969 : List Nat := [1, 2, 1, 2, 1, 6, 1, 2, 2, 4]
def baseStart_3906969 : Nat := 118140960795 + 3906969 * 2 ^ 59
def prefixEnd_3906969 : Nat := 4983230072969 + 3 ^ 40 * 3906969 * 2
def baseEnd_3906969 : Nat := 1337435332810686466346455

theorem tailTrace_3906969 : CollatzResearch.WordTrace tailWord_3906969 prefixEnd_3906969 1337435332810686466346455 := by
  unfold tailWord_3906969
  simp only [CollatzResearch.WordTrace]
  refine ⟨142498866182726045027251961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94999244121817363351501307 142498866182726045027251961)
  ·
    refine ⟨106874149637044533770438971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142498866182726045027251961 106874149637044533770438971)
    ·
      refine ⟨160311224455566800655658457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106874149637044533770438971 160311224455566800655658457)
      ·
        refine ⟨120233418341675100491743843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160311224455566800655658457 120233418341675100491743843)
        ·
          refine ⟨180350127512512650737615765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120233418341675100491743843 180350127512512650737615765)
          ·
            refine ⟨8453912227149030503325739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 180350127512512650737615765 8453912227149030503325739)
            ·
              refine ⟨12680868340723545754988609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8453912227149030503325739 12680868340723545754988609)
              ·
                refine ⟨9510651255542659316241457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12680868340723545754988609 9510651255542659316241457)
                ·
                  refine ⟨7132988441656994487181093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9510651255542659316241457 7132988441656994487181093)
                  ·
                    refine ⟨1337435332810686466346455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7132988441656994487181093 1337435332810686466346455)
                    ·
                      rfl

theorem cell22_3906969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 4].length) (baseStart_3906969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3906969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3906969 prefixEnd_3906969 := by exact prefixLift 3906969
  have htrace : WordTrace (prefixWord ++ tailWord_3906969) baseStart_3906969 baseEnd_3906969 := by
    simpa [prefixWord, tailWord_3906969, baseEnd_3906969] using wordTrace_append hprefix tailTrace_3906969
  have hstable : (prefixWord ++ tailWord_3906969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906969).length < 2 ^ (prefixWord ++ tailWord_3906969).sum := by decide
  have hdescent : baseEnd_3906969 < baseStart_3906969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906973 : List Nat := [1, 4, 2, 1, 3, 2, 3, 2, 4]
def baseStart_3906973 : Nat := 118140960795 + 3906973 * 2 ^ 59
def prefixEnd_3906973 : Nat := 4983230072969 + 3 ^ 40 * 3906973 * 2
def baseEnd_3906973 : Nat := 445812234030810596415481

theorem tailTrace_3906973 : CollatzResearch.WordTrace tailWord_3906973 prefixEnd_3906973 445812234030810596415481 := by
  unfold tailWord_3906973
  simp only [CollatzResearch.WordTrace]
  refine ⟨142499012074711553710397573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94999341383141035806931715 142499012074711553710397573)
  ·
    refine ⟨26718564764008416320699545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142499012074711553710397573 26718564764008416320699545)
    ·
      refine ⟨20038923573006312240524659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26718564764008416320699545 20038923573006312240524659)
      ·
        refine ⟨30058385359509468360786989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20038923573006312240524659 30058385359509468360786989)
        ·
          refine ⟨11271894509816050635295121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30058385359509468360786989 11271894509816050635295121)
          ·
            refine ⟨8453920882362037976471341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11271894509816050635295121 8453920882362037976471341)
            ·
              refine ⟨3170220330885764241176753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8453920882362037976471341 3170220330885764241176753)
              ·
                refine ⟨2377665248164323180882565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3170220330885764241176753 2377665248164323180882565)
                ·
                  refine ⟨445812234030810596415481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2377665248164323180882565 445812234030810596415481)
                  ·
                    rfl

theorem cell22_3906973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_3906973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3906973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3906973 prefixEnd_3906973 := by exact prefixLift 3906973
  have htrace : WordTrace (prefixWord ++ tailWord_3906973) baseStart_3906973 baseEnd_3906973 := by
    simpa [prefixWord, tailWord_3906973, baseEnd_3906973] using wordTrace_append hprefix tailTrace_3906973
  have hstable : (prefixWord ++ tailWord_3906973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906973).length < 2 ^ (prefixWord ++ tailWord_3906973).sum := by decide
  have hdescent : baseEnd_3906973 < baseStart_3906973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3906999 : List Nat := [1, 1, 3, 1, 3, 2, 2, 1, 5, 3]
def baseStart_3906999 : Nat := 118140960795 + 3906999 * 2 ^ 59
def prefixEnd_3906999 : Nat := 4983230072969 + 3 ^ 40 * 3906999 * 2
def baseEnd_3906999 : Nat := 1337445602423776388096363

theorem tailTrace_3906999 : CollatzResearch.WordTrace tailWord_3906999 prefixEnd_3906999 1337445602423776388096363 := by
  unfold tailWord_3906999
  simp only [CollatzResearch.WordTrace]
  refine ⟨142499960372617360150844051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94999973581744906767229367 142499960372617360150844051)
  ·
    refine ⟨213749940558926040226266077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142499960372617360150844051 213749940558926040226266077)
    ·
      refine ⟨80156227709597265084849779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213749940558926040226266077 80156227709597265084849779)
      ·
        refine ⟨120234341564395897627274669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80156227709597265084849779 120234341564395897627274669)
        ·
          refine ⟨45087878086648461610228001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120234341564395897627274669 45087878086648461610228001)
          ·
            refine ⟨33815908564986346207671001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45087878086648461610228001 33815908564986346207671001)
            ·
              refine ⟨25361931423739759655753251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33815908564986346207671001 25361931423739759655753251)
              ·
                refine ⟨38042897135609639483629877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25361931423739759655753251 38042897135609639483629877)
                ·
                  refine ⟨3566521606463403701590301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38042897135609639483629877 3566521606463403701590301)
                  ·
                    refine ⟨1337445602423776388096363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3566521606463403701590301 1337445602423776388096363)
                    ·
                      rfl

theorem cell22_3906999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 5, 3].length) (baseStart_3906999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3906999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3906999 prefixEnd_3906999 := by exact prefixLift 3906999
  have htrace : WordTrace (prefixWord ++ tailWord_3906999) baseStart_3906999 baseEnd_3906999 := by
    simpa [prefixWord, tailWord_3906999, baseEnd_3906999] using wordTrace_append hprefix tailTrace_3906999
  have hstable : (prefixWord ++ tailWord_3906999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3906999).length < 2 ^ (prefixWord ++ tailWord_3906999).sum := by decide
  have hdescent : baseEnd_3906999 < baseStart_3906999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3906999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907033 : List Nat := [1, 2, 1, 2, 4, 3, 1, 4, 1, 3]
def baseStart_3907033 : Nat := 118140960795 + 3907033 * 2 ^ 59
def prefixEnd_3907033 : Nat := 4983230072969 + 3 ^ 40 * 3907033 * 2
def baseEnd_3907033 : Nat := 1337457241318611632746259

theorem tailTrace_3907033 : CollatzResearch.WordTrace tailWord_3907033 prefixEnd_3907033 1337457241318611632746259 := by
  unfold tailWord_3907033
  simp only [CollatzResearch.WordTrace]
  refine ⟨142501200454494183957581753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95000800302996122638387835 142501200454494183957581753)
  ·
    refine ⟨106875900340870637968186315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142501200454494183957581753 106875900340870637968186315)
    ·
      refine ⟨160313850511305956952279473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106875900340870637968186315 160313850511305956952279473)
      ·
        refine ⟨120235387883479467714209605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160313850511305956952279473 120235387883479467714209605)
        ·
          refine ⟨22544135228152400196414301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120235387883479467714209605 22544135228152400196414301)
          ·
            refine ⟨8454050710557150073655363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22544135228152400196414301 8454050710557150073655363)
            ·
              refine ⟨12681076065835725110483045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8454050710557150073655363 12681076065835725110483045)
              ·
                refine ⟨2377701762344198458215571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12681076065835725110483045 2377701762344198458215571)
                ·
                  refine ⟨3566552643516297687323357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2377701762344198458215571 3566552643516297687323357)
                  ·
                    refine ⟨1337457241318611632746259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3566552643516297687323357 1337457241318611632746259)
                    ·
                      rfl

theorem cell22_3907033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 4, 1, 3].length) (baseStart_3907033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3907033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3907033 prefixEnd_3907033 := by exact prefixLift 3907033
  have htrace : WordTrace (prefixWord ++ tailWord_3907033) baseStart_3907033 baseEnd_3907033 := by
    simpa [prefixWord, tailWord_3907033, baseEnd_3907033] using wordTrace_append hprefix tailTrace_3907033
  have hstable : (prefixWord ++ tailWord_3907033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907033).length < 2 ^ (prefixWord ++ tailWord_3907033).sum := by decide
  have hdescent : baseEnd_3907033 < baseStart_3907033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907091 : List Nat := [1, 1, 1, 2, 1, 6, 2, 4, 4]
def baseStart_3907091 : Nat := 118140960795 + 3907091 * 2 ^ 59
def prefixEnd_3907091 : Nat := 4983230072969 + 3 ^ 40 * 3907091 * 2
def baseEnd_3907091 : Nat := 445825698634639604932027

theorem tailTrace_3907091 : CollatzResearch.WordTrace tailWord_3907091 prefixEnd_3907091 445825698634639604932027 := by
  unfold tailWord_3907091
  simp only [CollatzResearch.WordTrace]
  refine ⟨142503315888284059863193127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95002210592189373242128751 142503315888284059863193127)
  ·
    refine ⟨213754973832426089794789691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142503315888284059863193127 213754973832426089794789691)
    ·
      refine ⟨320632460748639134692184537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213754973832426089794789691 320632460748639134692184537)
      ·
        refine ⟨240474345561479351019138403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320632460748639134692184537 240474345561479351019138403)
        ·
          refine ⟨360711518342219026528707605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240474345561479351019138403 360711518342219026528707605)
          ·
            refine ⟨16908352422291516868533169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 360711518342219026528707605 16908352422291516868533169)
            ·
              refine ⟨12681264316718637651399877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16908352422291516868533169 12681264316718637651399877)
              ·
                refine ⟨2377737059384744559637477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12681264316718637651399877 2377737059384744559637477)
                ·
                  refine ⟨445825698634639604932027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2377737059384744559637477 445825698634639604932027)
                  ·
                    rfl

theorem cell22_3907091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 4, 4].length) (baseStart_3907091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3907091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3907091 prefixEnd_3907091 := by exact prefixLift 3907091
  have htrace : WordTrace (prefixWord ++ tailWord_3907091) baseStart_3907091 baseEnd_3907091 := by
    simpa [prefixWord, tailWord_3907091, baseEnd_3907091] using wordTrace_append hprefix tailTrace_3907091
  have hstable : (prefixWord ++ tailWord_3907091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907091).length < 2 ^ (prefixWord ++ tailWord_3907091).sum := by decide
  have hdescent : baseEnd_3907091 < baseStart_3907091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907106 : List Nat := [3, 3, 1, 1, 1, 1, 5, 1, 1, 5]
def baseStart_3907106 : Nat := 118140960795 + 3907106 * 2 ^ 59
def prefixEnd_3907106 : Nat := 4983230072969 + 3 ^ 40 * 3907106 * 2
def baseEnd_3907106 : Nat := 1337482230710463775671035

theorem tailTrace_3907106 : CollatzResearch.WordTrace tailWord_3907106 prefixEnd_3907106 1337482230710463775671035 := by
  unfold tailWord_3907106
  simp only [CollatzResearch.WordTrace]
  refine ⟨35625965745807429356247293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95002575322153144949992781 35625965745807429356247293)
  ·
    refine ⟨13359737154677786008592735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35625965745807429356247293 13359737154677786008592735)
    ·
      refine ⟨20039605732016679012889103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13359737154677786008592735 20039605732016679012889103)
      ·
        refine ⟨30059408598025018519333655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20039605732016679012889103 30059408598025018519333655)
        ·
          refine ⟨45089112897037527779000483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30059408598025018519333655 45089112897037527779000483)
          ·
            refine ⟨67633669345556291668500725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45089112897037527779000483 67633669345556291668500725)
            ·
              refine ⟨6340656501145902343921943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67633669345556291668500725 6340656501145902343921943)
              ·
                refine ⟨9510984751718853515882915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6340656501145902343921943 9510984751718853515882915)
                ·
                  refine ⟨14266477127578280273824373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9510984751718853515882915 14266477127578280273824373)
                  ·
                    refine ⟨1337482230710463775671035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14266477127578280273824373 1337482230710463775671035)
                    ·
                      rfl

theorem cell22_3907106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_3907106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3907106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3907106 prefixEnd_3907106 := by exact prefixLift 3907106
  have htrace : WordTrace (prefixWord ++ tailWord_3907106) baseStart_3907106 baseEnd_3907106 := by
    simpa [prefixWord, tailWord_3907106, baseEnd_3907106] using wordTrace_append hprefix tailTrace_3907106
  have hstable : (prefixWord ++ tailWord_3907106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907106).length < 2 ^ (prefixWord ++ tailWord_3907106).sum := by decide
  have hdescent : baseEnd_3907106 < baseStart_3907106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907142 : List Nat := [6, 1, 1, 1, 4, 1, 1, 1, 6]
def baseStart_3907142 : Nat := 118140960795 + 3907142 * 2 ^ 59
def prefixEnd_3907142 : Nat := 4983230072969 + 3 ^ 40 * 3907142 * 2
def baseEnd_3907142 : Nat := 445831518082057227256975

theorem tailTrace_3907142 : CollatzResearch.WordTrace tailWord_3907142 prefixEnd_3907142 445831518082057227256975 := by
  unfold tailWord_3907142
  simp only [CollatzResearch.WordTrace]
  refine ⟨4453286750346852986665615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 95003450674066197048866453 4453286750346852986665615)
  ·
    refine ⟨6679930125520279479998423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4453286750346852986665615 6679930125520279479998423)
    ·
      refine ⟨10019895188280419219997635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6679930125520279479998423 10019895188280419219997635)
      ·
        refine ⟨15029842782420628829996453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10019895188280419219997635 15029842782420628829996453)
        ·
          refine ⟨2818095521703867905624335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15029842782420628829996453 2818095521703867905624335)
          ·
            refine ⟨4227143282555801858436503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2818095521703867905624335 4227143282555801858436503)
            ·
              refine ⟨6340714923833702787654755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4227143282555801858436503 6340714923833702787654755)
              ·
                refine ⟨9511072385750554181482133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6340714923833702787654755 9511072385750554181482133)
                ·
                  refine ⟨445831518082057227256975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9511072385750554181482133 445831518082057227256975)
                  ·
                    rfl

theorem cell22_3907142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_3907142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3907142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3907142 prefixEnd_3907142 := by exact prefixLift 3907142
  have htrace : WordTrace (prefixWord ++ tailWord_3907142) baseStart_3907142 baseEnd_3907142 := by
    simpa [prefixWord, tailWord_3907142, baseEnd_3907142] using wordTrace_append hprefix tailTrace_3907142
  have hstable : (prefixWord ++ tailWord_3907142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907142).length < 2 ^ (prefixWord ++ tailWord_3907142).sum := by decide
  have hdescent : baseEnd_3907142 < baseStart_3907142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907256 : List Nat := [2, 1, 2, 1, 2, 1, 1, 6, 2, 4]
def baseStart_3907256 : Nat := 118140960795 + 3907256 * 2 ^ 59
def prefixEnd_3907256 : Nat := 4983230072969 + 3 ^ 40 * 3907256 * 2
def baseEnd_3907256 : Nat := 1337533578775913384420575

theorem tailTrace_3907256 : CollatzResearch.WordTrace tailWord_3907256 prefixEnd_3907256 1337533578775913384420575 := by
  unfold tailWord_3907256
  simp only [CollatzResearch.WordTrace]
  refine ⟨71254666966343146521474811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95006222621790862028633081 71254666966343146521474811)
  ·
    refine ⟨106882000449514719782212217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71254666966343146521474811 106882000449514719782212217)
    ·
      refine ⟨80161500337136039836659163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106882000449514719782212217 80161500337136039836659163)
      ·
        refine ⟨120242250505704059754988745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80161500337136039836659163 120242250505704059754988745)
        ·
          refine ⟨90181687879278044816241559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120242250505704059754988745 90181687879278044816241559)
          ·
            refine ⟨135272531818917067224362339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90181687879278044816241559 135272531818917067224362339)
            ·
              refine ⟨202908797728375600836543509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135272531818917067224362339 202908797728375600836543509)
              ·
                refine ⟨9511349893517606289212977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 202908797728375600836543509 9511349893517606289212977)
                ·
                  refine ⟨7133512420138204716909733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9511349893517606289212977 7133512420138204716909733)
                  ·
                    refine ⟨1337533578775913384420575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7133512420138204716909733 1337533578775913384420575)
                    ·
                      rfl

theorem cell22_3907256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_3907256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3907256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3907256 prefixEnd_3907256 := by exact prefixLift 3907256
  have htrace : WordTrace (prefixWord ++ tailWord_3907256) baseStart_3907256 baseEnd_3907256 := by
    simpa [prefixWord, tailWord_3907256, baseEnd_3907256] using wordTrace_append hprefix tailTrace_3907256
  have hstable : (prefixWord ++ tailWord_3907256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907256).length < 2 ^ (prefixWord ++ tailWord_3907256).sum := by decide
  have hdescent : baseEnd_3907256 < baseStart_3907256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907258 : List Nat := [3, 1, 1, 1, 2, 5, 1, 1, 4, 3]
def baseStart_3907258 : Nat := 118140960795 + 3907258 * 2 ^ 59
def prefixEnd_3907258 : Nat := 4983230072969 + 3 ^ 40 * 3907258 * 2
def baseEnd_3907258 : Nat := 1337534263416786045870569

theorem tailTrace_3907258 : CollatzResearch.WordTrace tailWord_3907258 prefixEnd_3907258 1337534263416786045870569 := by
  unfold tailWord_3907258
  simp only [CollatzResearch.WordTrace]
  refine ⟨35627351719669761846130607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95006271252452698256348285 35627351719669761846130607)
  ·
    refine ⟨53441027579504642769195911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35627351719669761846130607 53441027579504642769195911)
    ·
      refine ⟨80161541369256964153793867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53441027579504642769195911 80161541369256964153793867)
      ·
        refine ⟨120242312053885446230690801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80161541369256964153793867 120242312053885446230690801)
        ·
          refine ⟨90181734040414084673018101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120242312053885446230690801 90181734040414084673018101)
          ·
            refine ⟨8454537566288820438095447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90181734040414084673018101 8454537566288820438095447)
            ·
              refine ⟨12681806349433230657143171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8454537566288820438095447 12681806349433230657143171)
              ·
                refine ⟨19022709524149845985714757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12681806349433230657143171 19022709524149845985714757)
                ·
                  refine ⟨3566758035778096122321517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19022709524149845985714757 3566758035778096122321517)
                  ·
                    refine ⟨1337534263416786045870569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3566758035778096122321517 1337534263416786045870569)
                    ·
                      rfl

theorem cell22_3907258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 4, 3].length) (baseStart_3907258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3907258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3907258 prefixEnd_3907258 := by exact prefixLift 3907258
  have htrace : WordTrace (prefixWord ++ tailWord_3907258) baseStart_3907258 baseEnd_3907258 := by
    simpa [prefixWord, tailWord_3907258, baseEnd_3907258] using wordTrace_append hprefix tailTrace_3907258
  have hstable : (prefixWord ++ tailWord_3907258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907258).length < 2 ^ (prefixWord ++ tailWord_3907258).sum := by decide
  have hdescent : baseEnd_3907258 < baseStart_3907258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907326 : List Nat := [4, 2, 2, 1, 4, 1, 2, 1, 2, 3]
def baseStart_3907326 : Nat := 118140960795 + 3907326 * 2 ^ 59
def prefixEnd_3907326 : Nat := 4983230072969 + 3 ^ 40 * 3907326 * 2
def baseEnd_3907326 : Nat := 1337557541206456535170361

theorem tailTrace_3907326 : CollatzResearch.WordTrace tailWord_3907326 prefixEnd_3907326 1337557541206456535170361 := by
  unfold tailWord_3907326
  simp only [CollatzResearch.WordTrace]
  refine ⟨17813985880304086874749729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95007924694955129998665221 17813985880304086874749729)
  ·
    refine ⟨13360489410228065156062297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17813985880304086874749729 13360489410228065156062297)
    ·
      refine ⟨10020367057671048867046723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13360489410228065156062297 10020367057671048867046723)
      ·
        refine ⟨15030550586506573300570085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10020367057671048867046723 15030550586506573300570085)
        ·
          refine ⟨2818228234969982493856891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15030550586506573300570085 2818228234969982493856891)
          ·
            refine ⟨4227342352454973740785337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2818228234969982493856891 4227342352454973740785337)
            ·
              refine ⟨3170506764341230305589003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4227342352454973740785337 3170506764341230305589003)
              ·
                refine ⟨4755760146511845458383505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3170506764341230305589003 4755760146511845458383505)
                ·
                  refine ⟨3566820109883884093787629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4755760146511845458383505 3566820109883884093787629)
                  ·
                    refine ⟨1337557541206456535170361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3566820109883884093787629 1337557541206456535170361)
                    ·
                      rfl

theorem cell22_3907326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_3907326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3907326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3907326 prefixEnd_3907326 := by exact prefixLift 3907326
  have htrace : WordTrace (prefixWord ++ tailWord_3907326) baseStart_3907326 baseEnd_3907326 := by
    simpa [prefixWord, tailWord_3907326, baseEnd_3907326] using wordTrace_append hprefix tailTrace_3907326
  have hstable : (prefixWord ++ tailWord_3907326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907326).length < 2 ^ (prefixWord ++ tailWord_3907326).sum := by decide
  have hdescent : baseEnd_3907326 < baseStart_3907326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907331 : List Nat := [1, 1, 1, 3, 2, 2, 2, 3, 2, 5]
def baseStart_3907331 : Nat := 118140960795 + 3907331 * 2 ^ 59
def prefixEnd_3907331 : Nat := 4983230072969 + 3 ^ 40 * 3907331 * 2
def baseEnd_3907331 : Nat := 1337559252808638188795345

theorem tailTrace_3907331 : CollatzResearch.WordTrace tailWord_3907331 prefixEnd_3907331 1337559252808638188795345 := by
  unfold tailWord_3907331
  simp only [CollatzResearch.WordTrace]
  refine ⟨142512069407414580851929847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95008046271609720567953231 142512069407414580851929847)
  ·
    refine ⟨213768104111121871277894771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142512069407414580851929847 213768104111121871277894771)
    ·
      refine ⟨320652156166682806916842157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213768104111121871277894771 320652156166682806916842157)
      ·
        refine ⟨120244558562506052593815809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320652156166682806916842157 120244558562506052593815809)
        ·
          refine ⟨90183418921879539445361857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120244558562506052593815809 90183418921879539445361857)
          ·
            refine ⟨67637564191409654584021393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90183418921879539445361857 67637564191409654584021393)
            ·
              refine ⟨50728173143557240938016045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67637564191409654584021393 50728173143557240938016045)
              ·
                refine ⟨19023064928833965351756017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50728173143557240938016045 19023064928833965351756017)
                ·
                  refine ⟨14267298696625474013817013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19023064928833965351756017 14267298696625474013817013)
                  ·
                    refine ⟨1337559252808638188795345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14267298696625474013817013 1337559252808638188795345)
                    ·
                      rfl

theorem cell22_3907331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 5].length) (baseStart_3907331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3907331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3907331 prefixEnd_3907331 := by exact prefixLift 3907331
  have htrace : WordTrace (prefixWord ++ tailWord_3907331) baseStart_3907331 baseEnd_3907331 := by
    simpa [prefixWord, tailWord_3907331, baseEnd_3907331] using wordTrace_append hprefix tailTrace_3907331
  have hstable : (prefixWord ++ tailWord_3907331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907331).length < 2 ^ (prefixWord ++ tailWord_3907331).sum := by decide
  have hdescent : baseEnd_3907331 < baseStart_3907331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907341 : List Nat := [1, 7, 2, 1, 1, 1, 2, 1, 2, 4]
def baseStart_3907341 : Nat := 118140960795 + 3907341 * 2 ^ 59
def prefixEnd_3907341 : Nat := 4983230072969 + 3 ^ 40 * 3907341 * 2
def baseEnd_3907341 : Nat := 1337562676013001496045315

theorem tailTrace_3907341 : CollatzResearch.WordTrace tailWord_3907341 prefixEnd_3907341 1337562676013001496045315 := by
  unfold tailWord_3907341
  simp only [CollatzResearch.WordTrace]
  refine ⟨142512434137378352559793877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95008289424918901706529251 142512434137378352559793877)
  ·
    refine ⟨3340135175094805138120169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 142512434137378352559793877 3340135175094805138120169)
    ·
      refine ⟨2505101381321103853590127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3340135175094805138120169 2505101381321103853590127)
      ·
        refine ⟨3757652071981655780385191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2505101381321103853590127 3757652071981655780385191)
        ·
          refine ⟨5636478107972483670577787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3757652071981655780385191 5636478107972483670577787)
          ·
            refine ⟨8454717161958725505866681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5636478107972483670577787 8454717161958725505866681)
            ·
              refine ⟨6341037871469044129400011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8454717161958725505866681 6341037871469044129400011)
              ·
                refine ⟨9511556807203566194100017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6341037871469044129400011 9511556807203566194100017)
                ·
                  refine ⟨7133667605402674645575013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9511556807203566194100017 7133667605402674645575013)
                  ·
                    refine ⟨1337562676013001496045315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7133667605402674645575013 1337562676013001496045315)
                    ·
                      rfl

theorem cell22_3907341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_3907341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3907341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3907341 prefixEnd_3907341 := by exact prefixLift 3907341
  have htrace : WordTrace (prefixWord ++ tailWord_3907341) baseStart_3907341 baseEnd_3907341 := by
    simpa [prefixWord, tailWord_3907341, baseEnd_3907341] using wordTrace_append hprefix tailTrace_3907341
  have hstable : (prefixWord ++ tailWord_3907341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907341).length < 2 ^ (prefixWord ++ tailWord_3907341).sum := by decide
  have hdescent : baseEnd_3907341 < baseStart_3907341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907363 : List Nat := [1, 1, 1, 4, 2, 1, 2, 5, 1, 4]
def baseStart_3907363 : Nat := 118140960795 + 3907363 * 2 ^ 59
def prefixEnd_3907363 : Nat := 4983230072969 + 3 ^ 40 * 3907363 * 2
def baseEnd_3907363 : Nat := 1337570207062600771995247

theorem tailTrace_3907363 : CollatzResearch.WordTrace tailWord_3907363 prefixEnd_3907363 1337570207062600771995247 := by
  unfold tailWord_3907363
  simp only [CollatzResearch.WordTrace]
  refine ⟨142513236543298650317094743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95008824362199100211396495 142513236543298650317094743)
  ·
    refine ⟨213769854814947975475642115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142513236543298650317094743 213769854814947975475642115)
    ·
      refine ⟨320654782222421963213463173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213769854814947975475642115 320654782222421963213463173)
      ·
        refine ⟨60122771666704118102524345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 320654782222421963213463173 60122771666704118102524345)
        ·
          refine ⟨45092078750028088576893259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60122771666704118102524345 45092078750028088576893259)
          ·
            refine ⟨67638118125042132865339889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45092078750028088576893259 67638118125042132865339889)
            ·
              refine ⟨50728588593781599649004917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67638118125042132865339889 50728588593781599649004917)
              ·
                refine ⟨4755805180667024967094211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50728588593781599649004917 4755805180667024967094211)
                ·
                  refine ⟨7133707771000537450641317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4755805180667024967094211 7133707771000537450641317)
                  ·
                    refine ⟨1337570207062600771995247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7133707771000537450641317 1337570207062600771995247)
                    ·
                      rfl

theorem cell22_3907363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 4].length) (baseStart_3907363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3907363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3907363 prefixEnd_3907363 := by exact prefixLift 3907363
  have htrace : WordTrace (prefixWord ++ tailWord_3907363) baseStart_3907363 baseEnd_3907363 := by
    simpa [prefixWord, tailWord_3907363, baseEnd_3907363] using wordTrace_append hprefix tailTrace_3907363
  have hstable : (prefixWord ++ tailWord_3907363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907363).length < 2 ^ (prefixWord ++ tailWord_3907363).sum := by decide
  have hdescent : baseEnd_3907363 < baseStart_3907363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907380 : List Nat := [2, 5, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_3907380 : Nat := 118140960795 + 3907380 * 2 ^ 59
def prefixEnd_3907380 : Nat := 4983230072969 + 3 ^ 40 * 3907380 * 2
def baseEnd_3907380 : Nat := 1337576026510018394320195

theorem tailTrace_3907380 : CollatzResearch.WordTrace tailWord_3907380 prefixEnd_3907380 1337576026510018394320195 := by
  unfold tailWord_3907380
  simp only [CollatzResearch.WordTrace]
  refine ⟨71256928292118531110231797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95009237722824708146975729 71256928292118531110231797)
  ·
    refine ⟨6680337027386112291584231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71256928292118531110231797 6680337027386112291584231)
    ·
      refine ⟨10020505541079168437376347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6680337027386112291584231 10020505541079168437376347)
      ·
        refine ⟨15030758311618752656064521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10020505541079168437376347 15030758311618752656064521)
        ·
          refine ⟨11273068733714064492048391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15030758311618752656064521 11273068733714064492048391)
          ·
            refine ⟨16909603100571096738072587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11273068733714064492048391 16909603100571096738072587)
            ·
              refine ⟨25364404650856645107108881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16909603100571096738072587 25364404650856645107108881)
              ·
                refine ⟨19023303488142483830331661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25364404650856645107108881 19023303488142483830331661)
                ·
                  refine ⟨7133738808053431436374373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19023303488142483830331661 7133738808053431436374373)
                  ·
                    refine ⟨1337576026510018394320195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7133738808053431436374373 1337576026510018394320195)
                    ·
                      rfl

theorem cell22_3907380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_3907380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3907380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3907380 prefixEnd_3907380 := by exact prefixLift 3907380
  have htrace : WordTrace (prefixWord ++ tailWord_3907380) baseStart_3907380 baseEnd_3907380 := by
    simpa [prefixWord, tailWord_3907380, baseEnd_3907380] using wordTrace_append hprefix tailTrace_3907380
  have hstable : (prefixWord ++ tailWord_3907380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907380).length < 2 ^ (prefixWord ++ tailWord_3907380).sum := by decide
  have hdescent : baseEnd_3907380 < baseStart_3907380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907412 : List Nat := [2, 4, 1, 1, 3, 2, 2, 3, 4]
def baseStart_3907412 : Nat := 118140960795 + 3907412 * 2 ^ 59
def prefixEnd_3907412 : Nat := 4983230072969 + 3 ^ 40 * 3907412 * 2
def baseEnd_3907412 : Nat := 445862326921326992506699

theorem tailTrace_3907412 : CollatzResearch.WordTrace tailWord_3907412 prefixEnd_3907412 445862326921326992506699 := by
  unfold tailWord_3907412
  simp only [CollatzResearch.WordTrace]
  refine ⟨71257511860060565842814245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95010015813414087790418993 71257511860060565842814245)
  ·
    refine ⟨13360783473761356095527671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71257511860060565842814245 13360783473761356095527671)
    ·
      refine ⟨20041175210642034143291507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13360783473761356095527671 20041175210642034143291507)
      ·
        refine ⟨30061762815963051214937261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20041175210642034143291507 30061762815963051214937261)
        ·
          refine ⟨11273161055986144205601473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30061762815963051214937261 11273161055986144205601473)
          ·
            refine ⟨8454870791989608154201105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11273161055986144205601473 8454870791989608154201105)
            ·
              refine ⟨6341153093992206115650829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8454870791989608154201105 6341153093992206115650829)
              ·
                refine ⟨2377932410247077293369061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6341153093992206115650829 2377932410247077293369061)
                ·
                  refine ⟨445862326921326992506699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2377932410247077293369061 445862326921326992506699)
                  ·
                    rfl

theorem cell22_3907412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_3907412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3907412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3907412 prefixEnd_3907412 := by exact prefixLift 3907412
  have htrace : WordTrace (prefixWord ++ tailWord_3907412) baseStart_3907412 baseEnd_3907412 := by
    simpa [prefixWord, tailWord_3907412, baseEnd_3907412] using wordTrace_append hprefix tailTrace_3907412
  have hstable : (prefixWord ++ tailWord_3907412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907412).length < 2 ^ (prefixWord ++ tailWord_3907412).sum := by decide
  have hdescent : baseEnd_3907412 < baseStart_3907412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907489 : List Nat := [1, 2, 3, 4, 2, 2, 1, 1, 3, 3]
def baseStart_3907489 : Nat := 118140960795 + 3907489 * 2 ^ 59
def prefixEnd_3907489 : Nat := 4983230072969 + 3 ^ 40 * 3907489 * 2
def baseEnd_3907489 : Nat := 1337613339437578443344861

theorem tailTrace_3907489 : CollatzResearch.WordTrace tailWord_3907489 prefixEnd_3907489 1337613339437578443344861 := by
  unfold tailWord_3907489
  simp only [CollatzResearch.WordTrace]
  refine ⟨142517832140842173836181521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95011888093894782557454347 142517832140842173836181521)
  ·
    refine ⟨106888374105631630377136141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142517832140842173836181521 106888374105631630377136141)
    ·
      refine ⟨40083140289611861391426053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106888374105631630377136141 40083140289611861391426053)
      ·
        refine ⟨7515588804302224010892385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40083140289611861391426053 7515588804302224010892385)
        ·
          refine ⟨5636691603226668008169289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7515588804302224010892385 5636691603226668008169289)
          ·
            refine ⟨4227518702420001006126967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5636691603226668008169289 4227518702420001006126967)
            ·
              refine ⟨6341278053630001509190451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4227518702420001006126967 6341278053630001509190451)
              ·
                refine ⟨9511917080445002263785677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6341278053630001509190451 9511917080445002263785677)
                ·
                  refine ⟨3566968905166875848919629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9511917080445002263785677 3566968905166875848919629)
                  ·
                    refine ⟨1337613339437578443344861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3566968905166875848919629 1337613339437578443344861)
                    ·
                      rfl

theorem cell22_3907489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_3907489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3907489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3907489 prefixEnd_3907489 := by exact prefixLift 3907489
  have htrace : WordTrace (prefixWord ++ tailWord_3907489) baseStart_3907489 baseEnd_3907489 := by
    simpa [prefixWord, tailWord_3907489, baseEnd_3907489] using wordTrace_append hprefix tailTrace_3907489
  have hstable : (prefixWord ++ tailWord_3907489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907489).length < 2 ^ (prefixWord ++ tailWord_3907489).sum := by decide
  have hdescent : baseEnd_3907489 < baseStart_3907489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907513 : List Nat := [1, 2, 1, 4, 2, 1, 2, 1, 8]
def baseStart_3907513 : Nat := 118140960795 + 3907513 * 2 ^ 59
def prefixEnd_3907513 : Nat := 4983230072969 + 3 ^ 40 * 3907513 * 2
def baseEnd_3907513 : Nat := 445873851709350126914929

theorem tailTrace_3907513 : CollatzResearch.WordTrace tailWord_3907513 prefixEnd_3907513 445873851709350126914929 := by
  unfold tailWord_3907513
  simp only [CollatzResearch.WordTrace]
  refine ⟨142518707492755225935055193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95012471661836817290036795 142518707492755225935055193)
  ·
    refine ⟨106889030619566419451291395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142518707492755225935055193 106889030619566419451291395)
    ·
      refine ⟨160333545929349629176937093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106889030619566419451291395 160333545929349629176937093)
      ·
        refine ⟨30062539861753055470675705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160333545929349629176937093 30062539861753055470675705)
        ·
          refine ⟨22546904896314791603006779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30062539861753055470675705 22546904896314791603006779)
          ·
            refine ⟨33820357344472187404510169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22546904896314791603006779 33820357344472187404510169)
            ·
              refine ⟨25365268008354140553382627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33820357344472187404510169 25365268008354140553382627)
              ·
                refine ⟨38047902012531210830073941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25365268008354140553382627 38047902012531210830073941)
                ·
                  refine ⟨445873851709350126914929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38047902012531210830073941 445873851709350126914929)
                  ·
                    rfl

theorem cell22_3907513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 8].length) (baseStart_3907513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3907513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3907513 prefixEnd_3907513 := by exact prefixLift 3907513
  have htrace : WordTrace (prefixWord ++ tailWord_3907513) baseStart_3907513 baseEnd_3907513 := by
    simpa [prefixWord, tailWord_3907513, baseEnd_3907513] using wordTrace_append hprefix tailTrace_3907513
  have hstable : (prefixWord ++ tailWord_3907513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907513).length < 2 ^ (prefixWord ++ tailWord_3907513).sum := by decide
  have hdescent : baseEnd_3907513 < baseStart_3907513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907562 : List Nat := [3, 1, 3, 1, 2, 1, 1, 5, 2, 3]
def baseStart_3907562 : Nat := 118140960795 + 3907562 * 2 ^ 59
def prefixEnd_3907562 : Nat := 4983230072969 + 3 ^ 40 * 3907562 * 2
def baseEnd_3907562 : Nat := 1337638328829430586269637

theorem tailTrace_3907562 : CollatzResearch.WordTrace tailWord_3907562 prefixEnd_3907562 1337638328829430586269637 := by
  unfold tailWord_3907562
  simp only [CollatzResearch.WordTrace]
  refine ⟨35630123667394426825897235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95013663113051804869059293 35630123667394426825897235)
  ·
    refine ⟨53445185501091640238845853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35630123667394426825897235 53445185501091640238845853)
    ·
      refine ⟨20041944562909365089567195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53445185501091640238845853 20041944562909365089567195)
      ·
        refine ⟨30062916844364047634350793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20041944562909365089567195 30062916844364047634350793)
        ·
          refine ⟨22547187633273035725763095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30062916844364047634350793 22547187633273035725763095)
          ·
            refine ⟨33820781449909553588644643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22547187633273035725763095 33820781449909553588644643)
            ·
              refine ⟨50731172174864330382966965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33820781449909553588644643 50731172174864330382966965)
              ·
                refine ⟨4756047391393530973403153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50731172174864330382966965 4756047391393530973403153)
                ·
                  refine ⟨3567035543545148230052365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4756047391393530973403153 3567035543545148230052365)
                  ·
                    refine ⟨1337638328829430586269637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3567035543545148230052365 1337638328829430586269637)
                    ·
                      rfl

theorem cell22_3907562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_3907562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3907562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3907562 prefixEnd_3907562 := by exact prefixLift 3907562
  have htrace : WordTrace (prefixWord ++ tailWord_3907562) baseStart_3907562 baseEnd_3907562 := by
    simpa [prefixWord, tailWord_3907562, baseEnd_3907562] using wordTrace_append hprefix tailTrace_3907562
  have hstable : (prefixWord ++ tailWord_3907562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907562).length < 2 ^ (prefixWord ++ tailWord_3907562).sum := by decide
  have hdescent : baseEnd_3907562 < baseStart_3907562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907577 : List Nat := [1, 2, 1, 3, 1, 6, 1, 1, 2, 4]
def baseStart_3907577 : Nat := 118140960795 + 3907577 * 2 ^ 59
def prefixEnd_3907577 : Nat := 4983230072969 + 3 ^ 40 * 3907577 * 2
def baseEnd_3907577 : Nat := 1337643463635975547144591

theorem tailTrace_3907577 : CollatzResearch.WordTrace tailWord_3907577 prefixEnd_3907577 1337643463635975547144591 := by
  unfold tailWord_3907577
  simp only [CollatzResearch.WordTrace]
  refine ⟨142521041764523364865384985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95014027843015576576923323 142521041764523364865384985)
  ·
    refine ⟨106890781323392523649038739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142521041764523364865384985 106890781323392523649038739)
    ·
      refine ⟨160336171985088785473558109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106890781323392523649038739 160336171985088785473558109)
      ·
        refine ⟨60126064494408294552584291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160336171985088785473558109 60126064494408294552584291)
        ·
          refine ⟨90189096741612441828876437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60126064494408294552584291 90189096741612441828876437)
          ·
            refine ⟨4227613909763083210728583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 90189096741612441828876437 4227613909763083210728583)
            ·
              refine ⟨6341420864644624816092875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4227613909763083210728583 6341420864644624816092875)
              ·
                refine ⟨9512131296966937224139313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6341420864644624816092875 9512131296966937224139313)
                ·
                  refine ⟨7134098472725202918104485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9512131296966937224139313 7134098472725202918104485)
                  ·
                    refine ⟨1337643463635975547144591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7134098472725202918104485 1337643463635975547144591)
                    ·
                      rfl

theorem cell22_3907577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 4].length) (baseStart_3907577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3907577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3907577 prefixEnd_3907577 := by exact prefixLift 3907577
  have htrace : WordTrace (prefixWord ++ tailWord_3907577) baseStart_3907577 baseEnd_3907577 := by
    simpa [prefixWord, tailWord_3907577, baseEnd_3907577] using wordTrace_append hprefix tailTrace_3907577
  have hstable : (prefixWord ++ tailWord_3907577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907577).length < 2 ^ (prefixWord ++ tailWord_3907577).sum := by decide
  have hdescent : baseEnd_3907577 < baseStart_3907577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907654 : List Nat := [6, 1, 1, 1, 1, 1, 2, 4, 5]
def baseStart_3907654 : Nat := 118140960795 + 3907654 * 2 ^ 59
def prefixEnd_3907654 : Nat := 4983230072969 + 3 ^ 40 * 3907654 * 2
def baseEnd_3907654 : Nat := 445889940769857670989785

theorem tailTrace_3907654 : CollatzResearch.WordTrace tailWord_3907654 prefixEnd_3907654 445889940769857670989785 := by
  unfold tailWord_3907654
  simp only [CollatzResearch.WordTrace]
  refine ⟨4453870318288887719248063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 95015900123496271343958677 4453870318288887719248063)
  ·
    refine ⟨6680805477433331578872095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4453870318288887719248063 6680805477433331578872095)
    ·
      refine ⟨10021208216149997368308143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6680805477433331578872095 10021208216149997368308143)
      ·
        refine ⟨15031812324224996052462215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10021208216149997368308143 15031812324224996052462215)
        ·
          refine ⟨22547718486337494078693323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15031812324224996052462215 22547718486337494078693323)
          ·
            refine ⟨33821577729506241118039985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22547718486337494078693323 33821577729506241118039985)
            ·
              refine ⟨25366183297129680838529989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33821577729506241118039985 25366183297129680838529989)
              ·
                refine ⟨4756159368211815157224373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25366183297129680838529989 4756159368211815157224373)
                ·
                  refine ⟨445889940769857670989785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4756159368211815157224373 445889940769857670989785)
                  ·
                    rfl

theorem cell22_3907654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_3907654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3907654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3907654 prefixEnd_3907654 := by exact prefixLift 3907654
  have htrace : WordTrace (prefixWord ++ tailWord_3907654) baseStart_3907654 baseEnd_3907654 := by
    simpa [prefixWord, tailWord_3907654, baseEnd_3907654] using wordTrace_append hprefix tailTrace_3907654
  have hstable : (prefixWord ++ tailWord_3907654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907654).length < 2 ^ (prefixWord ++ tailWord_3907654).sum := by decide
  have hdescent : baseEnd_3907654 < baseStart_3907654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907746 : List Nat := [3, 3, 1, 3, 1, 3, 1, 1, 2, 4]
def baseStart_3907746 : Nat := 118140960795 + 3907746 * 2 ^ 59
def prefixEnd_3907746 : Nat := 4983230072969 + 3 ^ 40 * 3907746 * 2
def baseEnd_3907746 : Nat := 1337701315789715439669073

theorem tailTrace_3907746 : CollatzResearch.WordTrace tailWord_3907746 prefixEnd_3907746 1337701315789715439669073 := by
  unfold tailWord_3907746
  simp only [CollatzResearch.WordTrace]
  refine ⟨35631801425227776682071773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95018137133940737818858061 35631801425227776682071773)
  ·
    refine ⟨13361925534460416255776915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35631801425227776682071773 13361925534460416255776915)
    ·
      refine ⟨20042888301690624383665373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13361925534460416255776915 20042888301690624383665373)
      ·
        refine ⟨7516083113133984143874515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20042888301690624383665373 7516083113133984143874515)
        ·
          refine ⟨11274124669700976215811773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7516083113133984143874515 11274124669700976215811773)
          ·
            refine ⟨4227796751137866080929415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11274124669700976215811773 4227796751137866080929415)
            ·
              refine ⟨6341695126706799121394123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4227796751137866080929415 6341695126706799121394123)
              ·
                refine ⟨9512542690060198682091185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6341695126706799121394123 9512542690060198682091185)
                ·
                  refine ⟨7134407017545149011568389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9512542690060198682091185 7134407017545149011568389)
                  ·
                    refine ⟨1337701315789715439669073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7134407017545149011568389 1337701315789715439669073)
                    ·
                      rfl

theorem cell22_3907746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_3907746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3907746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3907746 prefixEnd_3907746 := by exact prefixLift 3907746
  have htrace : WordTrace (prefixWord ++ tailWord_3907746) baseStart_3907746 baseEnd_3907746 := by
    simpa [prefixWord, tailWord_3907746, baseEnd_3907746] using wordTrace_append hprefix tailTrace_3907746
  have hstable : (prefixWord ++ tailWord_3907746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907746).length < 2 ^ (prefixWord ++ tailWord_3907746).sum := by decide
  have hdescent : baseEnd_3907746 < baseStart_3907746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907765 : List Nat := [1, 3, 3, 4, 2, 1, 1, 2, 2, 3]
def baseStart_3907765 : Nat := 118140960795 + 3907765 * 2 ^ 59
def prefixEnd_3907765 : Nat := 4983230072969 + 3 ^ 40 * 3907765 * 2
def baseEnd_3907765 : Nat := 1337707819878005723444015

theorem tailTrace_3907765 : CollatzResearch.WordTrace tailWord_3907765 prefixEnd_3907765 1337707819878005723444015 := by
  unfold tailWord_3907765
  simp only [CollatzResearch.WordTrace]
  refine ⟨142527898687842272973228749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95018599125228181982152499 142527898687842272973228749)
  ·
    refine ⟨53447962007940852364960781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142527898687842272973228749 53447962007940852364960781)
    ·
      refine ⟨20042985752977819636860293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53447962007940852364960781 20042985752977819636860293)
      ·
        refine ⟨3758059828683341181911305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20042985752977819636860293 3758059828683341181911305)
        ·
          refine ⟨2818544871512505886433479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3758059828683341181911305 2818544871512505886433479)
          ·
            refine ⟨4227817307268758829650219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2818544871512505886433479 4227817307268758829650219)
            ·
              refine ⟨6341725960903138244475329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4227817307268758829650219 6341725960903138244475329)
              ·
                refine ⟨4756294470677353683356497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6341725960903138244475329 4756294470677353683356497)
                ·
                  refine ⟨3567220853008015262517373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4756294470677353683356497 3567220853008015262517373)
                  ·
                    refine ⟨1337707819878005723444015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3567220853008015262517373 1337707819878005723444015)
                    ·
                      rfl

theorem cell22_3907765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_3907765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3907765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3907765 prefixEnd_3907765 := by exact prefixLift 3907765
  have htrace : WordTrace (prefixWord ++ tailWord_3907765) baseStart_3907765 baseEnd_3907765 := by
    simpa [prefixWord, tailWord_3907765, baseEnd_3907765] using wordTrace_append hprefix tailTrace_3907765
  have hstable : (prefixWord ++ tailWord_3907765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907765).length < 2 ^ (prefixWord ++ tailWord_3907765).sum := by decide
  have hdescent : baseEnd_3907765 < baseStart_3907765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907776 : List Nat := [2, 1, 1, 2, 5, 1, 2, 4, 1, 3]
def baseStart_3907776 : Nat := 118140960795 + 3907776 * 2 ^ 59
def prefixEnd_3907776 : Nat := 4983230072969 + 3 ^ 40 * 3907776 * 2
def baseEnd_3907776 : Nat := 1337711585402805361418981

theorem tailTrace_3907776 : CollatzResearch.WordTrace tailWord_3907776 prefixEnd_3907776 1337711585402805361418981 := by
  unfold tailWord_3907776
  simp only [CollatzResearch.WordTrace]
  refine ⟨71264149945401210925939591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95018866593868281234586121 71264149945401210925939591)
  ·
    refine ⟨106896224918101816388909387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71264149945401210925939591 106896224918101816388909387)
    ·
      refine ⟨160344337377152724583364081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106896224918101816388909387 160344337377152724583364081)
      ·
        refine ⟨120258253032864543437523061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160344337377152724583364081 120258253032864543437523061)
        ·
          refine ⟨11274211221831050947267787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120258253032864543437523061 11274211221831050947267787)
          ·
            refine ⟨16911316832746576420901681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11274211221831050947267787 16911316832746576420901681)
            ·
              refine ⟨12683487624559932315676261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16911316832746576420901681 12683487624559932315676261)
              ·
                refine ⟨2378153929604987309189299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12683487624559932315676261 2378153929604987309189299)
                ·
                  refine ⟨3567230894407480963783949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2378153929604987309189299 3567230894407480963783949)
                  ·
                    refine ⟨1337711585402805361418981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3567230894407480963783949 1337711585402805361418981)
                    ·
                      rfl

theorem cell22_3907776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 4, 1, 3].length) (baseStart_3907776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3907776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3907776 prefixEnd_3907776 := by exact prefixLift 3907776
  have htrace : WordTrace (prefixWord ++ tailWord_3907776) baseStart_3907776 baseEnd_3907776 := by
    simpa [prefixWord, tailWord_3907776, baseEnd_3907776] using wordTrace_append hprefix tailTrace_3907776
  have hstable : (prefixWord ++ tailWord_3907776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907776).length < 2 ^ (prefixWord ++ tailWord_3907776).sum := by decide
  have hdescent : baseEnd_3907776 < baseStart_3907776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907785 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 2, 8]
def baseStart_3907785 : Nat := 118140960795 + 3907785 * 2 ^ 59
def prefixEnd_3907785 : Nat := 4983230072969 + 3 ^ 40 * 3907785 * 2
def baseEnd_3907785 : Nat := 1337714666286732337943953

theorem tailTrace_3907785 : CollatzResearch.WordTrace tailWord_3907785 prefixEnd_3907785 1337714666286732337943953 := by
  unfold tailWord_3907785
  simp only [CollatzResearch.WordTrace]
  refine ⟨142528628147769816388956809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95019085431846544259304539 142528628147769816388956809)
  ·
    refine ⟨106896471110827362291717607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142528628147769816388956809 106896471110827362291717607)
    ·
      refine ⟨160344706666241043437576411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106896471110827362291717607 160344706666241043437576411)
      ·
        refine ⟨240517059999361565156364617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160344706666241043437576411 240517059999361565156364617)
        ·
          refine ⟨180387794999521173867273463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240517059999361565156364617 180387794999521173867273463)
          ·
            refine ⟨270581692499281760800910195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180387794999521173867273463 270581692499281760800910195)
            ·
              refine ⟨405872538748922641201365293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270581692499281760800910195 405872538748922641201365293)
              ·
                refine ⟨152202202030845990450511985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 405872538748922641201365293 152202202030845990450511985)
                ·
                  refine ⟨114151651523134492837883989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152202202030845990450511985 114151651523134492837883989)
                  ·
                    refine ⟨1337714666286732337943953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 114151651523134492837883989 1337714666286732337943953)
                    ·
                      rfl

theorem cell22_3907785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 8].length) (baseStart_3907785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3907785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3907785 prefixEnd_3907785 := by exact prefixLift 3907785
  have htrace : WordTrace (prefixWord ++ tailWord_3907785) baseStart_3907785 baseEnd_3907785 := by
    simpa [prefixWord, tailWord_3907785, baseEnd_3907785] using wordTrace_append hprefix tailTrace_3907785
  have hstable : (prefixWord ++ tailWord_3907785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907785).length < 2 ^ (prefixWord ++ tailWord_3907785).sum := by decide
  have hdescent : baseEnd_3907785 < baseStart_3907785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907802 : List Nat := [3, 1, 1, 2, 2, 1, 2, 3, 3, 4]
def baseStart_3907802 : Nat := 118140960795 + 3907802 * 2 ^ 59
def prefixEnd_3907802 : Nat := 4983230072969 + 3 ^ 40 * 3907802 * 2
def baseEnd_3907802 : Nat := 1337720485734149960268901

theorem tailTrace_3907802 : CollatzResearch.WordTrace tailWord_3907802 prefixEnd_3907802 1337720485734149960268901 := by
  unfold tailWord_3907802
  simp only [CollatzResearch.WordTrace]
  refine ⟨35632312047177057073081415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95019498792472152194883773 35632312047177057073081415)
  ·
    refine ⟨53448468070765585609622123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35632312047177057073081415 53448468070765585609622123)
    ·
      refine ⟨80172702106148378414433185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53448468070765585609622123 80172702106148378414433185)
      ·
        refine ⟨60129526579611283810824889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80172702106148378414433185 60129526579611283810824889)
        ·
          refine ⟨45097144934708462858118667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60129526579611283810824889 45097144934708462858118667)
          ·
            refine ⟨67645717402062694287178001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45097144934708462858118667 67645717402062694287178001)
            ·
              refine ⟨50734288051547020715383501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67645717402062694287178001 50734288051547020715383501)
              ·
                refine ⟨19025358019330132768268813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50734288051547020715383501 19025358019330132768268813)
                ·
                  refine ⟨7134509257248799788100805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19025358019330132768268813 7134509257248799788100805)
                  ·
                    refine ⟨1337720485734149960268901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7134509257248799788100805 1337720485734149960268901)
                    ·
                      rfl

theorem cell22_3907802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_3907802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3907802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3907802 prefixEnd_3907802 := by exact prefixLift 3907802
  have htrace : WordTrace (prefixWord ++ tailWord_3907802) baseStart_3907802 baseEnd_3907802 := by
    simpa [prefixWord, tailWord_3907802, baseEnd_3907802] using wordTrace_append hprefix tailTrace_3907802
  have hstable : (prefixWord ++ tailWord_3907802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907802).length < 2 ^ (prefixWord ++ tailWord_3907802).sum := by decide
  have hdescent : baseEnd_3907802 < baseStart_3907802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907834 : List Nat := [3, 1, 1, 1, 1, 7, 1, 1, 6]
def baseStart_3907834 : Nat := 118140960795 + 3907834 * 2 ^ 59
def prefixEnd_3907834 : Nat := 4983230072969 + 3 ^ 40 * 3907834 * 2
def baseEnd_3907834 : Nat := 445910479996037514489601

theorem tailTrace_3907834 : CollatzResearch.WordTrace tailWord_3907834 prefixEnd_3907834 445910479996037514489601 := by
  unfold tailWord_3907834
  simp only [CollatzResearch.WordTrace]
  refine ⟨35632603831148074439372639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95020276883061531838327037 35632603831148074439372639)
  ·
    refine ⟨53448905746722111659058959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35632603831148074439372639 53448905746722111659058959)
    ·
      refine ⟨80173358620083167488588439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53448905746722111659058959 80173358620083167488588439)
      ·
        refine ⟨120260037930124751232882659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80173358620083167488588439 120260037930124751232882659)
        ·
          refine ⟨180390056895187126849323989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120260037930124751232882659 180390056895187126849323989)
          ·
            refine ⟨4227891958480948285531031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 180390056895187126849323989 4227891958480948285531031)
            ·
              refine ⟨6341837937721422428296547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4227891958480948285531031 6341837937721422428296547)
              ·
                refine ⟨9512756906582133642444821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6341837937721422428296547 9512756906582133642444821)
                ·
                  refine ⟨445910479996037514489601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9512756906582133642444821 445910479996037514489601)
                  ·
                    rfl

theorem cell22_3907834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 6].length) (baseStart_3907834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3907834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3907834 prefixEnd_3907834 := by exact prefixLift 3907834
  have htrace : WordTrace (prefixWord ++ tailWord_3907834) baseStart_3907834 baseEnd_3907834 := by
    simpa [prefixWord, tailWord_3907834, baseEnd_3907834] using wordTrace_append hprefix tailTrace_3907834
  have hstable : (prefixWord ++ tailWord_3907834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907834).length < 2 ^ (prefixWord ++ tailWord_3907834).sum := by decide
  have hdescent : baseEnd_3907834 < baseStart_3907834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907864 : List Nat := [2, 1, 2, 3, 1, 2, 4, 1, 2, 4]
def baseStart_3907864 : Nat := 118140960795 + 3907864 * 2 ^ 59
def prefixEnd_3907864 : Nat := 4983230072969 + 3 ^ 40 * 3907864 * 2
def baseEnd_3907864 : Nat := 1337741709601202465218711

theorem tailTrace_3907864 : CollatzResearch.WordTrace tailWord_3907864 prefixEnd_3907864 1337741709601202465218711 := by
  unfold tailWord_3907864
  simp only [CollatzResearch.WordTrace]
  refine ⟨71265754757241806440541323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95021006342989075254055097 71265754757241806440541323)
  ·
    refine ⟨106898632135862709660811985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71265754757241806440541323 106898632135862709660811985)
    ·
      refine ⟨80173974101897032245608989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106898632135862709660811985 80173974101897032245608989)
      ·
        refine ⟨30065240288211387092103371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80173974101897032245608989 30065240288211387092103371)
        ·
          refine ⟨45097860432317080638155057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30065240288211387092103371 45097860432317080638155057)
          ·
            refine ⟨33823395324237810478616293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45097860432317080638155057 33823395324237810478616293)
            ·
              refine ⟨6341886623294589464740555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33823395324237810478616293 6341886623294589464740555)
              ·
                refine ⟨9512829934941884197110833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6341886623294589464740555 9512829934941884197110833)
                ·
                  refine ⟨7134622451206413147833125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9512829934941884197110833 7134622451206413147833125)
                  ·
                    refine ⟨1337741709601202465218711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7134622451206413147833125 1337741709601202465218711)
                    ·
                      rfl

theorem cell22_3907864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 2, 4].length) (baseStart_3907864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3907864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3907864 prefixEnd_3907864 := by exact prefixLift 3907864
  have htrace : WordTrace (prefixWord ++ tailWord_3907864) baseStart_3907864 baseEnd_3907864 := by
    simpa [prefixWord, tailWord_3907864, baseEnd_3907864] using wordTrace_append hprefix tailTrace_3907864
  have hstable : (prefixWord ++ tailWord_3907864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907864).length < 2 ^ (prefixWord ++ tailWord_3907864).sum := by decide
  have hdescent : baseEnd_3907864 < baseStart_3907864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907870 : List Nat := [4, 3, 2, 1, 1, 2, 3, 1, 1, 4]
def baseStart_3907870 : Nat := 118140960795 + 3907870 * 2 ^ 59
def prefixEnd_3907870 : Nat := 4983230072969 + 3 ^ 40 * 3907870 * 2
def baseEnd_3907870 : Nat := 1337743763523820449568693

theorem tailTrace_3907870 : CollatzResearch.WordTrace tailWord_3907870 prefixEnd_3907870 1337743763523820449568693 := by
  unfold tailWord_3907870
  simp only [CollatzResearch.WordTrace]
  refine ⟨17816466044057734488225133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95021152234974583937200709 17816466044057734488225133)
  ·
    refine ⟨6681174766521650433084425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17816466044057734488225133 6681174766521650433084425)
    ·
      refine ⟨5010881074891237824813319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6681174766521650433084425 5010881074891237824813319)
      ·
        refine ⟨7516321612336856737219979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5010881074891237824813319 7516321612336856737219979)
        ·
          refine ⟨11274482418505285105829969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7516321612336856737219979 11274482418505285105829969)
          ·
            refine ⟨8455861813878963829372477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11274482418505285105829969 8455861813878963829372477)
            ·
              refine ⟨3170948180204611436014679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8455861813878963829372477 3170948180204611436014679)
              ·
                refine ⟨4756422270306917154022019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3170948180204611436014679 4756422270306917154022019)
                ·
                  refine ⟨7134633405460375731033029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4756422270306917154022019 7134633405460375731033029)
                  ·
                    refine ⟨1337743763523820449568693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7134633405460375731033029 1337743763523820449568693)
                    ·
                      rfl

theorem cell22_3907870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_3907870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3907870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3907870 prefixEnd_3907870 := by exact prefixLift 3907870
  have htrace : WordTrace (prefixWord ++ tailWord_3907870) baseStart_3907870 baseEnd_3907870 := by
    simpa [prefixWord, tailWord_3907870, baseEnd_3907870] using wordTrace_append hprefix tailTrace_3907870
  have hstable : (prefixWord ++ tailWord_3907870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907870).length < 2 ^ (prefixWord ++ tailWord_3907870).sum := by decide
  have hdescent : baseEnd_3907870 < baseStart_3907870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907941 : List Nat := [1, 3, 1, 3, 1, 5, 1, 2, 5]
def baseStart_3907941 : Nat := 118140960795 + 3907941 * 2 ^ 59
def prefixEnd_3907941 : Nat := 4983230072969 + 3 ^ 40 * 3907941 * 2
def baseEnd_3907941 : Nat := 445922689424933310347825

theorem tailTrace_3907941 : CollatzResearch.WordTrace tailWord_3907941 prefixEnd_3907941 445922689424933310347825 := by
  unfold tailWord_3907941
  simp only [CollatzResearch.WordTrace]
  refine ⟨142534317935204655031635677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95022878623469770021090451 142534317935204655031635677)
  ·
    refine ⟨53450369225701745636863379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142534317935204655031635677 53450369225701745636863379)
    ·
      refine ⟨80175553838552618455295069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53450369225701745636863379 80175553838552618455295069)
      ·
        refine ⟨30065832689457231920735651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80175553838552618455295069 30065832689457231920735651)
        ·
          refine ⟨45098749034185847881103477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30065832689457231920735651 45098749034185847881103477)
          ·
            refine ⟨4228007721954923238853451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45098749034185847881103477 4228007721954923238853451)
            ·
              refine ⟨6342011582932384858280177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4228007721954923238853451 6342011582932384858280177)
              ·
                refine ⟨4756508687199288643710133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6342011582932384858280177 4756508687199288643710133)
                ·
                  refine ⟨445922689424933310347825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4756508687199288643710133 445922689424933310347825)
                  ·
                    rfl

theorem cell22_3907941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 5].length) (baseStart_3907941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3907941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3907941 prefixEnd_3907941 := by exact prefixLift 3907941
  have htrace : WordTrace (prefixWord ++ tailWord_3907941) baseStart_3907941 baseEnd_3907941 := by
    simpa [prefixWord, tailWord_3907941, baseEnd_3907941] using wordTrace_append hprefix tailTrace_3907941
  have hstable : (prefixWord ++ tailWord_3907941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907941).length < 2 ^ (prefixWord ++ tailWord_3907941).sum := by decide
  have hdescent : baseEnd_3907941 < baseStart_3907941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908003 : List Nat := [1, 1, 1, 4, 1, 5, 3, 2, 4]
def baseStart_3908003 : Nat := 118140960795 + 3908003 * 2 ^ 59
def prefixEnd_3908003 : Nat := 4983230072969 + 3 ^ 40 * 3908003 * 2
def baseEnd_3908003 : Nat := 445929764047284145331095

theorem tailTrace_3908003 : CollatzResearch.WordTrace tailWord_3908003 prefixEnd_3908003 445929764047284145331095 := by
  unfold tailWord_3908003
  simp only [CollatzResearch.WordTrace]
  refine ⟨142536579260980039620392663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95024386173986693080261775 142536579260980039620392663)
  ·
    refine ⟨213804868891470059430588995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142536579260980039620392663 213804868891470059430588995)
    ·
      refine ⟨320707303337205089145883493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213804868891470059430588995 320707303337205089145883493)
      ·
        refine ⟨60132619375725954214853155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 320707303337205089145883493 60132619375725954214853155)
        ·
          refine ⟨90198929063588931322279733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60132619375725954214853155 90198929063588931322279733)
          ·
            refine ⟨8456149599711462311463725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90198929063588931322279733 8456149599711462311463725)
            ·
              refine ⟨3171056099891798366798897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8456149599711462311463725 3171056099891798366798897)
              ·
                refine ⟨2378292074918848775099173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3171056099891798366798897 2378292074918848775099173)
                ·
                  refine ⟨445929764047284145331095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2378292074918848775099173 445929764047284145331095)
                  ·
                    rfl

theorem cell22_3908003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 2, 4].length) (baseStart_3908003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3908003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3908003 prefixEnd_3908003 := by exact prefixLift 3908003
  have htrace : WordTrace (prefixWord ++ tailWord_3908003) baseStart_3908003 baseEnd_3908003 := by
    simpa [prefixWord, tailWord_3908003, baseEnd_3908003] using wordTrace_append hprefix tailTrace_3908003
  have hstable : (prefixWord ++ tailWord_3908003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908003).length < 2 ^ (prefixWord ++ tailWord_3908003).sum := by decide
  have hdescent : baseEnd_3908003 < baseStart_3908003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908104 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 10]
def baseStart_3908104 : Nat := 118140960795 + 3908104 * 2 ^ 59
def prefixEnd_3908104 : Nat := 4983230072969 + 3 ^ 40 * 3908104 * 2
def baseEnd_3908104 : Nat := 445941288835307279739325

theorem tailTrace_3908104 : CollatzResearch.WordTrace tailWord_3908104 prefixEnd_3908104 445941288835307279739325 := by
  unfold tailWord_3908104
  simp only [CollatzResearch.WordTrace]
  refine ⟨71270131516807066934909683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95026842022409422579879577 71270131516807066934909683)
  ·
    refine ⟨106905197275210600402364525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71270131516807066934909683 106905197275210600402364525)
    ·
      refine ⟨40089448978203975150886697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106905197275210600402364525 40089448978203975150886697)
      ·
        refine ⟨30067086733652981363165023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40089448978203975150886697 30067086733652981363165023)
        ·
          refine ⟨45100630100479472044747535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30067086733652981363165023 45100630100479472044747535)
          ·
            refine ⟨67650945150719208067121303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45100630100479472044747535 67650945150719208067121303)
            ·
              refine ⟨101476417726078812100681955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67650945150719208067121303 101476417726078812100681955)
              ·
                refine ⟨152214626589118218151022933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101476417726078812100681955 152214626589118218151022933)
                ·
                  refine ⟨445941288835307279739325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 152214626589118218151022933 445941288835307279739325)
                  ·
                    rfl

theorem cell22_3908104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 10].length) (baseStart_3908104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3908104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3908104 prefixEnd_3908104 := by exact prefixLift 3908104
  have htrace : WordTrace (prefixWord ++ tailWord_3908104) baseStart_3908104 baseEnd_3908104 := by
    simpa [prefixWord, tailWord_3908104, baseEnd_3908104] using wordTrace_append hprefix tailTrace_3908104
  have hstable : (prefixWord ++ tailWord_3908104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908104).length < 2 ^ (prefixWord ++ tailWord_3908104).sum := by decide
  have hdescent : baseEnd_3908104 < baseStart_3908104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908151 : List Nat := [1, 1, 3, 1, 2, 3, 2, 3, 2, 4]
def baseStart_3908151 : Nat := 118140960795 + 3908151 * 2 ^ 59
def prefixEnd_3908151 : Nat := 4983230072969 + 3 ^ 40 * 3908151 * 2
def baseEnd_3908151 : Nat := 1337839955566429383292831

theorem tailTrace_3908151 : CollatzResearch.WordTrace tailWord_3908151 prefixEnd_3908151 1337839955566429383292831 := by
  unfold tailWord_3908151
  simp only [CollatzResearch.WordTrace]
  refine ⟨142541977264443860896780307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95027984842962573931186871 142541977264443860896780307)
  ·
    refine ⟨213812965896665791345170461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142541977264443860896780307 213812965896665791345170461)
    ·
      refine ⟨80179862211249671754438923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213812965896665791345170461 80179862211249671754438923)
      ·
        refine ⟨120269793316874507631658385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80179862211249671754438923 120269793316874507631658385)
        ·
          refine ⟨90202344987655880723743789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120269793316874507631658385 90202344987655880723743789)
          ·
            refine ⟨33825879370370955271403921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90202344987655880723743789 33825879370370955271403921)
            ·
              refine ⟨25369409527778216453552941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33825879370370955271403921 25369409527778216453552941)
              ·
                refine ⟨9513528572916831170082353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25369409527778216453552941 9513528572916831170082353)
                ·
                  refine ⟨7135146429687623377561765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9513528572916831170082353 7135146429687623377561765)
                  ·
                    refine ⟨1337839955566429383292831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7135146429687623377561765 1337839955566429383292831)
                    ·
                      rfl

theorem cell22_3908151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_3908151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3908151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3908151 prefixEnd_3908151 := by exact prefixLift 3908151
  have htrace : WordTrace (prefixWord ++ tailWord_3908151) baseStart_3908151 baseEnd_3908151 := by
    simpa [prefixWord, tailWord_3908151, baseEnd_3908151] using wordTrace_append hprefix tailTrace_3908151
  have hstable : (prefixWord ++ tailWord_3908151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908151).length < 2 ^ (prefixWord ++ tailWord_3908151).sum := by decide
  have hdescent : baseEnd_3908151 < baseStart_3908151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908228 : List Nat := [2, 3, 2, 1, 3, 1, 1, 4, 5]
def baseStart_3908228 : Nat := 118140960795 + 3908228 * 2 ^ 59
def prefixEnd_3908228 : Nat := 4983230072969 + 3 ^ 40 * 3908228 * 2
def baseEnd_3908228 : Nat := 445955438080008949705865

theorem tailTrace_3908228 : CollatzResearch.WordTrace tailWord_3908228 prefixEnd_3908228 445955438080008949705865 := by
  unfold tailWord_3908228
  simp only [CollatzResearch.WordTrace]
  refine ⟨71272392842582451523666669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95029857123443268698222225 71272392842582451523666669)
  ·
    refine ⟨26727147315968419321375001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71272392842582451523666669 26727147315968419321375001)
    ·
      refine ⟨20045360486976314491031251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26727147315968419321375001 20045360486976314491031251)
      ·
        refine ⟨30068040730464471736546877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20045360486976314491031251 30068040730464471736546877)
        ·
          refine ⟨11275515273924176901205079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30068040730464471736546877 11275515273924176901205079)
          ·
            refine ⟨16913272910886265351807619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11275515273924176901205079 16913272910886265351807619)
            ·
              refine ⟨25369909366329398027711429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16913272910886265351807619 25369909366329398027711429)
              ·
                refine ⟨4756858006186762130195893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25369909366329398027711429 4756858006186762130195893)
                ·
                  refine ⟨445955438080008949705865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4756858006186762130195893 445955438080008949705865)
                  ·
                    rfl

theorem cell22_3908228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_3908228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3908228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3908228 prefixEnd_3908228 := by exact prefixLift 3908228
  have htrace : WordTrace (prefixWord ++ tailWord_3908228) baseStart_3908228 baseEnd_3908228 := by
    simpa [prefixWord, tailWord_3908228, baseEnd_3908228] using wordTrace_append hprefix tailTrace_3908228
  have hstable : (prefixWord ++ tailWord_3908228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908228).length < 2 ^ (prefixWord ++ tailWord_3908228).sum := by decide
  have hdescent : baseEnd_3908228 < baseStart_3908228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908266 : List Nat := [3, 1, 5, 2, 1, 1, 2, 3, 1, 3]
def baseStart_3908266 : Nat := 118140960795 + 3908266 * 2 ^ 59
def prefixEnd_3908266 : Nat := 4983230072969 + 3 ^ 40 * 3908266 * 2
def baseEnd_3908266 : Nat := 1337879322416607416667479

theorem tailTrace_3908266 : CollatzResearch.WordTrace tailWord_3908266 prefixEnd_3908266 1337879322416607416667479 := by
  unfold tailWord_3908266
  simp only [CollatzResearch.WordTrace]
  refine ⟨35636542914756808884304163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95030781106018157024811101 35636542914756808884304163)
  ·
    refine ⟨53454814372135213326456245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35636542914756808884304163 53454814372135213326456245)
    ·
      refine ⟨5011388847387676249355273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53454814372135213326456245 5011388847387676249355273)
      ·
        refine ⟨3758541635540757187016455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5011388847387676249355273 3758541635540757187016455)
        ·
          refine ⟨5637812453311135780524683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3758541635540757187016455 5637812453311135780524683)
          ·
            refine ⟨8456718679966703670787025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5637812453311135780524683 8456718679966703670787025)
            ·
              refine ⟨6342539009975027753090269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8456718679966703670787025 6342539009975027753090269)
              ·
                refine ⟨2378452128740635407408851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6342539009975027753090269 2378452128740635407408851)
                ·
                  refine ⟨3567678193110953111113277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2378452128740635407408851 3567678193110953111113277)
                  ·
                    refine ⟨1337879322416607416667479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3567678193110953111113277 1337879322416607416667479)
                    ·
                      rfl

theorem cell22_3908266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_3908266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3908266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3908266 prefixEnd_3908266 := by exact prefixLift 3908266
  have htrace : WordTrace (prefixWord ++ tailWord_3908266) baseStart_3908266 baseEnd_3908266 := by
    simpa [prefixWord, tailWord_3908266, baseEnd_3908266] using wordTrace_append hprefix tailTrace_3908266
  have hstable : (prefixWord ++ tailWord_3908266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908266).length < 2 ^ (prefixWord ++ tailWord_3908266).sum := by decide
  have hdescent : baseEnd_3908266 < baseStart_3908266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908275 : List Nat := [1, 1, 1, 2, 3, 4, 4, 1, 1, 4]
def baseStart_3908275 : Nat := 118140960795 + 3908275 * 2 ^ 59
def prefixEnd_3908275 : Nat := 4983230072969 + 3 ^ 40 * 3908275 * 2
def baseEnd_3908275 : Nat := 1337882403300534393192451

theorem tailTrace_3908275 : CollatzResearch.WordTrace tailWord_3908275 prefixEnd_3908275 1337882403300534393192451 := by
  unfold tailWord_3908275
  simp only [CollatzResearch.WordTrace]
  refine ⟨142546499915994630074294279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95030999943996420049529519 142546499915994630074294279)
  ·
    refine ⟨213819749873991945111441419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142546499915994630074294279 213819749873991945111441419)
    ·
      refine ⟨320729624810987917667162129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213819749873991945111441419 320729624810987917667162129)
      ·
        refine ⟨240547218608240938250371597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320729624810987917667162129 240547218608240938250371597)
        ·
          refine ⟨90205206978090351843889349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240547218608240938250371597 90205206978090351843889349)
          ·
            refine ⟨16913476308391940970729253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90205206978090351843889349 16913476308391940970729253)
            ·
              refine ⟨3171276807823488932011735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16913476308391940970729253 3171276807823488932011735)
              ·
                refine ⟨4756915211735233398017603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3171276807823488932011735 4756915211735233398017603)
                ·
                  refine ⟨7135372817602850097026405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4756915211735233398017603 7135372817602850097026405)
                  ·
                    refine ⟨1337882403300534393192451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7135372817602850097026405 1337882403300534393192451)
                    ·
                      rfl

theorem cell22_3908275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 1, 4].length) (baseStart_3908275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3908275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3908275 prefixEnd_3908275 := by exact prefixLift 3908275
  have htrace : WordTrace (prefixWord ++ tailWord_3908275) baseStart_3908275 baseEnd_3908275 := by
    simpa [prefixWord, tailWord_3908275, baseEnd_3908275] using wordTrace_append hprefix tailTrace_3908275
  have hstable : (prefixWord ++ tailWord_3908275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908275).length < 2 ^ (prefixWord ++ tailWord_3908275).sum := by decide
  have hdescent : baseEnd_3908275 < baseStart_3908275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908331 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 1, 8]
def baseStart_3908331 : Nat := 118140960795 + 3908331 * 2 ^ 59
def prefixEnd_3908331 : Nat := 4983230072969 + 3 ^ 40 * 3908331 * 2
def baseEnd_3908331 : Nat := 1337901573244968913792279

theorem tailTrace_3908331 : CollatzResearch.WordTrace tailWord_3908331 prefixEnd_3908331 1337901573244968913792279 := by
  unfold tailWord_3908331
  simp only [CollatzResearch.WordTrace]
  refine ⟨142548542403791751638332847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95032361602527834425555231 142548542403791751638332847)
  ·
    refine ⟨213822813605687627457499271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142548542403791751638332847 213822813605687627457499271)
    ·
      refine ⟨320734220408531441186248907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213822813605687627457499271 320734220408531441186248907)
      ·
        refine ⟨481101330612797161779373361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320734220408531441186248907 481101330612797161779373361)
        ·
          refine ⟨360825997959597871334530021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481101330612797161779373361 360825997959597871334530021)
          ·
            refine ⟨67654874617424600875224379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 360825997959597871334530021 67654874617424600875224379)
            ·
              refine ⟨101482311926136901312836569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67654874617424600875224379 101482311926136901312836569)
              ·
                refine ⟨76111733944602675984627427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101482311926136901312836569 76111733944602675984627427)
                ·
                  refine ⟨114167600916904013976941141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76111733944602675984627427 114167600916904013976941141)
                  ·
                    refine ⟨1337901573244968913792279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 114167600916904013976941141 1337901573244968913792279)
                    ·
                      rfl

theorem cell22_3908331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 8].length) (baseStart_3908331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3908331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3908331 prefixEnd_3908331 := by exact prefixLift 3908331
  have htrace : WordTrace (prefixWord ++ tailWord_3908331) baseStart_3908331 baseEnd_3908331 := by
    simpa [prefixWord, tailWord_3908331, baseEnd_3908331] using wordTrace_append hprefix tailTrace_3908331
  have hstable : (prefixWord ++ tailWord_3908331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908331).length < 2 ^ (prefixWord ++ tailWord_3908331).sum := by decide
  have hdescent : baseEnd_3908331 < baseStart_3908331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908341 : List Nat := [1, 3, 6, 1, 2, 1, 1, 1, 6]
def baseStart_3908341 : Nat := 118140960795 + 3908341 * 2 ^ 59
def prefixEnd_3908341 : Nat := 4983230072969 + 3 ^ 40 * 3908341 * 2
def baseEnd_3908341 : Nat := 445968332149777407014083

theorem tailTrace_3908341 : CollatzResearch.WordTrace tailWord_3908341 prefixEnd_3908341 445968332149777407014083 := by
  unfold tailWord_3908341
  simp only [CollatzResearch.WordTrace]
  refine ⟨142548907133755523346196877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95032604755837015564131251 142548907133755523346196877)
  ·
    refine ⟨53455840175158321254823829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142548907133755523346196877 53455840175158321254823829)
    ·
      refine ⟨2505742508210546308819867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53455840175158321254823829 2505742508210546308819867)
      ·
        refine ⟨3758613762315819463229801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2505742508210546308819867 3758613762315819463229801)
        ·
          refine ⟨2818960321736864597422351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3758613762315819463229801 2818960321736864597422351)
          ·
            refine ⟨4228440482605296896133527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2818960321736864597422351 4228440482605296896133527)
            ·
              refine ⟨6342660723907945344200291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4228440482605296896133527 6342660723907945344200291)
              ·
                refine ⟨9513991085861918016300437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6342660723907945344200291 9513991085861918016300437)
                ·
                  refine ⟨445968332149777407014083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9513991085861918016300437 445968332149777407014083)
                  ·
                    rfl

theorem cell22_3908341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 6].length) (baseStart_3908341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3908341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3908341 prefixEnd_3908341 := by exact prefixLift 3908341
  have htrace : WordTrace (prefixWord ++ tailWord_3908341) baseStart_3908341 baseEnd_3908341 := by
    simpa [prefixWord, tailWord_3908341, baseEnd_3908341] using wordTrace_append hprefix tailTrace_3908341
  have hstable : (prefixWord ++ tailWord_3908341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908341).length < 2 ^ (prefixWord ++ tailWord_3908341).sum := by decide
  have hdescent : baseEnd_3908341 < baseStart_3908341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908408 : List Nat := [2, 1, 2, 1, 3, 2, 2, 3, 6]
def baseStart_3908408 : Nat := 118140960795 + 3908408 * 2 ^ 59
def prefixEnd_3908408 : Nat := 4983230072969 + 3 ^ 40 * 3908408 * 2
def baseEnd_3908408 : Nat := 445975977306188793205681

theorem tailTrace_3908408 : CollatzResearch.WordTrace tailWord_3908408 prefixEnd_3908408 445975977306188793205681 := by
  unfold tailWord_3908408
  simp only [CollatzResearch.WordTrace]
  refine ⟨71275675412256396894442939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95034233883008529192590585 71275675412256396894442939)
  ·
    refine ⟨106913513118384595341664409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71275675412256396894442939 106913513118384595341664409)
    ·
      refine ⟨80185134838788446506248307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106913513118384595341664409 80185134838788446506248307)
      ·
        refine ⟨120277702258182669759372461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80185134838788446506248307 120277702258182669759372461)
        ·
          refine ⟨45104138346818501159764673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120277702258182669759372461 45104138346818501159764673)
          ·
            refine ⟨33828103760113875869823505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45104138346818501159764673 33828103760113875869823505)
            ·
              refine ⟨25371077820085406902367629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33828103760113875869823505 25371077820085406902367629)
              ·
                refine ⟨9514154182532027588387861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25371077820085406902367629 9514154182532027588387861)
                ·
                  refine ⟨445975977306188793205681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9514154182532027588387861 445975977306188793205681)
                  ·
                    rfl

theorem cell22_3908408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 6].length) (baseStart_3908408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3908408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3908408 prefixEnd_3908408 := by exact prefixLift 3908408
  have htrace : WordTrace (prefixWord ++ tailWord_3908408) baseStart_3908408 baseEnd_3908408 := by
    simpa [prefixWord, tailWord_3908408, baseEnd_3908408] using wordTrace_append hprefix tailTrace_3908408
  have hstable : (prefixWord ++ tailWord_3908408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908408).length < 2 ^ (prefixWord ++ tailWord_3908408).sum := by decide
  have hdescent : baseEnd_3908408 < baseStart_3908408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908442 : List Nat := [3, 1, 1, 2, 1, 5, 2, 3, 4]
def baseStart_3908442 : Nat := 118140960795 + 3908442 * 2 ^ 59
def prefixEnd_3908442 : Nat := 4983230072969 + 3 ^ 40 * 3908442 * 2
def baseEnd_3908442 : Nat := 445979856937800541422313

theorem tailTrace_3908442 : CollatzResearch.WordTrace tailWord_3908442 prefixEnd_3908442 445979856937800541422313 := by
  unfold tailWord_3908442
  simp only [CollatzResearch.WordTrace]
  refine ⟨35638147726597404398905895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95035060604259745063749053 35638147726597404398905895)
  ·
    refine ⟨53457221589896106598358843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35638147726597404398905895 53457221589896106598358843)
    ·
      refine ⟨80185832384844159897538265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53457221589896106598358843 80185832384844159897538265)
      ·
        refine ⟨60139374288633119923153699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80185832384844159897538265 60139374288633119923153699)
        ·
          refine ⟨90209061432949679884730549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60139374288633119923153699 90209061432949679884730549)
          ·
            refine ⟨8457099509339032489193489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90209061432949679884730549 8457099509339032489193489)
            ·
              refine ⟨6342824632004274366895117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8457099509339032489193489 6342824632004274366895117)
              ·
                refine ⟨2378559237001602887585669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6342824632004274366895117 2378559237001602887585669)
                ·
                  refine ⟨445979856937800541422313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2378559237001602887585669 445979856937800541422313)
                  ·
                    rfl

theorem cell22_3908442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 3, 4].length) (baseStart_3908442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3908442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3908442 prefixEnd_3908442 := by exact prefixLift 3908442
  have htrace : WordTrace (prefixWord ++ tailWord_3908442) baseStart_3908442 baseEnd_3908442 := by
    simpa [prefixWord, tailWord_3908442, baseEnd_3908442] using wordTrace_append hprefix tailTrace_3908442
  have hstable : (prefixWord ++ tailWord_3908442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908442).length < 2 ^ (prefixWord ++ tailWord_3908442).sum := by decide
  have hdescent : baseEnd_3908442 < baseStart_3908442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908444 : List Nat := [2, 2, 4, 2, 1, 1, 4, 1, 1, 4]
def baseStart_3908444 : Nat := 118140960795 + 3908444 * 2 ^ 59
def prefixEnd_3908444 : Nat := 4983230072969 + 3 ^ 40 * 3908444 * 2
def baseEnd_3908444 : Nat := 1337940255454274285716933

theorem tailTrace_3908444 : CollatzResearch.WordTrace tailWord_3908444 prefixEnd_3908444 1337940255454274285716933 := by
  unfold tailWord_3908444
  simp only [CollatzResearch.WordTrace]
  refine ⟨71276331926191185968598193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95035109234921581291464257 71276331926191185968598193)
  ·
    refine ⟨53457248944643389476448645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71276331926191185968598193 53457248944643389476448645)
    ·
      refine ⟨10023234177120635526834121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53457248944643389476448645 10023234177120635526834121)
      ·
        refine ⟨7517425632840476645125591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10023234177120635526834121 7517425632840476645125591)
        ·
          refine ⟨11276138449260714967688387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7517425632840476645125591 11276138449260714967688387)
          ·
            refine ⟨16914207673891072451532581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11276138449260714967688387 16914207673891072451532581)
            ·
              refine ⟨3171413938854576084662359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16914207673891072451532581 3171413938854576084662359)
              ·
                refine ⟨4757120908281864126993539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3171413938854576084662359 4757120908281864126993539)
                ·
                  refine ⟨7135681362422796190490309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4757120908281864126993539 7135681362422796190490309)
                  ·
                    refine ⟨1337940255454274285716933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7135681362422796190490309 1337940255454274285716933)
                    ·
                      rfl

theorem cell22_3908444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_3908444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3908444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3908444 prefixEnd_3908444 := by exact prefixLift 3908444
  have htrace : WordTrace (prefixWord ++ tailWord_3908444) baseStart_3908444 baseEnd_3908444 := by
    simpa [prefixWord, tailWord_3908444, baseEnd_3908444] using wordTrace_append hprefix tailTrace_3908444
  have hstable : (prefixWord ++ tailWord_3908444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908444).length < 2 ^ (prefixWord ++ tailWord_3908444).sum := by decide
  have hdescent : baseEnd_3908444 < baseStart_3908444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908487 : List Nat := [1, 1, 4, 2, 3, 3, 2, 6]
def baseStart_3908487 : Nat := 118140960795 + 3908487 * 2 ^ 59
def prefixEnd_3908487 : Nat := 4983230072969 + 3 ^ 40 * 3908487 * 2
def baseEnd_3908487 : Nat := 148661663914781834099089

theorem tailTrace_3908487 : CollatzResearch.WordTrace tailWord_3908487 prefixEnd_3908487 148661663914781834099089 := by
  unfold tailWord_3908487
  simp only [CollatzResearch.WordTrace]
  refine ⟨142554232191226590281011715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95036154794151060187341143 142554232191226590281011715)
  ·
    refine ⟨213831348286839885421517573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142554232191226590281011715 213831348286839885421517573)
    ·
      refine ⟨40093377803782478516534545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213831348286839885421517573 40093377803782478516534545)
      ·
        refine ⟨30070033352836858887400909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40093377803782478516534545 30070033352836858887400909)
        ·
          refine ⟨11276262507313822082775341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30070033352836858887400909 11276262507313822082775341)
          ·
            refine ⟨4228598440242683281040753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11276262507313822082775341 4228598440242683281040753)
            ·
              refine ⟨3171448830182012460780565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4228598440242683281040753 3171448830182012460780565)
              ·
                refine ⟨148661663914781834099089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3171448830182012460780565 148661663914781834099089)
                ·
                  rfl

theorem cell22_3908487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 6].length) (baseStart_3908487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3908487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3908487 prefixEnd_3908487 := by exact prefixLift 3908487
  have htrace : WordTrace (prefixWord ++ tailWord_3908487) baseStart_3908487 baseEnd_3908487 := by
    simpa [prefixWord, tailWord_3908487, baseEnd_3908487] using wordTrace_append hprefix tailTrace_3908487
  have hstable : (prefixWord ++ tailWord_3908487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908487).length < 2 ^ (prefixWord ++ tailWord_3908487).sum := by decide
  have hdescent : baseEnd_3908487 < baseStart_3908487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908525 : List Nat := [1, 5, 2, 3, 2, 1, 2, 1, 2, 3]
def baseStart_3908525 : Nat := 118140960795 + 3908525 * 2 ^ 59
def prefixEnd_3908525 : Nat := 4983230072969 + 3 ^ 40 * 3908525 * 2
def baseEnd_3908525 : Nat := 1337967983409617074441685

theorem tailTrace_3908525 : CollatzResearch.WordTrace tailWord_3908525 prefixEnd_3908525 1337967983409617074441685 := by
  unfold tailWord_3908525
  simp only [CollatzResearch.WordTrace]
  refine ⟨142555618165088922770895029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95037078776725948513930019 142555618165088922770895029)
  ·
    refine ⟨13364589202977086509771409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142555618165088922770895029 13364589202977086509771409)
    ·
      refine ⟨10023441902232814882328557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13364589202977086509771409 10023441902232814882328557)
      ·
        refine ⟨3758790713337305580873209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10023441902232814882328557 3758790713337305580873209)
        ·
          refine ⟨2819093035002979185654907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3758790713337305580873209 2819093035002979185654907)
          ·
            refine ⟨4228639552504468778482361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2819093035002979185654907 4228639552504468778482361)
            ·
              refine ⟨3171479664378351583861771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4228639552504468778482361 3171479664378351583861771)
              ·
                refine ⟨4757219496567527375792657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3171479664378351583861771 4757219496567527375792657)
                ·
                  refine ⟨3567914622425645531844493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4757219496567527375792657 3567914622425645531844493)
                  ·
                    refine ⟨1337967983409617074441685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3567914622425645531844493 1337967983409617074441685)
                    ·
                      rfl

theorem cell22_3908525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_3908525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3908525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3908525 prefixEnd_3908525 := by exact prefixLift 3908525
  have htrace : WordTrace (prefixWord ++ tailWord_3908525) baseStart_3908525 baseEnd_3908525 := by
    simpa [prefixWord, tailWord_3908525, baseEnd_3908525] using wordTrace_append hprefix tailTrace_3908525
  have hstable : (prefixWord ++ tailWord_3908525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908525).length < 2 ^ (prefixWord ++ tailWord_3908525).sum := by decide
  have hdescent : baseEnd_3908525 < baseStart_3908525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908594 : List Nat := [3, 2, 1, 5, 1, 1, 1, 2, 6]
def baseStart_3908594 : Nat := 118140960795 + 3908594 * 2 ^ 59
def prefixEnd_3908594 : Nat := 4983230072969 + 3 ^ 40 * 3908594 * 2
def baseEnd_3908594 : Nat := 445997201173241298155491

theorem tailTrace_3908594 : CollatzResearch.WordTrace tailWord_3908594 prefixEnd_3908594 445997201173241298155491 := by
  unfold tailWord_3908594
  simp only [CollatzResearch.WordTrace]
  refine ⟨35639533700459736888789209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95038756534559298370104557 35639533700459736888789209)
  ·
    refine ⟨26729650275344802666591907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35639533700459736888789209 26729650275344802666591907)
    ·
      refine ⟨40094475413017203999887861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26729650275344802666591907 40094475413017203999887861)
      ·
        refine ⟨3758857069970362874989487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40094475413017203999887861 3758857069970362874989487)
        ·
          refine ⟨5638285604955544312484231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3758857069970362874989487 5638285604955544312484231)
          ·
            refine ⟨8457428407433316468726347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5638285604955544312484231 8457428407433316468726347)
            ·
              refine ⟨12686142611149974703089521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8457428407433316468726347 12686142611149974703089521)
              ·
                refine ⟨9514606958362481027317141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12686142611149974703089521 9514606958362481027317141)
                ·
                  refine ⟨445997201173241298155491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9514606958362481027317141 445997201173241298155491)
                  ·
                    rfl

theorem cell22_3908594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_3908594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3908594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3908594 prefixEnd_3908594 := by exact prefixLift 3908594
  have htrace : WordTrace (prefixWord ++ tailWord_3908594) baseStart_3908594 baseEnd_3908594 := by
    simpa [prefixWord, tailWord_3908594, baseEnd_3908594] using wordTrace_append hprefix tailTrace_3908594
  have hstable : (prefixWord ++ tailWord_3908594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908594).length < 2 ^ (prefixWord ++ tailWord_3908594).sum := by decide
  have hdescent : baseEnd_3908594 < baseStart_3908594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908654 : List Nat := [4, 1, 3, 1, 1, 1, 1, 4, 3, 3]
def baseStart_3908654 : Nat := 118140960795 + 3908654 * 2 ^ 59
def prefixEnd_3908654 : Nat := 4983230072969 + 3 ^ 40 * 3908654 * 2
def baseEnd_3908654 : Nat := 1338012142745903737966289

theorem tailTrace_3908654 : CollatzResearch.WordTrace tailWord_3908654 prefixEnd_3908654 1338012142745903737966289 := by
  unfold tailWord_3908654
  simp only [CollatzResearch.WordTrace]
  refine ⟨17820040397702697225292627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95040215454414385201560677 17820040397702697225292627)
  ·
    refine ⟨26730060596554045837938941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17820040397702697225292627 26730060596554045837938941)
    ·
      refine ⟨10023772723707767189227103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26730060596554045837938941 10023772723707767189227103)
      ·
        refine ⟨15035659085561650783840655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10023772723707767189227103 15035659085561650783840655)
        ·
          refine ⟨22553488628342476175760983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15035659085561650783840655 22553488628342476175760983)
          ·
            refine ⟨33830232942513714263641475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22553488628342476175760983 33830232942513714263641475)
            ·
              refine ⟨50745349413770571395462213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33830232942513714263641475 50745349413770571395462213)
              ·
                refine ⟨9514753015081982136649165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50745349413770571395462213 9514753015081982136649165)
                ·
                  refine ⟨3568032380655743301243437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9514753015081982136649165 3568032380655743301243437)
                  ·
                    refine ⟨1338012142745903737966289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3568032380655743301243437 1338012142745903737966289)
                    ·
                      rfl

theorem cell22_3908654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_3908654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3908654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3908654 prefixEnd_3908654 := by exact prefixLift 3908654
  have htrace : WordTrace (prefixWord ++ tailWord_3908654) baseStart_3908654 baseEnd_3908654 := by
    simpa [prefixWord, tailWord_3908654, baseEnd_3908654] using wordTrace_append hprefix tailTrace_3908654
  have hstable : (prefixWord ++ tailWord_3908654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908654).length < 2 ^ (prefixWord ++ tailWord_3908654).sum := by decide
  have hdescent : baseEnd_3908654 < baseStart_3908654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908701 : List Nat := [1, 4, 4, 1, 2, 1, 1, 3, 5]
def baseStart_3908701 : Nat := 118140960795 + 3908701 * 2 ^ 59
def prefixEnd_3908701 : Nat := 4983230072969 + 3 ^ 40 * 3908701 * 2
def baseEnd_3908701 : Nat := 446009410602137094013715

theorem tailTrace_3908701 : CollatzResearch.WordTrace tailWord_3908701 prefixEnd_3908701 446009410602137094013715 := by
  unfold tailWord_3908701
  simp only [CollatzResearch.WordTrace]
  refine ⟨142562037412451304829301957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95041358274967536552867971 142562037412451304829301957)
  ·
    refine ⟨26730382014834619655494117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142562037412451304829301957 26730382014834619655494117)
    ·
      refine ⟨5011946627781491185405147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26730382014834619655494117 5011946627781491185405147)
      ·
        refine ⟨7517919941672236778107721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5011946627781491185405147 7517919941672236778107721)
        ·
          refine ⟨5638439956254177583580791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7517919941672236778107721 5638439956254177583580791)
          ·
            refine ⟨8457659934381266375371187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5638439956254177583580791 8457659934381266375371187)
            ·
              refine ⟨12686489901571899563056781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8457659934381266375371187 12686489901571899563056781)
              ·
                refine ⟨4757433713089462336146293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12686489901571899563056781 4757433713089462336146293)
                ·
                  refine ⟨446009410602137094013715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4757433713089462336146293 446009410602137094013715)
                  ·
                    rfl

theorem cell22_3908701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_3908701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3908701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3908701 prefixEnd_3908701 := by exact prefixLift 3908701
  have htrace : WordTrace (prefixWord ++ tailWord_3908701) baseStart_3908701 baseEnd_3908701 := by
    simpa [prefixWord, tailWord_3908701, baseEnd_3908701] using wordTrace_append hprefix tailTrace_3908701
  have hstable : (prefixWord ++ tailWord_3908701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908701).length < 2 ^ (prefixWord ++ tailWord_3908701).sum := by decide
  have hdescent : baseEnd_3908701 < baseStart_3908701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908714 : List Nat := [3, 1, 3, 2, 2, 2, 1, 1, 3, 4]
def baseStart_3908714 : Nat := 118140960795 + 3908714 * 2 ^ 59
def prefixEnd_3908714 : Nat := 4983230072969 + 3 ^ 40 * 3908714 * 2
def baseEnd_3908714 : Nat := 1338032681972083581466105

theorem tailTrace_3908714 : CollatzResearch.WordTrace tailWord_3908714 prefixEnd_3908714 1338032681972083581466105 := by
  unfold tailWord_3908714
  simp only [CollatzResearch.WordTrace]
  refine ⟨35640627890351052012381299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95041674374269472033016797 35640627890351052012381299)
  ·
    refine ⟨53460941835526578018571949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35640627890351052012381299 53460941835526578018571949)
    ·
      refine ⟨20047853188322466756964481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53460941835526578018571949 20047853188322466756964481)
      ·
        refine ⟨15035889891241850067723361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20047853188322466756964481 15035889891241850067723361)
        ·
          refine ⟨11276917418431387550792521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15035889891241850067723361 11276917418431387550792521)
          ·
            refine ⟨8457688063823540663094391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11276917418431387550792521 8457688063823540663094391)
            ·
              refine ⟨12686532095735310994641587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8457688063823540663094391 12686532095735310994641587)
              ·
                refine ⟨19029798143602966491962381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12686532095735310994641587 19029798143602966491962381)
                ·
                  refine ⟨7136174303851112434485893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19029798143602966491962381 7136174303851112434485893)
                  ·
                    refine ⟨1338032681972083581466105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7136174303851112434485893 1338032681972083581466105)
                    ·
                      rfl

theorem cell22_3908714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_3908714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3908714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3908714 prefixEnd_3908714 := by exact prefixLift 3908714
  have htrace : WordTrace (prefixWord ++ tailWord_3908714) baseStart_3908714 baseEnd_3908714 := by
    simpa [prefixWord, tailWord_3908714, baseEnd_3908714] using wordTrace_append hprefix tailTrace_3908714
  have hstable : (prefixWord ++ tailWord_3908714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908714).length < 2 ^ (prefixWord ++ tailWord_3908714).sum := by decide
  have hdescent : baseEnd_3908714 < baseStart_3908714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908727 : List Nat := [1, 1, 3, 1, 1, 4, 3, 2, 1, 5]
def baseStart_3908727 : Nat := 118140960795 + 3908727 * 2 ^ 59
def prefixEnd_3908727 : Nat := 4983230072969 + 3 ^ 40 * 3908727 * 2
def baseEnd_3908727 : Nat := 1338037132137755880891065

theorem tailTrace_3908727 : CollatzResearch.WordTrace tailWord_3908727 prefixEnd_3908727 1338037132137755880891065 := by
  unfold tailWord_3908727
  simp only [CollatzResearch.WordTrace]
  refine ⟨142562985710357111269748435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95041990473571407513165623 142562985710357111269748435)
  ·
    refine ⟨213844478565535666904622653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142562985710357111269748435 213844478565535666904622653)
    ·
      refine ⟨80191679462075875089233495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213844478565535666904622653 80191679462075875089233495)
      ·
        refine ⟨120287519193113812633850243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80191679462075875089233495 120287519193113812633850243)
        ·
          refine ⟨180431278789670718950775365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120287519193113812633850243 180431278789670718950775365)
          ·
            refine ⟨33830864773063259803270381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180431278789670718950775365 33830864773063259803270381)
            ·
              refine ⟨12686574289898722426226393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33830864773063259803270381 12686574289898722426226393)
              ·
                refine ⟨9514930717424041819669795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12686574289898722426226393 9514930717424041819669795)
                ·
                  refine ⟨14272396076136062729504693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9514930717424041819669795 14272396076136062729504693)
                  ·
                    refine ⟨1338037132137755880891065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14272396076136062729504693 1338037132137755880891065)
                    ·
                      rfl

theorem cell22_3908727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_3908727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3908727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3908727 prefixEnd_3908727 := by exact prefixLift 3908727
  have htrace : WordTrace (prefixWord ++ tailWord_3908727) baseStart_3908727 baseEnd_3908727 := by
    simpa [prefixWord, tailWord_3908727, baseEnd_3908727] using wordTrace_append hprefix tailTrace_3908727
  have hstable : (prefixWord ++ tailWord_3908727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908727).length < 2 ^ (prefixWord ++ tailWord_3908727).sum := by decide
  have hdescent : baseEnd_3908727 < baseStart_3908727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908896 : List Nat := [2, 1, 1, 5, 3, 1, 1, 2, 1, 5]
def baseStart_3908896 : Nat := 118140960795 + 3908896 * 2 ^ 59
def prefixEnd_3908896 : Nat := 4983230072969 + 3 ^ 40 * 3908896 * 2
def baseEnd_3908896 : Nat := 1338094984291495773415547

theorem tailTrace_3908896 : CollatzResearch.WordTrace tailWord_3908896 prefixEnd_3908896 1338094984291495773415547 := by
  unfold tailWord_3908896
  simp only [CollatzResearch.WordTrace]
  refine ⟨71284574823372426566325271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95046099764496568755100361 71284574823372426566325271)
  ·
    refine ⟨106926862235058639849487907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71284574823372426566325271 106926862235058639849487907)
    ·
      refine ⟨160390293352587959774231861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106926862235058639849487907 160390293352587959774231861)
      ·
        refine ⟨15036590001805121228834237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160390293352587959774231861 15036590001805121228834237)
        ·
          refine ⟨5638721250676920460812839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15036590001805121228834237 5638721250676920460812839)
          ·
            refine ⟨8458081876015380691219259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5638721250676920460812839 8458081876015380691219259)
            ·
              refine ⟨12687122814023071036828889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8458081876015380691219259 12687122814023071036828889)
              ·
                refine ⟨9515342110517303277621667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12687122814023071036828889 9515342110517303277621667)
                ·
                  refine ⟨14273013165775954916432501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9515342110517303277621667 14273013165775954916432501)
                  ·
                    refine ⟨1338094984291495773415547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14273013165775954916432501 1338094984291495773415547)
                    ·
                      rfl

theorem cell22_3908896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 1, 5].length) (baseStart_3908896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3908896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3908896 prefixEnd_3908896 := by exact prefixLift 3908896
  have htrace : WordTrace (prefixWord ++ tailWord_3908896) baseStart_3908896 baseEnd_3908896 := by
    simpa [prefixWord, tailWord_3908896, baseEnd_3908896] using wordTrace_append hprefix tailTrace_3908896
  have hstable : (prefixWord ++ tailWord_3908896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908896).length < 2 ^ (prefixWord ++ tailWord_3908896).sum := by decide
  have hdescent : baseEnd_3908896 < baseStart_3908896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908907 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 3, 9]
def baseStart_3908907 : Nat := 118140960795 + 3908907 * 2 ^ 59
def prefixEnd_3908907 : Nat := 4983230072969 + 3 ^ 40 * 3908907 * 2
def baseEnd_3908907 : Nat := 1338098749816295411390513

theorem tailTrace_3908907 : CollatzResearch.WordTrace tailWord_3908907 prefixEnd_3908907 1338098749816295411390513 := by
  unfold tailWord_3908907
  simp only [CollatzResearch.WordTrace]
  refine ⟨142569550849705002011300975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95046367233136668007533983 142569550849705002011300975)
  ·
    refine ⟨213854326274557503016951463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142569550849705002011300975 213854326274557503016951463)
    ·
      refine ⟨320781489411836254525427195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213854326274557503016951463 320781489411836254525427195)
      ·
        refine ⟨481172234117754381788140793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320781489411836254525427195 481172234117754381788140793)
        ·
          refine ⟨360879175588315786341105595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481172234117754381788140793 360879175588315786341105595)
          ·
            refine ⟨541318763382473679511658393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360879175588315786341105595 541318763382473679511658393)
            ·
              refine ⟨405989072536855259633743795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 541318763382473679511658393 405989072536855259633743795)
              ·
                refine ⟨608983608805282889450615693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 405989072536855259633743795 608983608805282889450615693)
                ·
                  refine ⟨228368853301981083543980885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 608983608805282889450615693 228368853301981083543980885)
                  ·
                    refine ⟨1338098749816295411390513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 228368853301981083543980885 1338098749816295411390513)
                    ·
                      rfl

theorem cell22_3908907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 9].length) (baseStart_3908907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3908907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3908907 prefixEnd_3908907 := by exact prefixLift 3908907
  have htrace : WordTrace (prefixWord ++ tailWord_3908907) baseStart_3908907 baseEnd_3908907 := by
    simpa [prefixWord, tailWord_3908907, baseEnd_3908907] using wordTrace_append hprefix tailTrace_3908907
  have hstable : (prefixWord ++ tailWord_3908907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908907).length < 2 ^ (prefixWord ++ tailWord_3908907).sum := by decide
  have hdescent : baseEnd_3908907 < baseStart_3908907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908913 : List Nat := [1, 2, 2, 3, 3, 2, 2, 2, 2, 3]
def baseStart_3908913 : Nat := 118140960795 + 3908913 * 2 ^ 59
def prefixEnd_3908913 : Nat := 4983230072969 + 3 ^ 40 * 3908913 * 2
def baseEnd_3908913 : Nat := 1338100803738913395740495

theorem tailTrace_3908913 : CollatzResearch.WordTrace tailWord_3908913 prefixEnd_3908913 1338100803738913395740495 := by
  unfold tailWord_3908913
  simp only [CollatzResearch.WordTrace]
  refine ⟨142569769687683265036019393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95046513125122176690679595 142569769687683265036019393)
  ·
    refine ⟨106927327265762448777014545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142569769687683265036019393 106927327265762448777014545)
    ·
      refine ⟨80195495449321836582760909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106927327265762448777014545 80195495449321836582760909)
      ·
        refine ⟨30073310793495688718535341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80195495449321836582760909 30073310793495688718535341)
        ·
          refine ⟨11277491547560883269450753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30073310793495688718535341 11277491547560883269450753)
          ·
            refine ⟨8458118660670662452088065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11277491547560883269450753 8458118660670662452088065)
            ·
              refine ⟨6343588995502996839066049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8458118660670662452088065 6343588995502996839066049)
              ·
                refine ⟨4757691746627247629299537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6343588995502996839066049 4757691746627247629299537)
                ·
                  refine ⟨3568268809970435721974653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4757691746627247629299537 3568268809970435721974653)
                  ·
                    refine ⟨1338100803738913395740495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3568268809970435721974653 1338100803738913395740495)
                    ·
                      rfl

theorem cell22_3908913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 2, 3].length) (baseStart_3908913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3908913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3908913 prefixEnd_3908913 := by exact prefixLift 3908913
  have htrace : WordTrace (prefixWord ++ tailWord_3908913) baseStart_3908913 baseEnd_3908913 := by
    simpa [prefixWord, tailWord_3908913, baseEnd_3908913] using wordTrace_append hprefix tailTrace_3908913
  have hstable : (prefixWord ++ tailWord_3908913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908913).length < 2 ^ (prefixWord ++ tailWord_3908913).sum := by decide
  have hdescent : baseEnd_3908913 < baseStart_3908913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909029 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 3, 6]
def baseStart_3909029 : Nat := 118140960795 + 3909029 * 2 ^ 59
def prefixEnd_3909029 : Nat := 4983230072969 + 3 ^ 40 * 3909029 * 2
def baseEnd_3909029 : Nat := 1338140512909527759840139

theorem tailTrace_3909029 : CollatzResearch.WordTrace tailWord_3909029 prefixEnd_3909029 1338140512909527759840139 := by
  unfold tailWord_3909029
  simp only [CollatzResearch.WordTrace]
  refine ⟨142574000555263016847242141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95049333703508677898161427 142574000555263016847242141)
  ·
    refine ⟨53465250208223631317715803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142574000555263016847242141 53465250208223631317715803)
    ·
      refine ⟨80197875312335446976573705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53465250208223631317715803 80197875312335446976573705)
      ·
        refine ⟨60148406484251585232430279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80197875312335446976573705 60148406484251585232430279)
        ·
          refine ⟨90222609726377377848645419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60148406484251585232430279 90222609726377377848645419)
          ·
            refine ⟨135333914589566066772968129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90222609726377377848645419 135333914589566066772968129)
            ·
              refine ⟨101500435942174550079726097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135333914589566066772968129 101500435942174550079726097)
              ·
                refine ⟨76125326956630912559794573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101500435942174550079726097 76125326956630912559794573)
                ·
                  refine ⟨28546997608736592209922965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76125326956630912559794573 28546997608736592209922965)
                  ·
                    refine ⟨1338140512909527759840139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28546997608736592209922965 1338140512909527759840139)
                    ·
                      rfl

theorem cell22_3909029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_3909029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3909029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3909029 prefixEnd_3909029 := by exact prefixLift 3909029
  have htrace : WordTrace (prefixWord ++ tailWord_3909029) baseStart_3909029 baseEnd_3909029 := by
    simpa [prefixWord, tailWord_3909029, baseEnd_3909029] using wordTrace_append hprefix tailTrace_3909029
  have hstable : (prefixWord ++ tailWord_3909029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909029).length < 2 ^ (prefixWord ++ tailWord_3909029).sum := by decide
  have hdescent : baseEnd_3909029 < baseStart_3909029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909052 : List Nat := [2, 2, 2, 4, 3, 1, 1, 2, 1, 4]
def baseStart_3909052 : Nat := 118140960795 + 3909052 * 2 ^ 59
def prefixEnd_3909052 : Nat := 4983230072969 + 3 ^ 40 * 3909052 * 2
def baseEnd_3909052 : Nat := 1338148386279563366515069

theorem tailTrace_3909052 : CollatzResearch.WordTrace tailWord_3909052 prefixEnd_3909052 1338148386279563366515069 := by
  unfold tailWord_3909052
  simp only [CollatzResearch.WordTrace]
  refine ⟨71287419717089845887664705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95049892956119794516886273 71287419717089845887664705)
  ·
    refine ⟨53465564787817384415748529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71287419717089845887664705 53465564787817384415748529)
    ·
      refine ⟨40099173590863038311811397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53465564787817384415748529 40099173590863038311811397)
      ·
        refine ⟨7518595048286819683464637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40099173590863038311811397 7518595048286819683464637)
        ·
          refine ⟨2819473143107557381299239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7518595048286819683464637 2819473143107557381299239)
          ·
            refine ⟨4229209714661336071948859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2819473143107557381299239 4229209714661336071948859)
            ·
              refine ⟨6343814571992004107923289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4229209714661336071948859 6343814571992004107923289)
              ·
                refine ⟨4757860928994003080942467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6343814571992004107923289 4757860928994003080942467)
                ·
                  refine ⟨7136791393491004621413701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4757860928994003080942467 7136791393491004621413701)
                  ·
                    refine ⟨1338148386279563366515069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7136791393491004621413701 1338148386279563366515069)
                    ·
                      rfl

theorem cell22_3909052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 1, 4].length) (baseStart_3909052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3909052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3909052 prefixEnd_3909052 := by exact prefixLift 3909052
  have htrace : WordTrace (prefixWord ++ tailWord_3909052) baseStart_3909052 baseEnd_3909052 := by
    simpa [prefixWord, tailWord_3909052, baseEnd_3909052] using wordTrace_append hprefix tailTrace_3909052
  have hstable : (prefixWord ++ tailWord_3909052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909052).length < 2 ^ (prefixWord ++ tailWord_3909052).sum := by decide
  have hdescent : baseEnd_3909052 < baseStart_3909052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909059 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 2, 7]
def baseStart_3909059 : Nat := 118140960795 + 3909059 * 2 ^ 59
def prefixEnd_3909059 : Nat := 4983230072969 + 3 ^ 40 * 3909059 * 2
def baseEnd_3909059 : Nat := 1338150782522617681590047

theorem tailTrace_3909059 : CollatzResearch.WordTrace tailWord_3909059 prefixEnd_3909059 1338150782522617681590047 := by
  unfold tailWord_3909059
  simp only [CollatzResearch.WordTrace]
  refine ⟨142575094745154331970834231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95050063163436221313889487 142575094745154331970834231)
  ·
    refine ⟨213862642117731497956251347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142575094745154331970834231 213862642117731497956251347)
    ·
      refine ⟨320793963176597246934377021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213862642117731497956251347 320793963176597246934377021)
      ·
        refine ⟨120297736191223967600391383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320793963176597246934377021 120297736191223967600391383)
        ·
          refine ⟨180446604286835951400587075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120297736191223967600391383 180446604286835951400587075)
          ·
            refine ⟨270669906430253927100880613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180446604286835951400587075 270669906430253927100880613)
            ·
              refine ⟨50750607455672611331415115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 270669906430253927100880613 50750607455672611331415115)
              ·
                refine ⟨76125911183508916997122673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50750607455672611331415115 76125911183508916997122673)
                ·
                  refine ⟨57094433387631687747842005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76125911183508916997122673 57094433387631687747842005)
                  ·
                    refine ⟨1338150782522617681590047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57094433387631687747842005 1338150782522617681590047)
                    ·
                      rfl

theorem cell22_3909059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 7].length) (baseStart_3909059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3909059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3909059 prefixEnd_3909059 := by exact prefixLift 3909059
  have htrace : WordTrace (prefixWord ++ tailWord_3909059) baseStart_3909059 baseEnd_3909059 := by
    simpa [prefixWord, tailWord_3909059, baseEnd_3909059] using wordTrace_append hprefix tailTrace_3909059
  have hstable : (prefixWord ++ tailWord_3909059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909059).length < 2 ^ (prefixWord ++ tailWord_3909059).sum := by decide
  have hdescent : baseEnd_3909059 < baseStart_3909059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909091 : List Nat := [1, 1, 1, 6, 2, 1, 1, 1, 2, 6]
def baseStart_3909091 : Nat := 118140960795 + 3909091 * 2 ^ 59
def prefixEnd_3909091 : Nat := 4983230072969 + 3 ^ 40 * 3909091 * 2
def baseEnd_3909091 : Nat := 1338161736776580264789949

theorem tailTrace_3909091 : CollatzResearch.WordTrace tailWord_3909091 prefixEnd_3909091 1338161736776580264789949 := by
  unfold tailWord_3909091
  simp only [CollatzResearch.WordTrace]
  refine ⟨142576261881038401435999127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95050841254025600957332751 142576261881038401435999127)
  ·
    refine ⟨213864392821557602153998691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142576261881038401435999127 213864392821557602153998691)
    ·
      refine ⟨320796589232336403230998037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213864392821557602153998691 320796589232336403230998037)
      ·
        refine ⟨15037340120265768901453033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 320796589232336403230998037 15037340120265768901453033)
        ·
          refine ⟨11278005090199326676089775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15037340120265768901453033 11278005090199326676089775)
          ·
            refine ⟨16917007635298990014134663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11278005090199326676089775 16917007635298990014134663)
            ·
              refine ⟨25375511452948485021201995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16917007635298990014134663 25375511452948485021201995)
              ·
                refine ⟨38063267179422727531802993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25375511452948485021201995 38063267179422727531802993)
                ·
                  refine ⟨28547450384567045648852245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38063267179422727531802993 28547450384567045648852245)
                  ·
                    refine ⟨1338161736776580264789949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28547450384567045648852245 1338161736776580264789949)
                    ·
                      rfl

theorem cell22_3909091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 6].length) (baseStart_3909091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3909091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3909091 prefixEnd_3909091 := by exact prefixLift 3909091
  have htrace : WordTrace (prefixWord ++ tailWord_3909091) baseStart_3909091 baseEnd_3909091 := by
    simpa [prefixWord, tailWord_3909091, baseEnd_3909091] using wordTrace_append hprefix tailTrace_3909091
  have hstable : (prefixWord ++ tailWord_3909091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909091).length < 2 ^ (prefixWord ++ tailWord_3909091).sum := by decide
  have hdescent : baseEnd_3909091 < baseStart_3909091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909110 : List Nat := [5, 1, 1, 1, 2, 3, 1, 2, 3, 3]
def baseStart_3909110 : Nat := 118140960795 + 3909110 * 2 ^ 59
def prefixEnd_3909110 : Nat := 4983230072969 + 3 ^ 40 * 3909110 * 2
def baseEnd_3909110 : Nat := 1338168240864870548564891

theorem tailTrace_3909110 : CollatzResearch.WordTrace tailWord_3909110 prefixEnd_3909110 1338168240864870548564891 := by
  unfold tailWord_3909110
  simp only [CollatzResearch.WordTrace]
  refine ⟨8911059679248097980058799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95051303245313045120627189 8911059679248097980058799)
  ·
    refine ⟨13366589518872146970088199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8911059679248097980058799 13366589518872146970088199)
    ·
      refine ⟨20049884278308220455132299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13366589518872146970088199 20049884278308220455132299)
      ·
        refine ⟨30074826417462330682698449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20049884278308220455132299 30074826417462330682698449)
        ·
          refine ⟨22556119813096748012023837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30074826417462330682698449 22556119813096748012023837)
          ·
            refine ⟨8458544929911280504508939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22556119813096748012023837 8458544929911280504508939)
            ·
              refine ⟨12687817394866920756763409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8458544929911280504508939 12687817394866920756763409)
              ·
                refine ⟨9515863046150190567572557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12687817394866920756763409 9515863046150190567572557)
                ·
                  refine ⟨3568448642306321462839709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9515863046150190567572557 3568448642306321462839709)
                  ·
                    refine ⟨1338168240864870548564891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3568448642306321462839709 1338168240864870548564891)
                    ·
                      rfl

theorem cell22_3909110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_3909110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3909110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3909110 prefixEnd_3909110 := by exact prefixLift 3909110
  have htrace : WordTrace (prefixWord ++ tailWord_3909110) baseStart_3909110 baseEnd_3909110 := by
    simpa [prefixWord, tailWord_3909110, baseEnd_3909110] using wordTrace_append hprefix tailTrace_3909110
  have hstable : (prefixWord ++ tailWord_3909110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909110).length < 2 ^ (prefixWord ++ tailWord_3909110).sum := by decide
  have hdescent : baseEnd_3909110 < baseStart_3909110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909127 : List Nat := [1, 1, 4, 3, 2, 2, 2, 3, 1, 3]
def baseStart_3909127 : Nat := 118140960795 + 3909127 * 2 ^ 59
def prefixEnd_3909127 : Nat := 4983230072969 + 3 ^ 40 * 3909127 * 2
def baseEnd_3909127 : Nat := 1338174060312288170889839

theorem tailTrace_3909127 : CollatzResearch.WordTrace tailWord_3909127 prefixEnd_3909127 1338174060312288170889839 := by
  unfold tailWord_3909127
  simp only [CollatzResearch.WordTrace]
  refine ⟨142577574908907979584309635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95051716605938653056206423 142577574908907979584309635)
  ·
    refine ⟨213866362363361969376464453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142577574908907979584309635 213866362363361969376464453)
    ·
      refine ⟨40099942943130369258087085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213866362363361969376464453 40099942943130369258087085)
      ·
        refine ⟨15037478603673888471782657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40099942943130369258087085 15037478603673888471782657)
        ·
          refine ⟨11278108952755416353836993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15037478603673888471782657 11278108952755416353836993)
          ·
            refine ⟨8458581714566562265377745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11278108952755416353836993 8458581714566562265377745)
            ·
              refine ⟨6343936285924921699033309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8458581714566562265377745 6343936285924921699033309)
              ·
                refine ⟨2378976107221845637137491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6343936285924921699033309 2378976107221845637137491)
                ·
                  refine ⟨3568464160832768455706237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2378976107221845637137491 3568464160832768455706237)
                  ·
                    refine ⟨1338174060312288170889839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3568464160832768455706237 1338174060312288170889839)
                    ·
                      rfl

theorem cell22_3909127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 3, 1, 3].length) (baseStart_3909127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3909127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3909127 prefixEnd_3909127 := by exact prefixLift 3909127
  have htrace : WordTrace (prefixWord ++ tailWord_3909127) baseStart_3909127 baseEnd_3909127 := by
    simpa [prefixWord, tailWord_3909127, baseEnd_3909127] using wordTrace_append hprefix tailTrace_3909127
  have hstable : (prefixWord ++ tailWord_3909127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909127).length < 2 ^ (prefixWord ++ tailWord_3909127).sum := by decide
  have hdescent : baseEnd_3909127 < baseStart_3909127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909140 : List Nat := [2, 4, 3, 1, 2, 1, 1, 1, 7]
def baseStart_3909140 : Nat := 118140960795 + 3909140 * 2 ^ 59
def prefixEnd_3909140 : Nat := 4983230072969 + 3 ^ 40 * 3909140 * 2
def baseEnd_3909140 : Nat := 446059503492653490104933

theorem tailTrace_3909140 : CollatzResearch.WordTrace tailWord_3909140 prefixEnd_3909140 446059503492653490104933 := by
  unfold tailWord_3909140
  simp only [CollatzResearch.WordTrace]
  refine ⟨71289024528930441402266437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95052032705240588536355249 71289024528930441402266437)
  ·
    refine ⟨13366692099174457762924957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71289024528930441402266437 13366692099174457762924957)
    ·
      refine ⟨5012509537190421661096859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13366692099174457762924957 5012509537190421661096859)
      ·
        refine ⟨7518764305785632491645289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5012509537190421661096859 7518764305785632491645289)
        ·
          refine ⟨5639073229339224368733967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7518764305785632491645289 5639073229339224368733967)
          ·
            refine ⟨8458609844008836553100951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5639073229339224368733967 8458609844008836553100951)
            ·
              refine ⟨12687914766013254829651427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8458609844008836553100951 12687914766013254829651427)
              ·
                refine ⟨19031872149019882244477141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12687914766013254829651427 19031872149019882244477141)
                ·
                  refine ⟨446059503492653490104933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19031872149019882244477141 446059503492653490104933)
                  ·
                    rfl

theorem cell22_3909140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_3909140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3909140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3909140 prefixEnd_3909140 := by exact prefixLift 3909140
  have htrace : WordTrace (prefixWord ++ tailWord_3909140) baseStart_3909140 baseEnd_3909140 := by
    simpa [prefixWord, tailWord_3909140, baseEnd_3909140] using wordTrace_append hprefix tailTrace_3909140
  have hstable : (prefixWord ++ tailWord_3909140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909140).length < 2 ^ (prefixWord ++ tailWord_3909140).sum := by decide
  have hdescent : baseEnd_3909140 < baseStart_3909140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909151 : List Nat := [1, 1, 2, 4, 1, 1, 3, 3, 6]
def baseStart_3909151 : Nat := 118140960795 + 3909151 * 2 ^ 59
def prefixEnd_3909151 : Nat := 4983230072969 + 3 ^ 40 * 3909151 * 2
def baseEnd_3909151 : Nat := 446060758667586702763255

theorem tailTrace_3909151 : CollatzResearch.WordTrace tailWord_3909151 prefixEnd_3909151 446060758667586702763255 := by
  unfold tailWord_3909151
  simp only [CollatzResearch.WordTrace]
  refine ⟨142578450260821031683183307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95052300173880687788788871 142578450260821031683183307)
  ·
    refine ⟨213867675391231547524774961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142578450260821031683183307 213867675391231547524774961)
    ·
      refine ⟨160400756543423660643581221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213867675391231547524774961 160400756543423660643581221)
      ·
        refine ⟨30075141851891936370671479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160400756543423660643581221 30075141851891936370671479)
        ·
          refine ⟨45112712777837904556007219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30075141851891936370671479 45112712777837904556007219)
          ·
            refine ⟨67669069166756856834010829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45112712777837904556007219 67669069166756856834010829)
            ·
              refine ⟨25375900937533821312754061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67669069166756856834010829 25375900937533821312754061)
              ·
                refine ⟨9515962851575182992282773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25375900937533821312754061 9515962851575182992282773)
                ·
                  refine ⟨446060758667586702763255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9515962851575182992282773 446060758667586702763255)
                  ·
                    rfl

theorem cell22_3909151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 6].length) (baseStart_3909151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3909151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3909151 prefixEnd_3909151 := by exact prefixLift 3909151
  have htrace : WordTrace (prefixWord ++ tailWord_3909151) baseStart_3909151 baseEnd_3909151 := by
    simpa [prefixWord, tailWord_3909151, baseEnd_3909151] using wordTrace_append hprefix tailTrace_3909151
  have hstable : (prefixWord ++ tailWord_3909151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909151).length < 2 ^ (prefixWord ++ tailWord_3909151).sum := by decide
  have hdescent : baseEnd_3909151 < baseStart_3909151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909183 : List Nat := [1, 1, 2, 2, 3, 3, 1, 2, 4, 3]
def baseStart_3909183 : Nat := 118140960795 + 3909183 * 2 ^ 59
def prefixEnd_3909183 : Nat := 4983230072969 + 3 ^ 40 * 3909183 * 2
def baseEnd_3909183 : Nat := 1338193230256722691489667

theorem tailTrace_3909183 : CollatzResearch.WordTrace tailWord_3909183 prefixEnd_3909183 1338193230256722691489667 := by
  unfold tailWord_3909183
  simp only [CollatzResearch.WordTrace]
  refine ⟨142579617396705101148348203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95053078264470067432232135 142579617396705101148348203)
  ·
    refine ⟨213869426095057651722522305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142579617396705101148348203 213869426095057651722522305)
    ·
      refine ⟨160402069571293238791891729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213869426095057651722522305 160402069571293238791891729)
      ·
        refine ⟨120301552178469929093918797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160402069571293238791891729 120301552178469929093918797)
        ·
          refine ⟨45113082066926223410219549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120301552178469929093918797 45113082066926223410219549)
          ·
            refine ⟨16917405775097333778832331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45113082066926223410219549 16917405775097333778832331)
            ·
              refine ⟨25376108662646000668248497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16917405775097333778832331 25376108662646000668248497)
              ·
                refine ⟨19032081496984500501186373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25376108662646000668248497 19032081496984500501186373)
                ·
                  refine ⟨3568515280684593843972445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19032081496984500501186373 3568515280684593843972445)
                  ·
                    refine ⟨1338193230256722691489667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3568515280684593843972445 1338193230256722691489667)
                    ·
                      rfl

theorem cell22_3909183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 4, 3].length) (baseStart_3909183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3909183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3909183 prefixEnd_3909183 := by exact prefixLift 3909183
  have htrace : WordTrace (prefixWord ++ tailWord_3909183) baseStart_3909183 baseEnd_3909183 := by
    simpa [prefixWord, tailWord_3909183, baseEnd_3909183] using wordTrace_append hprefix tailTrace_3909183
  have hstable : (prefixWord ++ tailWord_3909183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909183).length < 2 ^ (prefixWord ++ tailWord_3909183).sum := by decide
  have hdescent : baseEnd_3909183 < baseStart_3909183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909196 : List Nat := [2, 2, 1, 3, 1, 3, 10]
def baseStart_3909196 : Nat := 118140960795 + 3909196 * 2 ^ 59
def prefixEnd_3909196 : Nat := 4983230072969 + 3 ^ 40 * 3909196 * 2
def baseEnd_3909196 : Nat := 49562877052681295959801

theorem tailTrace_3909196 : CollatzResearch.WordTrace tailWord_3909196 prefixEnd_3909196 49562877052681295959801 := by
  unfold tailWord_3909196
  simp only [CollatzResearch.WordTrace]
  refine ⟨71290045772829002184285721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95053394363772002912380961 71290045772829002184285721)
  ·
    refine ⟨53467534329621751638214291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71290045772829002184285721 53467534329621751638214291)
    ·
      refine ⟨80201301494432627457321437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53467534329621751638214291 80201301494432627457321437)
      ·
        refine ⟨30075488060412235296495539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80201301494432627457321437 30075488060412235296495539)
        ·
          refine ⟨45113232090618352944743309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30075488060412235296495539 45113232090618352944743309)
          ·
            refine ⟨16917462033981882354278741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45113232090618352944743309 16917462033981882354278741)
            ·
              refine ⟨49562877052681295959801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16917462033981882354278741 49562877052681295959801)
              ·
                rfl

theorem cell22_3909196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 10].length) (baseStart_3909196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3909196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3909196 prefixEnd_3909196 := by exact prefixLift 3909196
  have htrace : WordTrace (prefixWord ++ tailWord_3909196) baseStart_3909196 baseEnd_3909196 := by
    simpa [prefixWord, tailWord_3909196, baseEnd_3909196] using wordTrace_append hprefix tailTrace_3909196
  have hstable : (prefixWord ++ tailWord_3909196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909196).length < 2 ^ (prefixWord ++ tailWord_3909196).sum := by decide
  have hdescent : baseEnd_3909196 < baseStart_3909196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909202 : List Nat := [3, 2, 2, 1, 2, 3, 3, 2, 4]
def baseStart_3909202 : Nat := 118140960795 + 3909202 * 2 ^ 59
def prefixEnd_3909202 : Nat := 4983230072969 + 3 ^ 40 * 3909202 * 2
def baseEnd_3909202 : Nat := 446066578115004325088203

theorem tailTrace_3909202 : CollatzResearch.WordTrace tailWord_3909202 prefixEnd_3909202 446066578115004325088203 := by
  unfold tailWord_3909202
  simp only [CollatzResearch.WordTrace]
  refine ⟨35645077595909066848322465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95053540255757511595526573 35645077595909066848322465)
  ·
    refine ⟨26733808196931800136241849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35645077595909066848322465 26733808196931800136241849)
    ·
      refine ⟨20050356147698850102181387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26733808196931800136241849 20050356147698850102181387)
      ·
        refine ⟨30075534221548275153272081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20050356147698850102181387 30075534221548275153272081)
        ·
          refine ⟨22556650666161206364954061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30075534221548275153272081 22556650666161206364954061)
          ·
            refine ⟨8458743999810452386857773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22556650666161206364954061 8458743999810452386857773)
            ·
              refine ⟨3172028999928919645071665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8458743999810452386857773 3172028999928919645071665)
              ·
                refine ⟨2379021749946689733803749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3172028999928919645071665 2379021749946689733803749)
                ·
                  refine ⟨446066578115004325088203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2379021749946689733803749 446066578115004325088203)
                  ·
                    rfl

theorem cell22_3909202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_3909202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3909202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3909202 prefixEnd_3909202 := by exact prefixLift 3909202
  have htrace : WordTrace (prefixWord ++ tailWord_3909202) baseStart_3909202 baseEnd_3909202 := by
    simpa [prefixWord, tailWord_3909202, baseEnd_3909202] using wordTrace_append hprefix tailTrace_3909202
  have hstable : (prefixWord ++ tailWord_3909202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909202).length < 2 ^ (prefixWord ++ tailWord_3909202).sum := by decide
  have hdescent : baseEnd_3909202 < baseStart_3909202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909228 : List Nat := [2, 2, 1, 1, 3, 1, 1, 3, 5, 3]
def baseStart_3909228 : Nat := 118140960795 + 3909228 * 2 ^ 59
def prefixEnd_3909228 : Nat := 4983230072969 + 3 ^ 40 * 3909228 * 2
def baseEnd_3909228 : Nat := 1338208634676357574114529

theorem tailTrace_3909228 : CollatzResearch.WordTrace tailWord_3909228 prefixEnd_3909228 1338208634676357574114529 := by
  unfold tailWord_3909228
  simp only [CollatzResearch.WordTrace]
  refine ⟨71290629340771036916868169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95054172454361382555824225 71290629340771036916868169)
  ·
    refine ⟨53467972005578277687651127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71290629340771036916868169 53467972005578277687651127)
    ·
      refine ⟨80201958008367416531476691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53467972005578277687651127 80201958008367416531476691)
      ·
        refine ⟨120302937012551124797215037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80201958008367416531476691 120302937012551124797215037)
        ·
          refine ⟨45113601379706671798955639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120302937012551124797215037 45113601379706671798955639)
          ·
            refine ⟨67670402069560007698433459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45113601379706671798955639 67670402069560007698433459)
            ·
              refine ⟨101505603104340011547650189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67670402069560007698433459 101505603104340011547650189)
              ·
                refine ⟨38064601164127504330368821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101505603104340011547650189 38064601164127504330368821)
                ·
                  refine ⟨3568556359136953530972077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38064601164127504330368821 3568556359136953530972077)
                  ·
                    refine ⟨1338208634676357574114529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3568556359136953530972077 1338208634676357574114529)
                    ·
                      rfl

theorem cell22_3909228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 3].length) (baseStart_3909228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3909228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3909228 prefixEnd_3909228 := by exact prefixLift 3909228
  have htrace : WordTrace (prefixWord ++ tailWord_3909228) baseStart_3909228 baseEnd_3909228 := by
    simpa [prefixWord, tailWord_3909228, baseEnd_3909228] using wordTrace_append hprefix tailTrace_3909228
  have hstable : (prefixWord ++ tailWord_3909228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909228).length < 2 ^ (prefixWord ++ tailWord_3909228).sum := by decide
  have hdescent : baseEnd_3909228 < baseStart_3909228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909320 : List Nat := [2, 1, 3, 1, 2, 2, 1, 6, 4]
def baseStart_3909320 : Nat := 118140960795 + 3909320 * 2 ^ 59
def prefixEnd_3909320 : Nat := 4983230072969 + 3 ^ 40 * 3909320 * 2
def baseEnd_3909320 : Nat := 446080042718833333604749

theorem tailTrace_3909320 : CollatzResearch.WordTrace tailWord_3909320 prefixEnd_3909320 446080042718833333604749 := by
  unfold tailWord_3909320
  simp only [CollatzResearch.WordTrace]
  refine ⟨71292307098604386773042707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95056409464805849030723609 71292307098604386773042707)
  ·
    refine ⟨106938460647906580159564061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71292307098604386773042707 106938460647906580159564061)
    ·
      refine ⟨40101922742964967559836523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106938460647906580159564061 40101922742964967559836523)
      ·
        refine ⟨60152884114447451339754785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40101922742964967559836523 60152884114447451339754785)
        ·
          refine ⟨45114663085835588504816089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60152884114447451339754785 45114663085835588504816089)
          ·
            refine ⟨33835997314376691378612067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45114663085835588504816089 33835997314376691378612067)
            ·
              refine ⟨50753995971565037067918101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33835997314376691378612067 50753995971565037067918101)
              ·
                refine ⟨2379093561167111112558661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50753995971565037067918101 2379093561167111112558661)
                ·
                  refine ⟨446080042718833333604749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2379093561167111112558661 446080042718833333604749)
                  ·
                    rfl

theorem cell22_3909320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 6, 4].length) (baseStart_3909320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3909320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3909320 prefixEnd_3909320 := by exact prefixLift 3909320
  have htrace : WordTrace (prefixWord ++ tailWord_3909320) baseStart_3909320 baseEnd_3909320 := by
    simpa [prefixWord, tailWord_3909320, baseEnd_3909320] using wordTrace_append hprefix tailTrace_3909320
  have hstable : (prefixWord ++ tailWord_3909320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909320).length < 2 ^ (prefixWord ++ tailWord_3909320).sum := by decide
  have hdescent : baseEnd_3909320 < baseStart_3909320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909348 : List Nat := [2, 3, 1, 1, 1, 3, 3, 8]
def baseStart_3909348 : Nat := 118140960795 + 3909348 * 2 ^ 59
def prefixEnd_3909348 : Nat := 4983230072969 + 3 ^ 40 * 3909348 * 2
def baseEnd_3909348 : Nat := 148694412569857473457129

theorem tailTrace_3909348 : CollatzResearch.WordTrace tailWord_3909348 prefixEnd_3909348 148694412569857473457129 := by
  unfold tailWord_3909348
  simp only [CollatzResearch.WordTrace]
  refine ⟨71292817720553667164052349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95057090294071556218736465 71292817720553667164052349)
  ·
    refine ⟨26734806645207625186519631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71292817720553667164052349 26734806645207625186519631)
    ·
      refine ⟨40102209967811437779779447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26734806645207625186519631 40102209967811437779779447)
      ·
        refine ⟨60153314951717156669669171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40102209967811437779779447 60153314951717156669669171)
        ·
          refine ⟨90229972427575735004503757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60153314951717156669669171 90229972427575735004503757)
          ·
            refine ⟨33836239660340900626688909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90229972427575735004503757 33836239660340900626688909)
            ·
              refine ⟨12688589872627837735008341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33836239660340900626688909 12688589872627837735008341)
              ·
                refine ⟨148694412569857473457129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12688589872627837735008341 148694412569857473457129)
                ·
                  rfl

theorem cell22_3909348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 8].length) (baseStart_3909348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3909348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3909348 prefixEnd_3909348 := by exact prefixLift 3909348
  have htrace : WordTrace (prefixWord ++ tailWord_3909348) baseStart_3909348 baseEnd_3909348 := by
    simpa [prefixWord, tailWord_3909348, baseEnd_3909348] using wordTrace_append hprefix tailTrace_3909348
  have hstable : (prefixWord ++ tailWord_3909348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909348).length < 2 ^ (prefixWord ++ tailWord_3909348).sum := by decide
  have hdescent : baseEnd_3909348 < baseStart_3909348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909427 : List Nat := [1, 1, 1, 2, 7, 1, 2, 2, 5]
def baseStart_3909427 : Nat := 118140960795 + 3909427 * 2 ^ 59
def prefixEnd_3909427 : Nat := 4983230072969 + 3 ^ 40 * 3909427 * 2
def baseEnd_3909427 : Nat := 446092252147729129462973

theorem tailTrace_3909427 : CollatzResearch.WordTrace tailWord_3909427 prefixEnd_3909427 446092252147729129462973 := by
  unfold tailWord_3909427
  simp only [CollatzResearch.WordTrace]
  refine ⟨142588516807821130820230535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95059011205214087213487023 142588516807821130820230535)
  ·
    refine ⟨213882775211731696230345803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142588516807821130820230535 213882775211731696230345803)
    ·
      refine ⟨320824162817597544345518705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213882775211731696230345803 320824162817597544345518705)
      ·
        refine ⟨240618122113198158259139029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320824162817597544345518705 240618122113198158259139029)
        ·
          refine ⟨5639487237028081834198571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 240618122113198158259139029 5639487237028081834198571)
          ·
            refine ⟨8459230855542122751297857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5639487237028081834198571 8459230855542122751297857)
            ·
              refine ⟨6344423141656592063473393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8459230855542122751297857 6344423141656592063473393)
              ·
                refine ⟨4758317356242444047605045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6344423141656592063473393 4758317356242444047605045)
                ·
                  refine ⟨446092252147729129462973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4758317356242444047605045 446092252147729129462973)
                  ·
                    rfl

theorem cell22_3909427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 5].length) (baseStart_3909427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3909427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3909427 prefixEnd_3909427 := by exact prefixLift 3909427
  have htrace : WordTrace (prefixWord ++ tailWord_3909427) baseStart_3909427 baseEnd_3909427 := by
    simpa [prefixWord, tailWord_3909427, baseEnd_3909427] using wordTrace_append hprefix tailTrace_3909427
  have hstable : (prefixWord ++ tailWord_3909427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909427).length < 2 ^ (prefixWord ++ tailWord_3909427).sum := by decide
  have hdescent : baseEnd_3909427 < baseStart_3909427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909472 : List Nat := [2, 1, 1, 3, 3, 2, 1, 5, 4]
def baseStart_3909472 : Nat := 118140960795 + 3909472 * 2 ^ 59
def prefixEnd_3909472 : Nat := 4983230072969 + 3 ^ 40 * 3909472 * 2
def baseEnd_3909472 : Nat := 446097386954274090337927

theorem tailTrace_3909472 : CollatzResearch.WordTrace tailWord_3909472 prefixEnd_3909472 446097386954274090337927 := by
  unfold tailWord_3909472
  simp only [CollatzResearch.WordTrace]
  refine ⟨71295079046329051752809335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95060105395105402337079113 71295079046329051752809335)
  ·
    refine ⟨106942618569493577629214003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71295079046329051752809335 106942618569493577629214003)
    ·
      refine ⟨160413927854240366443821005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106942618569493577629214003 160413927854240366443821005)
      ·
        refine ⟨60155222945340137416432877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160413927854240366443821005 60155222945340137416432877)
        ·
          refine ⟨22558208604502551531162329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60155222945340137416432877 22558208604502551531162329)
          ·
            refine ⟨16918656453376913648371747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22558208604502551531162329 16918656453376913648371747)
            ·
              refine ⟨25377984680065370472557621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16918656453376913648371747 25377984680065370472557621)
              ·
                refine ⟨2379186063756128481802277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25377984680065370472557621 2379186063756128481802277)
                ·
                  refine ⟨446097386954274090337927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2379186063756128481802277 446097386954274090337927)
                  ·
                    rfl

theorem cell22_3909472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 5, 4].length) (baseStart_3909472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3909472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3909472 prefixEnd_3909472 := by exact prefixLift 3909472
  have htrace : WordTrace (prefixWord ++ tailWord_3909472) baseStart_3909472 baseEnd_3909472 := by
    simpa [prefixWord, tailWord_3909472, baseEnd_3909472] using wordTrace_append hprefix tailTrace_3909472
  have hstable : (prefixWord ++ tailWord_3909472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909472).length < 2 ^ (prefixWord ++ tailWord_3909472).sum := by decide
  have hdescent : baseEnd_3909472 < baseStart_3909472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909474 : List Nat := [3, 3, 2, 1, 2, 2, 1, 3, 1, 4]
def baseStart_3909474 : Nat := 118140960795 + 3909474 * 2 ^ 59
def prefixEnd_3909474 : Nat := 4983230072969 + 3 ^ 40 * 3909474 * 2
def baseEnd_3909474 : Nat := 1338292845503694932463775

theorem tailTrace_3909474 : CollatzResearch.WordTrace tailWord_3909474 prefixEnd_3909474 1338292845503694932463775 := by
  unfold tailWord_3909474
  simp only [CollatzResearch.WordTrace]
  refine ⟨35647557759662714461797869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95060154025767238564794317 35647557759662714461797869)
  ·
    refine ⟨13367834159873517923174201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35647557759662714461797869 13367834159873517923174201)
    ·
      refine ⟨10025875619905138442380651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13367834159873517923174201 10025875619905138442380651)
      ·
        refine ⟨15038813429857707663570977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10025875619905138442380651 15038813429857707663570977)
        ·
          refine ⟨11279110072393280747678233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15038813429857707663570977 11279110072393280747678233)
          ·
            refine ⟨8459332554294960560758675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11279110072393280747678233 8459332554294960560758675)
            ·
              refine ⟨12688998831442440841138013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8459332554294960560758675 12688998831442440841138013)
              ·
                refine ⟨4758374561790915315426755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12688998831442440841138013 4758374561790915315426755)
                ·
                  refine ⟨7137561842686372973140133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4758374561790915315426755 7137561842686372973140133)
                  ·
                    refine ⟨1338292845503694932463775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7137561842686372973140133 1338292845503694932463775)
                    ·
                      rfl

theorem cell22_3909474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_3909474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3909474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3909474 prefixEnd_3909474 := by exact prefixLift 3909474
  have htrace : WordTrace (prefixWord ++ tailWord_3909474) baseStart_3909474 baseEnd_3909474 := by
    simpa [prefixWord, tailWord_3909474, baseEnd_3909474] using wordTrace_append hprefix tailTrace_3909474
  have hstable : (prefixWord ++ tailWord_3909474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909474).length < 2 ^ (prefixWord ++ tailWord_3909474).sum := by decide
  have hdescent : baseEnd_3909474 < baseStart_3909474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909504 : List Nat := [2, 1, 1, 2, 1, 2, 7, 1, 2, 3]
def baseStart_3909504 : Nat := 118140960795 + 3909504 * 2 ^ 59
def prefixEnd_3909504 : Nat := 4983230072969 + 3 ^ 40 * 3909504 * 2
def baseEnd_3909504 : Nat := 1338303115116784854213683

theorem tailTrace_3909504 : CollatzResearch.WordTrace tailWord_3909504 prefixEnd_3909504 1338303115116784854213683 := by
  unfold tailWord_3909504
  simp only [CollatzResearch.WordTrace]
  refine ⟨71295662614271086485391783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95060883485694781980522377 71295662614271086485391783)
  ·
    refine ⟨106943493921406629728087675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71295662614271086485391783 106943493921406629728087675)
    ·
      refine ⟨160415240882109944592131513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106943493921406629728087675 160415240882109944592131513)
      ·
        refine ⟨120311430661582458444098635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160415240882109944592131513 120311430661582458444098635)
        ·
          refine ⟨180467145992373687666147953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120311430661582458444098635 180467145992373687666147953)
          ·
            refine ⟨135350359494280265749610965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180467145992373687666147953 135350359494280265749610965)
            ·
              refine ⟨3172274050647193728506507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 135350359494280265749610965 3172274050647193728506507)
              ·
                refine ⟨4758411075970790592759761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3172274050647193728506507 4758411075970790592759761)
                ·
                  refine ⟨3568808306978092944569821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4758411075970790592759761 3568808306978092944569821)
                  ·
                    refine ⟨1338303115116784854213683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3568808306978092944569821 1338303115116784854213683)
                    ·
                      rfl

theorem cell22_3909504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 2, 3].length) (baseStart_3909504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3909504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3909504 prefixEnd_3909504 := by exact prefixLift 3909504
  have htrace : WordTrace (prefixWord ++ tailWord_3909504) baseStart_3909504 baseEnd_3909504 := by
    simpa [prefixWord, tailWord_3909504, baseEnd_3909504] using wordTrace_append hprefix tailTrace_3909504
  have hstable : (prefixWord ++ tailWord_3909504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909504).length < 2 ^ (prefixWord ++ tailWord_3909504).sum := by decide
  have hdescent : baseEnd_3909504 < baseStart_3909504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909560 : List Nat := [2, 1, 2, 1, 2, 3, 2, 1, 1, 7]
def baseStart_3909560 : Nat := 118140960795 + 3909560 * 2 ^ 59
def prefixEnd_3909560 : Nat := 4983230072969 + 3 ^ 40 * 3909560 * 2
def baseEnd_3909560 : Nat := 1338322285061219374813511

theorem tailTrace_3909560 : CollatzResearch.WordTrace tailWord_3909560 prefixEnd_3909560 1338322285061219374813511 := by
  unfold tailWord_3909560
  simp only [CollatzResearch.WordTrace]
  refine ⟨71296683858169647267411067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95062245144226196356548089 71296683858169647267411067)
  ·
    refine ⟨106945025787254470901116601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71296683858169647267411067 106945025787254470901116601)
    ·
      refine ⟨80208769340440853175837451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106945025787254470901116601 80208769340440853175837451)
      ·
        refine ⟨120313154010661279763756177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80208769340440853175837451 120313154010661279763756177)
        ·
          refine ⟨90234865507995959822817133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120313154010661279763756177 90234865507995959822817133)
          ·
            refine ⟨33838074565498484933556425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90234865507995959822817133 33838074565498484933556425)
            ·
              refine ⟨25378555924123863700167319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33838074565498484933556425 25378555924123863700167319)
              ·
                refine ⟨38067833886185795550250979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25378555924123863700167319 38067833886185795550250979)
                ·
                  refine ⟨57101750829278693325376469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38067833886185795550250979 57101750829278693325376469)
                  ·
                    refine ⟨1338322285061219374813511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57101750829278693325376469 1338322285061219374813511)
                    ·
                      rfl

theorem cell22_3909560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_3909560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3909560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3909560 prefixEnd_3909560 := by exact prefixLift 3909560
  have htrace : WordTrace (prefixWord ++ tailWord_3909560) baseStart_3909560 baseEnd_3909560 := by
    simpa [prefixWord, tailWord_3909560, baseEnd_3909560] using wordTrace_append hprefix tailTrace_3909560
  have hstable : (prefixWord ++ tailWord_3909560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909560).length < 2 ^ (prefixWord ++ tailWord_3909560).sum := by decide
  have hdescent : baseEnd_3909560 < baseStart_3909560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909635 : List Nat := [1, 1, 1, 3, 2, 1, 1, 12]
def baseStart_3909635 : Nat := 118140960795 + 3909635 * 2 ^ 59
def prefixEnd_3909635 : Nat := 4983230072969 + 3 ^ 40 * 3909635 * 2
def baseEnd_3909635 : Nat := 148705328788216019909809

theorem tailTrace_3909635 : CollatzResearch.WordTrace tailWord_3909635 prefixEnd_3909635 148705328788216019909809 := by
  unfold tailWord_3909635
  simp only [CollatzResearch.WordTrace]
  refine ⟨142596103191067582343802359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95064068794045054895868239 142596103191067582343802359)
  ·
    refine ⟨213894154786601373515703539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142596103191067582343802359 213894154786601373515703539)
    ·
      refine ⟨320841232179902060273555309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213894154786601373515703539 320841232179902060273555309)
      ·
        refine ⟨120315462067463272602583241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320841232179902060273555309 120315462067463272602583241)
        ·
          refine ⟨90236596550597454451937431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120315462067463272602583241 90236596550597454451937431)
          ·
            refine ⟨135354894825896181677906147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90236596550597454451937431 135354894825896181677906147)
            ·
              refine ⟨203032342238844272516859221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135354894825896181677906147 203032342238844272516859221)
              ·
                refine ⟨148705328788216019909809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 203032342238844272516859221 148705328788216019909809)
                ·
                  rfl

theorem cell22_3909635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 12].length) (baseStart_3909635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3909635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3909635 prefixEnd_3909635 := by exact prefixLift 3909635
  have htrace : WordTrace (prefixWord ++ tailWord_3909635) baseStart_3909635 baseEnd_3909635 := by
    simpa [prefixWord, tailWord_3909635, baseEnd_3909635] using wordTrace_append hprefix tailTrace_3909635
  have hstable : (prefixWord ++ tailWord_3909635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909635).length < 2 ^ (prefixWord ++ tailWord_3909635).sum := by decide
  have hdescent : baseEnd_3909635 < baseStart_3909635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909637 : List Nat := [1, 3, 1, 1, 2, 5, 1, 1, 1, 6]
def baseStart_3909637 : Nat := 118140960795 + 3909637 * 2 ^ 59
def prefixEnd_3909637 : Nat := 4983230072969 + 3 ^ 40 * 3909637 * 2
def baseEnd_3909637 : Nat := 1338348643734816840638275

theorem tailTrace_3909637 : CollatzResearch.WordTrace tailWord_3909637 prefixEnd_3909637 1338348643734816840638275 := by
  unfold tailWord_3909637
  simp only [CollatzResearch.WordTrace]
  refine ⟨142596176137060336685375165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95064117424706891123583443 142596176137060336685375165)
  ·
    refine ⟨53473566051397626257015687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142596176137060336685375165 53473566051397626257015687)
    ·
      refine ⟨80210349077096439385523531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53473566051397626257015687 80210349077096439385523531)
      ·
        refine ⟨120315523615644659078285297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80210349077096439385523531 120315523615644659078285297)
        ·
          refine ⟨90236642711733494308713973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120315523615644659078285297 90236642711733494308713973)
          ·
            refine ⟨8459685254225015091441935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90236642711733494308713973 8459685254225015091441935)
            ·
              refine ⟨12689527881337522637162903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8459685254225015091441935 12689527881337522637162903)
              ·
                refine ⟨19034291822006283955744355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12689527881337522637162903 19034291822006283955744355)
                ·
                  refine ⟨28551437733009425933616533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19034291822006283955744355 28551437733009425933616533)
                  ·
                    refine ⟨1338348643734816840638275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28551437733009425933616533 1338348643734816840638275)
                    ·
                      rfl

theorem cell22_3909637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_3909637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3909637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3909637 prefixEnd_3909637 := by exact prefixLift 3909637
  have htrace : WordTrace (prefixWord ++ tailWord_3909637) baseStart_3909637 baseEnd_3909637 := by
    simpa [prefixWord, tailWord_3909637, baseEnd_3909637] using wordTrace_append hprefix tailTrace_3909637
  have hstable : (prefixWord ++ tailWord_3909637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909637).length < 2 ^ (prefixWord ++ tailWord_3909637).sum := by decide
  have hdescent : baseEnd_3909637 < baseStart_3909637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909744 : List Nat := [2, 1, 1, 1, 5, 3, 1, 1, 3, 4]
def baseStart_3909744 : Nat := 118140960795 + 3909744 * 2 ^ 59
def prefixEnd_3909744 : Nat := 4983230072969 + 3 ^ 40 * 3909744 * 2
def baseEnd_3909744 : Nat := 1338385272021504228212947

theorem tailTrace_3909744 : CollatzResearch.WordTrace tailWord_3909744 prefixEnd_3909744 1338385272021504228212947 := by
  unfold tailWord_3909744
  simp only [CollatzResearch.WordTrace]
  refine ⟨71300039373836346979760143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95066719165115129306346857 71300039373836346979760143)
  ·
    refine ⟨106950059060754520469640215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71300039373836346979760143 106950059060754520469640215)
    ·
      refine ⟨160425088591131780704460323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106950059060754520469640215 160425088591131780704460323)
      ·
        refine ⟨240637632886697671056690485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160425088591131780704460323 240637632886697671056690485)
        ·
          refine ⟨22559778083127906661564733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 240637632886697671056690485 22559778083127906661564733)
          ·
            refine ⟨8459916781172964998086775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22559778083127906661564733 8459916781172964998086775)
            ·
              refine ⟨12689875171759447497130163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8459916781172964998086775 12689875171759447497130163)
              ·
                refine ⟨19034812757639171245695245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12689875171759447497130163 19034812757639171245695245)
                ·
                  refine ⟨7138054784114689217135717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19034812757639171245695245 7138054784114689217135717)
                  ·
                    refine ⟨1338385272021504228212947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7138054784114689217135717 1338385272021504228212947)
                    ·
                      rfl

theorem cell22_3909744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 3, 4].length) (baseStart_3909744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3909744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3909744 prefixEnd_3909744 := by exact prefixLift 3909744
  have htrace : WordTrace (prefixWord ++ tailWord_3909744) baseStart_3909744 baseEnd_3909744 := by
    simpa [prefixWord, tailWord_3909744, baseEnd_3909744] using wordTrace_append hprefix tailTrace_3909744
  have hstable : (prefixWord ++ tailWord_3909744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909744).length < 2 ^ (prefixWord ++ tailWord_3909744).sum := by decide
  have hdescent : baseEnd_3909744 < baseStart_3909744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909772 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 5, 6]
def baseStart_3909772 : Nat := 118140960795 + 3909772 * 2 ^ 59
def prefixEnd_3909772 : Nat := 4983230072969 + 3 ^ 40 * 3909772 * 2
def baseEnd_3909772 : Nat := 1338394856993721488512861

theorem tailTrace_3909772 : CollatzResearch.WordTrace tailWord_3909772 prefixEnd_3909772 1338394856993721488512861 := by
  unfold tailWord_3909772
  simp only [CollatzResearch.WordTrace]
  refine ⟨71300549995785627370769785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95067399994380836494359713 71300549995785627370769785)
  ·
    refine ⟨53475412496839220528077339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71300549995785627370769785 53475412496839220528077339)
    ·
      refine ⟨80213118745258830792116009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53475412496839220528077339 80213118745258830792116009)
      ·
        refine ⟨60159839058944123094087007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80213118745258830792116009 60159839058944123094087007)
        ·
          refine ⟨90239758588416184641130511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60159839058944123094087007 90239758588416184641130511)
          ·
            refine ⟨135359637882624276961695767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90239758588416184641130511 135359637882624276961695767)
            ·
              refine ⟨203039456823936415442543651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135359637882624276961695767 203039456823936415442543651)
              ·
                refine ⟨304559185235904623163815477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203039456823936415442543651 304559185235904623163815477)
                ·
                  refine ⟨28552423615866058421607701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 304559185235904623163815477 28552423615866058421607701)
                  ·
                    refine ⟨1338394856993721488512861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28552423615866058421607701 1338394856993721488512861)
                    ·
                      rfl

theorem cell22_3909772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_3909772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3909772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3909772 prefixEnd_3909772 := by exact prefixLift 3909772
  have htrace : WordTrace (prefixWord ++ tailWord_3909772) baseStart_3909772 baseEnd_3909772 := by
    simpa [prefixWord, tailWord_3909772, baseEnd_3909772] using wordTrace_append hprefix tailTrace_3909772
  have hstable : (prefixWord ++ tailWord_3909772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909772).length < 2 ^ (prefixWord ++ tailWord_3909772).sum := by decide
  have hdescent : baseEnd_3909772 < baseStart_3909772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909791 : List Nat := [1, 1, 2, 6, 1, 2, 2, 1, 1, 5]
def baseStart_3909791 : Nat := 118140960795 + 3909791 * 2 ^ 59
def prefixEnd_3909791 : Nat := 4983230072969 + 3 ^ 40 * 3909791 * 2
def baseEnd_3909791 : Nat := 1338401361082011772287803

theorem tailTrace_3909791 : CollatzResearch.WordTrace tailWord_3909791 prefixEnd_3909791 1338401361082011772287803 := by
  unfold tailWord_3909791
  simp only [CollatzResearch.WordTrace]
  refine ⟨142601792978502420986481227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95067861985668280657654151 142601792978502420986481227)
  ·
    refine ⟨213902689467753631479721841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142601792978502420986481227 213902689467753631479721841)
    ·
      refine ⟨160427017100815223609791381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213902689467753631479721841 160427017100815223609791381)
      ·
        refine ⟨7520016426600713606708971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 160427017100815223609791381 7520016426600713606708971)
        ·
          refine ⟨11280024639901070410063457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7520016426600713606708971 11280024639901070410063457)
          ·
            refine ⟨8460018479925802807547593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11280024639901070410063457 8460018479925802807547593)
            ·
              refine ⟨6345013859944352105660695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8460018479925802807547593 6345013859944352105660695)
              ·
                refine ⟨9517520789916528158491043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6345013859944352105660695 9517520789916528158491043)
                ·
                  refine ⟨14276281184874792237736565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9517520789916528158491043 14276281184874792237736565)
                  ·
                    refine ⟨1338401361082011772287803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14276281184874792237736565 1338401361082011772287803)
                    ·
                      rfl

theorem cell22_3909791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 5].length) (baseStart_3909791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3909791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3909791 prefixEnd_3909791 := by exact prefixLift 3909791
  have htrace : WordTrace (prefixWord ++ tailWord_3909791) baseStart_3909791 baseEnd_3909791 := by
    simpa [prefixWord, tailWord_3909791, baseEnd_3909791] using wordTrace_append hprefix tailTrace_3909791
  have hstable : (prefixWord ++ tailWord_3909791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909791).length < 2 ^ (prefixWord ++ tailWord_3909791).sum := by decide
  have hdescent : baseEnd_3909791 < baseStart_3909791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909812 : List Nat := [2, 5, 3, 1, 1, 1, 1, 3, 1, 4]
def baseStart_3909812 : Nat := 118140960795 + 3909812 * 2 ^ 59
def prefixEnd_3909812 : Nat := 4983230072969 + 3 ^ 40 * 3909812 * 2
def baseEnd_3909812 : Nat := 1338408549811174717512739

theorem tailTrace_3909812 : CollatzResearch.WordTrace tailWord_3909812 prefixEnd_3909812 1338408549811174717512739 := by
  unfold tailWord_3909812
  simp only [CollatzResearch.WordTrace]
  refine ⟨71301279455713170786497845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95068372607617561048663793 71301279455713170786497845)
  ·
    refine ⟨6684494948973109761234173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71301279455713170786497845 6684494948973109761234173)
    ·
      refine ⟨2506685605864916160462815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6684494948973109761234173 2506685605864916160462815)
      ·
        refine ⟨3760028408797374240694223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2506685605864916160462815 3760028408797374240694223)
        ·
          refine ⟨5640042613196061361041335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3760028408797374240694223 5640042613196061361041335)
          ·
            refine ⟨8460063919794092041562003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5640042613196061361041335 8460063919794092041562003)
            ·
              refine ⟨12690095879691138062343005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8460063919794092041562003 12690095879691138062343005)
              ·
                refine ⟨4758785954884176773378627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12690095879691138062343005 4758785954884176773378627)
                ·
                  refine ⟨7138178932326265160067941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4758785954884176773378627 7138178932326265160067941)
                  ·
                    refine ⟨1338408549811174717512739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7138178932326265160067941 1338408549811174717512739)
                    ·
                      rfl

theorem cell22_3909812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_3909812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3909812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3909812 prefixEnd_3909812 := by exact prefixLift 3909812
  have htrace : WordTrace (prefixWord ++ tailWord_3909812) baseStart_3909812 baseEnd_3909812 := by
    simpa [prefixWord, tailWord_3909812, baseEnd_3909812] using wordTrace_append hprefix tailTrace_3909812
  have hstable : (prefixWord ++ tailWord_3909812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909812).length < 2 ^ (prefixWord ++ tailWord_3909812).sum := by decide
  have hdescent : baseEnd_3909812 < baseStart_3909812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909819 : List Nat := [1, 1, 1, 1, 1, 2, 5, 2, 5, 3]
def baseStart_3909819 : Nat := 118140960795 + 3909819 * 2 ^ 59
def prefixEnd_3909819 : Nat := 4983230072969 + 3 ^ 40 * 3909819 * 2
def baseEnd_3909819 : Nat := 1338410946054229032587717

theorem tailTrace_3909819 : CollatzResearch.WordTrace tailWord_3909819 prefixEnd_3909819 1338410946054229032587717 := by
  unfold tailWord_3909819
  simp only [CollatzResearch.WordTrace]
  refine ⟨142602814222400981768500511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95068542814933987845667007 142602814222400981768500511)
  ·
    refine ⟨213904221333601472652750767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142602814222400981768500511 213904221333601472652750767)
    ·
      refine ⟨320856332000402208979126151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213904221333601472652750767 320856332000402208979126151)
      ·
        refine ⟨481284498000603313468689227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320856332000402208979126151 481284498000603313468689227)
        ·
          refine ⟨721926747000904970203033841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481284498000603313468689227 721926747000904970203033841)
          ·
            refine ⟨541445060250678727652275381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 721926747000904970203033841 541445060250678727652275381)
            ·
              refine ⟨50760474398501130717400817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 541445060250678727652275381 50760474398501130717400817)
              ·
                refine ⟨38070355798875848038050613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50760474398501130717400817 38070355798875848038050613)
                ·
                  refine ⟨3569095856144610753567245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38070355798875848038050613 3569095856144610753567245)
                  ·
                    refine ⟨1338410946054229032587717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3569095856144610753567245 1338410946054229032587717)
                    ·
                      rfl

theorem cell22_3909819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 5, 3].length) (baseStart_3909819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3909819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3909819 prefixEnd_3909819 := by exact prefixLift 3909819
  have htrace : WordTrace (prefixWord ++ tailWord_3909819) baseStart_3909819 baseEnd_3909819 := by
    simpa [prefixWord, tailWord_3909819, baseEnd_3909819] using wordTrace_append hprefix tailTrace_3909819
  have hstable : (prefixWord ++ tailWord_3909819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909819).length < 2 ^ (prefixWord ++ tailWord_3909819).sum := by decide
  have hdescent : baseEnd_3909819 < baseStart_3909819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909849 : List Nat := [1, 2, 1, 2, 3, 1, 2, 5, 5]
def baseStart_3909849 : Nat := 118140960795 + 3909849 * 2 ^ 59
def prefixEnd_3909849 : Nat := 4983230072969 + 3 ^ 40 * 3909849 * 2
def baseEnd_3909849 : Nat := 446140405222439651445875

theorem tailTrace_3909849 : CollatzResearch.WordTrace tailWord_3909849 prefixEnd_3909849 446140405222439651445875 := by
  unfold tailWord_3909849
  simp only [CollatzResearch.WordTrace]
  refine ⟨142603908412292296892092601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95069272274861531261395067 142603908412292296892092601)
  ·
    refine ⟨106952931309219222669069451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142603908412292296892092601 106952931309219222669069451)
    ·
      refine ⟨160429396963828834003604177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106952931309219222669069451 160429396963828834003604177)
      ·
        refine ⟨120322047722871625502703133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160429396963828834003604177 120322047722871625502703133)
        ·
          refine ⟨45120767896076859563513675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120322047722871625502703133 45120767896076859563513675)
          ·
            refine ⟨67681151844115289345270513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45120767896076859563513675 67681151844115289345270513)
            ·
              refine ⟨50760863883086467008952885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67681151844115289345270513 50760863883086467008952885)
              ·
                refine ⟨4758830989039356282089333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50760863883086467008952885 4758830989039356282089333)
                ·
                  refine ⟨446140405222439651445875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4758830989039356282089333 446140405222439651445875)
                  ·
                    rfl

theorem cell22_3909849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 5].length) (baseStart_3909849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3909849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3909849 prefixEnd_3909849 := by exact prefixLift 3909849
  have htrace : WordTrace (prefixWord ++ tailWord_3909849) baseStart_3909849 baseEnd_3909849 := by
    simpa [prefixWord, tailWord_3909849, baseEnd_3909849] using wordTrace_append hprefix tailTrace_3909849
  have hstable : (prefixWord ++ tailWord_3909849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909849).length < 2 ^ (prefixWord ++ tailWord_3909849).sum := by decide
  have hdescent : baseEnd_3909849 < baseStart_3909849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909853 : List Nat := [1, 4, 3, 2, 1, 1, 2, 2, 3, 3]
def baseStart_3909853 : Nat := 118140960795 + 3909853 * 2 ^ 59
def prefixEnd_3909853 : Nat := 4983230072969 + 3 ^ 40 * 3909853 * 2
def baseEnd_3909853 : Nat := 1338422584949064277237613

theorem tailTrace_3909853 : CollatzResearch.WordTrace tailWord_3909853 prefixEnd_3909853 1338422584949064277237613 := by
  unfold tailWord_3909853
  simp only [CollatzResearch.WordTrace]
  refine ⟨142604054304277805575238213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95069369536185203716825475 142604054304277805575238213)
  ·
    refine ⟨26738260182052088545357165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142604054304277805575238213 26738260182052088545357165)
    ·
      refine ⟨10026847568269533204508937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26738260182052088545357165 10026847568269533204508937)
      ·
        refine ⟨7520135676202149903381703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10026847568269533204508937 7520135676202149903381703)
        ·
          refine ⟨11280203514303224855072555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7520135676202149903381703 11280203514303224855072555)
          ·
            refine ⟨16920305271454837282608833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11280203514303224855072555 16920305271454837282608833)
            ·
              refine ⟨12690228953591127961956625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16920305271454837282608833 12690228953591127961956625)
              ·
                refine ⟨9517671715193345971467469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12690228953591127961956625 9517671715193345971467469)
                ·
                  refine ⟨3569126893197504739300301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9517671715193345971467469 3569126893197504739300301)
                  ·
                    refine ⟨1338422584949064277237613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3569126893197504739300301 1338422584949064277237613)
                    ·
                      rfl

theorem cell22_3909853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_3909853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3909853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3909853 prefixEnd_3909853 := by exact prefixLift 3909853
  have htrace : WordTrace (prefixWord ++ tailWord_3909853) baseStart_3909853 baseEnd_3909853 := by
    simpa [prefixWord, tailWord_3909853, baseEnd_3909853] using wordTrace_append hprefix tailTrace_3909853
  have hstable : (prefixWord ++ tailWord_3909853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909853).length < 2 ^ (prefixWord ++ tailWord_3909853).sum := by decide
  have hdescent : baseEnd_3909853 < baseStart_3909853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909941 : List Nat := [1, 3, 3, 1, 2, 1, 1, 4, 2, 4]
def baseStart_3909941 : Nat := 118140960795 + 3909941 * 2 ^ 59
def prefixEnd_3909941 : Nat := 4983230072969 + 3 ^ 40 * 3909941 * 2
def baseEnd_3909941 : Nat := 1338452709147461381037343

theorem tailTrace_3909941 : CollatzResearch.WordTrace tailWord_3909941 prefixEnd_3909941 1338452709147461381037343 := by
  unfold tailWord_3909941
  simp only [CollatzResearch.WordTrace]
  refine ⟨142607263927958996604441677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95071509285305997736294451 142607263927958996604441677)
  ·
    refine ⟨53477723972984623726665629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142607263927958996604441677 53477723972984623726665629)
    ·
      refine ⟨20054146489869233897499611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53477723972984623726665629 20054146489869233897499611)
      ·
        refine ⟨30081219734803850846249417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20054146489869233897499611 30081219734803850846249417)
        ·
          refine ⟨22560914801102888134687063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30081219734803850846249417 22560914801102888134687063)
          ·
            refine ⟨33841372201654332202030595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22560914801102888134687063 33841372201654332202030595)
            ·
              refine ⟨50762058302481498303045893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33841372201654332202030595 50762058302481498303045893)
              ·
                refine ⟨9517885931715280931821105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50762058302481498303045893 9517885931715280931821105)
                ·
                  refine ⟨7138414448786460698865829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9517885931715280931821105 7138414448786460698865829)
                  ·
                    refine ⟨1338452709147461381037343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7138414448786460698865829 1338452709147461381037343)
                    ·
                      rfl

theorem cell22_3909941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_3909941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3909941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3909941 prefixEnd_3909941 := by exact prefixLift 3909941
  have htrace : WordTrace (prefixWord ++ tailWord_3909941) baseStart_3909941 baseEnd_3909941 := by
    simpa [prefixWord, tailWord_3909941, baseEnd_3909941] using wordTrace_append hprefix tailTrace_3909941
  have hstable : (prefixWord ++ tailWord_3909941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909941).length < 2 ^ (prefixWord ++ tailWord_3909941).sum := by decide
  have hdescent : baseEnd_3909941 < baseStart_3909941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909945 : List Nat := [1, 2, 1, 6, 1, 1, 4, 2, 4]
def baseStart_3909945 : Nat := 118140960795 + 3909945 * 2 ^ 59
def prefixEnd_3909945 : Nat := 4983230072969 + 3 ^ 40 * 3909945 * 2
def baseEnd_3909945 : Nat := 446151359476402234645777

theorem tailTrace_3909945 : CollatzResearch.WordTrace tailWord_3909945 prefixEnd_3909945 446151359476402234645777 := by
  unfold tailWord_3909945
  simp only [CollatzResearch.WordTrace]
  refine ⟨142607409819944505287587289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95071606546629670191724859 142607409819944505287587289)
  ·
    refine ⟨106955557364958378965690467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142607409819944505287587289 106955557364958378965690467)
    ·
      refine ⟨160433336047437568448535701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106955557364958378965690467 160433336047437568448535701)
      ·
        refine ⟨7520312627223636021025111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 160433336047437568448535701 7520312627223636021025111)
        ·
          refine ⟨11280468940835454031537667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7520312627223636021025111 11280468940835454031537667)
          ·
            refine ⟨16920703411253181047306501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11280468940835454031537667 16920703411253181047306501)
            ·
              refine ⟨3172631889609971446369969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16920703411253181047306501 3172631889609971446369969)
              ·
                refine ⟨2379473917207478584777477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3172631889609971446369969 2379473917207478584777477)
                ·
                  refine ⟨446151359476402234645777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2379473917207478584777477 446151359476402234645777)
                  ·
                    rfl

theorem cell22_3909945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 2, 4].length) (baseStart_3909945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3909945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3909945 prefixEnd_3909945 := by exact prefixLift 3909945
  have htrace : WordTrace (prefixWord ++ tailWord_3909945) baseStart_3909945 baseEnd_3909945 := by
    simpa [prefixWord, tailWord_3909945, baseEnd_3909945] using wordTrace_append hprefix tailTrace_3909945
  have hstable : (prefixWord ++ tailWord_3909945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909945).length < 2 ^ (prefixWord ++ tailWord_3909945).sum := by decide
  have hdescent : baseEnd_3909945 < baseStart_3909945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909973 : List Nat := [1, 3, 2, 2, 4, 1, 3, 6]
def baseStart_3909973 : Nat := 118140960795 + 3909973 * 2 ^ 59
def prefixEnd_3909973 : Nat := 4983230072969 + 3 ^ 40 * 3909973 * 2
def baseEnd_3909973 : Nat := 148718184822380440470805

theorem tailTrace_3909973 : CollatzResearch.WordTrace tailWord_3909973 prefixEnd_3909973 148718184822380440470805 := by
  unfold tailWord_3909973
  simp only [CollatzResearch.WordTrace]
  refine ⟨142608431063843066069606573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95072287375895377379737715 142608431063843066069606573)
  ·
    refine ⟨53478161648941149776102465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142608431063843066069606573 53478161648941149776102465)
    ·
      refine ⟨40108621236705862332076849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53478161648941149776102465 40108621236705862332076849)
      ·
        refine ⟨30081465927529396749057637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40108621236705862332076849 30081465927529396749057637)
        ·
          refine ⟨5640274861411761890448307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30081465927529396749057637 5640274861411761890448307)
          ·
            refine ⟨8460412292117642835672461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5640274861411761890448307 8460412292117642835672461)
            ·
              refine ⟨3172654609544116063377173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8460412292117642835672461 3172654609544116063377173)
              ·
                refine ⟨148718184822380440470805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3172654609544116063377173 148718184822380440470805)
                ·
                  rfl

theorem cell22_3909973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 6].length) (baseStart_3909973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3909973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3909973 prefixEnd_3909973 := by exact prefixLift 3909973
  have htrace : WordTrace (prefixWord ++ tailWord_3909973) baseStart_3909973 baseEnd_3909973 := by
    simpa [prefixWord, tailWord_3909973, baseEnd_3909973] using wordTrace_append hprefix tailTrace_3909973
  have hstable : (prefixWord ++ tailWord_3909973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909973).length < 2 ^ (prefixWord ++ tailWord_3909973).sum := by decide
  have hdescent : baseEnd_3909973 < baseStart_3909973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910005 : List Nat := [1, 3, 4, 1, 2, 2, 2, 1, 3, 3]
def baseStart_3910005 : Nat := 118140960795 + 3910005 * 2 ^ 59
def prefixEnd_3910005 : Nat := 4983230072969 + 3 ^ 40 * 3910005 * 2
def baseEnd_3910005 : Nat := 1338474617655386547437147

theorem tailTrace_3910005 : CollatzResearch.WordTrace tailWord_3910005 prefixEnd_3910005 1338474617655386547437147 := by
  unfold tailWord_3910005
  simp only [CollatzResearch.WordTrace]
  refine ⟨142609598199727135534771469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95073065466484757023180979 142609598199727135534771469)
  ·
    refine ⟨53478599324897675825539301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142609598199727135534771469 53478599324897675825539301)
    ·
      refine ⟨10027237373418314217288619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53478599324897675825539301 10027237373418314217288619)
      ·
        refine ⟨15040856060127471325932929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10027237373418314217288619 15040856060127471325932929)
        ·
          refine ⟨11280642045095603494449697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15040856060127471325932929 11280642045095603494449697)
          ·
            refine ⟨8460481533821702620837273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11280642045095603494449697 8460481533821702620837273)
            ·
              refine ⟨6345361150366276965627955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8460481533821702620837273 6345361150366276965627955)
              ·
                refine ⟨9518041725549415448441933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6345361150366276965627955 9518041725549415448441933)
                ·
                  refine ⟨3569265647081030793165725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9518041725549415448441933 3569265647081030793165725)
                  ·
                    refine ⟨1338474617655386547437147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3569265647081030793165725 1338474617655386547437147)
                    ·
                      rfl

theorem cell22_3910005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_3910005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3910005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3910005 prefixEnd_3910005 := by exact prefixLift 3910005
  have htrace : WordTrace (prefixWord ++ tailWord_3910005) baseStart_3910005 baseEnd_3910005 := by
    simpa [prefixWord, tailWord_3910005, baseEnd_3910005] using wordTrace_append hprefix tailTrace_3910005
  have hstable : (prefixWord ++ tailWord_3910005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910005).length < 2 ^ (prefixWord ++ tailWord_3910005).sum := by decide
  have hdescent : baseEnd_3910005 < baseStart_3910005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910048 : List Nat := [2, 1, 1, 4, 1, 3, 2, 3, 1, 4]
def baseStart_3910048 : Nat := 118140960795 + 3910048 * 2 ^ 59
def prefixEnd_3910048 : Nat := 4983230072969 + 3 ^ 40 * 3910048 * 2
def baseEnd_3910048 : Nat := 1338489337434148768612015

theorem tailTrace_3910048 : CollatzResearch.WordTrace tailWord_3910048 prefixEnd_3910048 1338489337434148768612015 := by
  unfold tailWord_3910048
  simp only [CollatzResearch.WordTrace]
  refine ⟨71305583269285676939293399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95074111025714235919057865 71305583269285676939293399)
  ·
    refine ⟨106958374903928515408940099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71305583269285676939293399 106958374903928515408940099)
    ·
      refine ⟨160437562355892773113410149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106958374903928515408940099 160437562355892773113410149)
      ·
        refine ⟨30082042941729894958764403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160437562355892773113410149 30082042941729894958764403)
        ·
          refine ⟨45123064412594842438146605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30082042941729894958764403 45123064412594842438146605)
          ·
            refine ⟨16921149154723065914304977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45123064412594842438146605 16921149154723065914304977)
            ·
              refine ⟨12690861866042299435728733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16921149154723065914304977 12690861866042299435728733)
              ·
                refine ⟨4759073199765862288398275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12690861866042299435728733 4759073199765862288398275)
                ·
                  refine ⟨7138609799648793432597413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4759073199765862288398275 7138609799648793432597413)
                  ·
                    refine ⟨1338489337434148768612015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7138609799648793432597413 1338489337434148768612015)
                    ·
                      rfl

theorem cell22_3910048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 1, 4].length) (baseStart_3910048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3910048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3910048 prefixEnd_3910048 := by exact prefixLift 3910048
  have htrace : WordTrace (prefixWord ++ tailWord_3910048) baseStart_3910048 baseEnd_3910048 := by
    simpa [prefixWord, tailWord_3910048, baseEnd_3910048] using wordTrace_append hprefix tailTrace_3910048
  have hstable : (prefixWord ++ tailWord_3910048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910048).length < 2 ^ (prefixWord ++ tailWord_3910048).sum := by decide
  have hdescent : baseEnd_3910048 < baseStart_3910048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910114 : List Nat := [3, 3, 3, 2, 1, 1, 1, 4, 4]
def baseStart_3910114 : Nat := 118140960795 + 3910114 * 2 ^ 59
def prefixEnd_3910114 : Nat := 4983230072969 + 3 ^ 40 * 3910114 * 2
def baseEnd_3910114 : Nat := 446170643527648865487271

theorem tailTrace_3910114 : CollatzResearch.WordTrace tailWord_3910114 prefixEnd_3910114 446170643527648865487271 := by
  unfold tailWord_3910114
  simp only [CollatzResearch.WordTrace]
  refine ⟨35653393439083061787622349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95075715837554831433659597 35653393439083061787622349)
  ·
    refine ⟨13370022539656148170358381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35653393439083061787622349 13370022539656148170358381)
    ·
      refine ⟨5013758452371055563884393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13370022539656148170358381 5013758452371055563884393)
      ·
        refine ⟨3760318839278291672913295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5013758452371055563884393 3760318839278291672913295)
        ·
          refine ⟨5640478258917437509369943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3760318839278291672913295 5640478258917437509369943)
          ·
            refine ⟨8460717388376156264054915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5640478258917437509369943 8460717388376156264054915)
            ·
              refine ⟨12691076082564234396082373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8460717388376156264054915 12691076082564234396082373)
              ·
                refine ⟨2379576765480793949265445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12691076082564234396082373 2379576765480793949265445)
                ·
                  refine ⟨446170643527648865487271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2379576765480793949265445 446170643527648865487271)
                  ·
                    rfl

theorem cell22_3910114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_3910114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3910114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3910114 prefixEnd_3910114 := by exact prefixLift 3910114
  have htrace : WordTrace (prefixWord ++ tailWord_3910114) baseStart_3910114 baseEnd_3910114 := by
    simpa [prefixWord, tailWord_3910114, baseEnd_3910114] using wordTrace_append hprefix tailTrace_3910114
  have hstable : (prefixWord ++ tailWord_3910114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910114).length < 2 ^ (prefixWord ++ tailWord_3910114).sum := by decide
  have hdescent : baseEnd_3910114 < baseStart_3910114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910123 : List Nat := [1, 1, 1, 1, 2, 3, 4, 3, 3, 3]
def baseStart_3910123 : Nat := 118140960795 + 3910123 * 2 ^ 59
def prefixEnd_3910123 : Nat := 4983230072969 + 3 ^ 40 * 3910123 * 2
def baseEnd_3910123 : Nat := 1338515011466873572986785

theorem tailTrace_3910123 : CollatzResearch.WordTrace tailWord_3910123 prefixEnd_3910123 1338515011466873572986785 := by
  unfold tailWord_3910123
  simp only [CollatzResearch.WordTrace]
  refine ⟨142613902013299641687567023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95075934675533094458378015 142613902013299641687567023)
  ·
    refine ⟨213920853019949462531350535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142613902013299641687567023 213920853019949462531350535)
    ·
      refine ⟨320881279529924193797025803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213920853019949462531350535 320881279529924193797025803)
      ·
        refine ⟨481321919294886290695538705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320881279529924193797025803 481321919294886290695538705)
        ·
          refine ⟨360991439471164718021654029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481321919294886290695538705 360991439471164718021654029)
          ·
            refine ⟨135371789801686769258120261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360991439471164718021654029 135371789801686769258120261)
            ·
              refine ⟨25382210587816269235897549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135371789801686769258120261 25382210587816269235897549)
              ·
                refine ⟨9518328970431100963461581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25382210587816269235897549 9518328970431100963461581)
                ·
                  refine ⟨3569373363911662861298093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9518328970431100963461581 3569373363911662861298093)
                  ·
                    refine ⟨1338515011466873572986785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3569373363911662861298093 1338515011466873572986785)
                    ·
                      rfl

theorem cell22_3910123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 3, 3].length) (baseStart_3910123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3910123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3910123 prefixEnd_3910123 := by exact prefixLift 3910123
  have htrace : WordTrace (prefixWord ++ tailWord_3910123) baseStart_3910123 baseEnd_3910123 := by
    simpa [prefixWord, tailWord_3910123, baseEnd_3910123] using wordTrace_append hprefix tailTrace_3910123
  have hstable : (prefixWord ++ tailWord_3910123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910123).length < 2 ^ (prefixWord ++ tailWord_3910123).sum := by decide
  have hdescent : baseEnd_3910123 < baseStart_3910123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910125 : List Nat := [1, 5, 1, 3, 1, 3, 1, 7]
def baseStart_3910125 : Nat := 118140960795 + 3910125 * 2 ^ 59
def prefixEnd_3910125 : Nat := 4983230072969 + 3 ^ 40 * 3910125 * 2
def baseEnd_3910125 : Nat := 148723966234194026048531

theorem tailTrace_3910125 : CollatzResearch.WordTrace tailWord_3910125 prefixEnd_3910125 148723966234194026048531 := by
  unfold tailWord_3910125
  simp only [CollatzResearch.WordTrace]
  refine ⟨142613974959292396029139829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95075983306194930686093219 142613974959292396029139829)
  ·
    refine ⟨13370060152433662127731859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142613974959292396029139829 13370060152433662127731859)
    ·
      refine ⟨20055090228650493191597789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13370060152433662127731859 20055090228650493191597789)
      ·
        refine ⟨7520658835743934946849171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20055090228650493191597789 7520658835743934946849171)
        ·
          refine ⟨11280988253615902420273757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7520658835743934946849171 11280988253615902420273757)
          ·
            refine ⟨4230370595105963407602659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11280988253615902420273757 4230370595105963407602659)
            ·
              refine ⟨6345555892658945111403989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4230370595105963407602659 6345555892658945111403989)
              ·
                refine ⟨148723966234194026048531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6345555892658945111403989 148723966234194026048531)
                ·
                  rfl

theorem cell22_3910125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 7].length) (baseStart_3910125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3910125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3910125 prefixEnd_3910125 := by exact prefixLift 3910125
  have htrace : WordTrace (prefixWord ++ tailWord_3910125) baseStart_3910125 baseEnd_3910125 := by
    simpa [prefixWord, tailWord_3910125, baseEnd_3910125] using wordTrace_append hprefix tailTrace_3910125
  have hstable : (prefixWord ++ tailWord_3910125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910125).length < 2 ^ (prefixWord ++ tailWord_3910125).sum := by decide
  have hdescent : baseEnd_3910125 < baseStart_3910125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910168 : List Nat := [2, 1, 2, 3, 3, 1, 1, 2, 2, 5]
def baseStart_3910168 : Nat := 118140960795 + 3910168 * 2 ^ 59
def prefixEnd_3910168 : Nat := 4983230072969 + 3 ^ 40 * 3910168 * 2
def baseEnd_3910168 : Nat := 1338530415886508455611647

theorem tailTrace_3910168 : CollatzResearch.WordTrace tailWord_3910168 prefixEnd_3910168 1338530415886508455611647 := by
  unfold tailWord_3910168
  simp only [CollatzResearch.WordTrace]
  refine ⟨71307771649068307186477579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95077028865424409581970105 71307771649068307186477579)
  ·
    refine ⟨106961657473602460779716369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71307771649068307186477579 106961657473602460779716369)
    ·
      refine ⟨80221243105201845584787277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106961657473602460779716369 80221243105201845584787277)
      ·
        refine ⟨30082966164450692094295229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80221243105201845584787277 30082966164450692094295229)
        ·
          refine ⟨11281112311669009535360711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30082966164450692094295229 11281112311669009535360711)
          ·
            refine ⟨16921668467503514303041067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11281112311669009535360711 16921668467503514303041067)
            ·
              refine ⟨25382502701255271454561601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16921668467503514303041067 25382502701255271454561601)
              ·
                refine ⟨19036877025941453590921201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25382502701255271454561601 19036877025941453590921201)
                ·
                  refine ⟨14277657769456090193190901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19036877025941453590921201 14277657769456090193190901)
                  ·
                    refine ⟨1338530415886508455611647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14277657769456090193190901 1338530415886508455611647)
                    ·
                      rfl

theorem cell22_3910168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_3910168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3910168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3910168 prefixEnd_3910168 := by exact prefixLift 3910168
  have htrace : WordTrace (prefixWord ++ tailWord_3910168) baseStart_3910168 baseEnd_3910168 := by
    simpa [prefixWord, tailWord_3910168, baseEnd_3910168] using wordTrace_append hprefix tailTrace_3910168
  have hstable : (prefixWord ++ tailWord_3910168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910168).length < 2 ^ (prefixWord ++ tailWord_3910168).sum := by decide
  have hdescent : baseEnd_3910168 < baseStart_3910168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910200 : List Nat := [2, 1, 2, 1, 4, 1, 4, 2, 1, 4]
def baseStart_3910200 : Nat := 118140960795 + 3910200 * 2 ^ 59
def prefixEnd_3910200 : Nat := 4983230072969 + 3 ^ 40 * 3910200 * 2
def baseEnd_3910200 : Nat := 1338541370140471038811549

theorem tailTrace_3910200 : CollatzResearch.WordTrace tailWord_3910200 prefixEnd_3910200 1338541370140471038811549 := by
  unfold tailWord_3910200
  simp only [CollatzResearch.WordTrace]
  refine ⟨71308355217010341919060027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95077806956013789225413369 71308355217010341919060027)
  ·
    refine ⟨106962532825515512878590041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71308355217010341919060027 106962532825515512878590041)
    ·
      refine ⟨80221899619136634658942531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106962532825515512878590041 80221899619136634658942531)
      ·
        refine ⟨120332849428704951988413797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80221899619136634658942531 120332849428704951988413797)
        ·
          refine ⟨22562409267882178497827587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120332849428704951988413797 22562409267882178497827587)
          ·
            refine ⟨33843613901823267746741381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22562409267882178497827587 33843613901823267746741381)
            ·
              refine ⟨6345677606591862702514009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33843613901823267746741381 6345677606591862702514009)
              ·
                refine ⟨4759258204943897026885507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6345677606591862702514009 4759258204943897026885507)
                ·
                  refine ⟨7138887307415845540328261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4759258204943897026885507 7138887307415845540328261)
                  ·
                    refine ⟨1338541370140471038811549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7138887307415845540328261 1338541370140471038811549)
                    ·
                      rfl

theorem cell22_3910200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 1, 4].length) (baseStart_3910200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3910200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3910200 prefixEnd_3910200 := by exact prefixLift 3910200
  have htrace : WordTrace (prefixWord ++ tailWord_3910200) baseStart_3910200 baseEnd_3910200 := by
    simpa [prefixWord, tailWord_3910200, baseEnd_3910200] using wordTrace_append hprefix tailTrace_3910200
  have hstable : (prefixWord ++ tailWord_3910200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910200).length < 2 ^ (prefixWord ++ tailWord_3910200).sum := by decide
  have hdescent : baseEnd_3910200 < baseStart_3910200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910238 : List Nat := [4, 4, 1, 2, 1, 2, 2, 1, 5]
def baseStart_3910238 : Nat := 118140960795 + 3910238 * 2 ^ 59
def prefixEnd_3910238 : Nat := 4983230072969 + 3 ^ 40 * 3910238 * 2
def baseEnd_3910238 : Nat := 446184792772350535453811

theorem tailTrace_3910238 : CollatzResearch.WordTrace tailWord_3910238 prefixEnd_3910238 446184792772350535453811 := by
  unfold tailWord_3910238
  simp only [CollatzResearch.WordTrace]
  refine ⟨17827262050985377041000421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95078730938588677552002245 17827262050985377041000421)
  ·
    refine ⟨3342611634559758195187579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17827262050985377041000421 3342611634559758195187579)
    ·
      refine ⟨5013917451839637292781369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3342611634559758195187579 5013917451839637292781369)
      ·
        refine ⟨3760438088879727969586027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5013917451839637292781369 3760438088879727969586027)
        ·
          refine ⟨5640657133319591954379041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3760438088879727969586027 5640657133319591954379041)
          ·
            refine ⟨4230492849989693965784281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5640657133319591954379041 4230492849989693965784281)
            ·
              refine ⟨3172869637492270474338211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4230492849989693965784281 3172869637492270474338211)
              ·
                refine ⟨4759304456238405711507317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3172869637492270474338211 4759304456238405711507317)
                ·
                  refine ⟨446184792772350535453811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4759304456238405711507317 446184792772350535453811)
                  ·
                    rfl

theorem cell22_3910238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_3910238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3910238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3910238 prefixEnd_3910238 := by exact prefixLift 3910238
  have htrace : WordTrace (prefixWord ++ tailWord_3910238) baseStart_3910238 baseEnd_3910238 := by
    simpa [prefixWord, tailWord_3910238, baseEnd_3910238] using wordTrace_append hprefix tailTrace_3910238
  have hstable : (prefixWord ++ tailWord_3910238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910238).length < 2 ^ (prefixWord ++ tailWord_3910238).sum := by decide
  have hdescent : baseEnd_3910238 < baseStart_3910238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910243 : List Nat := [1, 1, 1, 5, 1, 2, 4, 7]
def baseStart_3910243 : Nat := 118140960795 + 3910243 * 2 ^ 59
def prefixEnd_3910243 : Nat := 4983230072969 + 3 ^ 40 * 3910243 * 2
def baseEnd_3910243 : Nat := 148728454435470362220713

theorem tailTrace_3910243 : CollatzResearch.WordTrace tailWord_3910243 prefixEnd_3910243 148728454435470362220713 := by
  unfold tailWord_3910243
  simp only [CollatzResearch.WordTrace]
  refine ⟨142618278772864902181935383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95078852515243268121290255 142618278772864902181935383)
  ·
    refine ⟨213927418159297353272903075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142618278772864902181935383 213927418159297353272903075)
    ·
      refine ⟨320891127238946029909354613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213927418159297353272903075 320891127238946029909354613)
      ·
        refine ⟨30083543178651190304001995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 320891127238946029909354613 30083543178651190304001995)
        ·
          refine ⟨45125314767976785456002993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30083543178651190304001995 45125314767976785456002993)
          ·
            refine ⟨33843986075982589092002245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45125314767976785456002993 33843986075982589092002245)
            ·
              refine ⟨6345747389246735454750421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33843986075982589092002245 6345747389246735454750421)
              ·
                refine ⟨148728454435470362220713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6345747389246735454750421 148728454435470362220713)
                ·
                  rfl

theorem cell22_3910243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 7].length) (baseStart_3910243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3910243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3910243 prefixEnd_3910243 := by exact prefixLift 3910243
  have htrace : WordTrace (prefixWord ++ tailWord_3910243) baseStart_3910243 baseEnd_3910243 := by
    simpa [prefixWord, tailWord_3910243, baseEnd_3910243] using wordTrace_append hprefix tailTrace_3910243
  have hstable : (prefixWord ++ tailWord_3910243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910243).length < 2 ^ (prefixWord ++ tailWord_3910243).sum := by decide
  have hdescent : baseEnd_3910243 < baseStart_3910243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910290 : List Nat := [3, 2, 3, 1, 2, 1, 1, 1, 2, 6]
def baseStart_3910290 : Nat := 118140960795 + 3910290 * 2 ^ 59
def prefixEnd_3910290 : Nat := 4983230072969 + 3 ^ 40 * 3910290 * 2
def baseEnd_3910290 : Nat := 1338572178979740804061273

theorem tailTrace_3910290 : CollatzResearch.WordTrace tailWord_3910290 prefixEnd_3910290 1338572178979740804061273 := by
  unfold tailWord_3910290
  simp only [CollatzResearch.WordTrace]
  refine ⟨35654998250923657302224081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95079995335796419472597549 35654998250923657302224081)
  ·
    refine ⟨26741248688192742976668061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35654998250923657302224081 26741248688192742976668061)
    ·
      refine ⟨10027968258072278616250523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26741248688192742976668061 10027968258072278616250523)
      ·
        refine ⟨15041952387108417924375785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10027968258072278616250523 15041952387108417924375785)
        ·
          refine ⟨11281464290331313443281839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15041952387108417924375785 11281464290331313443281839)
          ·
            refine ⟨16922196435496970164922759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11281464290331313443281839 16922196435496970164922759)
            ·
              refine ⟨25383294653245455247384139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16922196435496970164922759 25383294653245455247384139)
              ·
                refine ⟨38074941979868182871076209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25383294653245455247384139 38074941979868182871076209)
                ·
                  refine ⟨28556206484901137153307157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38074941979868182871076209 28556206484901137153307157)
                  ·
                    refine ⟨1338572178979740804061273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28556206484901137153307157 1338572178979740804061273)
                    ·
                      rfl

theorem cell22_3910290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_3910290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3910290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3910290 prefixEnd_3910290 := by exact prefixLift 3910290
  have htrace : WordTrace (prefixWord ++ tailWord_3910290) baseStart_3910290 baseEnd_3910290 := by
    simpa [prefixWord, tailWord_3910290, baseEnd_3910290] using wordTrace_append hprefix tailTrace_3910290
  have hstable : (prefixWord ++ tailWord_3910290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910290).length < 2 ^ (prefixWord ++ tailWord_3910290).sum := by decide
  have hdescent : baseEnd_3910290 < baseStart_3910290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910350 : List Nat := [4, 1, 1, 1, 3, 2, 1, 3, 6]
def baseStart_3910350 : Nat := 118140960795 + 3910350 * 2 ^ 59
def prefixEnd_3910350 : Nat := 4983230072969 + 3 ^ 40 * 3910350 * 2
def baseEnd_3910350 : Nat := 446197572735306882520363

theorem tailTrace_3910350 : CollatzResearch.WordTrace tailWord_3910350 prefixEnd_3910350 446197572735306882520363 := by
  unfold tailWord_3910350
  simp only [CollatzResearch.WordTrace]
  refine ⟨17827772672934657432010063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95081454255651506304053669 17827772672934657432010063)
  ·
    refine ⟨26741659009401986148015095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17827772672934657432010063 26741659009401986148015095)
    ·
      refine ⟨40112488514102979222022643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26741659009401986148015095 40112488514102979222022643)
      ·
        refine ⟨60168732771154468833033965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40112488514102979222022643 60168732771154468833033965)
        ·
          refine ⟨22563274789182925812387737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60168732771154468833033965 22563274789182925812387737)
          ·
            refine ⟨16922456091887194359290803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22563274789182925812387737 16922456091887194359290803)
            ·
              refine ⟨25383684137830791538936205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16922456091887194359290803 25383684137830791538936205)
              ·
                refine ⟨9518881551686546827101077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25383684137830791538936205 9518881551686546827101077)
                ·
                  refine ⟨446197572735306882520363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9518881551686546827101077 446197572735306882520363)
                  ·
                    rfl

theorem cell22_3910350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_3910350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3910350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3910350 prefixEnd_3910350 := by exact prefixLift 3910350
  have htrace : WordTrace (prefixWord ++ tailWord_3910350) baseStart_3910350 baseEnd_3910350 := by
    simpa [prefixWord, tailWord_3910350, baseEnd_3910350] using wordTrace_append hprefix tailTrace_3910350
  have hstable : (prefixWord ++ tailWord_3910350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910350).length < 2 ^ (prefixWord ++ tailWord_3910350).sum := by decide
  have hdescent : baseEnd_3910350 < baseStart_3910350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910380 : List Nat := [2, 2, 1, 1, 2, 2, 1, 5, 2, 4]
def baseStart_3910380 : Nat := 118140960795 + 3910380 * 2 ^ 59
def prefixEnd_3910380 : Nat := 4983230072969 + 3 ^ 40 * 3910380 * 2
def baseEnd_3910380 : Nat := 1338602987819010569310997

theorem tailTrace_3910380 : CollatzResearch.WordTrace tailWord_3910380 prefixEnd_3910380 1338602987819010569310997 := by
  unfold tailWord_3910380
  simp only [CollatzResearch.WordTrace]
  refine ⟨71311637786684287289836297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95082183715579049719781729 71311637786684287289836297)
  ·
    refine ⟨53483728340013215467377223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71311637786684287289836297 53483728340013215467377223)
    ·
      refine ⟨80225592510019823201065835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53483728340013215467377223 80225592510019823201065835)
      ·
        refine ⟨120338388765029734801598753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80225592510019823201065835 120338388765029734801598753)
        ·
          refine ⟨90253791573772301101199065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120338388765029734801598753 90253791573772301101199065)
          ·
            refine ⟨67690343680329225825899299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90253791573772301101199065 67690343680329225825899299)
            ·
              refine ⟨101535515520493838738848949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67690343680329225825899299 101535515520493838738848949)
              ·
                refine ⟨9518954580046297381767089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101535515520493838738848949 9518954580046297381767089)
                ·
                  refine ⟨7139215935034723036325317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9518954580046297381767089 7139215935034723036325317)
                  ·
                    refine ⟨1338602987819010569310997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7139215935034723036325317 1338602987819010569310997)
                    ·
                      rfl

theorem cell22_3910380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_3910380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3910380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3910380 prefixEnd_3910380 := by exact prefixLift 3910380
  have htrace : WordTrace (prefixWord ++ tailWord_3910380) baseStart_3910380 baseEnd_3910380 := by
    simpa [prefixWord, tailWord_3910380, baseEnd_3910380] using wordTrace_append hprefix tailTrace_3910380
  have hstable : (prefixWord ++ tailWord_3910380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910380).length < 2 ^ (prefixWord ++ tailWord_3910380).sum := by decide
  have hdescent : baseEnd_3910380 < baseStart_3910380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910382 : List Nat := [4, 1, 2, 1, 1, 3, 1, 2, 4, 3]
def baseStart_3910382 : Nat := 118140960795 + 3910382 * 2 ^ 59
def prefixEnd_3910382 : Nat := 4983230072969 + 3 ^ 40 * 3910382 * 2
def baseEnd_3910382 : Nat := 1338603672459883230760991

theorem tailTrace_3910382 : CollatzResearch.WordTrace tailWord_3910382 prefixEnd_3910382 1338603672459883230760991 := by
  unfold tailWord_3910382
  simp only [CollatzResearch.WordTrace]
  refine ⟨17827918564920166115155675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95082232346240885947496933 17827918564920166115155675)
  ·
    refine ⟨26741877847380249172733513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17827918564920166115155675 26741877847380249172733513)
    ·
      refine ⟨20056408385535186879550135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26741877847380249172733513 20056408385535186879550135)
      ·
        refine ⟨30084612578302780319325203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20056408385535186879550135 30084612578302780319325203)
        ·
          refine ⟨45126918867454170478987805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30084612578302780319325203 45126918867454170478987805)
          ·
            refine ⟨16922594575295313929620427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45126918867454170478987805 16922594575295313929620427)
            ·
              refine ⟨25383891862942970894430641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16922594575295313929620427 25383891862942970894430641)
              ·
                refine ⟨19037918897207228170822981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25383891862942970894430641 19037918897207228170822981)
                ·
                  refine ⟨3569609793226355282029309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19037918897207228170822981 3569609793226355282029309)
                  ·
                    refine ⟨1338603672459883230760991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3569609793226355282029309 1338603672459883230760991)
                    ·
                      rfl

theorem cell22_3910382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_3910382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3910382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3910382 prefixEnd_3910382 := by exact prefixLift 3910382
  have htrace : WordTrace (prefixWord ++ tailWord_3910382) baseStart_3910382 baseEnd_3910382 := by
    simpa [prefixWord, tailWord_3910382, baseEnd_3910382] using wordTrace_append hprefix tailTrace_3910382
  have hstable : (prefixWord ++ tailWord_3910382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910382).length < 2 ^ (prefixWord ++ tailWord_3910382).sum := by decide
  have hdescent : baseEnd_3910382 < baseStart_3910382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910444 : List Nat := [2, 2, 1, 1, 1, 4, 2, 5, 1, 3]
def baseStart_3910444 : Nat := 118140960795 + 3910444 * 2 ^ 59
def prefixEnd_3910444 : Nat := 4983230072969 + 3 ^ 40 * 3910444 * 2
def baseEnd_3910444 : Nat := 1338624896326935735710801

theorem tailTrace_3910444 : CollatzResearch.WordTrace tailWord_3910444 prefixEnd_3910444 1338624896326935735710801 := by
  unfold tailWord_3910444
  simp only [CollatzResearch.WordTrace]
  refine ⟨71312804922568356755001193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95083739896757809006668257 71312804922568356755001193)
  ·
    refine ⟨53484603691926267566250895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71312804922568356755001193 53484603691926267566250895)
    ·
      refine ⟨80226905537889401349376343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53484603691926267566250895 80226905537889401349376343)
      ·
        refine ⟨120340358306834102024064515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80226905537889401349376343 120340358306834102024064515)
        ·
          refine ⟨180510537460251153036096773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120340358306834102024064515 180510537460251153036096773)
          ·
            refine ⟨33845725773797091194268145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180510537460251153036096773 33845725773797091194268145)
            ·
              refine ⟨25384294330347818395701109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33845725773797091194268145 25384294330347818395701109)
              ·
                refine ⟨2379777593470107974596979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25384294330347818395701109 2379777593470107974596979)
                ·
                  refine ⟨3569666390205161961895469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2379777593470107974596979 3569666390205161961895469)
                  ·
                    refine ⟨1338624896326935735710801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3569666390205161961895469 1338624896326935735710801)
                    ·
                      rfl

theorem cell22_3910444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 5, 1, 3].length) (baseStart_3910444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3910444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3910444 prefixEnd_3910444 := by exact prefixLift 3910444
  have htrace : WordTrace (prefixWord ++ tailWord_3910444) baseStart_3910444 baseEnd_3910444 := by
    simpa [prefixWord, tailWord_3910444, baseEnd_3910444] using wordTrace_append hprefix tailTrace_3910444
  have hstable : (prefixWord ++ tailWord_3910444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910444).length < 2 ^ (prefixWord ++ tailWord_3910444).sum := by decide
  have hdescent : baseEnd_3910444 < baseStart_3910444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910455 : List Nat := [1, 1, 3, 1, 2, 1, 4, 2, 2, 5]
def baseStart_3910455 : Nat := 118140960795 + 3910455 * 2 ^ 59
def prefixEnd_3910455 : Nat := 4983230072969 + 3 ^ 40 * 3910455 * 2
def baseEnd_3910455 : Nat := 1338628661851735373685767

theorem tailTrace_3910455 : CollatzResearch.WordTrace tailWord_3910455 prefixEnd_3910455 1338628661851735373685767 := by
  unfold tailWord_3910455
  simp only [CollatzResearch.WordTrace]
  refine ⟨142626011048096862388652819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95084007365397908259101879 142626011048096862388652819)
  ·
    refine ⟨213939016572145293582979229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142626011048096862388652819 213939016572145293582979229)
    ·
      refine ⟨80227131214554485093617211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213939016572145293582979229 80227131214554485093617211)
      ·
        refine ⟨120340696821831727640425817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80227131214554485093617211 120340696821831727640425817)
        ·
          refine ⟨90255522616373795730319363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120340696821831727640425817 90255522616373795730319363)
          ·
            refine ⟨135383283924560693595479045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90255522616373795730319363 135383283924560693595479045)
            ·
              refine ⟨25384365735855130049152321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135383283924560693595479045 25384365735855130049152321)
              ·
                refine ⟨19038274301891347536864241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25384365735855130049152321 19038274301891347536864241)
                ·
                  refine ⟨14278705726418510652648181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19038274301891347536864241 14278705726418510652648181)
                  ·
                    refine ⟨1338628661851735373685767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14278705726418510652648181 1338628661851735373685767)
                    ·
                      rfl

theorem cell22_3910455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_3910455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3910455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3910455 prefixEnd_3910455 := by exact prefixLift 3910455
  have htrace : WordTrace (prefixWord ++ tailWord_3910455) baseStart_3910455 baseEnd_3910455 := by
    simpa [prefixWord, tailWord_3910455, baseEnd_3910455] using wordTrace_append hprefix tailTrace_3910455
  have hstable : (prefixWord ++ tailWord_3910455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910455).length < 2 ^ (prefixWord ++ tailWord_3910455).sum := by decide
  have hdescent : baseEnd_3910455 < baseStart_3910455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910487 : List Nat := [1, 1, 3, 2, 4, 1, 2, 1, 3, 4]
def baseStart_3910487 : Nat := 118140960795 + 3910487 * 2 ^ 59
def prefixEnd_3910487 : Nat := 4983230072969 + 3 ^ 40 * 3910487 * 2
def baseEnd_3910487 : Nat := 1338639616105697956885669

theorem tailTrace_3910487 : CollatzResearch.WordTrace tailWord_3910487 prefixEnd_3910487 1338639616105697956885669 := by
  unfold tailWord_3910487
  simp only [CollatzResearch.WordTrace]
  refine ⟨142627178183980931853817715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95084785455987287902545143 142627178183980931853817715)
  ·
    refine ⟨213940767275971397780726573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142627178183980931853817715 213940767275971397780726573)
    ·
      refine ⟨80227787728489274167772465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213940767275971397780726573 80227787728489274167772465)
      ·
        refine ⟨60170840796366955625829349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80227787728489274167772465 60170840796366955625829349)
        ·
          refine ⟨11282032649318804179843003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60170840796366955625829349 11282032649318804179843003)
          ·
            refine ⟨16923048973978206269764505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11282032649318804179843003 16923048973978206269764505)
            ·
              refine ⟨12692286730483654702323379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16923048973978206269764505 12692286730483654702323379)
              ·
                refine ⟨19038430095725482053485069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12692286730483654702323379 19038430095725482053485069)
                ·
                  refine ⟨7139411285897055770056901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19038430095725482053485069 7139411285897055770056901)
                  ·
                    refine ⟨1338639616105697956885669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7139411285897055770056901 1338639616105697956885669)
                    ·
                      rfl

theorem cell22_3910487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_3910487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3910487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3910487 prefixEnd_3910487 := by exact prefixLift 3910487
  have htrace : WordTrace (prefixWord ++ tailWord_3910487) baseStart_3910487 baseEnd_3910487 := by
    simpa [prefixWord, tailWord_3910487, baseEnd_3910487] using wordTrace_append hprefix tailTrace_3910487
  have hstable : (prefixWord ++ tailWord_3910487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910487).length < 2 ^ (prefixWord ++ tailWord_3910487).sum := by decide
  have hdescent : baseEnd_3910487 < baseStart_3910487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910504 : List Nat := [2, 1, 4, 2, 1, 3, 1, 3, 1, 4]
def baseStart_3910504 : Nat := 118140960795 + 3910504 * 2 ^ 59
def prefixEnd_3910504 : Nat := 4983230072969 + 3 ^ 40 * 3910504 * 2
def baseEnd_3910504 : Nat := 1338645435553115579210617

theorem tailTrace_3910504 : CollatzResearch.WordTrace tailWord_3910504 prefixEnd_3910504 1338645435553115579210617 := by
  unfold tailWord_3910504
  simp only [CollatzResearch.WordTrace]
  refine ⟨71313899112459671878593283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95085198816612895838124377 71313899112459671878593283)
  ·
    refine ⟨106970848668689507817889925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71313899112459671878593283 106970848668689507817889925)
    ·
      refine ⟨20057034125379282715854361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106970848668689507817889925 20057034125379282715854361)
      ·
        refine ⟨15042775594034462036890771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20057034125379282715854361 15042775594034462036890771)
        ·
          refine ⟨22564163391051693055336157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15042775594034462036890771 22564163391051693055336157)
          ·
            refine ⟨8461561271644384895751059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22564163391051693055336157 8461561271644384895751059)
            ·
              refine ⟨12692341907466577343626589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8461561271644384895751059 12692341907466577343626589)
              ·
                refine ⟨4759628215299966503859971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12692341907466577343626589 4759628215299966503859971)
                ·
                  refine ⟨7139442322949949755789957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4759628215299966503859971 7139442322949949755789957)
                  ·
                    refine ⟨1338645435553115579210617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7139442322949949755789957 1338645435553115579210617)
                    ·
                      rfl

theorem cell22_3910504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_3910504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3910504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3910504 prefixEnd_3910504 := by exact prefixLift 3910504
  have htrace : WordTrace (prefixWord ++ tailWord_3910504) baseStart_3910504 baseEnd_3910504 := by
    simpa [prefixWord, tailWord_3910504, baseEnd_3910504] using wordTrace_append hprefix tailTrace_3910504
  have hstable : (prefixWord ++ tailWord_3910504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910504).length < 2 ^ (prefixWord ++ tailWord_3910504).sum := by decide
  have hdescent : baseEnd_3910504 < baseStart_3910504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910545 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 1, 9]
def baseStart_3910545 : Nat := 118140960795 + 3910545 * 2 ^ 59
def prefixEnd_3910545 : Nat := 4983230072969 + 3 ^ 40 * 3910545 * 2
def baseEnd_3910545 : Nat := 1338659470691005138935491

theorem tailTrace_3910545 : CollatzResearch.WordTrace tailWord_3910545 prefixEnd_3910545 1338659470691005138935491 := by
  unfold tailWord_3910545
  simp only [CollatzResearch.WordTrace]
  refine ⟨142629293617770807759429089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95086195745180538506286059 142629293617770807759429089)
  ·
    refine ⟨106971970213328105819571817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142629293617770807759429089 106971970213328105819571817)
    ·
      refine ⟨80228977659996079364678863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106971970213328105819571817 80228977659996079364678863)
      ·
        refine ⟨120343466489994119047018295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80228977659996079364678863 120343466489994119047018295)
        ·
          refine ⟨180515199734991178570527443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120343466489994119047018295 180515199734991178570527443)
          ·
            refine ⟨270772799602486767855791165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180515199734991178570527443 270772799602486767855791165)
            ·
              refine ⟨101539799850932537945921687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270772799602486767855791165 101539799850932537945921687)
              ·
                refine ⟨152309699776398806918882531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101539799850932537945921687 152309699776398806918882531)
                ·
                  refine ⟨228464549664598210378323797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152309699776398806918882531 228464549664598210378323797)
                  ·
                    refine ⟨1338659470691005138935491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 228464549664598210378323797 1338659470691005138935491)
                    ·
                      rfl

theorem cell22_3910545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_3910545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3910545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3910545 prefixEnd_3910545 := by exact prefixLift 3910545
  have htrace : WordTrace (prefixWord ++ tailWord_3910545) baseStart_3910545 baseEnd_3910545 := by
    simpa [prefixWord, tailWord_3910545, baseEnd_3910545] using wordTrace_append hprefix tailTrace_3910545
  have hstable : (prefixWord ++ tailWord_3910545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910545).length < 2 ^ (prefixWord ++ tailWord_3910545).sum := by decide
  have hdescent : baseEnd_3910545 < baseStart_3910545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910626 : List Nat := [3, 3, 3, 1, 1, 1, 1, 4, 5]
def baseStart_3910626 : Nat := 118140960795 + 3910626 * 2 ^ 59
def prefixEnd_3910626 : Nat := 4983230072969 + 3 ^ 40 * 3910626 * 2
def baseEnd_3910626 : Nat := 446229066215449309220081

theorem tailTrace_3910626 : CollatzResearch.WordTrace tailWord_3910626 prefixEnd_3910626 446229066215449309220081 := by
  unfold tailWord_3910626
  simp only [CollatzResearch.WordTrace]
  refine ⟨35658061982619339648281933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95088165286984905728751821 35658061982619339648281933)
  ·
    refine ⟨13371773243482252368105725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35658061982619339648281933 13371773243482252368105725)
    ·
      refine ⟨5014414966305844638039647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13371773243482252368105725 5014414966305844638039647)
      ·
        refine ⟨7521622449458766957059471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5014414966305844638039647 7521622449458766957059471)
        ·
          refine ⟨11282433674188150435589207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7521622449458766957059471 11282433674188150435589207)
          ·
            refine ⟨16923650511282225653383811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11282433674188150435589207 16923650511282225653383811)
            ·
              refine ⟨25385475766923338480075717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16923650511282225653383811 25385475766923338480075717)
              ·
                refine ⟨4759776706298125965014197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25385475766923338480075717 4759776706298125965014197)
                ·
                  refine ⟨446229066215449309220081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4759776706298125965014197 446229066215449309220081)
                  ·
                    rfl

theorem cell22_3910626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_3910626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3910626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3910626 prefixEnd_3910626 := by exact prefixLift 3910626
  have htrace : WordTrace (prefixWord ++ tailWord_3910626) baseStart_3910626 baseEnd_3910626 := by
    simpa [prefixWord, tailWord_3910626, baseEnd_3910626] using wordTrace_append hprefix tailTrace_3910626
  have hstable : (prefixWord ++ tailWord_3910626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910626).length < 2 ^ (prefixWord ++ tailWord_3910626).sum := by decide
  have hdescent : baseEnd_3910626 < baseStart_3910626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910682 : List Nat := [3, 1, 1, 3, 1, 2, 11]
def baseStart_3910682 : Nat := 118140960795 + 3910682 * 2 ^ 59
def prefixEnd_3910682 : Nat := 4983230072969 + 3 ^ 40 * 3910682 * 2
def baseEnd_3910682 : Nat := 49581717355214164750373

theorem tailTrace_3910682 : CollatzResearch.WordTrace tailWord_3910682 prefixEnd_3910682 49581717355214164750373 := by
  unfold tailWord_3910682
  simp only [CollatzResearch.WordTrace]
  refine ⟨35658572604568620039291575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95089526945516320104777533 35658572604568620039291575)
  ·
    refine ⟨53487858906852930058937363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35658572604568620039291575 53487858906852930058937363)
    ·
      refine ⟨80231788360279395088406045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53487858906852930058937363 80231788360279395088406045)
      ·
        refine ⟨30086920635104773158152267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80231788360279395088406045 30086920635104773158152267)
        ·
          refine ⟨45130380952657159737228401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30086920635104773158152267 45130380952657159737228401)
          ·
            refine ⟨33847785714492869802921301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45130380952657159737228401 33847785714492869802921301)
            ·
              refine ⟨49581717355214164750373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 33847785714492869802921301 49581717355214164750373)
              ·
                rfl

theorem cell22_3910682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 11].length) (baseStart_3910682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3910682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3910682 prefixEnd_3910682 := by exact prefixLift 3910682
  have htrace : WordTrace (prefixWord ++ tailWord_3910682) baseStart_3910682 baseEnd_3910682 := by
    simpa [prefixWord, tailWord_3910682, baseEnd_3910682] using wordTrace_append hprefix tailTrace_3910682
  have hstable : (prefixWord ++ tailWord_3910682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910682).length < 2 ^ (prefixWord ++ tailWord_3910682).sum := by decide
  have hdescent : baseEnd_3910682 < baseStart_3910682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910716 : List Nat := [2, 2, 2, 2, 2, 4, 2, 6]
def baseStart_3910716 : Nat := 118140960795 + 3910716 * 2 ^ 59
def prefixEnd_3910716 : Nat := 4983230072969 + 3 ^ 40 * 3910716 * 2
def baseEnd_3910716 : Nat := 148746445276179743656663

theorem tailTrace_3910716 : CollatzResearch.WordTrace tailWord_3910716 prefixEnd_3910716 148746445276179743656663 := by
  unfold tailWord_3910716
  simp only [CollatzResearch.WordTrace]
  refine ⟨71317765250075651981952001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95090353666767535975936001 71317765250075651981952001)
  ·
    refine ⟨53488323937556738986464001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71317765250075651981952001 53488323937556738986464001)
    ·
      refine ⟨40116242953167554239848001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53488323937556738986464001 40116242953167554239848001)
      ·
        refine ⟨30087182214875665679886001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40116242953167554239848001 30087182214875665679886001)
        ·
          refine ⟨22565386661156749259914501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30087182214875665679886001 22565386661156749259914501)
          ·
            refine ⟨4231009998966890486233969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22565386661156749259914501 4231009998966890486233969)
            ·
              refine ⟨3173257499225167864675477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4231009998966890486233969 3173257499225167864675477)
              ·
                refine ⟨148746445276179743656663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3173257499225167864675477 148746445276179743656663)
                ·
                  rfl

theorem cell22_3910716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 6].length) (baseStart_3910716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3910716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3910716 prefixEnd_3910716 := by exact prefixLift 3910716
  have htrace : WordTrace (prefixWord ++ tailWord_3910716) baseStart_3910716 baseEnd_3910716 := by
    simpa [prefixWord, tailWord_3910716, baseEnd_3910716] using wordTrace_append hprefix tailTrace_3910716
  have hstable : (prefixWord ++ tailWord_3910716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910716).length < 2 ^ (prefixWord ++ tailWord_3910716).sum := by decide
  have hdescent : baseEnd_3910716 < baseStart_3910716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910744 : List Nat := [2, 1, 2, 2, 1, 3, 2, 4, 5]
def baseStart_3910744 : Nat := 118140960795 + 3910744 * 2 ^ 59
def prefixEnd_3910744 : Nat := 4983230072969 + 3 ^ 40 * 3910744 * 2
def baseEnd_3910744 : Nat := 446242530819278317736627

theorem tailTrace_3910744 : CollatzResearch.WordTrace tailWord_3910744 prefixEnd_3910744 446242530819278317736627 := by
  unfold tailWord_3910744
  simp only [CollatzResearch.WordTrace]
  refine ⟨71318275872024932372961643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95091034496033243163948857 71318275872024932372961643)
  ·
    refine ⟨106977413808037398559442465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71318275872024932372961643 106977413808037398559442465)
    ·
      refine ⟨80233060356028048919581849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106977413808037398559442465 80233060356028048919581849)
      ·
        refine ⟨60174795267021036689686387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80233060356028048919581849 60174795267021036689686387)
        ·
          refine ⟨90262192900531555034529581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60174795267021036689686387 90262192900531555034529581)
          ·
            refine ⟨33848322337699333137948593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90262192900531555034529581 33848322337699333137948593)
            ·
              refine ⟨25386241753274499853461445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33848322337699333137948593 25386241753274499853461445)
              ·
                refine ⟨4759920328738968722524021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25386241753274499853461445 4759920328738968722524021)
                ·
                  refine ⟨446242530819278317736627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4759920328738968722524021 446242530819278317736627)
                  ·
                    rfl

theorem cell22_3910744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 5].length) (baseStart_3910744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3910744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3910744 prefixEnd_3910744 := by exact prefixLift 3910744
  have htrace : WordTrace (prefixWord ++ tailWord_3910744) baseStart_3910744 baseEnd_3910744 := by
    simpa [prefixWord, tailWord_3910744, baseEnd_3910744] using wordTrace_append hprefix tailTrace_3910744
  have hstable : (prefixWord ++ tailWord_3910744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910744).length < 2 ^ (prefixWord ++ tailWord_3910744).sum := by decide
  have hdescent : baseEnd_3910744 < baseStart_3910744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910761 : List Nat := [1, 2, 1, 1, 1, 6, 4, 1, 5]
def baseStart_3910761 : Nat := 118140960795 + 3910761 * 2 ^ 59
def prefixEnd_3910761 : Nat := 4983230072969 + 3 ^ 40 * 3910761 * 2
def baseEnd_3910761 : Nat := 446244470635084191844943

theorem tailTrace_3910761 : CollatzResearch.WordTrace tailWord_3910761 prefixEnd_3910761 446244470635084191844943 := by
  unfold tailWord_3910761
  simp only [CollatzResearch.WordTrace]
  refine ⟨142637171784988276649292137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95091447856658851099528091 142637171784988276649292137)
  ·
    refine ⟨106977878838741207486969103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142637171784988276649292137 106977878838741207486969103)
    ·
      refine ⟨160466818258111811230453655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106977878838741207486969103 160466818258111811230453655)
      ·
        refine ⟨240700227387167716845680483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160466818258111811230453655 240700227387167716845680483)
        ·
          refine ⟨361050341080751575268520725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240700227387167716845680483 361050341080751575268520725)
          ·
            refine ⟨16924234738160230090711909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 361050341080751575268520725 16924234738160230090711909)
            ·
              refine ⟨3173294013405043142008483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16924234738160230090711909 3173294013405043142008483)
              ·
                refine ⟨4759941020107564713012725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3173294013405043142008483 4759941020107564713012725)
                ·
                  refine ⟨446244470635084191844943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4759941020107564713012725 446244470635084191844943)
                  ·
                    rfl

theorem cell22_3910761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 5].length) (baseStart_3910761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3910761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3910761 prefixEnd_3910761 := by exact prefixLift 3910761
  have htrace : WordTrace (prefixWord ++ tailWord_3910761) baseStart_3910761 baseEnd_3910761 := by
    simpa [prefixWord, tailWord_3910761, baseEnd_3910761] using wordTrace_append hprefix tailTrace_3910761
  have hstable : (prefixWord ++ tailWord_3910761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910761).length < 2 ^ (prefixWord ++ tailWord_3910761).sum := by decide
  have hdescent : baseEnd_3910761 < baseStart_3910761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910819 : List Nat := [1, 1, 1, 4, 1, 1, 1, 4, 4, 4]
def baseStart_3910819 : Nat := 118140960795 + 3910819 * 2 ^ 59
def prefixEnd_3910819 : Nat := 4983230072969 + 3 ^ 40 * 3910819 * 2
def baseEnd_3910819 : Nat := 1338753266490559757584651

theorem tailTrace_3910819 : CollatzResearch.WordTrace tailWord_3910819 prefixEnd_3910819 1338753266490559757584651 := by
  unfold tailWord_3910819
  simp only [CollatzResearch.WordTrace]
  refine ⟨142639287218778152554903511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95092858145852101703269007 142639287218778152554903511)
  ·
    refine ⟨213958930828167228832355267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142639287218778152554903511 213958930828167228832355267)
    ·
      refine ⟨320938396242250843248532901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213958930828167228832355267 320938396242250843248532901)
      ·
        refine ⟨60175949295422033109099919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 320938396242250843248532901 60175949295422033109099919)
        ·
          refine ⟨90263923943133049663649879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60175949295422033109099919 90263923943133049663649879)
          ·
            refine ⟨135395885914699574495474819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90263923943133049663649879 135395885914699574495474819)
            ·
              refine ⟨203093828872049361743212229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135395885914699574495474819 203093828872049361743212229)
              ·
                refine ⟨38080092913509255326852293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 203093828872049361743212229 38080092913509255326852293)
                ·
                  refine ⟨7140017421282985373784805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38080092913509255326852293 7140017421282985373784805)
                  ·
                    refine ⟨1338753266490559757584651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7140017421282985373784805 1338753266490559757584651)
                    ·
                      rfl

theorem cell22_3910819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 4].length) (baseStart_3910819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3910819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3910819 prefixEnd_3910819 := by exact prefixLift 3910819
  have htrace : WordTrace (prefixWord ++ tailWord_3910819) baseStart_3910819 baseEnd_3910819 := by
    simpa [prefixWord, tailWord_3910819, baseEnd_3910819] using wordTrace_append hprefix tailTrace_3910819
  have hstable : (prefixWord ++ tailWord_3910819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910819).length < 2 ^ (prefixWord ++ tailWord_3910819).sum := by decide
  have hdescent : baseEnd_3910819 < baseStart_3910819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910821 : List Nat := [1, 3, 1, 2, 1, 5, 2, 1, 1, 5]
def baseStart_3910821 : Nat := 118140960795 + 3910821 * 2 ^ 59
def prefixEnd_3910821 : Nat := 4983230072969 + 3 ^ 40 * 3910821 * 2
def baseEnd_3910821 : Nat := 1338753951131432419034645

theorem tailTrace_3910821 : CollatzResearch.WordTrace tailWord_3910821 prefixEnd_3910821 1338753951131432419034645 := by
  unfold tailWord_3910821
  simp only [CollatzResearch.WordTrace]
  refine ⟨142639360164770906896476317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95092906776513937930984211 142639360164770906896476317)
  ·
    refine ⟨53489760061789090086178619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142639360164770906896476317 53489760061789090086178619)
    ·
      refine ⟨80234640092683635129267929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53489760061789090086178619 80234640092683635129267929)
      ·
        refine ⟨60175980069512726346950947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80234640092683635129267929 60175980069512726346950947)
        ·
          refine ⟨90263970104269089520426421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60175980069512726346950947 90263970104269089520426421)
          ·
            refine ⟨8462247197275227142539977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90263970104269089520426421 8462247197275227142539977)
            ·
              refine ⟨6346685397956420356904983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8462247197275227142539977 6346685397956420356904983)
              ·
                refine ⟨9520028096934630535357475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6346685397956420356904983 9520028096934630535357475)
                ·
                  refine ⟨14280042145401945803036213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9520028096934630535357475 14280042145401945803036213)
                  ·
                    refine ⟨1338753951131432419034645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14280042145401945803036213 1338753951131432419034645)
                    ·
                      rfl

theorem cell22_3910821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 5].length) (baseStart_3910821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3910821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3910821 prefixEnd_3910821 := by exact prefixLift 3910821
  have htrace : WordTrace (prefixWord ++ tailWord_3910821) baseStart_3910821 baseEnd_3910821 := by
    simpa [prefixWord, tailWord_3910821, baseEnd_3910821] using wordTrace_append hprefix tailTrace_3910821
  have hstable : (prefixWord ++ tailWord_3910821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910821).length < 2 ^ (prefixWord ++ tailWord_3910821).sum := by decide
  have hdescent : baseEnd_3910821 < baseStart_3910821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910885 : List Nat := [1, 3, 1, 4, 4, 1, 2, 6]
def baseStart_3910885 : Nat := 118140960795 + 3910885 * 2 ^ 59
def prefixEnd_3910885 : Nat := 4983230072969 + 3 ^ 40 * 3910885 * 2
def baseEnd_3910885 : Nat := 148752873293261953937161

theorem tailTrace_3910885 : CollatzResearch.WordTrace tailWord_3910885 prefixEnd_3910885 148752873293261953937161 := by
  unfold tailWord_3910885
  simp only [CollatzResearch.WordTrace]
  refine ⟨142641694436539045826806109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95094462957692697217870739 142641694436539045826806109)
  ·
    refine ⟨53490635413702142185052291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142641694436539045826806109 53490635413702142185052291)
    ·
      refine ⟨80235953120553213277578437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53490635413702142185052291 80235953120553213277578437)
      ·
        refine ⟨15044241210103727489545957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80235953120553213277578437 15044241210103727489545957)
        ·
          refine ⟨2820795226894448904289867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15044241210103727489545957 2820795226894448904289867)
          ·
            refine ⟨4231192840341673356434801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2820795226894448904289867 4231192840341673356434801)
            ·
              refine ⟨3173394630256255017326101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4231192840341673356434801 3173394630256255017326101)
              ·
                refine ⟨148752873293261953937161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3173394630256255017326101 148752873293261953937161)
                ·
                  rfl

theorem cell22_3910885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 6].length) (baseStart_3910885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3910885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3910885 prefixEnd_3910885 := by exact prefixLift 3910885
  have htrace : WordTrace (prefixWord ++ tailWord_3910885) baseStart_3910885 baseEnd_3910885 := by
    simpa [prefixWord, tailWord_3910885, baseEnd_3910885] using wordTrace_append hprefix tailTrace_3910885
  have hstable : (prefixWord ++ tailWord_3910885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910885).length < 2 ^ (prefixWord ++ tailWord_3910885).sum := by decide
  have hdescent : baseEnd_3910885 < baseStart_3910885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910943 : List Nat := [1, 1, 2, 4, 4, 1, 1, 1, 3, 4]
def baseStart_3910943 : Nat := 118140960795 + 3910943 * 2 ^ 59
def prefixEnd_3910943 : Nat := 4983230072969 + 3 ^ 40 * 3910943 * 2
def baseEnd_3910943 : Nat := 1338795714224664767484271

theorem tailTrace_3910943 : CollatzResearch.WordTrace tailWord_3910943 prefixEnd_3910943 1338795714224664767484271 := by
  unfold tailWord_3910943
  simp only [CollatzResearch.WordTrace]
  refine ⟨142643809870328921732417483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95095873246885947821611655 142643809870328921732417483)
  ·
    refine ⟨213965714805493382598626225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142643809870328921732417483 213965714805493382598626225)
    ·
      refine ⟨160474286104120036948969669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213965714805493382598626225 160474286104120036948969669)
      ·
        refine ⟨30088928644522506927931813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160474286104120036948969669 30088928644522506927931813)
        ·
          refine ⟨5641674120847970048987215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30088928644522506927931813 5641674120847970048987215)
          ·
            refine ⟨8462511181271955073480823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5641674120847970048987215 8462511181271955073480823)
            ·
              refine ⟨12693766771907932610221235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8462511181271955073480823 12693766771907932610221235)
              ·
                refine ⟨19040650157861898915331853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12693766771907932610221235 19040650157861898915331853)
                ·
                  refine ⟨7140243809198212093249445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19040650157861898915331853 7140243809198212093249445)
                  ·
                    refine ⟨1338795714224664767484271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7140243809198212093249445 1338795714224664767484271)
                    ·
                      rfl

theorem cell22_3910943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 4].length) (baseStart_3910943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3910943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3910943 prefixEnd_3910943 := by exact prefixLift 3910943
  have htrace : WordTrace (prefixWord ++ tailWord_3910943) baseStart_3910943 baseEnd_3910943 := by
    simpa [prefixWord, tailWord_3910943, baseEnd_3910943] using wordTrace_append hprefix tailTrace_3910943
  have hstable : (prefixWord ++ tailWord_3910943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910943).length < 2 ^ (prefixWord ++ tailWord_3910943).sum := by decide
  have hdescent : baseEnd_3910943 < baseStart_3910943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910975 : List Nat := [1, 1, 2, 2, 4, 2, 4, 2, 4]
def baseStart_3910975 : Nat := 118140960795 + 3910975 * 2 ^ 59
def prefixEnd_3910975 : Nat := 4983230072969 + 3 ^ 40 * 3910975 * 2
def baseEnd_3910975 : Nat := 446268889492875783561391

theorem tailTrace_3910975 : CollatzResearch.WordTrace tailWord_3910975 prefixEnd_3910975 446268889492875783561391 := by
  unfold tailWord_3910975
  simp only [CollatzResearch.WordTrace]
  refine ⟨142644977006212991197582379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95096651337475327465054919 142644977006212991197582379)
  ·
    refine ⟨213967465509319486796373569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142644977006212991197582379 213967465509319486796373569)
    ·
      refine ⟨160475599131989615097280177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213967465509319486796373569 160475599131989615097280177)
      ·
        refine ⟨120356699348992211322960133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160475599131989615097280177 120356699348992211322960133)
        ·
          refine ⟨22566881127936039623055025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120356699348992211322960133 22566881127936039623055025)
          ·
            refine ⟨16925160845952029717291269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22566881127936039623055025 16925160845952029717291269)
            ·
              refine ⟨3173467658616005571992113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16925160845952029717291269 3173467658616005571992113)
              ·
                refine ⟨2380100743962004178994085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3173467658616005571992113 2380100743962004178994085)
                ·
                  refine ⟨446268889492875783561391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2380100743962004178994085 446268889492875783561391)
                  ·
                    rfl

theorem cell22_3910975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 2, 4].length) (baseStart_3910975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3910975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3910975 prefixEnd_3910975 := by exact prefixLift 3910975
  have htrace : WordTrace (prefixWord ++ tailWord_3910975) baseStart_3910975 baseEnd_3910975 := by
    simpa [prefixWord, tailWord_3910975, baseEnd_3910975] using wordTrace_append hprefix tailTrace_3910975
  have hstable : (prefixWord ++ tailWord_3910975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910975).length < 2 ^ (prefixWord ++ tailWord_3910975).sum := by decide
  have hdescent : baseEnd_3910975 < baseStart_3910975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911031 : List Nat := [1, 1, 3, 1, 1, 2, 5, 1, 7]
def baseStart_3911031 : Nat := 118140960795 + 3911031 * 2 ^ 59
def prefixEnd_3911031 : Nat := 4983230072969 + 3 ^ 40 * 3911031 * 2
def baseEnd_3911031 : Nat := 446275279474353957094667

theorem tailTrace_3911031 : CollatzResearch.WordTrace tailWord_3911031 prefixEnd_3911031 446275279474353957094667 := by
  unfold tailWord_3911031
  simp only [CollatzResearch.WordTrace]
  refine ⟨142647019494010112761620947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95098012996006741841080631 142647019494010112761620947)
  ·
    refine ⟨213970529241015169142431421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142647019494010112761620947 213970529241015169142431421)
    ·
      refine ⟨80238948465380688428411783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213970529241015169142431421 80238948465380688428411783)
      ·
        refine ⟨120358422698071032642617675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80238948465380688428411783 120358422698071032642617675)
        ·
          refine ⟨180537634047106548963926513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120358422698071032642617675 180537634047106548963926513)
          ·
            refine ⟨135403225535329911722944885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180537634047106548963926513 135403225535329911722944885)
            ·
              refine ⟨12694052393937179224026083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135403225535329911722944885 12694052393937179224026083)
              ·
                refine ⟨19041078590905768836039125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12694052393937179224026083 19041078590905768836039125)
                ·
                  refine ⟨446275279474353957094667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19041078590905768836039125 446275279474353957094667)
                  ·
                    rfl

theorem cell22_3911031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 7].length) (baseStart_3911031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3911031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3911031 prefixEnd_3911031 := by exact prefixLift 3911031
  have htrace : WordTrace (prefixWord ++ tailWord_3911031) baseStart_3911031 baseEnd_3911031 := by
    simpa [prefixWord, tailWord_3911031, baseEnd_3911031] using wordTrace_append hprefix tailTrace_3911031
  have hstable : (prefixWord ++ tailWord_3911031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911031).length < 2 ^ (prefixWord ++ tailWord_3911031).sum := by decide
  have hdescent : baseEnd_3911031 < baseStart_3911031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911035 : List Nat := [1, 1, 1, 1, 1, 6, 1, 6, 1, 3]
def baseStart_3911035 : Nat := 118140960795 + 3911035 * 2 ^ 59
def prefixEnd_3911035 : Nat := 4983230072969 + 3 ^ 40 * 3911035 * 2
def baseEnd_3911035 : Nat := 1338827207704807194183989

theorem tailTrace_3911035 : CollatzResearch.WordTrace tailWord_3911035 prefixEnd_3911035 1338827207704807194183989 := by
  unfold tailWord_3911035
  simp only [CollatzResearch.WordTrace]
  refine ⟨142647165385995621444766559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95098110257330414296511039 142647165385995621444766559)
  ·
    refine ⟨213970748078993432167149839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142647165385995621444766559 213970748078993432167149839)
    ·
      refine ⟨320956122118490148250724759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213970748078993432167149839 320956122118490148250724759)
      ·
        refine ⟨481434183177735222376087139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320956122118490148250724759 481434183177735222376087139)
        ·
          refine ⟨722151274766602833564130709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481434183177735222376087139 722151274766602833564130709)
          ·
            refine ⟨33850841004684507823318627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 722151274766602833564130709 33850841004684507823318627)
            ·
              refine ⟨50776261507026761734977941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33850841004684507823318627 50776261507026761734977941)
              ·
                refine ⟨2380137258141879456327091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50776261507026761734977941 2380137258141879456327091)
                ·
                  refine ⟨3570205887212819184490637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2380137258141879456327091 3570205887212819184490637)
                  ·
                    refine ⟨1338827207704807194183989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3570205887212819184490637 1338827207704807194183989)
                    ·
                      rfl

theorem cell22_3911035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 6, 1, 3].length) (baseStart_3911035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3911035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3911035 prefixEnd_3911035 := by exact prefixLift 3911035
  have htrace : WordTrace (prefixWord ++ tailWord_3911035) baseStart_3911035 baseEnd_3911035 := by
    simpa [prefixWord, tailWord_3911035, baseEnd_3911035] using wordTrace_append hprefix tailTrace_3911035
  have hstable : (prefixWord ++ tailWord_3911035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911035).length < 2 ^ (prefixWord ++ tailWord_3911035).sum := by decide
  have hdescent : baseEnd_3911035 < baseStart_3911035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911069 : List Nat := [1, 4, 2, 1, 3, 3, 1, 3, 1, 3]
def baseStart_3911069 : Nat := 118140960795 + 3911069 * 2 ^ 59
def prefixEnd_3911069 : Nat := 4983230072969 + 3 ^ 40 * 3911069 * 2
def baseEnd_3911069 : Nat := 1338838846599642438833885

theorem tailTrace_3911069 : CollatzResearch.WordTrace tailWord_3911069 prefixEnd_3911069 1338838846599642438833885 := by
  unfold tailWord_3911069
  simp only [CollatzResearch.WordTrace]
  refine ⟨142648405467872445251504261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95098936978581630167669507 142648405467872445251504261)
  ·
    refine ⟨26746576025226083484657049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142648405467872445251504261 26746576025226083484657049)
    ·
      refine ⟨20059932018919562613492787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26746576025226083484657049 20059932018919562613492787)
      ·
        refine ⟨30089898028379343920239181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20059932018919562613492787 30089898028379343920239181)
        ·
          refine ⟨11283711760642253970089693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30089898028379343920239181 11283711760642253970089693)
          ·
            refine ⟨4231391910240845238783635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11283711760642253970089693 4231391910240845238783635)
            ·
              refine ⟨6347087865361267858175453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4231391910240845238783635 6347087865361267858175453)
              ·
                refine ⟨2380157949510475446815795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6347087865361267858175453 2380157949510475446815795)
                ·
                  refine ⟨3570236924265713170223693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2380157949510475446815795 3570236924265713170223693)
                  ·
                    refine ⟨1338838846599642438833885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3570236924265713170223693 1338838846599642438833885)
                    ·
                      rfl

theorem cell22_3911069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_3911069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3911069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3911069 prefixEnd_3911069 := by exact prefixLift 3911069
  have htrace : WordTrace (prefixWord ++ tailWord_3911069) baseStart_3911069 baseEnd_3911069 := by
    simpa [prefixWord, tailWord_3911069, baseEnd_3911069] using wordTrace_append hprefix tailTrace_3911069
  have hstable : (prefixWord ++ tailWord_3911069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911069).length < 2 ^ (prefixWord ++ tailWord_3911069).sum := by decide
  have hdescent : baseEnd_3911069 < baseStart_3911069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911138 : List Nat := [3, 3, 3, 13]
def baseStart_3911138 : Nat := 118140960795 + 3911138 * 2 ^ 59
def prefixEnd_3911138 : Nat := 4983230072969 + 3 ^ 40 * 3911138 * 2
def baseEnd_3911138 : Nat := 1836574028408435197337

theorem tailTrace_3911138 : CollatzResearch.WordTrace tailWord_3911138 prefixEnd_3911138 1836574028408435197337 := by
  unfold tailWord_3911138
  simp only [CollatzResearch.WordTrace]
  refine ⟨35662730526155617508941517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95100614736414980023844045 35662730526155617508941517)
  ·
    refine ⟨13373523947308356565853069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35662730526155617508941517 13373523947308356565853069)
    ·
      refine ⟨5015071480240633712194901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13373523947308356565853069 5015071480240633712194901)
      ·
        refine ⟨1836574028408435197337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 5015071480240633712194901 1836574028408435197337)
        ·
          rfl

theorem cell22_3911138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 13].length) (baseStart_3911138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3911138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3911138 prefixEnd_3911138 := by exact prefixLift 3911138
  have htrace : WordTrace (prefixWord ++ tailWord_3911138) baseStart_3911138 baseEnd_3911138 := by
    simpa [prefixWord, tailWord_3911138, baseEnd_3911138] using wordTrace_append hprefix tailTrace_3911138
  have hstable : (prefixWord ++ tailWord_3911138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911138).length < 2 ^ (prefixWord ++ tailWord_3911138).sum := by decide
  have hdescent : baseEnd_3911138 < baseStart_3911138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911172 : List Nat := [2, 3, 2, 3, 2, 1, 3, 6]
def baseStart_3911172 : Nat := 118140960795 + 3911172 * 2 ^ 59
def prefixEnd_3911172 : Nat := 4983230072969 + 3 ^ 40 * 3911172 * 2
def baseEnd_3911172 : Nat := 148763789511620500389841

theorem tailTrace_3911172 : CollatzResearch.WordTrace tailWord_3911172 prefixEnd_3911172 148763789511620500389841 := by
  unfold tailWord_3911172
  simp only [CollatzResearch.WordTrace]
  refine ⟨71326081093249646921251885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95101441457666195895002513 71326081093249646921251885)
  ·
    refine ⟨26747280409968617595469457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71326081093249646921251885 26747280409968617595469457)
    ·
      refine ⟨20060460307476463196602093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26747280409968617595469457 20060460307476463196602093)
      ·
        refine ⟨7522672615303673698725785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20060460307476463196602093 7522672615303673698725785)
        ·
          refine ⟨5642004461477755274044339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7522672615303673698725785 5642004461477755274044339)
          ·
            refine ⟨8463006692216632911066509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5642004461477755274044339 8463006692216632911066509)
            ·
              refine ⟨3173627509581237341649941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8463006692216632911066509 3173627509581237341649941)
              ·
                refine ⟨148763789511620500389841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3173627509581237341649941 148763789511620500389841)
                ·
                  rfl

theorem cell22_3911172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 6].length) (baseStart_3911172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3911172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3911172 prefixEnd_3911172 := by exact prefixLift 3911172
  have htrace : WordTrace (prefixWord ++ tailWord_3911172) baseStart_3911172 baseEnd_3911172 := by
    simpa [prefixWord, tailWord_3911172, baseEnd_3911172] using wordTrace_append hprefix tailTrace_3911172
  have hstable : (prefixWord ++ tailWord_3911172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911172).length < 2 ^ (prefixWord ++ tailWord_3911172).sum := by decide
  have hdescent : baseEnd_3911172 < baseStart_3911172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911187 : List Nat := [1, 1, 1, 2, 1, 6, 1, 5, 1, 3]
def baseStart_3911187 : Nat := 118140960795 + 3911187 * 2 ^ 59
def prefixEnd_3911187 : Nat := 4983230072969 + 3 ^ 40 * 3911187 * 2
def baseEnd_3911187 : Nat := 1338879240411129464383523

theorem tailTrace_3911187 : CollatzResearch.WordTrace tailWord_3911187 prefixEnd_3911187 1338879240411129464383523 := by
  unfold tailWord_3911187
  simp only [CollatzResearch.WordTrace]
  refine ⟨142652709281444951404299815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95101806187629967602866543 142652709281444951404299815)
  ·
    refine ⟨213979063922167427106449723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142652709281444951404299815 213979063922167427106449723)
    ·
      refine ⟨320968595883251140659674585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213979063922167427106449723 320968595883251140659674585)
      ·
        refine ⟨240726446912438355494755939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320968595883251140659674585 240726446912438355494755939)
        ·
          refine ⟨361089670368657533242133909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240726446912438355494755939 361089670368657533242133909)
          ·
            refine ⟨16926078298530821870725027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 361089670368657533242133909 16926078298530821870725027)
            ·
              refine ⟨25389117447796232806087541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16926078298530821870725027 25389117447796232806087541)
              ·
                refine ⟨2380229760730896825570707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25389117447796232806087541 2380229760730896825570707)
                ·
                  refine ⟨3570344641096345238356061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2380229760730896825570707 3570344641096345238356061)
                  ·
                    refine ⟨1338879240411129464383523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3570344641096345238356061 1338879240411129464383523)
                    ·
                      rfl

theorem cell22_3911187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 5, 1, 3].length) (baseStart_3911187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3911187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3911187 prefixEnd_3911187 := by exact prefixLift 3911187
  have htrace : WordTrace (prefixWord ++ tailWord_3911187) baseStart_3911187 baseEnd_3911187 := by
    simpa [prefixWord, tailWord_3911187, baseEnd_3911187] using wordTrace_append hprefix tailTrace_3911187
  have hstable : (prefixWord ++ tailWord_3911187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911187).length < 2 ^ (prefixWord ++ tailWord_3911187).sum := by decide
  have hdescent : baseEnd_3911187 < baseStart_3911187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911200 : List Nat := [2, 1, 1, 6, 1, 2, 1, 1, 7]
def baseStart_3911200 : Nat := 118140960795 + 3911200 * 2 ^ 59
def prefixEnd_3911200 : Nat := 4983230072969 + 3 ^ 40 * 3911200 * 2
def baseEnd_3911200 : Nat := 446294563525600587936161

theorem tailTrace_3911200 : CollatzResearch.WordTrace tailWord_3911200 prefixEnd_3911200 446294563525600587936161 := by
  unfold tailWord_3911200
  simp only [CollatzResearch.WordTrace]
  refine ⟨71326591715198927312261527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95102122286931903083015369 71326591715198927312261527)
  ·
    refine ⟨106989887572798390968392291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71326591715198927312261527 106989887572798390968392291)
    ·
      refine ⟨160484831359197586452588437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106989887572798390968392291 160484831359197586452588437)
      ·
        refine ⟨7522726469962386864965083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 160484831359197586452588437 7522726469962386864965083)
        ·
          refine ⟨11284089704943580297447625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7522726469962386864965083 11284089704943580297447625)
          ·
            refine ⟨8463067278707685223085719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11284089704943580297447625 8463067278707685223085719)
            ·
              refine ⟨12694600918061527834628579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8463067278707685223085719 12694600918061527834628579)
              ·
                refine ⟨19041901377092291751942869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12694600918061527834628579 19041901377092291751942869)
                ·
                  refine ⟨446294563525600587936161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19041901377092291751942869 446294563525600587936161)
                  ·
                    rfl

theorem cell22_3911200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 7].length) (baseStart_3911200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3911200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3911200 prefixEnd_3911200 := by exact prefixLift 3911200
  have htrace : WordTrace (prefixWord ++ tailWord_3911200) baseStart_3911200 baseEnd_3911200 := by
    simpa [prefixWord, tailWord_3911200, baseEnd_3911200] using wordTrace_append hprefix tailTrace_3911200
  have hstable : (prefixWord ++ tailWord_3911200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911200).length < 2 ^ (prefixWord ++ tailWord_3911200).sum := by decide
  have hdescent : baseEnd_3911200 < baseStart_3911200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911243 : List Nat := [1, 1, 1, 1, 3, 1, 3, 3, 3, 5]
def baseStart_3911243 : Nat := 118140960795 + 3911243 * 2 ^ 59
def prefixEnd_3911243 : Nat := 4983230072969 + 3 ^ 40 * 3911243 * 2
def baseEnd_3911243 : Nat := 1338898410355563984983351

theorem tailTrace_3911243 : CollatzResearch.WordTrace tailWord_3911243 prefixEnd_3911243 1338898410355563984983351 := by
  unfold tailWord_3911243
  simp only [CollatzResearch.WordTrace]
  refine ⟨142654751769242072968338383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95103167846161381978892255 142654751769242072968338383)
  ·
    refine ⟨213982127653863109452507575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142654751769242072968338383 213982127653863109452507575)
    ·
      refine ⟨320973191480794664178761363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213982127653863109452507575 320973191480794664178761363)
      ·
        refine ⟨481459787221191996268142045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320973191480794664178761363 481459787221191996268142045)
        ·
          refine ⟨180547420207946998600553267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 481459787221191996268142045 180547420207946998600553267)
          ·
            refine ⟨270821130311920497900829901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180547420207946998600553267 270821130311920497900829901)
            ·
              refine ⟨101557923866970186712811213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270821130311920497900829901 101557923866970186712811213)
              ·
                refine ⟨38084221450113820017304205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101557923866970186712811213 38084221450113820017304205)
                ·
                  refine ⟨14281583043792682506489077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38084221450113820017304205 14281583043792682506489077)
                  ·
                    refine ⟨1338898410355563984983351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14281583043792682506489077 1338898410355563984983351)
                    ·
                      rfl

theorem cell22_3911243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 5].length) (baseStart_3911243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3911243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3911243 prefixEnd_3911243 := by exact prefixLift 3911243
  have htrace : WordTrace (prefixWord ++ tailWord_3911243) baseStart_3911243 baseEnd_3911243 := by
    simpa [prefixWord, tailWord_3911243, baseEnd_3911243] using wordTrace_append hprefix tailTrace_3911243
  have hstable : (prefixWord ++ tailWord_3911243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911243).length < 2 ^ (prefixWord ++ tailWord_3911243).sum := by decide
  have hdescent : baseEnd_3911243 < baseStart_3911243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911273 : List Nat := [1, 2, 1, 1, 1, 4, 3, 9]
def baseStart_3911273 : Nat := 118140960795 + 3911273 * 2 ^ 59
def prefixEnd_3911273 : Nat := 4983230072969 + 3 ^ 40 * 3911273 * 2
def baseEnd_3911273 : Nat := 148767631107628211859251

theorem tailTrace_3911273 : CollatzResearch.WordTrace tailWord_3911273 prefixEnd_3911273 148767631107628211859251 := by
  unfold tailWord_3911273
  simp only [CollatzResearch.WordTrace]
  refine ⟨142655845959133388091930473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95103897306088925394620315 142655845959133388091930473)
  ·
    refine ⟨106991884469350041068947855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142655845959133388091930473 106991884469350041068947855)
    ·
      refine ⟨160487826704025061603421783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106991884469350041068947855 160487826704025061603421783)
      ·
        refine ⟨240731740056037592405132675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160487826704025061603421783 240731740056037592405132675)
        ·
          refine ⟨361097610084056388607699013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240731740056037592405132675 361097610084056388607699013)
          ·
            refine ⟨67705801890760572863943565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 361097610084056388607699013 67705801890760572863943565)
            ·
              refine ⟨25389675709035214823978837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67705801890760572863943565 25389675709035214823978837)
              ·
                refine ⟨148767631107628211859251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25389675709035214823978837 148767631107628211859251)
                ·
                  rfl

theorem cell22_3911273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 9].length) (baseStart_3911273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3911273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3911273 prefixEnd_3911273 := by exact prefixLift 3911273
  have htrace : WordTrace (prefixWord ++ tailWord_3911273) baseStart_3911273 baseEnd_3911273 := by
    simpa [prefixWord, tailWord_3911273, baseEnd_3911273] using wordTrace_append hprefix tailTrace_3911273
  have hstable : (prefixWord ++ tailWord_3911273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911273).length < 2 ^ (prefixWord ++ tailWord_3911273).sum := by decide
  have hdescent : baseEnd_3911273 < baseStart_3911273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911320 : List Nat := [2, 1, 2, 4, 1, 2, 1, 1, 2, 6]
def baseStart_3911320 : Nat := 118140960795 + 3911320 * 2 ^ 59
def prefixEnd_3911320 : Nat := 4983230072969 + 3 ^ 40 * 3911320 * 2
def baseEnd_3911320 : Nat := 1338924769029161450808115

theorem tailTrace_3911320 : CollatzResearch.WordTrace tailWord_3911320 prefixEnd_3911320 1338924769029161450808115 := by
  unfold tailWord_3911320
  simp only [CollatzResearch.WordTrace]
  refine ⟨71328780094981557559445707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95105040126642076745927609 71328780094981557559445707)
  ·
    refine ⟨106993170142472336339168561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71328780094981557559445707 106993170142472336339168561)
    ·
      refine ⟨80244877606854252254376421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106993170142472336339168561 80244877606854252254376421)
      ·
        refine ⟨15045914551285172297695579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80244877606854252254376421 15045914551285172297695579)
        ·
          refine ⟨22568871826927758446543369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15045914551285172297695579 22568871826927758446543369)
          ·
            refine ⟨16926653870195818834907527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22568871826927758446543369 16926653870195818834907527)
            ·
              refine ⟨25389980805293728252361291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16926653870195818834907527 25389980805293728252361291)
              ·
                refine ⟨38084971207940592378541937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25389980805293728252361291 38084971207940592378541937)
                ·
                  refine ⟨28563728405955444283906453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38084971207940592378541937 28563728405955444283906453)
                  ·
                    refine ⟨1338924769029161450808115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28563728405955444283906453 1338924769029161450808115)
                    ·
                      rfl

theorem cell22_3911320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_3911320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3911320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3911320 prefixEnd_3911320 := by exact prefixLift 3911320
  have htrace : WordTrace (prefixWord ++ tailWord_3911320) baseStart_3911320 baseEnd_3911320 := by
    simpa [prefixWord, tailWord_3911320, baseEnd_3911320] using wordTrace_append hprefix tailTrace_3911320
  have hstable : (prefixWord ++ tailWord_3911320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911320).length < 2 ^ (prefixWord ++ tailWord_3911320).sum := by decide
  have hdescent : baseEnd_3911320 < baseStart_3911320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911324 : List Nat := [2, 2, 3, 2, 4, 1, 1, 7]
def baseStart_3911324 : Nat := 118140960795 + 3911324 * 2 ^ 59
def prefixEnd_3911324 : Nat := 4983230072969 + 3 ^ 40 * 3911324 * 2
def baseEnd_3911324 : Nat := 148769570923434085967567

theorem tailTrace_3911324 : CollatzResearch.WordTrace tailWord_3911324 prefixEnd_3911324 148769570923434085967567 := by
  unfold tailWord_3911324
  simp only [CollatzResearch.WordTrace]
  refine ⟨71328853040974311901018513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95105137387965749201358017 71328853040974311901018513)
  ·
    refine ⟨53496639780730733925763885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71328853040974311901018513 53496639780730733925763885)
    ·
      refine ⟨20061239917774025222161457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53496639780730733925763885 20061239917774025222161457)
      ·
        refine ⟨15045929938330518916621093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20061239917774025222161457 15045929938330518916621093)
        ·
          refine ⟨2821111863436972296866455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15045929938330518916621093 2821111863436972296866455)
          ·
            refine ⟨4231667795155458445299683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2821111863436972296866455 4231667795155458445299683)
            ·
              refine ⟨6347501692733187667949525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4231667795155458445299683 6347501692733187667949525)
              ·
                refine ⟨148769570923434085967567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6347501692733187667949525 148769570923434085967567)
                ·
                  rfl

theorem cell22_3911324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 7].length) (baseStart_3911324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3911324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3911324 prefixEnd_3911324 := by exact prefixLift 3911324
  have htrace : WordTrace (prefixWord ++ tailWord_3911324) baseStart_3911324 baseEnd_3911324 := by
    simpa [prefixWord, tailWord_3911324, baseEnd_3911324] using wordTrace_append hprefix tailTrace_3911324
  have hstable : (prefixWord ++ tailWord_3911324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911324).length < 2 ^ (prefixWord ++ tailWord_3911324).sum := by decide
  have hdescent : baseEnd_3911324 < baseStart_3911324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911356 : List Nat := [2, 2, 2, 3, 1, 3, 2, 3, 1, 3]
def baseStart_3911356 : Nat := 118140960795 + 3911356 * 2 ^ 59
def prefixEnd_3911356 : Nat := 4983230072969 + 3 ^ 40 * 3911356 * 2
def baseEnd_3911356 : Nat := 1338937092564869356908005

theorem tailTrace_3911356 : CollatzResearch.WordTrace tailWord_3911356 prefixEnd_3911356 1338937092564869356908005 := by
  unfold tailWord_3911356
  simp only [CollatzResearch.WordTrace]
  refine ⟨71329436608916346633600961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95105915478555128844801281 71329436608916346633600961)
  ·
    refine ⟨53497077456687259975200721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71329436608916346633600961 53497077456687259975200721)
    ·
      refine ⟨40122808092515444981400541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53497077456687259975200721 40122808092515444981400541)
      ·
        refine ⟨15046053034693291868025203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40122808092515444981400541 15046053034693291868025203)
        ·
          refine ⟨22569079552039937802037805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15046053034693291868025203 22569079552039937802037805)
          ·
            refine ⟨8463404832014976675764177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22569079552039937802037805 8463404832014976675764177)
            ·
              refine ⟨6347553624011232506823133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8463404832014976675764177 6347553624011232506823133)
              ·
                refine ⟨2380332609004212190058675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6347553624011232506823133 2380332609004212190058675)
                ·
                  refine ⟨3570498913506318285088013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2380332609004212190058675 3570498913506318285088013)
                  ·
                    refine ⟨1338937092564869356908005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3570498913506318285088013 1338937092564869356908005)
                    ·
                      rfl

theorem cell22_3911356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 3, 1, 3].length) (baseStart_3911356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3911356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3911356 prefixEnd_3911356 := by exact prefixLift 3911356
  have htrace : WordTrace (prefixWord ++ tailWord_3911356) baseStart_3911356 baseEnd_3911356 := by
    simpa [prefixWord, tailWord_3911356, baseEnd_3911356] using wordTrace_append hprefix tailTrace_3911356
  have hstable : (prefixWord ++ tailWord_3911356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911356).length < 2 ^ (prefixWord ++ tailWord_3911356).sum := by decide
  have hdescent : baseEnd_3911356 < baseStart_3911356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911362 : List Nat := [3, 5, 1, 2, 2, 1, 1, 2, 2, 3]
def baseStart_3911362 : Nat := 118140960795 + 3911362 * 2 ^ 59
def prefixEnd_3911362 : Nat := 4983230072969 + 3 ^ 40 * 3911362 * 2
def baseEnd_3911362 : Nat := 1338939146487487341257987

theorem tailTrace_3911362 : CollatzResearch.WordTrace tailWord_3911362 prefixEnd_3911362 1338939146487487341257987 := by
  unfold tailWord_3911362
  simp only [CollatzResearch.WordTrace]
  refine ⟨35664773013952739072980085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95106061370540637527946893 35664773013952739072980085)
  ·
    refine ⟨3343572470058069288091883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35664773013952739072980085 3343572470058069288091883)
    ·
      refine ⟨5015358705087103932137825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3343572470058069288091883 5015358705087103932137825)
      ·
        refine ⟨3761519028815327949103369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5015358705087103932137825 3761519028815327949103369)
        ·
          refine ⟨2821139271611495961827527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3761519028815327949103369 2821139271611495961827527)
          ·
            refine ⟨4231708907417243942741291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2821139271611495961827527 4231708907417243942741291)
            ·
              refine ⟨6347563361125865914111937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4231708907417243942741291 6347563361125865914111937)
              ·
                refine ⟨4760672520844399435583953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6347563361125865914111937 4760672520844399435583953)
                ·
                  refine ⟨3570504390633299576687965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4760672520844399435583953 3570504390633299576687965)
                  ·
                    refine ⟨1338939146487487341257987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3570504390633299576687965 1338939146487487341257987)
                    ·
                      rfl

theorem cell22_3911362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_3911362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3911362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3911362 prefixEnd_3911362 := by exact prefixLift 3911362
  have htrace : WordTrace (prefixWord ++ tailWord_3911362) baseStart_3911362 baseEnd_3911362 := by
    simpa [prefixWord, tailWord_3911362, baseEnd_3911362] using wordTrace_append hprefix tailTrace_3911362
  have hstable : (prefixWord ++ tailWord_3911362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911362).length < 2 ^ (prefixWord ++ tailWord_3911362).sum := by decide
  have hdescent : baseEnd_3911362 < baseStart_3911362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911373 : List Nat := [1, 6, 2, 1, 1, 1, 2, 4, 1, 3]
def baseStart_3911373 : Nat := 118140960795 + 3911373 * 2 ^ 59
def prefixEnd_3911373 : Nat := 4983230072969 + 3 ^ 40 * 3911373 * 2
def baseEnd_3911373 : Nat := 1338942912012286979232953

theorem tailTrace_3911373 : CollatzResearch.WordTrace tailWord_3911373 prefixEnd_3911373 1338942912012286979232953 := by
  unfold tailWord_3911373
  simp only [CollatzResearch.WordTrace]
  refine ⟨142659493258771105170570773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95106328839180736780380515 142659493258771105170570773)
  ·
    refine ⟨6687163746504895554870505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 142659493258771105170570773 6687163746504895554870505)
    ·
      refine ⟨5015372809878671666152879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6687163746504895554870505 5015372809878671666152879)
      ·
        refine ⟨7523059214818007499229319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5015372809878671666152879 7523059214818007499229319)
        ·
          refine ⟨11284588822227011248843979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7523059214818007499229319 11284588822227011248843979)
          ·
            refine ⟨16926883233340516873265969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11284588822227011248843979 16926883233340516873265969)
            ·
              refine ⟨12695162425005387654949477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16926883233340516873265969 12695162425005387654949477)
              ·
                refine ⟨2380342954688510185303027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12695162425005387654949477 2380342954688510185303027)
                ·
                  refine ⟨3570514432032765277954541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2380342954688510185303027 3570514432032765277954541)
                  ·
                    refine ⟨1338942912012286979232953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3570514432032765277954541 1338942912012286979232953)
                    ·
                      rfl

theorem cell22_3911373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_3911373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3911373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3911373 prefixEnd_3911373 := by exact prefixLift 3911373
  have htrace : WordTrace (prefixWord ++ tailWord_3911373) baseStart_3911373 baseEnd_3911373 := by
    simpa [prefixWord, tailWord_3911373, baseEnd_3911373] using wordTrace_append hprefix tailTrace_3911373
  have hstable : (prefixWord ++ tailWord_3911373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911373).length < 2 ^ (prefixWord ++ tailWord_3911373).sum := by decide
  have hdescent : baseEnd_3911373 < baseStart_3911373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911425 : List Nat := [1, 2, 4, 1, 1, 1, 12]
def baseStart_3911425 : Nat := 118140960795 + 3911425 * 2 ^ 59
def prefixEnd_3911425 : Nat := 4983230072969 + 3 ^ 40 * 3911425 * 2
def baseEnd_3911425 : Nat := 49591137506480599145659

theorem tailTrace_3911425 : CollatzResearch.WordTrace tailWord_3911425 prefixEnd_3911425 49591137506480599145659 := by
  unfold tailWord_3911425
  simp only [CollatzResearch.WordTrace]
  refine ⟨142661389854582718051463729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95107593236388478700975819 142661389854582718051463729)
  ·
    refine ⟨106996042390937038538597797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142661389854582718051463729 106996042390937038538597797)
    ·
      refine ⟨20061757948300694725987087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106996042390937038538597797 20061757948300694725987087)
      ·
        refine ⟨30092636922451042088980631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20061757948300694725987087 30092636922451042088980631)
        ·
          refine ⟨45138955383676563133470947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30092636922451042088980631 45138955383676563133470947)
          ·
            refine ⟨67708433075514844700206421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45138955383676563133470947 67708433075514844700206421)
            ·
              refine ⟨49591137506480599145659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 67708433075514844700206421 49591137506480599145659)
              ·
                rfl

theorem cell22_3911425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 12].length) (baseStart_3911425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3911425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3911425 prefixEnd_3911425 := by exact prefixLift 3911425
  have htrace : WordTrace (prefixWord ++ tailWord_3911425) baseStart_3911425 baseEnd_3911425 := by
    simpa [prefixWord, tailWord_3911425, baseEnd_3911425] using wordTrace_append hprefix tailTrace_3911425
  have hstable : (prefixWord ++ tailWord_3911425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911425).length < 2 ^ (prefixWord ++ tailWord_3911425).sum := by decide
  have hdescent : baseEnd_3911425 < baseStart_3911425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911431 : List Nat := [1, 1, 4, 4, 3, 1, 1, 1, 6]
def baseStart_3911431 : Nat := 118140960795 + 3911431 * 2 ^ 59
def prefixEnd_3911431 : Nat := 4983230072969 + 3 ^ 40 * 3911431 * 2
def baseEnd_3911431 : Nat := 446320922199198053760925

theorem tailTrace_3911431 : CollatzResearch.WordTrace tailWord_3911431 prefixEnd_3911431 446320922199198053760925 := by
  unfold tailWord_3911431
  simp only [CollatzResearch.WordTrace]
  refine ⟨142661608692560981076182147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95107739128373987384121431 142661608692560981076182147)
  ·
    refine ⟨213992413038841471614273221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142661608692560981076182147 213992413038841471614273221)
    ·
      refine ⟨40123577444782775927676229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213992413038841471614273221 40123577444782775927676229)
      ·
        refine ⟨7523170770896770486439293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40123577444782775927676229 7523170770896770486439293)
        ·
          refine ⟨2821189039086288932414735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7523170770896770486439293 2821189039086288932414735)
          ·
            refine ⟨4231783558629433398622103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2821189039086288932414735 4231783558629433398622103)
            ·
              refine ⟨6347675337944150097933155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4231783558629433398622103 6347675337944150097933155)
              ·
                refine ⟨9521513006916225146899733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6347675337944150097933155 9521513006916225146899733)
                ·
                  refine ⟨446320922199198053760925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9521513006916225146899733 446320922199198053760925)
                  ·
                    rfl

theorem cell22_3911431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 6].length) (baseStart_3911431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3911431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3911431 prefixEnd_3911431 := by exact prefixLift 3911431
  have htrace : WordTrace (prefixWord ++ tailWord_3911431) baseStart_3911431 baseEnd_3911431 := by
    simpa [prefixWord, tailWord_3911431, baseEnd_3911431] using wordTrace_append hprefix tailTrace_3911431
  have hstable : (prefixWord ++ tailWord_3911431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911431).length < 2 ^ (prefixWord ++ tailWord_3911431).sum := by decide
  have hdescent : baseEnd_3911431 < baseStart_3911431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911437 : List Nat := [1, 7, 2, 1, 1, 2, 2, 1, 5]
def baseStart_3911437 : Nat := 118140960795 + 3911437 * 2 ^ 59
def prefixEnd_3911437 : Nat := 4983230072969 + 3 ^ 40 * 3911437 * 2
def baseEnd_3911437 : Nat := 446321606840070715210919

theorem tailTrace_3911437 : CollatzResearch.WordTrace tailWord_3911437 prefixEnd_3911437 446321606840070715210919 := by
  unfold tailWord_3911437
  simp only [CollatzResearch.WordTrace]
  refine ⟨142661827530539244100900565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95107885020359496067267043 142661827530539244100900565)
  ·
    refine ⟨3343636582747013533614857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 142661827530539244100900565 3343636582747013533614857)
    ·
      refine ⟨2507727437060260150211143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3343636582747013533614857 2507727437060260150211143)
      ·
        refine ⟨3761591155590390225316715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2507727437060260150211143 3761591155590390225316715)
        ·
          refine ⟨5642386733385585337975073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3761591155590390225316715 5642386733385585337975073)
          ·
            refine ⟨4231790050039189003481305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5642386733385585337975073 4231790050039189003481305)
            ·
              refine ⟨3173842537529391752610979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4231790050039189003481305 3173842537529391752610979)
              ·
                refine ⟨4760763806294087628916469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3173842537529391752610979 4760763806294087628916469)
                ·
                  refine ⟨446321606840070715210919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4760763806294087628916469 446321606840070715210919)
                  ·
                    rfl

theorem cell22_3911437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_3911437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3911437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3911437 prefixEnd_3911437 := by exact prefixLift 3911437
  have htrace : WordTrace (prefixWord ++ tailWord_3911437) baseStart_3911437 baseEnd_3911437 := by
    simpa [prefixWord, tailWord_3911437, baseEnd_3911437] using wordTrace_append hprefix tailTrace_3911437
  have hstable : (prefixWord ++ tailWord_3911437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911437).length < 2 ^ (prefixWord ++ tailWord_3911437).sum := by decide
  have hdescent : baseEnd_3911437 < baseStart_3911437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911491 : List Nat := [1, 1, 1, 3, 1, 6, 1, 4, 1, 3]
def baseStart_3911491 : Nat := 118140960795 + 3911491 * 2 ^ 59
def prefixEnd_3911491 : Nat := 4983230072969 + 3 ^ 40 * 3911491 * 2
def baseEnd_3911491 : Nat := 1338983305823774004782591

theorem tailTrace_3911491 : CollatzResearch.WordTrace tailWord_3911491 prefixEnd_3911491 1338983305823774004782591 := by
  unfold tailWord_3911491
  simp only [CollatzResearch.WordTrace]
  refine ⟨142663797072343611323366327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95109198048229074215577551 142663797072343611323366327)
  ·
    refine ⟨213995695608515416985049491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142663797072343611323366327 213995695608515416985049491)
    ·
      refine ⟨320993543412773125477574237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213995695608515416985049491 320993543412773125477574237)
      ·
        refine ⟨120372578779789922054090339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320993543412773125477574237 120372578779789922054090339)
        ·
          refine ⟨180558868169684883081135509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120372578779789922054090339 180558868169684883081135509)
          ·
            refine ⟨8463696945453978894428227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 180558868169684883081135509 8463696945453978894428227)
            ·
              refine ⟨12695545418180968341642341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8463696945453978894428227 12695545418180968341642341)
              ·
                refine ⟨2380414765908931564057939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12695545418180968341642341 2380414765908931564057939)
                ·
                  refine ⟨3570622148863397346086909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2380414765908931564057939 3570622148863397346086909)
                  ·
                    refine ⟨1338983305823774004782591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3570622148863397346086909 1338983305823774004782591)
                    ·
                      rfl

theorem cell22_3911491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 4, 1, 3].length) (baseStart_3911491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3911491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3911491 prefixEnd_3911491 := by exact prefixLift 3911491
  have htrace : WordTrace (prefixWord ++ tailWord_3911491) baseStart_3911491 baseEnd_3911491 := by
    simpa [prefixWord, tailWord_3911491, baseEnd_3911491] using wordTrace_append hprefix tailTrace_3911491
  have hstable : (prefixWord ++ tailWord_3911491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911491).length < 2 ^ (prefixWord ++ tailWord_3911491).sum := by decide
  have hdescent : baseEnd_3911491 < baseStart_3911491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911583 : List Nat := [1, 1, 2, 5, 3, 2, 1, 3, 4]
def baseStart_3911583 : Nat := 118140960795 + 3911583 * 2 ^ 59
def prefixEnd_3911583 : Nat := 4983230072969 + 3 ^ 40 * 3911583 * 2
def baseEnd_3911583 : Nat := 446338266434638810494103

theorem tailTrace_3911583 : CollatzResearch.WordTrace tailWord_3911583 prefixEnd_3911583 446338266434638810494103 := by
  unfold tailWord_3911583
  simp only [CollatzResearch.WordTrace]
  refine ⟨142667152588010311035715403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95111435058673540690476935 142667152588010311035715403)
  ·
    refine ⟨214000728882015466553573105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142667152588010311035715403 214000728882015466553573105)
    ·
      refine ⟨160500546661511599915179829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214000728882015466553573105 160500546661511599915179829)
      ·
        refine ⟨15046926249516712492048109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160500546661511599915179829 15046926249516712492048109)
        ·
          refine ⟨5642597343568767184518041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15046926249516712492048109 5642597343568767184518041)
          ·
            refine ⟨4231948007676575388388531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5642597343568767184518041 4231948007676575388388531)
            ·
              refine ⟨6347922011514863082582797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4231948007676575388388531 6347922011514863082582797)
              ·
                refine ⟨2380470754318073655968549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6347922011514863082582797 2380470754318073655968549)
                ·
                  refine ⟨446338266434638810494103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2380470754318073655968549 446338266434638810494103)
                  ·
                    rfl

theorem cell22_3911583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 3, 4].length) (baseStart_3911583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3911583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3911583 prefixEnd_3911583 := by exact prefixLift 3911583
  have htrace : WordTrace (prefixWord ++ tailWord_3911583) baseStart_3911583 baseEnd_3911583 := by
    simpa [prefixWord, tailWord_3911583, baseEnd_3911583] using wordTrace_append hprefix tailTrace_3911583
  have hstable : (prefixWord ++ tailWord_3911583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911583).length < 2 ^ (prefixWord ++ tailWord_3911583).sum := by decide
  have hdescent : baseEnd_3911583 < baseStart_3911583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911607 : List Nat := [1, 1, 3, 1, 3, 1, 1, 3, 2, 6]
def baseStart_3911607 : Nat := 118140960795 + 3911607 * 2 ^ 59
def prefixEnd_3911607 : Nat := 4983230072969 + 3 ^ 40 * 3911607 * 2
def baseEnd_3911607 : Nat := 1339023014994388368882235

theorem tailTrace_3911607 : CollatzResearch.WordTrace tailWord_3911607 prefixEnd_3911607 1339023014994388368882235 := by
  unfold tailWord_3911607
  simp only [CollatzResearch.WordTrace]
  refine ⟨142668027939923363134589075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95112018626615575423059383 142668027939923363134589075)
  ·
    refine ⟨214002041909885044701883613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142668027939923363134589075 214002041909885044701883613)
    ·
      refine ⟨80250765716206891763206355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214002041909885044701883613 80250765716206891763206355)
      ·
        refine ⟨120376148574310337644809533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80250765716206891763206355 120376148574310337644809533)
        ·
          refine ⟨45141055715366376616803575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120376148574310337644809533 45141055715366376616803575)
          ·
            refine ⟨67711583573049564925205363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45141055715366376616803575 67711583573049564925205363)
            ·
              refine ⟨101567375359574347387808045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67711583573049564925205363 101567375359574347387808045)
              ·
                refine ⟨38087765759840380270428017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101567375359574347387808045 38087765759840380270428017)
                ·
                  refine ⟨28565824319880285202821013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38087765759840380270428017 28565824319880285202821013)
                  ·
                    refine ⟨1339023014994388368882235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28565824319880285202821013 1339023014994388368882235)
                    ·
                      rfl

theorem cell22_3911607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_3911607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3911607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3911607 prefixEnd_3911607 := by exact prefixLift 3911607
  have htrace : WordTrace (prefixWord ++ tailWord_3911607) baseStart_3911607 baseEnd_3911607 := by
    simpa [prefixWord, tailWord_3911607, baseEnd_3911607] using wordTrace_append hprefix tailTrace_3911607
  have hstable : (prefixWord ++ tailWord_3911607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911607).length < 2 ^ (prefixWord ++ tailWord_3911607).sum := by decide
  have hdescent : baseEnd_3911607 < baseStart_3911607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911667 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 10]
def baseStart_3911667 : Nat := 118140960795 + 3911667 * 2 ^ 59
def prefixEnd_3911667 : Nat := 4983230072969 + 3 ^ 40 * 3911667 * 2
def baseEnd_3911667 : Nat := 446347851406856070794017

theorem tailTrace_3911667 : CollatzResearch.WordTrace tailWord_3911667 prefixEnd_3911667 446347851406856070794017 := by
  unfold tailWord_3911667
  simp only [CollatzResearch.WordTrace]
  refine ⟨142670216319705993381773255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95113477546470662254515503 142670216319705993381773255)
  ·
    refine ⟨214005324479558990072659883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142670216319705993381773255 214005324479558990072659883)
    ·
      refine ⟨321007986719338485108989825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214005324479558990072659883 321007986719338485108989825)
      ·
        refine ⟨240755990039503863831742369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321007986719338485108989825 240755990039503863831742369)
        ·
          refine ⟨180566992529627897873806777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240755990039503863831742369 180566992529627897873806777)
          ·
            refine ⟨135425244397220923405355083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180566992529627897873806777 135425244397220923405355083)
            ·
              refine ⟨203137866595831385108032625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135425244397220923405355083 203137866595831385108032625)
              ·
                refine ⟨152353399946873538831024469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203137866595831385108032625 152353399946873538831024469)
                ·
                  refine ⟨446347851406856070794017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 152353399946873538831024469 446347851406856070794017)
                  ·
                    rfl

theorem cell22_3911667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 10].length) (baseStart_3911667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3911667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3911667 prefixEnd_3911667 := by exact prefixLift 3911667
  have htrace : WordTrace (prefixWord ++ tailWord_3911667) baseStart_3911667 baseEnd_3911667 := by
    simpa [prefixWord, tailWord_3911667, baseEnd_3911667] using wordTrace_append hprefix tailTrace_3911667
  have hstable : (prefixWord ++ tailWord_3911667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911667).length < 2 ^ (prefixWord ++ tailWord_3911667).sum := by decide
  have hdescent : baseEnd_3911667 < baseStart_3911667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911699 : List Nat := [1, 1, 1, 2, 1, 4, 4, 2, 1, 5]
def baseStart_3911699 : Nat := 118140960795 + 3911699 * 2 ^ 59
def prefixEnd_3911699 : Nat := 4983230072969 + 3 ^ 40 * 3911699 * 2
def baseEnd_3911699 : Nat := 1339054508474530795581953

theorem tailTrace_3911699 : CollatzResearch.WordTrace tailWord_3911699 prefixEnd_3911699 1339054508474530795581953 := by
  unfold tailWord_3911699
  simp only [CollatzResearch.WordTrace]
  refine ⟨142671383455590062846938151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95114255637060041897958767 142671383455590062846938151)
  ·
    refine ⟨214007075183385094270407227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142671383455590062846938151 214007075183385094270407227)
    ·
      refine ⟨321010612775077641405610841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214007075183385094270407227 321010612775077641405610841)
      ·
        refine ⟨240757959581308231054208131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321010612775077641405610841 240757959581308231054208131)
        ·
          refine ⟨361136939371962346581312197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240757959581308231054208131 361136939371962346581312197)
          ·
            refine ⟨67713176132242939983996037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 361136939371962346581312197 67713176132242939983996037)
            ·
              refine ⟨12696220524795551246999257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67713176132242939983996037 12696220524795551246999257)
              ·
                refine ⟨9522165393596663435249443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12696220524795551246999257 9522165393596663435249443)
                ·
                  refine ⟨14283248090394995152874165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9522165393596663435249443 14283248090394995152874165)
                  ·
                    refine ⟨1339054508474530795581953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14283248090394995152874165 1339054508474530795581953)
                    ·
                      rfl

theorem cell22_3911699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 5].length) (baseStart_3911699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3911699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3911699 prefixEnd_3911699 := by exact prefixLift 3911699
  have htrace : WordTrace (prefixWord ++ tailWord_3911699) baseStart_3911699 baseEnd_3911699 := by
    simpa [prefixWord, tailWord_3911699, baseEnd_3911699] using wordTrace_append hprefix tailTrace_3911699
  have hstable : (prefixWord ++ tailWord_3911699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911699).length < 2 ^ (prefixWord ++ tailWord_3911699).sum := by decide
  have hdescent : baseEnd_3911699 < baseStart_3911699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911703 : List Nat := [1, 1, 3, 5, 2, 1, 1, 3, 1, 4]
def baseStart_3911703 : Nat := 118140960795 + 3911703 * 2 ^ 59
def prefixEnd_3911703 : Nat := 4983230072969 + 3 ^ 40 * 3911703 * 2
def baseEnd_3911703 : Nat := 1339055877756276118481941

theorem tailTrace_3911703 : CollatzResearch.WordTrace tailWord_3911703 prefixEnd_3911703 1339055877756276118481941 := by
  unfold tailWord_3911703
  simp only [CollatzResearch.WordTrace]
  refine ⟨142671529347575571530083763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95114352898383714353389175 142671529347575571530083763)
  ·
    refine ⟨214007294021363357295125645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142671529347575571530083763 214007294021363357295125645)
    ·
      refine ⟨80252735258011258985672117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214007294021363357295125645 80252735258011258985672117)
      ·
        refine ⟨7523693930438555529906761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80252735258011258985672117 7523693930438555529906761)
        ·
          refine ⟨5642770447828916647430071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7523693930438555529906761 5642770447828916647430071)
          ·
            refine ⟨8464155671743374971145107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5642770447828916647430071 8464155671743374971145107)
            ·
              refine ⟨12696233507615062456717661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8464155671743374971145107 12696233507615062456717661)
              ·
                refine ⟨4761087565355648421269123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12696233507615062456717661 4761087565355648421269123)
                ·
                  refine ⟨7141631348033472631903685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4761087565355648421269123 7141631348033472631903685)
                  ·
                    refine ⟨1339055877756276118481941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7141631348033472631903685 1339055877756276118481941)
                    ·
                      rfl

theorem cell22_3911703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 1, 4].length) (baseStart_3911703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3911703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3911703 prefixEnd_3911703 := by exact prefixLift 3911703
  have htrace : WordTrace (prefixWord ++ tailWord_3911703) baseStart_3911703 baseEnd_3911703 := by
    simpa [prefixWord, tailWord_3911703, baseEnd_3911703] using wordTrace_append hprefix tailTrace_3911703
  have hstable : (prefixWord ++ tailWord_3911703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911703).length < 2 ^ (prefixWord ++ tailWord_3911703).sum := by decide
  have hdescent : baseEnd_3911703 < baseStart_3911703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911791 : List Nat := [1, 1, 2, 1, 3, 5, 1, 3, 5]
def baseStart_3911791 : Nat := 118140960795 + 3911791 * 2 ^ 59
def prefixEnd_3911791 : Nat := 4983230072969 + 3 ^ 40 * 3911791 * 2
def baseEnd_3911791 : Nat := 446362000651557740760557

theorem tailTrace_3911791 : CollatzResearch.WordTrace tailWord_3911791 prefixEnd_3911791 446362000651557740760557 := by
  unfold tailWord_3911791
  simp only [CollatzResearch.WordTrace]
  refine ⟨142674738971256762559287227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95116492647504508372858151 142674738971256762559287227)
  ·
    refine ⟨214012108456885143838930841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142674738971256762559287227 214012108456885143838930841)
    ·
      refine ⟨160509081342663857879198131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214012108456885143838930841 160509081342663857879198131)
      ·
        refine ⟨240763622013995786818797197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160509081342663857879198131 240763622013995786818797197)
        ·
          refine ⟨90286358255248420057048949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240763622013995786818797197 90286358255248420057048949)
          ·
            refine ⟨8464346086429539380348339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90286358255248420057048949 8464346086429539380348339)
            ·
              refine ⟨12696519129644309070522509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8464346086429539380348339 12696519129644309070522509)
              ·
                refine ⟨4761194673616615901445941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12696519129644309070522509 4761194673616615901445941)
                ·
                  refine ⟨446362000651557740760557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4761194673616615901445941 446362000651557740760557)
                  ·
                    rfl

theorem cell22_3911791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 5].length) (baseStart_3911791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3911791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3911791 prefixEnd_3911791 := by exact prefixLift 3911791
  have htrace : WordTrace (prefixWord ++ tailWord_3911791) baseStart_3911791 baseEnd_3911791 := by
    simpa [prefixWord, tailWord_3911791, baseEnd_3911791] using wordTrace_append hprefix tailTrace_3911791
  have hstable : (prefixWord ++ tailWord_3911791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911791).length < 2 ^ (prefixWord ++ tailWord_3911791).sum := by decide
  have hdescent : baseEnd_3911791 < baseStart_3911791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911836 : List Nat := [2, 2, 3, 2, 1, 1, 2, 3, 6]
def baseStart_3911836 : Nat := 118140960795 + 3911836 * 2 ^ 59
def prefixEnd_3911836 : Nat := 4983230072969 + 3 ^ 40 * 3911836 * 2
def baseEnd_3911836 : Nat := 446367135458102701635511

theorem tailTrace_3911836 : CollatzResearch.WordTrace tailWord_3911836 prefixEnd_3911836 446367135458102701635511 := by
  unfold tailWord_3911836
  simp only [CollatzResearch.WordTrace]
  refine ⟨71338190128046867622337681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95117586837395823496450241 71338190128046867622337681)
  ·
    refine ⟨53503642596035150716753261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71338190128046867622337681 53503642596035150716753261)
    ·
      refine ⟨20063865973513181518782473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53503642596035150716753261 20063865973513181518782473)
      ·
        refine ⟨15047899480134886139086855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20063865973513181518782473 15047899480134886139086855)
        ·
          refine ⟨22571849220202329208630283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15047899480134886139086855 22571849220202329208630283)
          ·
            refine ⟨33857773830303493812945425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22571849220202329208630283 33857773830303493812945425)
            ·
              refine ⟨25393330372727620359709069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33857773830303493812945425 25393330372727620359709069)
              ·
                refine ⟨9522498889772857634890901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25393330372727620359709069 9522498889772857634890901)
                ·
                  refine ⟨446367135458102701635511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9522498889772857634890901 446367135458102701635511)
                  ·
                    rfl

theorem cell22_3911836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 6].length) (baseStart_3911836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3911836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3911836 prefixEnd_3911836 := by exact prefixLift 3911836
  have htrace : WordTrace (prefixWord ++ tailWord_3911836) baseStart_3911836 baseEnd_3911836 := by
    simpa [prefixWord, tailWord_3911836, baseEnd_3911836] using wordTrace_append hprefix tailTrace_3911836
  have hstable : (prefixWord ++ tailWord_3911836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911836).length < 2 ^ (prefixWord ++ tailWord_3911836).sum := by decide
  have hdescent : baseEnd_3911836 < baseStart_3911836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911853 : List Nat := [1, 5, 2, 1, 2, 2, 1, 2, 6]
def baseStart_3911853 : Nat := 118140960795 + 3911853 * 2 ^ 59
def prefixEnd_3911853 : Nat := 4983230072969 + 3 ^ 40 * 3911853 * 2
def baseEnd_3911853 : Nat := 446369075273908575743827

theorem tailTrace_3911853 : CollatzResearch.WordTrace tailWord_3911853 prefixEnd_3911853 446369075273908575743827 := by
  unfold tailWord_3911853
  simp only [CollatzResearch.WordTrace]
  refine ⟨142677000297032147148044213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95118000198021431432029475 142677000297032147148044213)
  ·
    refine ⟨13375968777846763795129145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142677000297032147148044213 13375968777846763795129145)
    ·
      refine ⟨10031976583385072846346859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13375968777846763795129145 10031976583385072846346859)
      ·
        refine ⟨15047964875077609269520289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10031976583385072846346859 15047964875077609269520289)
        ·
          refine ⟨11285973656308206952140217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15047964875077609269520289 11285973656308206952140217)
          ·
            refine ⟨8464480242231155214105163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11285973656308206952140217 8464480242231155214105163)
            ·
              refine ⟨12696720363346732821157745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8464480242231155214105163 12696720363346732821157745)
              ·
                refine ⟨9522540272510049615868309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12696720363346732821157745 9522540272510049615868309)
                ·
                  refine ⟨446369075273908575743827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9522540272510049615868309 446369075273908575743827)
                  ·
                    rfl

theorem cell22_3911853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_3911853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3911853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3911853 prefixEnd_3911853 := by exact prefixLift 3911853
  have htrace : WordTrace (prefixWord ++ tailWord_3911853) baseStart_3911853 baseEnd_3911853 := by
    simpa [prefixWord, tailWord_3911853, baseEnd_3911853] using wordTrace_append hprefix tailTrace_3911853
  have hstable : (prefixWord ++ tailWord_3911853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911853).length < 2 ^ (prefixWord ++ tailWord_3911853).sum := by decide
  have hdescent : baseEnd_3911853 < baseStart_3911853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911941 : List Nat := [1, 3, 1, 1, 2, 1, 2, 4, 2, 5]
def baseStart_3911941 : Nat := 118140960795 + 3911941 * 2 ^ 59
def prefixEnd_3911941 : Nat := 4983230072969 + 3 ^ 40 * 3911941 * 2
def baseEnd_3911941 : Nat := 1339137350020122831031211

theorem tailTrace_3911941 : CollatzResearch.WordTrace tailWord_3911941 prefixEnd_3911941 1339137350020122831031211 := by
  unfold tailWord_3911941
  simp only [CollatzResearch.WordTrace]
  refine ⟨142680209920713338177247677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95120139947142225451498451 142680209920713338177247677)
  ·
    refine ⟨53505078720267501816467879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142680209920713338177247677 53505078720267501816467879)
    ·
      refine ⟨80257618080401252724701819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53505078720267501816467879 80257618080401252724701819)
      ·
        refine ⟨120386427120601879087052729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80257618080401252724701819 120386427120601879087052729)
        ·
          refine ⟨90289820340451409315289547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120386427120601879087052729 90289820340451409315289547)
          ·
            refine ⟨135434730510677113972934321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90289820340451409315289547 135434730510677113972934321)
            ·
              refine ⟨101576047883007835479700741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135434730510677113972934321 101576047883007835479700741)
              ·
                refine ⟨19045508978063969152443889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101576047883007835479700741 19045508978063969152443889)
                ·
                  refine ⟨14284131733547976864332917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19045508978063969152443889 14284131733547976864332917)
                  ·
                    refine ⟨1339137350020122831031211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14284131733547976864332917 1339137350020122831031211)
                    ·
                      rfl

theorem cell22_3911941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_3911941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3911941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3911941 prefixEnd_3911941 := by exact prefixLift 3911941
  have htrace : WordTrace (prefixWord ++ tailWord_3911941) baseStart_3911941 baseEnd_3911941 := by
    simpa [prefixWord, tailWord_3911941, baseEnd_3911941] using wordTrace_append hprefix tailTrace_3911941
  have hstable : (prefixWord ++ tailWord_3911941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911941).length < 2 ^ (prefixWord ++ tailWord_3911941).sum := by decide
  have hdescent : baseEnd_3911941 < baseStart_3911941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911947 : List Nat := [1, 1, 1, 1, 5, 2, 5, 2, 1, 3]
def baseStart_3911947 : Nat := 118140960795 + 3911947 * 2 ^ 59
def prefixEnd_3911947 : Nat := 4983230072969 + 3 ^ 40 * 3911947 * 2
def baseEnd_3911947 : Nat := 1339139403942740815381193

theorem tailTrace_3911947 : CollatzResearch.WordTrace tailWord_3911947 prefixEnd_3911947 1339139403942740815381193 := by
  unfold tailWord_3911947
  simp only [CollatzResearch.WordTrace]
  refine ⟨142680428758691601201966095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95120285839127734134644063 142680428758691601201966095)
  ·
    refine ⟨214020643138037401802949143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142680428758691601201966095 214020643138037401802949143)
    ·
      refine ⟨321030964707056102704423715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214020643138037401802949143 321030964707056102704423715)
      ·
        refine ⟨481546447060584154056635573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321030964707056102704423715 481546447060584154056635573)
        ·
          refine ⟨45144979411929764442809585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 481546447060584154056635573 45144979411929764442809585)
          ·
            refine ⟨33858734558947323332107189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45144979411929764442809585 33858734558947323332107189)
            ·
              refine ⟨3174256364901311562385049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33858734558947323332107189 3174256364901311562385049)
              ·
                refine ⟨2380692273675983671788787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3174256364901311562385049 2380692273675983671788787)
                ·
                  refine ⟨3571038410513975507683181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2380692273675983671788787 3571038410513975507683181)
                  ·
                    refine ⟨1339139403942740815381193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3571038410513975507683181 1339139403942740815381193)
                    ·
                      rfl

theorem cell22_3911947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 2, 1, 3].length) (baseStart_3911947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3911947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3911947 prefixEnd_3911947 := by exact prefixLift 3911947
  have htrace : WordTrace (prefixWord ++ tailWord_3911947) baseStart_3911947 baseEnd_3911947 := by
    simpa [prefixWord, tailWord_3911947, baseEnd_3911947] using wordTrace_append hprefix tailTrace_3911947
  have hstable : (prefixWord ++ tailWord_3911947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911947).length < 2 ^ (prefixWord ++ tailWord_3911947).sum := by decide
  have hdescent : baseEnd_3911947 < baseStart_3911947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911971 : List Nat := [1, 1, 1, 4, 2, 2, 2, 1, 8]
def baseStart_3911971 : Nat := 118140960795 + 3911971 * 2 ^ 59
def prefixEnd_3911971 : Nat := 4983230072969 + 3 ^ 40 * 3911971 * 2
def baseEnd_3911971 : Nat := 446382539877737584260373

theorem tailTrace_3911971 : CollatzResearch.WordTrace tailWord_3911971 prefixEnd_3911971 446382539877737584260373 := by
  unfold tailWord_3911971
  simp only [CollatzResearch.WordTrace]
  refine ⟨142681304110604653300839767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95120869407069768867226511 142681304110604653300839767)
  ·
    refine ⟨214021956165906979951259651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142681304110604653300839767 214021956165906979951259651)
    ·
      refine ⟨321032934248860469926889477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214021956165906979951259651 321032934248860469926889477)
      ·
        refine ⟨60193675171661338111291777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 321032934248860469926889477 60193675171661338111291777)
        ·
          refine ⟨45145256378746003583468833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60193675171661338111291777 45145256378746003583468833)
          ·
            refine ⟨33858942284059502687601625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45145256378746003583468833 33858942284059502687601625)
            ·
              refine ⟨25394206713044627015701219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33858942284059502687601625 25394206713044627015701219)
              ·
                refine ⟨38091310069566940523551829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25394206713044627015701219 38091310069566940523551829)
                ·
                  refine ⟨446382539877737584260373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38091310069566940523551829 446382539877737584260373)
                  ·
                    rfl

theorem cell22_3911971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 8].length) (baseStart_3911971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3911971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3911971 prefixEnd_3911971 := by exact prefixLift 3911971
  have htrace : WordTrace (prefixWord ++ tailWord_3911971) baseStart_3911971 baseEnd_3911971 := by
    simpa [prefixWord, tailWord_3911971, baseEnd_3911971] using wordTrace_append hprefix tailTrace_3911971
  have hstable : (prefixWord ++ tailWord_3911971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911971).length < 2 ^ (prefixWord ++ tailWord_3911971).sum := by decide
  have hdescent : baseEnd_3911971 < baseStart_3911971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912003 : List Nat := [1, 1, 1, 3, 1, 3, 2, 3, 4, 3]
def baseStart_3912003 : Nat := 118140960795 + 3912003 * 2 ^ 59
def prefixEnd_3912003 : Nat := 4983230072969 + 3 ^ 40 * 3912003 * 2
def baseEnd_3912003 : Nat := 1339158573887175335981021

theorem tailTrace_3912003 : CollatzResearch.WordTrace tailWord_3912003 prefixEnd_3912003 1339158573887175335981021 := by
  unfold tailWord_3912003
  simp only [CollatzResearch.WordTrace]
  refine ⟨142682471246488722766004663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95121647497659148510669775 142682471246488722766004663)
  ·
    refine ⟨214023706869733084149006995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142682471246488722766004663 214023706869733084149006995)
    ·
      refine ⟨321035560304599626223510493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214023706869733084149006995 321035560304599626223510493)
      ·
        refine ⟨120388335114224859833816435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321035560304599626223510493 120388335114224859833816435)
        ·
          refine ⟨180582502671337289750724653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120388335114224859833816435 180582502671337289750724653)
          ·
            refine ⟨67718438501751483656521745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180582502671337289750724653 67718438501751483656521745)
            ·
              refine ⟨50788828876313612742391309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67718438501751483656521745 50788828876313612742391309)
              ·
                refine ⟨19045810828617604778396741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50788828876313612742391309 19045810828617604778396741)
                ·
                  refine ⟨3571089530365800895949389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19045810828617604778396741 3571089530365800895949389)
                  ·
                    refine ⟨1339158573887175335981021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3571089530365800895949389 1339158573887175335981021)
                    ·
                      rfl

theorem cell22_3912003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 4, 3].length) (baseStart_3912003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3912003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3912003 prefixEnd_3912003 := by exact prefixLift 3912003
  have htrace : WordTrace (prefixWord ++ tailWord_3912003) baseStart_3912003 baseEnd_3912003 := by
    simpa [prefixWord, tailWord_3912003, baseEnd_3912003] using wordTrace_append hprefix tailTrace_3912003
  have hstable : (prefixWord ++ tailWord_3912003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912003).length < 2 ^ (prefixWord ++ tailWord_3912003).sum := by decide
  have hdescent : baseEnd_3912003 < baseStart_3912003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912018 : List Nat := [3, 2, 2, 1, 1, 1, 2, 2, 4, 4]
def baseStart_3912018 : Nat := 118140960795 + 3912018 * 2 ^ 59
def prefixEnd_3912018 : Nat := 4983230072969 + 3 ^ 40 * 3912018 * 2
def baseEnd_3912018 : Nat := 1339163708693720296855975

theorem tailTrace_3912018 : CollatzResearch.WordTrace tailWord_3912018 prefixEnd_3912018 1339163708693720296855975 := by
  unfold tailWord_3912018
  simp only [CollatzResearch.WordTrace]
  refine ⟨35670754585358595081950177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95122012227622920218533805 35670754585358595081950177)
  ·
    refine ⟨26753065939018946311462633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35670754585358595081950177 26753065939018946311462633)
    ·
      refine ⟨20064799454264209733596975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26753065939018946311462633 20064799454264209733596975)
      ·
        refine ⟨30097199181396314600395463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20064799454264209733596975 30097199181396314600395463)
        ·
          refine ⟨45145798772094471900593195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30097199181396314600395463 45145798772094471900593195)
          ·
            refine ⟨67718698158141707850889793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45145798772094471900593195 67718698158141707850889793)
            ·
              refine ⟨50789023618606280888167345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67718698158141707850889793 50789023618606280888167345)
              ·
                refine ⟨38091767713954710666125509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50789023618606280888167345 38091767713954710666125509)
                ·
                  refine ⟨7142206446366508249898533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38091767713954710666125509 7142206446366508249898533)
                  ·
                    refine ⟨1339163708693720296855975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7142206446366508249898533 1339163708693720296855975)
                    ·
                      rfl

theorem cell22_3912018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_3912018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3912018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3912018 prefixEnd_3912018 := by exact prefixLift 3912018
  have htrace : WordTrace (prefixWord ++ tailWord_3912018) baseStart_3912018 baseEnd_3912018 := by
    simpa [prefixWord, tailWord_3912018, baseEnd_3912018] using wordTrace_append hprefix tailTrace_3912018
  have hstable : (prefixWord ++ tailWord_3912018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912018).length < 2 ^ (prefixWord ++ tailWord_3912018).sum := by decide
  have hdescent : baseEnd_3912018 < baseStart_3912018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912020 : List Nat := [2, 4, 1, 1, 2, 3, 2, 1, 1, 5]
def baseStart_3912020 : Nat := 118140960795 + 3912020 * 2 ^ 59
def prefixEnd_3912020 : Nat := 4983230072969 + 3 ^ 40 * 3912020 * 2
def baseEnd_3912020 : Nat := 1339164393334592958305969

theorem tailTrace_3912020 : CollatzResearch.WordTrace tailWord_3912020 prefixEnd_3912020 1339164393334592958305969 := by
  unfold tailWord_3912020
  simp only [CollatzResearch.WordTrace]
  refine ⟨71341545643713567334686757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95122060858284756446249009 71341545643713567334686757)
  ·
    refine ⟨13376539808196293875253767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71341545643713567334686757 13376539808196293875253767)
    ·
      refine ⟨20064809712294440812880651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13376539808196293875253767 20064809712294440812880651)
      ·
        refine ⟨30097214568441661219320977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20064809712294440812880651 30097214568441661219320977)
        ·
          refine ⟨22572910926331245914490733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30097214568441661219320977 22572910926331245914490733)
          ·
            refine ⟨8464841597374217217934025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22572910926331245914490733 8464841597374217217934025)
            ·
              refine ⟨6348631198030662913450519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8464841597374217217934025 6348631198030662913450519)
              ·
                refine ⟨9522946797045994370175779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6348631198030662913450519 9522946797045994370175779)
                ·
                  refine ⟨14284420195568991555263669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9522946797045994370175779 14284420195568991555263669)
                  ·
                    refine ⟨1339164393334592958305969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14284420195568991555263669 1339164393334592958305969)
                    ·
                      rfl

theorem cell22_3912020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_3912020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3912020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3912020 prefixEnd_3912020 := by exact prefixLift 3912020
  have htrace : WordTrace (prefixWord ++ tailWord_3912020) baseStart_3912020 baseEnd_3912020 := by
    simpa [prefixWord, tailWord_3912020, baseEnd_3912020] using wordTrace_append hprefix tailTrace_3912020
  have hstable : (prefixWord ++ tailWord_3912020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912020).length < 2 ^ (prefixWord ++ tailWord_3912020).sum := by decide
  have hdescent : baseEnd_3912020 < baseStart_3912020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912054 : List Nat := [5, 1, 1, 4, 1, 1, 1, 1, 4, 3]
def baseStart_3912054 : Nat := 118140960795 + 3912054 * 2 ^ 59
def prefixEnd_3912054 : Nat := 4983230072969 + 3 ^ 40 * 3912054 * 2
def baseEnd_3912054 : Nat := 1339176032229428202955865

theorem tailTrace_3912054 : CollatzResearch.WordTrace tailWord_3912054 prefixEnd_3912054 1339176032229428202955865 := by
  unfold tailWord_3912054
  simp only [CollatzResearch.WordTrace]
  refine ⟨8917770710581497404756951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95122887579535972317407477 8917770710581497404756951)
  ·
    refine ⟨13376656065872246107135427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8917770710581497404756951 13376656065872246107135427)
    ·
      refine ⟨20064984098808369160703141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13376656065872246107135427 20064984098808369160703141)
      ·
        refine ⟨3762184518526569217631839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20064984098808369160703141 3762184518526569217631839)
        ·
          refine ⟨5643276777789853826447759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3762184518526569217631839 5643276777789853826447759)
          ·
            refine ⟨8464915166684780739671639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5643276777789853826447759 8464915166684780739671639)
            ·
              refine ⟨12697372750027171109507459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8464915166684780739671639 12697372750027171109507459)
              ·
                refine ⟨19046059125040756664261189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12697372750027171109507459 19046059125040756664261189)
                ·
                  refine ⟨3571136085945141874548973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19046059125040756664261189 3571136085945141874548973)
                  ·
                    refine ⟨1339176032229428202955865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3571136085945141874548973 1339176032229428202955865)
                    ·
                      rfl

theorem cell22_3912054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_3912054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3912054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3912054 prefixEnd_3912054 := by exact prefixLift 3912054
  have htrace : WordTrace (prefixWord ++ tailWord_3912054) baseStart_3912054 baseEnd_3912054 := by
    simpa [prefixWord, tailWord_3912054, baseEnd_3912054] using wordTrace_append hprefix tailTrace_3912054
  have hstable : (prefixWord ++ tailWord_3912054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912054).length < 2 ^ (prefixWord ++ tailWord_3912054).sum := by decide
  have hdescent : baseEnd_3912054 < baseStart_3912054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912084 : List Nat := [2, 4, 2, 1, 4, 1, 2, 6]
def baseStart_3912084 : Nat := 118140960795 + 3912084 * 2 ^ 59
def prefixEnd_3912084 : Nat := 4983230072969 + 3 ^ 40 * 3912084 * 2
def baseEnd_3912084 : Nat := 148798477982502013856197

theorem tailTrace_3912084 : CollatzResearch.WordTrace tailWord_3912084 prefixEnd_3912084 148798477982502013856197 := by
  unfold tailWord_3912084
  simp only [CollatzResearch.WordTrace]
  refine ⟨71342712779597636799851653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95123617039463515733135537 71342712779597636799851653)
  ·
    refine ⟨13376758646174556899972185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71342712779597636799851653 13376758646174556899972185)
    ·
      refine ⟨10032568984630917674979139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13376758646174556899972185 10032568984630917674979139)
      ·
        refine ⟨15048853476946376512468709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10032568984630917674979139 15048853476946376512468709)
        ·
          refine ⟨2821660026927445596087883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15048853476946376512468709 2821660026927445596087883)
          ·
            refine ⟨4232490040391168394131825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2821660026927445596087883 4232490040391168394131825)
            ·
              refine ⟨3174367530293376295598869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4232490040391168394131825 3174367530293376295598869)
              ·
                refine ⟨148798477982502013856197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3174367530293376295598869 148798477982502013856197)
                ·
                  rfl

theorem cell22_3912084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 6].length) (baseStart_3912084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3912084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3912084 prefixEnd_3912084 := by exact prefixLift 3912084
  have htrace : WordTrace (prefixWord ++ tailWord_3912084) baseStart_3912084 baseEnd_3912084 := by
    simpa [prefixWord, tailWord_3912084, baseEnd_3912084] using wordTrace_append hprefix tailTrace_3912084
  have hstable : (prefixWord ++ tailWord_3912084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912084).length < 2 ^ (prefixWord ++ tailWord_3912084).sum := by decide
  have hdescent : baseEnd_3912084 < baseStart_3912084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912099 : List Nat := [1, 1, 1, 4, 1, 6, 1, 3, 1, 3]
def baseStart_3912099 : Nat := 118140960795 + 3912099 * 2 ^ 59
def prefixEnd_3912099 : Nat := 4983230072969 + 3 ^ 40 * 3912099 * 2
def baseEnd_3912099 : Nat := 1339191436649063085580727

theorem tailTrace_3912099 : CollatzResearch.WordTrace tailWord_3912099 prefixEnd_3912099 1339191436649063085580727 := by
  unfold tailWord_3912099
  simp only [CollatzResearch.WordTrace]
  refine ⟨142685972654140931161499351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95123981769427287440999567 142685972654140931161499351)
  ·
    refine ⟨214028958981211396742249027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142685972654140931161499351 214028958981211396742249027)
    ·
      refine ⟨321043438471817095113373541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214028958981211396742249027 321043438471817095113373541)
      ·
        refine ⟨60195644713465705333757539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 321043438471817095113373541 60195644713465705333757539)
        ·
          refine ⟨90293467070198558000636309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60195644713465705333757539 90293467070198558000636309)
          ·
            refine ⟨4232506268915557406279827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 90293467070198558000636309 4232506268915557406279827)
            ·
              refine ⟨6348759403373336109419741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4232506268915557406279827 6348759403373336109419741)
              ·
                refine ⟨2380784776265001041032403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6348759403373336109419741 2380784776265001041032403)
                ·
                  refine ⟨3571177164397501561548605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2380784776265001041032403 3571177164397501561548605)
                  ·
                    refine ⟨1339191436649063085580727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3571177164397501561548605 1339191436649063085580727)
                    ·
                      rfl

theorem cell22_3912099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 3, 1, 3].length) (baseStart_3912099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3912099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3912099 prefixEnd_3912099 := by exact prefixLift 3912099
  have htrace : WordTrace (prefixWord ++ tailWord_3912099) baseStart_3912099 baseEnd_3912099 := by
    simpa [prefixWord, tailWord_3912099, baseEnd_3912099] using wordTrace_append hprefix tailTrace_3912099
  have hstable : (prefixWord ++ tailWord_3912099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912099).length < 2 ^ (prefixWord ++ tailWord_3912099).sum := by decide
  have hdescent : baseEnd_3912099 < baseStart_3912099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912108 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 5, 4]
def baseStart_3912108 : Nat := 118140960795 + 3912108 * 2 ^ 59
def prefixEnd_3912108 : Nat := 4983230072969 + 3 ^ 40 * 3912108 * 2
def baseEnd_3912108 : Nat := 1339194517532990062105699

theorem tailTrace_3912108 : CollatzResearch.WordTrace tailWord_3912108 prefixEnd_3912108 1339194517532990062105699 := by
  unfold tailWord_3912108
  simp only [CollatzResearch.WordTrace]
  refine ⟨71343150455554162849288489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95124200607405550465717985 71343150455554162849288489)
  ·
    refine ⟨53507362841665622136966367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71343150455554162849288489 53507362841665622136966367)
    ·
      refine ⟨80261044262498433205449551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53507362841665622136966367 80261044262498433205449551)
      ·
        refine ⟨120391566393747649808174327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80261044262498433205449551 120391566393747649808174327)
        ·
          refine ⟨180587349590621474712261491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120391566393747649808174327 180587349590621474712261491)
          ·
            refine ⟨270881024385932212068392237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180587349590621474712261491 270881024385932212068392237)
            ·
              refine ⟨101580384144724579525647089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270881024385932212068392237 101580384144724579525647089)
              ·
                refine ⟨76185288108543434644235317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101580384144724579525647089 76185288108543434644235317)
                ·
                  refine ⟨7142370760175946997897061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76185288108543434644235317 7142370760175946997897061)
                  ·
                    refine ⟨1339194517532990062105699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7142370760175946997897061 1339194517532990062105699)
                    ·
                      rfl

theorem cell22_3912108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_3912108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3912108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3912108 prefixEnd_3912108 := by exact prefixLift 3912108
  have htrace : WordTrace (prefixWord ++ tailWord_3912108) baseStart_3912108 baseEnd_3912108 := by
    simpa [prefixWord, tailWord_3912108, baseEnd_3912108] using wordTrace_append hprefix tailTrace_3912108
  have hstable : (prefixWord ++ tailWord_3912108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912108).length < 2 ^ (prefixWord ++ tailWord_3912108).sum := by decide
  have hdescent : baseEnd_3912108 < baseStart_3912108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912157 : List Nat := [1, 4, 3, 1, 1, 1, 2, 5, 4]
def baseStart_3912157 : Nat := 118140960795 + 3912157 * 2 ^ 59
def prefixEnd_3912157 : Nat := 4983230072969 + 3 ^ 40 * 3912157 * 2
def baseEnd_3912157 : Nat := 446403763744790089210183

theorem tailTrace_3912157 : CollatzResearch.WordTrace tailWord_3912157 prefixEnd_3912157 446403763744790089210183 := by
  unfold tailWord_3912157
  simp only [CollatzResearch.WordTrace]
  refine ⟨142688088087930807067110725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95125392058620538044740483 142688088087930807067110725)
  ·
    refine ⟨26754016516487026325083261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142688088087930807067110725 26754016516487026325083261)
    ·
      refine ⟨10032756193682634871906223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26754016516487026325083261 10032756193682634871906223)
      ·
        refine ⟨15049134290523952307859335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10032756193682634871906223 15049134290523952307859335)
        ·
          refine ⟨22573701435785928461789003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15049134290523952307859335 22573701435785928461789003)
          ·
            refine ⟨33860552153678892692683505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22573701435785928461789003 33860552153678892692683505)
            ·
              refine ⟨25395414115259169519512629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33860552153678892692683505 25395414115259169519512629)
              ·
                refine ⟨2380820073305547142454309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25395414115259169519512629 2380820073305547142454309)
                ·
                  refine ⟨446403763744790089210183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2380820073305547142454309 446403763744790089210183)
                  ·
                    rfl

theorem cell22_3912157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_3912157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3912157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3912157 prefixEnd_3912157 := by exact prefixLift 3912157
  have htrace : WordTrace (prefixWord ++ tailWord_3912157) baseStart_3912157 baseEnd_3912157 := by
    simpa [prefixWord, tailWord_3912157, baseEnd_3912157] using wordTrace_append hprefix tailTrace_3912157
  have hstable : (prefixWord ++ tailWord_3912157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912157).length < 2 ^ (prefixWord ++ tailWord_3912157).sum := by decide
  have hdescent : baseEnd_3912157 < baseStart_3912157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912168 : List Nat := [2, 1, 4, 1, 1, 13]
def baseStart_3912168 : Nat := 118140960795 + 3912168 * 2 ^ 59
def prefixEnd_3912168 : Nat := 4983230072969 + 3 ^ 40 * 3912168 * 2
def baseEnd_3912168 : Nat := 16533519219249011180315

theorem tailTrace_3912168 : CollatzResearch.WordTrace tailWord_3912168 prefixEnd_3912168 16533519219249011180315 := by
  unfold tailWord_3912168
  simp only [CollatzResearch.WordTrace]
  refine ⟨71344244645445477972880579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95125659527260637297174105 71344244645445477972880579)
  ·
    refine ⟨107016366968168216959320869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71344244645445477972880579 107016366968168216959320869)
    ·
      refine ⟨20065568806531540679872663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107016366968168216959320869 20065568806531540679872663)
      ·
        refine ⟨30098353209797311019808995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20065568806531540679872663 30098353209797311019808995)
        ·
          refine ⟨45147529814695966529713493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30098353209797311019808995 45147529814695966529713493)
          ·
            refine ⟨16533519219249011180315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 45147529814695966529713493 16533519219249011180315)
            ·
              rfl

theorem cell22_3912168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 13].length) (baseStart_3912168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3912168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3912168 prefixEnd_3912168 := by exact prefixLift 3912168
  have htrace : WordTrace (prefixWord ++ tailWord_3912168) baseStart_3912168 baseEnd_3912168 := by
    simpa [prefixWord, tailWord_3912168, baseEnd_3912168] using wordTrace_append hprefix tailTrace_3912168
  have hstable : (prefixWord ++ tailWord_3912168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912168).length < 2 ^ (prefixWord ++ tailWord_3912168).sum := by decide
  have hdescent : baseEnd_3912168 < baseStart_3912168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912172 : List Nat := [2, 2, 1, 1, 2, 1, 6, 2, 2, 3]
def baseStart_3912172 : Nat := 118140960795 + 3912172 * 2 ^ 59
def prefixEnd_3912172 : Nat := 4983230072969 + 3 ^ 40 * 3912172 * 2
def baseEnd_3912172 : Nat := 1339216426040915228505503

theorem tailTrace_3912172 : CollatzResearch.WordTrace tailWord_3912172 prefixEnd_3912172 1339216426040915228505503 := by
  unfold tailWord_3912172
  simp only [CollatzResearch.WordTrace]
  refine ⟨71344317591438232314453385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95125756788584309752604513 71344317591438232314453385)
  ·
    refine ⟨53508238193578674235840039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71344317591438232314453385 53508238193578674235840039)
    ·
      refine ⟨80262357290368011353760059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53508238193578674235840039 80262357290368011353760059)
      ·
        refine ⟨120393535935552017030640089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80262357290368011353760059 120393535935552017030640089)
        ·
          refine ⟨90295151951664012772980067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120393535935552017030640089 90295151951664012772980067)
          ·
            refine ⟨135442727927496019159470101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90295151951664012772980067 135442727927496019159470101)
            ·
              refine ⟨6348877871601375898100161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 135442727927496019159470101 6348877871601375898100161)
              ·
                refine ⟨4761658403701031923575121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6348877871601375898100161 4761658403701031923575121)
                ·
                  refine ⟨3571243802775773942681341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4761658403701031923575121 3571243802775773942681341)
                  ·
                    refine ⟨1339216426040915228505503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3571243802775773942681341 1339216426040915228505503)
                    ·
                      rfl

theorem cell22_3912172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 3].length) (baseStart_3912172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3912172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3912172 prefixEnd_3912172 := by exact prefixLift 3912172
  have htrace : WordTrace (prefixWord ++ tailWord_3912172) baseStart_3912172 baseEnd_3912172 := by
    simpa [prefixWord, tailWord_3912172, baseEnd_3912172] using wordTrace_append hprefix tailTrace_3912172
  have hstable : (prefixWord ++ tailWord_3912172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912172).length < 2 ^ (prefixWord ++ tailWord_3912172).sum := by decide
  have hdescent : baseEnd_3912172 < baseStart_3912172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912174 : List Nat := [4, 1, 2, 1, 2, 2, 4, 2, 4]
def baseStart_3912174 : Nat := 118140960795 + 3912174 * 2 ^ 59
def prefixEnd_3912174 : Nat := 4983230072969 + 3 ^ 40 * 3912174 * 2
def baseEnd_3912174 : Nat := 446405703560595963318499

theorem tailTrace_3912174 : CollatzResearch.WordTrace tailWord_3912174 prefixEnd_3912174 446405703560595963318499 := by
  unfold tailWord_3912174
  simp only [CollatzResearch.WordTrace]
  refine ⟨17836088516108652371309947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95125805419246145980319717 17836088516108652371309947)
  ·
    refine ⟨26754132774162978556964921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17836088516108652371309947 26754132774162978556964921)
    ·
      refine ⟨20065599580622233917723691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26754132774162978556964921 20065599580622233917723691)
      ·
        refine ⟨30098399370933350876585537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20065599580622233917723691 30098399370933350876585537)
        ·
          refine ⟨22573799528200013157439153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30098399370933350876585537 22573799528200013157439153)
          ·
            refine ⟨16930349646150009868079365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22573799528200013157439153 16930349646150009868079365)
            ·
              refine ⟨3174440558653126850264881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16930349646150009868079365 3174440558653126850264881)
              ·
                refine ⟨2380830418989845137698661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3174440558653126850264881 2380830418989845137698661)
                ·
                  refine ⟨446405703560595963318499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2380830418989845137698661 446405703560595963318499)
                  ·
                    rfl

theorem cell22_3912174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_3912174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3912174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3912174 prefixEnd_3912174 := by exact prefixLift 3912174
  have htrace : WordTrace (prefixWord ++ tailWord_3912174) baseStart_3912174 baseEnd_3912174 := by
    simpa [prefixWord, tailWord_3912174, baseEnd_3912174] using wordTrace_append hprefix tailTrace_3912174
  have hstable : (prefixWord ++ tailWord_3912174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912174).length < 2 ^ (prefixWord ++ tailWord_3912174).sum := by decide
  have hdescent : baseEnd_3912174 < baseStart_3912174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912234 : List Nat := [3, 1, 4, 1, 1, 3, 2, 1, 3, 3]
def baseStart_3912234 : Nat := 118140960795 + 3912234 * 2 ^ 59
def prefixEnd_3912234 : Nat := 4983230072969 + 3 ^ 40 * 3912234 * 2
def baseEnd_3912234 : Nat := 1339237649907967733455313

theorem tailTrace_3912234 : CollatzResearch.WordTrace tailWord_3912234 prefixEnd_3912234 1339237649907967733455313 := by
  unfold tailWord_3912234
  simp only [CollatzResearch.WordTrace]
  refine ⟨35672724127162962304415939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95127264339101232811775837 35672724127162962304415939)
  ·
    refine ⟨53509086190744443456623909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35672724127162962304415939 53509086190744443456623909)
    ·
      refine ⟨10032953660764583148116983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53509086190744443456623909 10032953660764583148116983)
      ·
        refine ⟨15049430491146874722175475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10032953660764583148116983 15049430491146874722175475)
        ·
          refine ⟨22574145736720312083263213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15049430491146874722175475 22574145736720312083263213)
          ·
            refine ⟨8465304651270117031223705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22574145736720312083263213 8465304651270117031223705)
            ·
              refine ⟨6348978488452587773417779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8465304651270117031223705 6348978488452587773417779)
              ·
                refine ⟨9523467732678881660126669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6348978488452587773417779 9523467732678881660126669)
                ·
                  refine ⟨3571300399754580622547501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9523467732678881660126669 3571300399754580622547501)
                  ·
                    refine ⟨1339237649907967733455313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3571300399754580622547501 1339237649907967733455313)
                    ·
                      rfl

theorem cell22_3912234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_3912234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3912234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3912234 prefixEnd_3912234 := by exact prefixLift 3912234
  have htrace : WordTrace (prefixWord ++ tailWord_3912234) baseStart_3912234 baseEnd_3912234 := by
    simpa [prefixWord, tailWord_3912234, baseEnd_3912234] using wordTrace_append hprefix tailTrace_3912234
  have hstable : (prefixWord ++ tailWord_3912234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912234).length < 2 ^ (prefixWord ++ tailWord_3912234).sum := by decide
  have hdescent : baseEnd_3912234 < baseStart_3912234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912245 : List Nat := [1, 3, 3, 1, 1, 2, 1, 3, 2, 5]
def baseStart_3912245 : Nat := 118140960795 + 3912245 * 2 ^ 59
def prefixEnd_3912245 : Nat := 4983230072969 + 3 ^ 40 * 3912245 * 2
def baseEnd_3912245 : Nat := 1339241415432767371430279

theorem tailTrace_3912245 : CollatzResearch.WordTrace tailWord_3912245 prefixEnd_3912245 1339241415432767371430279 := by
  unfold tailWord_3912245
  simp only [CollatzResearch.WordTrace]
  refine ⟨142691297711611998096314189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95127531807741332064209459 142691297711611998096314189)
  ·
    refine ⟨53509236641854499286117821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142691297711611998096314189 53509236641854499286117821)
    ·
      refine ⟨20065963740695437232294183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53509236641854499286117821 20065963740695437232294183)
      ·
        refine ⟨30098945611043155848441275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20065963740695437232294183 30098945611043155848441275)
        ·
          refine ⟨45148418416564733772661913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30098945611043155848441275 45148418416564733772661913)
          ·
            refine ⟨33861313812423550329496435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45148418416564733772661913 33861313812423550329496435)
            ·
              refine ⟨50791970718635325494244653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33861313812423550329496435 50791970718635325494244653)
              ·
                refine ⟨19046989019488247060341745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50791970718635325494244653 19046989019488247060341745)
                ·
                  refine ⟨14285241764616185295256309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19046989019488247060341745 14285241764616185295256309)
                  ·
                    refine ⟨1339241415432767371430279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14285241764616185295256309 1339241415432767371430279)
                    ·
                      rfl

theorem cell22_3912245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_3912245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3912245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3912245 prefixEnd_3912245 := by exact prefixLift 3912245
  have htrace : WordTrace (prefixWord ++ tailWord_3912245) baseStart_3912245 baseEnd_3912245 := by
    simpa [prefixWord, tailWord_3912245, baseEnd_3912245] using wordTrace_append hprefix tailTrace_3912245
  have hstable : (prefixWord ++ tailWord_3912245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912245).length < 2 ^ (prefixWord ++ tailWord_3912245).sum := by decide
  have hdescent : baseEnd_3912245 < baseStart_3912245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912247 : List Nat := [1, 1, 3, 1, 2, 3, 5, 1, 5]
def baseStart_3912247 : Nat := 118140960795 + 3912247 * 2 ^ 59
def prefixEnd_3912247 : Nat := 4983230072969 + 3 ^ 40 * 3912247 * 2
def baseEnd_3912247 : Nat := 446414033357880010960091

theorem tailTrace_3912247 : CollatzResearch.WordTrace tailWord_3912247 prefixEnd_3912247 446414033357880010960091 := by
  unfold tailWord_3912247
  simp only [CollatzResearch.WordTrace]
  refine ⟨142691370657604752437886995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95127580438403168291924663 142691370657604752437886995)
  ·
    refine ⟨214037055986407128656830493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142691370657604752437886995 214037055986407128656830493)
    ·
      refine ⟨80263895994902673246311435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214037055986407128656830493 80263895994902673246311435)
      ·
        refine ⟨120395843992354009869467153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80263895994902673246311435 120395843992354009869467153)
        ·
          refine ⟨90296882994265507402100365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120395843992354009869467153 90296882994265507402100365)
          ·
            refine ⟨33861331122849565275787637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90296882994265507402100365 33861331122849565275787637)
            ·
              refine ⟨3174499792767146744605091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33861331122849565275787637 3174499792767146744605091)
              ·
                refine ⟨4761749689150720116907637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3174499792767146744605091 4761749689150720116907637)
                ·
                  refine ⟨446414033357880010960091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4761749689150720116907637 446414033357880010960091)
                  ·
                    rfl

theorem cell22_3912247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 5].length) (baseStart_3912247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3912247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3912247 prefixEnd_3912247 := by exact prefixLift 3912247
  have htrace : WordTrace (prefixWord ++ tailWord_3912247) baseStart_3912247 baseEnd_3912247 := by
    simpa [prefixWord, tailWord_3912247, baseEnd_3912247] using wordTrace_append hprefix tailTrace_3912247
  have hstable : (prefixWord ++ tailWord_3912247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912247).length < 2 ^ (prefixWord ++ tailWord_3912247).sum := by decide
  have hdescent : baseEnd_3912247 < baseStart_3912247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912277 : List Nat := [1, 3, 2, 2, 1, 1, 4, 3, 1, 4]
def baseStart_3912277 : Nat := 118140960795 + 3912277 * 2 ^ 59
def prefixEnd_3912277 : Nat := 4983230072969 + 3 ^ 40 * 3912277 * 2
def baseEnd_3912277 : Nat := 1339252369686729954630181

theorem tailTrace_3912277 : CollatzResearch.WordTrace tailWord_3912277 prefixEnd_3912277 1339252369686729954630181 := by
  unfold tailWord_3912277
  simp only [CollatzResearch.WordTrace]
  refine ⟨142692464847496067561479085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95128309898330711707652723 142692464847496067561479085)
  ·
    refine ⟨53509674317811025335554657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142692464847496067561479085 53509674317811025335554657)
    ·
      refine ⟨40132255738358269001665993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53509674317811025335554657 40132255738358269001665993)
      ·
        refine ⟨30099191803768701751249495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40132255738358269001665993 30099191803768701751249495)
        ·
          refine ⟨45148787705653052626874243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30099191803768701751249495 45148787705653052626874243)
          ·
            refine ⟨67723181558479578940311365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45148787705653052626874243 67723181558479578940311365)
            ·
              refine ⟨12698096542214921051308381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67723181558479578940311365 12698096542214921051308381)
              ·
                refine ⟨4761786203330595394240643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12698096542214921051308381 4761786203330595394240643)
                ·
                  refine ⟨7142679304995893091360965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4761786203330595394240643 7142679304995893091360965)
                  ·
                    refine ⟨1339252369686729954630181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7142679304995893091360965 1339252369686729954630181)
                    ·
                      rfl

theorem cell22_3912277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_3912277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3912277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3912277 prefixEnd_3912277 := by exact prefixLift 3912277
  have htrace : WordTrace (prefixWord ++ tailWord_3912277) baseStart_3912277 baseEnd_3912277 := by
    simpa [prefixWord, tailWord_3912277, baseEnd_3912277] using wordTrace_append hprefix tailTrace_3912277
  have hstable : (prefixWord ++ tailWord_3912277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912277).length < 2 ^ (prefixWord ++ tailWord_3912277).sum := by decide
  have hdescent : baseEnd_3912277 < baseStart_3912277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912320 : List Nat := [2, 1, 1, 2, 1, 5, 2, 8]
def baseStart_3912320 : Nat := 118140960795 + 3912320 * 2 ^ 59
def prefixEnd_3912320 : Nat := 4983230072969 + 3 ^ 40 * 3912320 * 2
def baseEnd_3912320 : Nat := 148807454385054686200561

theorem tailTrace_3912320 : CollatzResearch.WordTrace tailWord_3912320 prefixEnd_3912320 148807454385054686200561 := by
  unfold tailWord_3912320
  simp only [CollatzResearch.WordTrace]
  refine ⟨71347016593170142952647207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95129355457560190603529609 71347016593170142952647207)
  ·
    refine ⟨107020524889755214428970811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71347016593170142952647207 107020524889755214428970811)
    ·
      refine ⟨160530787334632821643456217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107020524889755214428970811 160530787334632821643456217)
      ·
        refine ⟨120398090500974616232592163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160530787334632821643456217 120398090500974616232592163)
        ·
          refine ⟨180597135751461924348888245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120398090500974616232592163 180597135751461924348888245)
          ·
            refine ⟨16930981476699555407708273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 180597135751461924348888245 16930981476699555407708273)
            ·
              refine ⟨12698236107524666555781205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16930981476699555407708273 12698236107524666555781205)
              ·
                refine ⟨148807454385054686200561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12698236107524666555781205 148807454385054686200561)
                ·
                  rfl

theorem cell22_3912320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 8].length) (baseStart_3912320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3912320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3912320 prefixEnd_3912320 := by exact prefixLift 3912320
  have htrace : WordTrace (prefixWord ++ tailWord_3912320) baseStart_3912320 baseEnd_3912320 := by
    simpa [prefixWord, tailWord_3912320, baseEnd_3912320] using wordTrace_append hprefix tailTrace_3912320
  have hstable : (prefixWord ++ tailWord_3912320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912320).length < 2 ^ (prefixWord ++ tailWord_3912320).sum := by decide
  have hdescent : baseEnd_3912320 < baseStart_3912320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912382 : List Nat := [4, 2, 1, 1, 2, 1, 2, 2, 7]
def baseStart_3912382 : Nat := 118140960795 + 3912382 * 2 ^ 59
def prefixEnd_3912382 : Nat := 4983230072969 + 3 ^ 40 * 3912382 * 2
def baseEnd_3912382 : Nat := 446429437777514893584953

theorem tailTrace_3912382 : CollatzResearch.WordTrace tailWord_3912382 prefixEnd_3912382 446429437777514893584953 := by
  unfold tailWord_3912382
  simp only [CollatzResearch.WordTrace]
  refine ⟨17837036814014458811756425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95130863008077113662700933 17837036814014458811756425)
  ·
    refine ⟨13377777610510844108817319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17837036814014458811756425 13377777610510844108817319)
    ·
      refine ⟨20066666415766266163225979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13377777610510844108817319 20066666415766266163225979)
      ·
        refine ⟨30099999623649399244838969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20066666415766266163225979 30099999623649399244838969)
        ·
          refine ⟨22574999717737049433629227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30099999623649399244838969 22574999717737049433629227)
          ·
            refine ⟨33862499576605574150443841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22574999717737049433629227 33862499576605574150443841)
            ·
              refine ⟨25396874682454180612832881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33862499576605574150443841 25396874682454180612832881)
              ·
                refine ⟨19047656011840635459624661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25396874682454180612832881 19047656011840635459624661)
                ·
                  refine ⟨446429437777514893584953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19047656011840635459624661 446429437777514893584953)
                  ·
                    rfl

theorem cell22_3912382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_3912382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3912382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3912382 prefixEnd_3912382 := by exact prefixLift 3912382
  have htrace : WordTrace (prefixWord ++ tailWord_3912382) baseStart_3912382 baseEnd_3912382 := by
    simpa [prefixWord, tailWord_3912382, baseEnd_3912382] using wordTrace_append hprefix tailTrace_3912382
  have hstable : (prefixWord ++ tailWord_3912382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912382).length < 2 ^ (prefixWord ++ tailWord_3912382).sum := by decide
  have hdescent : baseEnd_3912382 < baseStart_3912382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912442 : List Nat := [3, 1, 1, 1, 1, 3, 2, 4, 1, 5]
def baseStart_3912442 : Nat := 118140960795 + 3912442 * 2 ^ 59
def prefixEnd_3912442 : Nat := 4983230072969 + 3 ^ 40 * 3912442 * 2
def baseEnd_3912442 : Nat := 1339308852558724524254675

theorem tailTrace_3912442 : CollatzResearch.WordTrace tailWord_3912442 prefixEnd_3912442 1339308852558724524254675 := by
  unfold tailWord_3912442
  simp only [CollatzResearch.WordTrace]
  refine ⟨35674620722974575185308895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95132321927932200494157053 35674620722974575185308895)
  ·
    refine ⟨53511931084461862777963343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35674620722974575185308895 53511931084461862777963343)
    ·
      refine ⟨80267896626692794166945015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53511931084461862777963343 80267896626692794166945015)
      ·
        refine ⟨120401844940039191250417523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80267896626692794166945015 120401844940039191250417523)
        ·
          refine ⟨180602767410058786875626285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120401844940039191250417523 180602767410058786875626285)
          ·
            refine ⟨67726037778772045078359857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180602767410058786875626285 67726037778772045078359857)
            ·
              refine ⟨50794528334079033808769893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67726037778772045078359857 50794528334079033808769893)
              ·
                refine ⟨9523974062639818839144355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50794528334079033808769893 9523974062639818839144355)
                ·
                  refine ⟨14285961093959728258716533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9523974062639818839144355 14285961093959728258716533)
                  ·
                    refine ⟨1339308852558724524254675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14285961093959728258716533 1339308852558724524254675)
                    ·
                      rfl

theorem cell22_3912442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_3912442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3912442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3912442 prefixEnd_3912442 := by exact prefixLift 3912442
  have htrace : WordTrace (prefixWord ++ tailWord_3912442) baseStart_3912442 baseEnd_3912442 := by
    simpa [prefixWord, tailWord_3912442, baseEnd_3912442] using wordTrace_append hprefix tailTrace_3912442
  have hstable : (prefixWord ++ tailWord_3912442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912442).length < 2 ^ (prefixWord ++ tailWord_3912442).sum := by decide
  have hdescent : baseEnd_3912442 < baseStart_3912442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912446 : List Nat := [4, 2, 2, 1, 2, 1, 2, 3, 1, 4]
def baseStart_3912446 : Nat := 118140960795 + 3912446 * 2 ^ 59
def prefixEnd_3912446 : Nat := 4983230072969 + 3 ^ 40 * 3912446 * 2
def baseEnd_3912446 : Nat := 1339310221840469847154663

theorem tailTrace_3912446 : CollatzResearch.WordTrace tailWord_3912446 prefixEnd_3912446 1339310221840469847154663 := by
  unfold tailWord_3912446
  simp only [CollatzResearch.WordTrace]
  refine ⟨17837328597985476178047649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95132419189255872949587461 17837328597985476178047649)
  ·
    refine ⟨13377996448489107133535737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17837328597985476178047649 13377996448489107133535737)
    ·
      refine ⟨10033497336366830350151803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13377996448489107133535737 10033497336366830350151803)
      ·
        refine ⟨15050246004550245525227705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10033497336366830350151803 15050246004550245525227705)
        ·
          refine ⟨11287684503412684143920779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15050246004550245525227705 11287684503412684143920779)
          ·
            refine ⟨16931526755119026215881169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11287684503412684143920779 16931526755119026215881169)
            ·
              refine ⟨12698645066339269661910877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16931526755119026215881169 12698645066339269661910877)
              ·
                refine ⟨4761991899877226123216579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12698645066339269661910877 4761991899877226123216579)
                ·
                  refine ⟨7142987849815839184824869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4761991899877226123216579 7142987849815839184824869)
                  ·
                    refine ⟨1339310221840469847154663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7142987849815839184824869 1339310221840469847154663)
                    ·
                      rfl

theorem cell22_3912446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_3912446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3912446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3912446 prefixEnd_3912446 := by exact prefixLift 3912446
  have htrace : WordTrace (prefixWord ++ tailWord_3912446) baseStart_3912446 baseEnd_3912446 := by
    simpa [prefixWord, tailWord_3912446, baseEnd_3912446] using wordTrace_append hprefix tailTrace_3912446
  have hstable : (prefixWord ++ tailWord_3912446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912446).length < 2 ^ (prefixWord ++ tailWord_3912446).sum := by decide
  have hdescent : baseEnd_3912446 < baseStart_3912446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912457 : List Nat := [1, 2, 1, 1, 3, 2, 3, 1, 4, 4]
def baseStart_3912457 : Nat := 118140960795 + 3912457 * 2 ^ 59
def prefixEnd_3912457 : Nat := 4983230072969 + 3 ^ 40 * 3912457 * 2
def baseEnd_3912457 : Nat := 1339313987365269485129629

theorem tailTrace_3912457 : CollatzResearch.WordTrace tailWord_3912457 prefixEnd_3912457 1339313987365269485129629 := by
  unfold tailWord_3912457
  simp only [CollatzResearch.WordTrace]
  refine ⟨142699029986843958303031625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95132686657895972202021083 142699029986843958303031625)
  ·
    refine ⟨107024272490132968727273719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142699029986843958303031625 107024272490132968727273719)
    ·
      refine ⟨160536408735199453090910579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107024272490132968727273719 160536408735199453090910579)
      ·
        refine ⟨240804613102799179636365869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160536408735199453090910579 240804613102799179636365869)
        ·
          refine ⟨90301729913549692363637201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240804613102799179636365869 90301729913549692363637201)
          ·
            refine ⟨67726297435162269272727901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90301729913549692363637201 67726297435162269272727901)
            ·
              refine ⟨25397361538185850977272963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67726297435162269272727901 25397361538185850977272963)
              ·
                refine ⟨38096042307278776465909445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25397361538185850977272963 38096042307278776465909445)
                ·
                  refine ⟨7143007932614770587358021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38096042307278776465909445 7143007932614770587358021)
                  ·
                    refine ⟨1339313987365269485129629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7143007932614770587358021 1339313987365269485129629)
                    ·
                      rfl

theorem cell22_3912457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 4].length) (baseStart_3912457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3912457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3912457 prefixEnd_3912457 := by exact prefixLift 3912457
  have htrace : WordTrace (prefixWord ++ tailWord_3912457) baseStart_3912457 baseEnd_3912457 := by
    simpa [prefixWord, tailWord_3912457, baseEnd_3912457] using wordTrace_append hprefix tailTrace_3912457
  have hstable : (prefixWord ++ tailWord_3912457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912457).length < 2 ^ (prefixWord ++ tailWord_3912457).sum := by decide
  have hdescent : baseEnd_3912457 < baseStart_3912457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912459 : List Nat := [1, 1, 1, 1, 5, 1, 1, 6, 2, 3]
def baseStart_3912459 : Nat := 118140960795 + 3912459 * 2 ^ 59
def prefixEnd_3912459 : Nat := 4983230072969 + 3 ^ 40 * 3912459 * 2
def baseEnd_3912459 : Nat := 1339314672006142146579623

theorem tailTrace_3912459 : CollatzResearch.WordTrace tailWord_3912459 prefixEnd_3912459 1339314672006142146579623 := by
  unfold tailWord_3912459
  simp only [CollatzResearch.WordTrace]
  refine ⟨142699102932836712644604431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95132735288557808429736287 142699102932836712644604431)
  ·
    refine ⟨214048654399255068966906647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142699102932836712644604431 214048654399255068966906647)
    ·
      refine ⟨321072981598882603450359971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214048654399255068966906647 321072981598882603450359971)
      ·
        refine ⟨481609472398323905175539957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321072981598882603450359971 481609472398323905175539957)
        ·
          refine ⟨45150888037342866110206871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 481609472398323905175539957 45150888037342866110206871)
          ·
            refine ⟨67726332056014299165310307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45150888037342866110206871 67726332056014299165310307)
            ·
              refine ⟨101589498084021448747965461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67726332056014299165310307 101589498084021448747965461)
              ·
                refine ⟨4762007722688505410060881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101589498084021448747965461 4762007722688505410060881)
                ·
                  refine ⟨3571505792016379057545661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4762007722688505410060881 3571505792016379057545661)
                  ·
                    refine ⟨1339314672006142146579623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3571505792016379057545661 1339314672006142146579623)
                    ·
                      rfl

theorem cell22_3912459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 2, 3].length) (baseStart_3912459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3912459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3912459 prefixEnd_3912459 := by exact prefixLift 3912459
  have htrace : WordTrace (prefixWord ++ tailWord_3912459) baseStart_3912459 baseEnd_3912459 := by
    simpa [prefixWord, tailWord_3912459, baseEnd_3912459] using wordTrace_append hprefix tailTrace_3912459
  have hstable : (prefixWord ++ tailWord_3912459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912459).length < 2 ^ (prefixWord ++ tailWord_3912459).sum := by decide
  have hdescent : baseEnd_3912459 < baseStart_3912459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912476 : List Nat := [2, 2, 3, 1, 1, 4, 1, 3, 2, 3]
def baseStart_3912476 : Nat := 118140960795 + 3912476 * 2 ^ 59
def prefixEnd_3912476 : Nat := 4983230072969 + 3 ^ 40 * 3912476 * 2
def baseEnd_3912476 : Nat := 1339320491453559768904571

theorem tailTrace_3912476 : CollatzResearch.WordTrace tailWord_3912476 prefixEnd_3912476 1339320491453559768904571 := by
  unfold tailWord_3912476
  simp only [CollatzResearch.WordTrace]
  refine ⟨71349861486887562273986641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95133148649183416365315521 71349861486887562273986641)
  ·
    refine ⟨53512396115165671705489981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71349861486887562273986641 53512396115165671705489981)
    ·
      refine ⟨20067148543187126889558743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53512396115165671705489981 20067148543187126889558743)
      ·
        refine ⟨30100722814780690334338115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20067148543187126889558743 30100722814780690334338115)
        ·
          refine ⟨45151084222171035501507173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30100722814780690334338115 45151084222171035501507173)
          ·
            refine ⟨8465828291657069156532595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45151084222171035501507173 8465828291657069156532595)
            ·
              refine ⟨12698742437485603734798893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8465828291657069156532595 12698742437485603734798893)
              ·
                refine ⟨4762028414057101400549585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12698742437485603734798893 4762028414057101400549585)
                ·
                  refine ⟨3571521310542826050412189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4762028414057101400549585 3571521310542826050412189)
                  ·
                    refine ⟨1339320491453559768904571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3571521310542826050412189 1339320491453559768904571)
                    ·
                      rfl

theorem cell22_3912476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_3912476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3912476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3912476 prefixEnd_3912476 := by exact prefixLift 3912476
  have htrace : WordTrace (prefixWord ++ tailWord_3912476) baseStart_3912476 baseEnd_3912476 := by
    simpa [prefixWord, tailWord_3912476, baseEnd_3912476] using wordTrace_append hprefix tailTrace_3912476
  have hstable : (prefixWord ++ tailWord_3912476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912476).length < 2 ^ (prefixWord ++ tailWord_3912476).sum := by decide
  have hdescent : baseEnd_3912476 < baseStart_3912476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912493 : List Nat := [1, 5, 3, 2, 1, 1, 1, 2, 1, 5]
def baseStart_3912493 : Nat := 118140960795 + 3912493 * 2 ^ 59
def prefixEnd_3912493 : Nat := 4983230072969 + 3 ^ 40 * 3912493 * 2
def baseEnd_3912493 : Nat := 1339326310900977391229519

theorem tailTrace_3912493 : CollatzResearch.WordTrace tailWord_3912493 prefixEnd_3912493 1339326310900977391229519 := by
  unfold tailWord_3912493
  simp only [CollatzResearch.WordTrace]
  refine ⟨142700343014713536451342133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95133562009809024300894755 142700343014713536451342133)
  ·
    refine ⟨13378157157629394042313325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142700343014713536451342133 13378157157629394042313325)
    ·
      refine ⟨5016808934111022765867497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13378157157629394042313325 5016808934111022765867497)
      ·
        refine ⟨3762606700583267074400623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5016808934111022765867497 3762606700583267074400623)
        ·
          refine ⟨5643910050874900611600935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3762606700583267074400623 5643910050874900611600935)
          ·
            refine ⟨8465865076312350917401403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5643910050874900611600935 8465865076312350917401403)
            ·
              refine ⟨12698797614468526376102105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8465865076312350917401403 12698797614468526376102105)
              ·
                refine ⟨9524098210851394782076579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12698797614468526376102105 9524098210851394782076579)
                ·
                  refine ⟨14286147316277092173114869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9524098210851394782076579 14286147316277092173114869)
                  ·
                    refine ⟨1339326310900977391229519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14286147316277092173114869 1339326310900977391229519)
                    ·
                      rfl

theorem cell22_3912493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_3912493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3912493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3912493 prefixEnd_3912493 := by exact prefixLift 3912493
  have htrace : WordTrace (prefixWord ++ tailWord_3912493) baseStart_3912493 baseEnd_3912493 := by
    simpa [prefixWord, tailWord_3912493, baseEnd_3912493] using wordTrace_append hprefix tailTrace_3912493
  have hstable : (prefixWord ++ tailWord_3912493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912493).length < 2 ^ (prefixWord ++ tailWord_3912493).sum := by decide
  have hdescent : baseEnd_3912493 < baseStart_3912493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912566 : List Nat := [5, 1, 1, 3, 1, 1, 1, 2, 2, 5]
def baseStart_3912566 : Nat := 118140960795 + 3912566 * 2 ^ 59
def prefixEnd_3912566 : Nat := 4983230072969 + 3 ^ 40 * 3912566 * 2
def baseEnd_3912566 : Nat := 1339351300292829534154295

theorem tailTrace_3912566 : CollatzResearch.WordTrace tailWord_3912566 prefixEnd_3912566 1339351300292829534154295 := by
  unfold tailWord_3912566
  simp only [CollatzResearch.WordTrace]
  refine ⟨8918937846465566869921847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95135337028966046612499701 8918937846465566869921847)
  ·
    refine ⟨13378406769698350304882771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8918937846465566869921847 13378406769698350304882771)
    ·
      refine ⟨20067610154547525457324157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13378406769698350304882771 20067610154547525457324157)
      ·
        refine ⟨7525353807955322046496559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20067610154547525457324157 7525353807955322046496559)
        ·
          refine ⟨11288030711932983069744839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7525353807955322046496559 11288030711932983069744839)
          ·
            refine ⟨16932046067899474604617259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11288030711932983069744839 16932046067899474604617259)
            ·
              refine ⟨25398069101849211906925889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16932046067899474604617259 25398069101849211906925889)
              ·
                refine ⟨19048551826386908930194417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25398069101849211906925889 19048551826386908930194417)
                ·
                  refine ⟨14286413869790181697645813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19048551826386908930194417 14286413869790181697645813)
                  ·
                    refine ⟨1339351300292829534154295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14286413869790181697645813 1339351300292829534154295)
                    ·
                      rfl

theorem cell22_3912566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_3912566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3912566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3912566 prefixEnd_3912566 := by exact prefixLift 3912566
  have htrace : WordTrace (prefixWord ++ tailWord_3912566) baseStart_3912566 baseEnd_3912566 := by
    simpa [prefixWord, tailWord_3912566, baseEnd_3912566] using wordTrace_append hprefix tailTrace_3912566
  have hstable : (prefixWord ++ tailWord_3912566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912566).length < 2 ^ (prefixWord ++ tailWord_3912566).sum := by decide
  have hdescent : baseEnd_3912566 < baseStart_3912566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912579 : List Nat := [1, 1, 1, 3, 4, 1, 4, 1, 6]
def baseStart_3912579 : Nat := 118140960795 + 3912579 * 2 ^ 59
def prefixEnd_3912579 : Nat := 4983230072969 + 3 ^ 40 * 3912579 * 2
def baseEnd_3912579 : Nat := 446451916819500611193085

theorem tailTrace_3912579 : CollatzResearch.WordTrace tailWord_3912579 prefixEnd_3912579 446451916819500611193085 := by
  unfold tailWord_3912579
  simp only [CollatzResearch.WordTrace]
  refine ⟨142703479692401973138972791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95135653128267982092648527 142703479692401973138972791)
  ·
    refine ⟨214055219538602959708459187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142703479692401973138972791 214055219538602959708459187)
    ·
      refine ⟨321082829307904439562688781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214055219538602959708459187 321082829307904439562688781)
      ·
        refine ⟨120406060990464164836008293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321082829307904439562688781 120406060990464164836008293)
        ·
          refine ⟨22576136435712030906751555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120406060990464164836008293 22576136435712030906751555)
          ·
            refine ⟨33864204653568046360127333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22576136435712030906751555 33864204653568046360127333)
            ·
              refine ⟨6349538372544008692523875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33864204653568046360127333 6349538372544008692523875)
              ·
                refine ⟨9524307558816013038785813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6349538372544008692523875 9524307558816013038785813)
                ·
                  refine ⟨446451916819500611193085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9524307558816013038785813 446451916819500611193085)
                  ·
                    rfl

theorem cell22_3912579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 6].length) (baseStart_3912579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3912579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3912579 prefixEnd_3912579 := by exact prefixLift 3912579
  have htrace : WordTrace (prefixWord ++ tailWord_3912579) baseStart_3912579 baseEnd_3912579 := by
    simpa [prefixWord, tailWord_3912579, baseEnd_3912579] using wordTrace_append hprefix tailTrace_3912579
  have hstable : (prefixWord ++ tailWord_3912579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912579).length < 2 ^ (prefixWord ++ tailWord_3912579).sum := by decide
  have hdescent : baseEnd_3912579 < baseStart_3912579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912673 : List Nat := [1, 2, 3, 1, 2, 1, 1, 7, 1, 3]
def baseStart_3912673 : Nat := 118140960795 + 3912673 * 2 ^ 59
def prefixEnd_3912673 : Nat := 4983230072969 + 3 ^ 40 * 3912673 * 2
def baseEnd_3912673 : Nat := 1339387928579516921728967

theorem tailTrace_3912673 : CollatzResearch.WordTrace tailWord_3912673 prefixEnd_3912673 1339387928579516921728967 := by
  unfold tailWord_3912673
  simp only [CollatzResearch.WordTrace]
  refine ⟨142706908154061427192894673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95137938769374284795263115 142706908154061427192894673)
  ·
    refine ⟨107030181115546070394671005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142706908154061427192894673 107030181115546070394671005)
    ·
      refine ⟨40136317918329776398001627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107030181115546070394671005 40136317918329776398001627)
      ·
        refine ⟨60204476877494664597002441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40136317918329776398001627 60204476877494664597002441)
        ·
          refine ⟨45153357658120998447751831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60204476877494664597002441 45153357658120998447751831)
          ·
            refine ⟨67730036487181497671627747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45153357658120998447751831 67730036487181497671627747)
            ·
              refine ⟨101595054730772246507441621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67730036487181497671627747 101595054730772246507441621)
              ·
                refine ⟨2381134095252474527518163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 101595054730772246507441621 2381134095252474527518163)
                ·
                  refine ⟨3571701142878711791277245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2381134095252474527518163 3571701142878711791277245)
                  ·
                    refine ⟨1339387928579516921728967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3571701142878711791277245 1339387928579516921728967)
                    ·
                      rfl

theorem cell22_3912673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 7, 1, 3].length) (baseStart_3912673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3912673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3912673 prefixEnd_3912673 := by exact prefixLift 3912673
  have htrace : WordTrace (prefixWord ++ tailWord_3912673) baseStart_3912673 baseEnd_3912673 := by
    simpa [prefixWord, tailWord_3912673, baseEnd_3912673] using wordTrace_append hprefix tailTrace_3912673
  have hstable : (prefixWord ++ tailWord_3912673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912673).length < 2 ^ (prefixWord ++ tailWord_3912673).sum := by decide
  have hdescent : baseEnd_3912673 < baseStart_3912673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912716 : List Nat := [2, 2, 1, 2, 3, 2, 2, 1, 3, 4]
def baseStart_3912716 : Nat := 118140960795 + 3912716 * 2 ^ 59
def prefixEnd_3912716 : Nat := 4983230072969 + 3 ^ 40 * 3912716 * 2
def baseEnd_3912716 : Nat := 1339402648358279142903835

theorem tailTrace_3912716 : CollatzResearch.WordTrace tailWord_3912716 prefixEnd_3912716 1339402648358279142903835 := by
  unfold tailWord_3912716
  simp only [CollatzResearch.WordTrace]
  refine ⟨71354238246452822768355001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95138984328603763691140001 71354238246452822768355001)
  ·
    refine ⟨53515678684839617076266251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71354238246452822768355001 53515678684839617076266251)
    ·
      refine ⟨80273518027259425614399377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53515678684839617076266251 80273518027259425614399377)
      ·
        refine ⟨60205138520444569210799533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80273518027259425614399377 60205138520444569210799533)
        ·
          refine ⟨22576926945166713454049825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60205138520444569210799533 22576926945166713454049825)
          ·
            refine ⟨16932695208875035090537369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22576926945166713454049825 16932695208875035090537369)
            ·
              refine ⟨12699521406656276317903027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16932695208875035090537369 12699521406656276317903027)
              ·
                refine ⟨19049282109984414476854541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12699521406656276317903027 19049282109984414476854541)
                ·
                  refine ⟨7143480791244155428820453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19049282109984414476854541 7143480791244155428820453)
                  ·
                    refine ⟨1339402648358279142903835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7143480791244155428820453 1339402648358279142903835)
                    ·
                      rfl

theorem cell22_3912716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_3912716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3912716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3912716 prefixEnd_3912716 := by exact prefixLift 3912716
  have htrace : WordTrace (prefixWord ++ tailWord_3912716) baseStart_3912716 baseEnd_3912716 := by
    simpa [prefixWord, tailWord_3912716, baseEnd_3912716] using wordTrace_append hprefix tailTrace_3912716
  have hstable : (prefixWord ++ tailWord_3912716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912716).length < 2 ^ (prefixWord ++ tailWord_3912716).sum := by decide
  have hdescent : baseEnd_3912716 < baseStart_3912716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912759 : List Nat := [1, 1, 3, 1, 2, 2, 1, 11]
def baseStart_3912759 : Nat := 118140960795 + 3912759 * 2 ^ 59
def prefixEnd_3912759 : Nat := 4983230072969 + 3 ^ 40 * 3912759 * 2
def baseEnd_3912759 : Nat := 148824152015226818230967

theorem tailTrace_3912759 : CollatzResearch.WordTrace tailWord_3912759 prefixEnd_3912759 148824152015226818230967 := by
  unfold tailWord_3912759
  simp only [CollatzResearch.WordTrace]
  refine ⟨142710044831749863880525331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95140029887833242587016887 142710044831749863880525331)
  ·
    refine ⟨214065067247624795820787997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142710044831749863880525331 214065067247624795820787997)
    ·
      refine ⟨80274400217859298432795499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214065067247624795820787997 80274400217859298432795499)
      ·
        refine ⟨120411600326788947649193249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80274400217859298432795499 120411600326788947649193249)
        ·
          refine ⟨90308700245091710736894937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120411600326788947649193249 90308700245091710736894937)
          ·
            refine ⟨67731525183818783052671203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90308700245091710736894937 67731525183818783052671203)
            ·
              refine ⟨101597287775728174579006805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67731525183818783052671203 101597287775728174579006805)
              ·
                refine ⟨148824152015226818230967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 101597287775728174579006805 148824152015226818230967)
                ·
                  rfl

theorem cell22_3912759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 11].length) (baseStart_3912759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3912759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3912759 prefixEnd_3912759 := by exact prefixLift 3912759
  have htrace : WordTrace (prefixWord ++ tailWord_3912759) baseStart_3912759 baseEnd_3912759 := by
    simpa [prefixWord, tailWord_3912759, baseEnd_3912759] using wordTrace_append hprefix tailTrace_3912759
  have hstable : (prefixWord ++ tailWord_3912759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912759).length < 2 ^ (prefixWord ++ tailWord_3912759).sum := by decide
  have hdescent : baseEnd_3912759 < baseStart_3912759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912761 : List Nat := [1, 2, 1, 5, 2, 1, 1, 2, 1, 6]
def baseStart_3912761 : Nat := 118140960795 + 3912761 * 2 ^ 59
def prefixEnd_3912761 : Nat := 4983230072969 + 3 ^ 40 * 3912761 * 2
def baseEnd_3912761 : Nat := 1339418052777914025528697

theorem tailTrace_3912761 : CollatzResearch.WordTrace tailWord_3912761 prefixEnd_3912761 1339418052777914025528697 := by
  unfold tailWord_3912761
  simp only [CollatzResearch.WordTrace]
  refine ⟨142710117777742618222098137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95140078518495078814732091 142710117777742618222098137)
  ·
    refine ⟨107032588333306963666573603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142710117777742618222098137 107032588333306963666573603)
    ·
      refine ⟨160548882499960445499860405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107032588333306963666573603 160548882499960445499860405)
      ·
        refine ⟨15051457734371291765611913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160548882499960445499860405 15051457734371291765611913)
        ·
          refine ⟨11288593300778468824208935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15051457734371291765611913 11288593300778468824208935)
          ·
            refine ⟨16932889951167703236313403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11288593300778468824208935 16932889951167703236313403)
            ·
              refine ⟨25399334926751554854470105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16932889951167703236313403 25399334926751554854470105)
              ·
                refine ⟨19049501195063666140852579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25399334926751554854470105 19049501195063666140852579)
                ·
                  refine ⟨28574251792595499211278869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19049501195063666140852579 28574251792595499211278869)
                  ·
                    refine ⟨1339418052777914025528697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28574251792595499211278869 1339418052777914025528697)
                    ·
                      rfl

theorem cell22_3912761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 6].length) (baseStart_3912761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3912761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3912761 prefixEnd_3912761 := by exact prefixLift 3912761
  have htrace : WordTrace (prefixWord ++ tailWord_3912761) baseStart_3912761 baseEnd_3912761 := by
    simpa [prefixWord, tailWord_3912761, baseEnd_3912761] using wordTrace_append hprefix tailTrace_3912761
  have hstable : (prefixWord ++ tailWord_3912761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912761).length < 2 ^ (prefixWord ++ tailWord_3912761).sum := by decide
  have hdescent : baseEnd_3912761 < baseStart_3912761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912868 : List Nat := [2, 3, 1, 2, 3, 1, 1, 2, 3, 4]
def baseStart_3912868 : Nat := 118140960795 + 3912868 * 2 ^ 59
def prefixEnd_3912868 : Nat := 4983230072969 + 3 ^ 40 * 3912868 * 2
def baseEnd_3912868 : Nat := 1339454681064601413103369

theorem tailTrace_3912868 : CollatzResearch.WordTrace tailWord_3912868 prefixEnd_3912868 1339454681064601413103369 := by
  unfold tailWord_3912868
  simp only [CollatzResearch.WordTrace]
  refine ⟨71357010194177487748121629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95142680258903316997495505 71357010194177487748121629)
  ·
    refine ⟨26758878822816557905545611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71357010194177487748121629 26758878822816557905545611)
    ·
      refine ⟨40138318234224836858318417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26758878822816557905545611 40138318234224836858318417)
      ·
        refine ⟨30103738675668627643738813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40138318234224836858318417 30103738675668627643738813)
        ·
          refine ⟨11288902003375735366402055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30103738675668627643738813 11288902003375735366402055)
          ·
            refine ⟨16933353005063603049603083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11288902003375735366402055 16933353005063603049603083)
            ·
              refine ⟨25400029507595404574404625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16933353005063603049603083 25400029507595404574404625)
              ·
                refine ⟨19050022130696553430803469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25400029507595404574404625 19050022130696553430803469)
                ·
                  refine ⟨7143758299011207536551301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19050022130696553430803469 7143758299011207536551301)
                  ·
                    refine ⟨1339454681064601413103369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7143758299011207536551301 1339454681064601413103369)
                    ·
                      rfl

theorem cell22_3912868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_3912868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3912868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3912868 prefixEnd_3912868 := by exact prefixLift 3912868
  have htrace : WordTrace (prefixWord ++ tailWord_3912868) baseStart_3912868 baseEnd_3912868 := by
    simpa [prefixWord, tailWord_3912868, baseEnd_3912868] using wordTrace_append hprefix tailTrace_3912868
  have hstable : (prefixWord ++ tailWord_3912868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912868).length < 2 ^ (prefixWord ++ tailWord_3912868).sum := by decide
  have hdescent : baseEnd_3912868 < baseStart_3912868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912962 : List Nat := [3, 4, 1, 1, 4, 1, 8]
def baseStart_3912962 : Nat := 118140960795 + 3912962 * 2 ^ 59
def prefixEnd_3912962 : Nat := 4983230072969 + 3 ^ 40 * 3912962 * 2
def baseEnd_3912962 : Nat := 49610624414282092639003

theorem tailTrace_3912962 : CollatzResearch.WordTrace tailWord_3912962 prefixEnd_3912962 49610624414282092639003 := by
  unfold tailWord_3912962
  simp only [CollatzResearch.WordTrace]
  refine ⟨35679362212503607387541285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95144965900009619700110093 35679362212503607387541285)
  ·
    refine ⟨6689880414844426385163991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35679362212503607387541285 6689880414844426385163991)
    ·
      refine ⟨10034820622266639577745987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6689880414844426385163991 10034820622266639577745987)
      ·
        refine ⟨15052230933399959366618981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10034820622266639577745987 15052230933399959366618981)
        ·
          refine ⟨2822293300012492381241059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15052230933399959366618981 2822293300012492381241059)
          ·
            refine ⟨4233439950018738571861589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2822293300012492381241059 4233439950018738571861589)
            ·
              refine ⟨49610624414282092639003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4233439950018738571861589 49610624414282092639003)
              ·
                rfl

theorem cell22_3912962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 8].length) (baseStart_3912962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3912962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3912962 prefixEnd_3912962 := by exact prefixLift 3912962
  have htrace : WordTrace (prefixWord ++ tailWord_3912962) baseStart_3912962 baseEnd_3912962 := by
    simpa [prefixWord, tailWord_3912962, baseEnd_3912962] using wordTrace_append hprefix tailTrace_3912962
  have hstable : (prefixWord ++ tailWord_3912962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912962).length < 2 ^ (prefixWord ++ tailWord_3912962).sum := by decide
  have hdescent : baseEnd_3912962 < baseStart_3912962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912988 : List Nat := [2, 2, 3, 1, 1, 1, 2, 3, 2, 5]
def baseStart_3912988 : Nat := 118140960795 + 3912988 * 2 ^ 59
def prefixEnd_3912988 : Nat := 4983230072969 + 3 ^ 40 * 3912988 * 2
def baseEnd_3912988 : Nat := 1339495759516961100103001

theorem tailTrace_3912988 : CollatzResearch.WordTrace tailWord_3912988 prefixEnd_3912988 1339495759516961100103001 := by
  unfold tailWord_3912988
  simp only [CollatzResearch.WordTrace]
  refine ⟨71359198573960117995305809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95145598098613490660407745 71359198573960117995305809)
  ·
    refine ⟨53519398930470088496479357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71359198573960117995305809 53519398930470088496479357)
    ·
      refine ⟨20069774598926283186179759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53519398930470088496479357 20069774598926283186179759)
      ·
        refine ⟨30104661898389424779269639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20069774598926283186179759 30104661898389424779269639)
        ·
          refine ⟨45156992847584137168904459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30104661898389424779269639 45156992847584137168904459)
          ·
            refine ⟨67735489271376205753356689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45156992847584137168904459 67735489271376205753356689)
            ·
              refine ⟨50801616953532154315017517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67735489271376205753356689 50801616953532154315017517)
              ·
                refine ⟨19050606357574557868131569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50801616953532154315017517 19050606357574557868131569)
                ·
                  refine ⟨14287954768180918401098677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19050606357574557868131569 14287954768180918401098677)
                  ·
                    refine ⟨1339495759516961100103001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14287954768180918401098677 1339495759516961100103001)
                    ·
                      rfl

theorem cell22_3912988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_3912988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3912988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3912988 prefixEnd_3912988 := by exact prefixLift 3912988
  have htrace : WordTrace (prefixWord ++ tailWord_3912988) baseStart_3912988 baseEnd_3912988 := by
    simpa [prefixWord, tailWord_3912988, baseEnd_3912988] using wordTrace_append hprefix tailTrace_3912988
  have hstable : (prefixWord ++ tailWord_3912988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912988).length < 2 ^ (prefixWord ++ tailWord_3912988).sum := by decide
  have hdescent : baseEnd_3912988 < baseStart_3912988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913028 : List Nat := [2, 3, 4, 1, 1, 3, 2, 2, 1, 3]
def baseStart_3913028 : Nat := 118140960795 + 3913028 * 2 ^ 59
def prefixEnd_3913028 : Nat := 4983230072969 + 3 ^ 40 * 3913028 * 2
def baseEnd_3913028 : Nat := 1339509452334414329102879

theorem tailTrace_3913028 : CollatzResearch.WordTrace tailWord_3913028 prefixEnd_3913028 1339509452334414329102879 := by
  unfold tailWord_3913028
  simp only [CollatzResearch.WordTrace]
  refine ⟨71359928033887661411033869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95146570711850215214711825 71359928033887661411033869)
  ·
    refine ⟨26759973012707873029137701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71359928033887661411033869 26759973012707873029137701)
    ·
      refine ⟨5017494939882726192963319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26759973012707873029137701 5017494939882726192963319)
      ·
        refine ⟨7526242409824089289444979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5017494939882726192963319 7526242409824089289444979)
        ·
          refine ⟨11289363614736133934167469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7526242409824089289444979 11289363614736133934167469)
          ·
            refine ⟨4233511355526050225312801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11289363614736133934167469 4233511355526050225312801)
            ·
              refine ⟨3175133516644537668984601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4233511355526050225312801 3175133516644537668984601)
              ·
                refine ⟨2381350137483403251738451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3175133516644537668984601 2381350137483403251738451)
                ·
                  refine ⟨3572025206225104877607677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2381350137483403251738451 3572025206225104877607677)
                  ·
                    refine ⟨1339509452334414329102879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3572025206225104877607677 1339509452334414329102879)
                    ·
                      rfl

theorem cell22_3913028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_3913028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3913028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3913028 prefixEnd_3913028 := by exact prefixLift 3913028
  have htrace : WordTrace (prefixWord ++ tailWord_3913028) baseStart_3913028 baseEnd_3913028 := by
    simpa [prefixWord, tailWord_3913028, baseEnd_3913028] using wordTrace_append hprefix tailTrace_3913028
  have hstable : (prefixWord ++ tailWord_3913028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913028).length < 2 ^ (prefixWord ++ tailWord_3913028).sum := by decide
  have hdescent : baseEnd_3913028 < baseStart_3913028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913048 : List Nat := [2, 1, 2, 2, 1, 1, 4, 2, 1, 6]
def baseStart_3913048 : Nat := 118140960795 + 3913048 * 2 ^ 59
def prefixEnd_3913048 : Nat := 4983230072969 + 3 ^ 40 * 3913048 * 2
def baseEnd_3913048 : Nat := 1339516298743140943602817

theorem tailTrace_3913048 : CollatzResearch.WordTrace tailWord_3913048 prefixEnd_3913048 1339516298743140943602817 := by
  unfold tailWord_3913048
  simp only [CollatzResearch.WordTrace]
  refine ⟨71360292763851433118897899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95147057018468577491863865 71360292763851433118897899)
  ·
    refine ⟨107040439145777149678346849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71360292763851433118897899 107040439145777149678346849)
    ·
      refine ⟨80280329359332862258760137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107040439145777149678346849 80280329359332862258760137)
      ·
        refine ⟨60210247019499646694070103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80280329359332862258760137 60210247019499646694070103)
        ·
          refine ⟨90315370529249470041105155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60210247019499646694070103 90315370529249470041105155)
          ·
            refine ⟨135473055793874205061657733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90315370529249470041105155 135473055793874205061657733)
            ·
              refine ⟨25401197961351413449060825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135473055793874205061657733 25401197961351413449060825)
              ·
                refine ⟨19050898471013560086795619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25401197961351413449060825 19050898471013560086795619)
                ·
                  refine ⟨28576347706520340130193429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19050898471013560086795619 28576347706520340130193429)
                  ·
                    refine ⟨1339516298743140943602817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28576347706520340130193429 1339516298743140943602817)
                    ·
                      rfl

theorem cell22_3913048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_3913048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3913048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3913048 prefixEnd_3913048 := by exact prefixLift 3913048
  have htrace : WordTrace (prefixWord ++ tailWord_3913048) baseStart_3913048 baseEnd_3913048 := by
    simpa [prefixWord, tailWord_3913048, baseEnd_3913048] using wordTrace_append hprefix tailTrace_3913048
  have hstable : (prefixWord ++ tailWord_3913048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913048).length < 2 ^ (prefixWord ++ tailWord_3913048).sum := by decide
  have hdescent : baseEnd_3913048 < baseStart_3913048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913093 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 1, 8]
def baseStart_3913093 : Nat := 118140960795 + 3913093 * 2 ^ 59
def prefixEnd_3913093 : Nat := 4983230072969 + 3 ^ 40 * 3913093 * 2
def baseEnd_3913093 : Nat := 1339531703162775826227679

theorem tailTrace_3913093 : CollatzResearch.WordTrace tailWord_3913093 prefixEnd_3913093 1339531703162775826227679 := by
  unfold tailWord_3913093
  simp only [CollatzResearch.WordTrace]
  refine ⟨142722226812539838923183933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95148151208359892615455955 142722226812539838923183933)
  ·
    refine ⟨53520835054702439596193975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142722226812539838923183933 53520835054702439596193975)
    ·
      refine ⟨80281252582053659394290963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53520835054702439596193975 80281252582053659394290963)
      ·
        refine ⟨120421878873080489091436445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80281252582053659394290963 120421878873080489091436445)
        ·
          refine ⟨45158204577405183409288667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120421878873080489091436445 45158204577405183409288667)
          ·
            refine ⟨67737306866107775113933001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45158204577405183409288667 67737306866107775113933001)
            ·
              refine ⟨50802980149580831335449751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67737306866107775113933001 50802980149580831335449751)
              ·
                refine ⟨76204470224371247003174627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50802980149580831335449751 76204470224371247003174627)
                ·
                  refine ⟨114306705336556870504761941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76204470224371247003174627 114306705336556870504761941)
                  ·
                    refine ⟨1339531703162775826227679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 114306705336556870504761941 1339531703162775826227679)
                    ·
                      rfl

theorem cell22_3913093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_3913093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3913093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3913093 prefixEnd_3913093 := by exact prefixLift 3913093
  have htrace : WordTrace (prefixWord ++ tailWord_3913093) baseStart_3913093 baseEnd_3913093 := by
    simpa [prefixWord, tailWord_3913093, baseEnd_3913093] using wordTrace_append hprefix tailTrace_3913093
  have hstable : (prefixWord ++ tailWord_3913093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913093).length < 2 ^ (prefixWord ++ tailWord_3913093).sum := by decide
  have hdescent : baseEnd_3913093 < baseStart_3913093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913185 : List Nat := [1, 2, 3, 1, 2, 3, 1, 1, 3, 5]
def baseStart_3913185 : Nat := 118140960795 + 3913185 * 2 ^ 59
def prefixEnd_3913185 : Nat := 4983230072969 + 3 ^ 40 * 3913185 * 2
def baseEnd_3913185 : Nat := 1339563196642918252927397

theorem tailTrace_3913185 : CollatzResearch.WordTrace tailWord_3913185 prefixEnd_3913185 1339563196642918252927397 := by
  unfold tailWord_3913185
  simp only [CollatzResearch.WordTrace]
  refine ⟨142725582328206538635533009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95150388218804359090355339 142725582328206538635533009)
  ·
    refine ⟨107044186746154903976649757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142725582328206538635533009 107044186746154903976649757)
    ·
      refine ⟨40141570029808088991243659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107044186746154903976649757 40141570029808088991243659)
      ·
        refine ⟨60212355044712133486865489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40141570029808088991243659 60212355044712133486865489)
        ·
          refine ⟨45159266283534100115149117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60212355044712133486865489 45159266283534100115149117)
          ·
            refine ⟨16934724856325287543180919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45159266283534100115149117 16934724856325287543180919)
            ·
              refine ⟨25402087284487931314771379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16934724856325287543180919 25402087284487931314771379)
              ·
                refine ⟨38103130926731896972157069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25402087284487931314771379 38103130926731896972157069)
                ·
                  refine ⟨14288674097524461364558901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38103130926731896972157069 14288674097524461364558901)
                  ·
                    refine ⟨1339563196642918252927397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14288674097524461364558901 1339563196642918252927397)
                    ·
                      rfl

theorem cell22_3913185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_3913185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3913185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3913185 prefixEnd_3913185 := by exact prefixLift 3913185
  have htrace : WordTrace (prefixWord ++ tailWord_3913185) baseStart_3913185 baseEnd_3913185 := by
    simpa [prefixWord, tailWord_3913185, baseEnd_3913185] using wordTrace_append hprefix tailTrace_3913185
  have hstable : (prefixWord ++ tailWord_3913185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913185).length < 2 ^ (prefixWord ++ tailWord_3913185).sum := by decide
  have hdescent : baseEnd_3913185 < baseStart_3913185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913298 : List Nat := [3, 2, 2, 1, 2, 4, 1, 3, 1, 3]
def baseStart_3913298 : Nat := 118140960795 + 3913298 * 2 ^ 59
def prefixEnd_3913298 : Nat := 4983230072969 + 3 ^ 40 * 3913298 * 2
def baseEnd_3913298 : Nat := 1339601878852223624852051

theorem tailTrace_3913298 : CollatzResearch.WordTrace tailWord_3913298 prefixEnd_3913298 1339601878852223624852051 := by
  unfold tailWord_3913298
  simp only [CollatzResearch.WordTrace]
  refine ⟨35682425944199289733599137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95153135851198105956264365 35682425944199289733599137)
  ·
    refine ⟨26761819458149467300199353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35682425944199289733599137 26761819458149467300199353)
    ·
      refine ⟨20071364593612100475149515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26761819458149467300199353 20071364593612100475149515)
      ·
        refine ⟨30107046890418150712724273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20071364593612100475149515 30107046890418150712724273)
        ·
          refine ⟨22580285167813613034543205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30107046890418150712724273 22580285167813613034543205)
          ·
            refine ⟨4233803468965052443976851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22580285167813613034543205 4233803468965052443976851)
            ·
              refine ⟨6350705203447578665965277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4233803468965052443976851 6350705203447578665965277)
              ·
                refine ⟨2381514451292841999736979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6350705203447578665965277 2381514451292841999736979)
                ·
                  refine ⟨3572271676939262999605469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2381514451292841999736979 3572271676939262999605469)
                  ·
                    refine ⟨1339601878852223624852051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3572271676939262999605469 1339601878852223624852051)
                    ·
                      rfl

theorem cell22_3913298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_3913298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3913298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3913298 prefixEnd_3913298 := by exact prefixLift 3913298
  have htrace : WordTrace (prefixWord ++ tailWord_3913298) baseStart_3913298 baseEnd_3913298 := by
    simpa [prefixWord, tailWord_3913298, baseEnd_3913298] using wordTrace_append hprefix tailTrace_3913298
  have hstable : (prefixWord ++ tailWord_3913298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913298).length < 2 ^ (prefixWord ++ tailWord_3913298).sum := by decide
  have hdescent : baseEnd_3913298 < baseStart_3913298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913305 : List Nat := [1, 2, 1, 2, 2, 1, 1, 4, 8]
def baseStart_3913305 : Nat := 118140960795 + 3913305 * 2 ^ 59
def prefixEnd_3913305 : Nat := 4983230072969 + 3 ^ 40 * 3913305 * 2
def baseEnd_3913305 : Nat := 446534758365092646642343

theorem tailTrace_3913305 : CollatzResearch.WordTrace tailWord_3913305 prefixEnd_3913305 446534758365092646642343 := by
  unfold tailWord_3913305
  simp only [CollatzResearch.WordTrace]
  refine ⟨142729959087771799129901369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95153306058514532753267579 142729959087771799129901369)
  ·
    refine ⟨107047469315828849347426027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142729959087771799129901369 107047469315828849347426027)
    ·
      refine ⟨160571203973743274021139041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107047469315828849347426027 160571203973743274021139041)
      ·
        refine ⟨120428402980307455515854281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160571203973743274021139041 120428402980307455515854281)
        ·
          refine ⟨90321302235230591636890711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120428402980307455515854281 90321302235230591636890711)
          ·
            refine ⟨135481953352845887455336067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90321302235230591636890711 135481953352845887455336067)
            ·
              refine ⟨203222930029268831183004101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135481953352845887455336067 203222930029268831183004101)
              ·
                refine ⟨38104299380487905846813269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 203222930029268831183004101 38104299380487905846813269)
                ·
                  refine ⟨446534758365092646642343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38104299380487905846813269 446534758365092646642343)
                  ·
                    rfl

theorem cell22_3913305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 8].length) (baseStart_3913305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3913305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3913305 prefixEnd_3913305 := by exact prefixLift 3913305
  have htrace : WordTrace (prefixWord ++ tailWord_3913305) baseStart_3913305 baseEnd_3913305 := by
    simpa [prefixWord, tailWord_3913305, baseEnd_3913305] using wordTrace_append hprefix tailTrace_3913305
  have hstable : (prefixWord ++ tailWord_3913305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913305).length < 2 ^ (prefixWord ++ tailWord_3913305).sum := by decide
  have hdescent : baseEnd_3913305 < baseStart_3913305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913337 : List Nat := [1, 2, 1, 3, 3, 1, 2, 3, 1, 5]
def baseStart_3913337 : Nat := 118140960795 + 3913337 * 2 ^ 59
def prefixEnd_3913337 : Nat := 4983230072969 + 3 ^ 40 * 3913337 * 2
def baseEnd_3913337 : Nat := 1339615229349240523126931

theorem tailTrace_3913337 : CollatzResearch.WordTrace tailWord_3913337 prefixEnd_3913337 1339615229349240523126931 := by
  unfold tailWord_3913337
  simp only [CollatzResearch.WordTrace]
  refine ⟨142731126223655868595066265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95154084149103912396710843 142731126223655868595066265)
  ·
    refine ⟨107048344667741901446299699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142731126223655868595066265 107048344667741901446299699)
    ·
      refine ⟨160572517001612852169449549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107048344667741901446299699 160572517001612852169449549)
      ·
        refine ⟨60214693875604819563543581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160572517001612852169449549 60214693875604819563543581)
        ·
          refine ⟨22580510203351807336328843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60214693875604819563543581 22580510203351807336328843)
          ·
            refine ⟨33870765305027711004493265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22580510203351807336328843 33870765305027711004493265)
            ·
              refine ⟨25403073978770783253369949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33870765305027711004493265 25403073978770783253369949)
              ·
                refine ⟨9526152742039043720013731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25403073978770783253369949 9526152742039043720013731)
                ·
                  refine ⟨14289229113058565580020597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9526152742039043720013731 14289229113058565580020597)
                  ·
                    refine ⟨1339615229349240523126931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14289229113058565580020597 1339615229349240523126931)
                    ·
                      rfl

theorem cell22_3913337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 5].length) (baseStart_3913337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3913337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3913337 prefixEnd_3913337 := by exact prefixLift 3913337
  have htrace : WordTrace (prefixWord ++ tailWord_3913337) baseStart_3913337 baseEnd_3913337 := by
    simpa [prefixWord, tailWord_3913337, baseEnd_3913337] using wordTrace_append hprefix tailTrace_3913337
  have hstable : (prefixWord ++ tailWord_3913337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913337).length < 2 ^ (prefixWord ++ tailWord_3913337).sum := by decide
  have hdescent : baseEnd_3913337 < baseStart_3913337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913341 : List Nat := [1, 4, 1, 1, 4, 3, 1, 2, 1, 4]
def baseStart_3913341 : Nat := 118140960795 + 3913341 * 2 ^ 59
def prefixEnd_3913341 : Nat := 4983230072969 + 3 ^ 40 * 3913341 * 2
def baseEnd_3913341 : Nat := 1339616598630985846026919

theorem tailTrace_3913341 : CollatzResearch.WordTrace tailWord_3913341 prefixEnd_3913341 1339616598630985846026919 := by
  unfold tailWord_3913341
  simp only [CollatzResearch.WordTrace]
  refine ⟨142731272115641377278211877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95154181410427584852141251 142731272115641377278211877)
  ·
    refine ⟨26762113521682758239664727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142731272115641377278211877 26762113521682758239664727)
    ·
      refine ⟨40143170282524137359497091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26762113521682758239664727 40143170282524137359497091)
      ·
        refine ⟨60214755423786206039245637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40143170282524137359497091 60214755423786206039245637)
        ·
          refine ⟨11290266641959913632358557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60214755423786206039245637 11290266641959913632358557)
          ·
            refine ⟨4233849990734967612134459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11290266641959913632358557 4233849990734967612134459)
            ·
              refine ⟨6350774986102451418201689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4233849990734967612134459 6350774986102451418201689)
              ·
                refine ⟨4763081239576838563651267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6350774986102451418201689 4763081239576838563651267)
                ·
                  refine ⟨7144621859365257845476901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4763081239576838563651267 7144621859365257845476901)
                  ·
                    refine ⟨1339616598630985846026919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7144621859365257845476901 1339616598630985846026919)
                    ·
                      rfl

theorem cell22_3913341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_3913341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3913341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3913341 prefixEnd_3913341 := by exact prefixLift 3913341
  have htrace : WordTrace (prefixWord ++ tailWord_3913341) baseStart_3913341 baseEnd_3913341 := by
    simpa [prefixWord, tailWord_3913341, baseEnd_3913341] using wordTrace_append hprefix tailTrace_3913341
  have hstable : (prefixWord ++ tailWord_3913341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913341).length < 2 ^ (prefixWord ++ tailWord_3913341).sum := by decide
  have hdescent : baseEnd_3913341 < baseStart_3913341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913354 : List Nat := [3, 1, 2, 3, 2, 2, 1, 2, 1, 5]
def baseStart_3913354 : Nat := 118140960795 + 3913354 * 2 ^ 59
def prefixEnd_3913354 : Nat := 4983230072969 + 3 ^ 40 * 3913354 * 2
def baseEnd_3913354 : Nat := 1339621048796658145451879

theorem tailTrace_3913354 : CollatzResearch.WordTrace tailWord_3913354 prefixEnd_3913354 1339621048796658145451879 := by
  unfold tailWord_3913354
  simp only [CollatzResearch.WordTrace]
  refine ⟨35682936566148570124608779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95154497509729520332290077 35682936566148570124608779)
  ·
    refine ⟨53524404849222855186913169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35682936566148570124608779 53524404849222855186913169)
    ·
      refine ⟨40143303636917141390184877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53524404849222855186913169 40143303636917141390184877)
      ·
        refine ⟨15053738863843928021319329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40143303636917141390184877 15053738863843928021319329)
        ·
          refine ⟨11290304147882946015989497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15053738863843928021319329 11290304147882946015989497)
          ·
            refine ⟨8467728110912209511992123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11290304147882946015989497 8467728110912209511992123)
            ·
              refine ⟨12701592166368314267988185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8467728110912209511992123 12701592166368314267988185)
              ·
                refine ⟨9526194124776235700991139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12701592166368314267988185 9526194124776235700991139)
                ·
                  refine ⟨14289291187164353551486709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9526194124776235700991139 14289291187164353551486709)
                  ·
                    refine ⟨1339621048796658145451879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14289291187164353551486709 1339621048796658145451879)
                    ·
                      rfl

theorem cell22_3913354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_3913354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3913354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3913354 prefixEnd_3913354 := by exact prefixLift 3913354
  have htrace : WordTrace (prefixWord ++ tailWord_3913354) baseStart_3913354 baseEnd_3913354 := by
    simpa [prefixWord, tailWord_3913354, baseEnd_3913354] using wordTrace_append hprefix tailTrace_3913354
  have hstable : (prefixWord ++ tailWord_3913354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913354).length < 2 ^ (prefixWord ++ tailWord_3913354).sum := by decide
  have hdescent : baseEnd_3913354 < baseStart_3913354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913399 : List Nat := [1, 1, 3, 1, 5, 1, 1, 1, 5, 3]
def baseStart_3913399 : Nat := 118140960795 + 3913399 * 2 ^ 59
def prefixEnd_3913399 : Nat := 4983230072969 + 3 ^ 40 * 3913399 * 2
def baseEnd_3913399 : Nat := 1339636453216293028076741

theorem tailTrace_3913399 : CollatzResearch.WordTrace tailWord_3913399 prefixEnd_3913399 1339636453216293028076741 := by
  unfold tailWord_3913399
  simp only [CollatzResearch.WordTrace]
  refine ⟨142733387549431253183823251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95155591699620835455882167 142733387549431253183823251)
  ·
    refine ⟨214100081324146879775734877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142733387549431253183823251 214100081324146879775734877)
    ·
      refine ⟨80287530496555079915900579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214100081324146879775734877 80287530496555079915900579)
      ·
        refine ⟨120431295744832619873850869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80287530496555079915900579 120431295744832619873850869)
        ·
          refine ⟨11290433976078058113173519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120431295744832619873850869 11290433976078058113173519)
          ·
            refine ⟨16935650964117087169760279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11290433976078058113173519 16935650964117087169760279)
            ·
              refine ⟨25403476446175630754640419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16935650964117087169760279 25403476446175630754640419)
              ·
                refine ⟨38105214669263446131960629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25403476446175630754640419 38105214669263446131960629)
                ·
                  refine ⟨3572363875243448074871309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38105214669263446131960629 3572363875243448074871309)
                  ·
                    refine ⟨1339636453216293028076741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3572363875243448074871309 1339636453216293028076741)
                    ·
                      rfl

theorem cell22_3913399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 5, 3].length) (baseStart_3913399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3913399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3913399 prefixEnd_3913399 := by exact prefixLift 3913399
  have htrace : WordTrace (prefixWord ++ tailWord_3913399) baseStart_3913399 baseEnd_3913399 := by
    simpa [prefixWord, tailWord_3913399, baseEnd_3913399] using wordTrace_append hprefix tailTrace_3913399
  have hstable : (prefixWord ++ tailWord_3913399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913399).length < 2 ^ (prefixWord ++ tailWord_3913399).sum := by decide
  have hdescent : baseEnd_3913399 < baseStart_3913399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913459 : List Nat := [1, 1, 1, 2, 2, 3, 3, 4, 1, 4]
def baseStart_3913459 : Nat := 118140960795 + 3913459 * 2 ^ 59
def prefixEnd_3913459 : Nat := 4983230072969 + 3 ^ 40 * 3913459 * 2
def baseEnd_3913459 : Nat := 1339656992442472871576557

theorem tailTrace_3913459 : CollatzResearch.WordTrace tailWord_3913459 prefixEnd_3913459 1339656992442472871576557 := by
  unfold tailWord_3913459
  simp only [CollatzResearch.WordTrace]
  refine ⟨142735575929213883431007431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95157050619475922287338287 142735575929213883431007431)
  ·
    refine ⟨214103363893820825146511147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142735575929213883431007431 214103363893820825146511147)
    ·
      refine ⟨321155045840731237719766721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214103363893820825146511147 321155045840731237719766721)
      ·
        refine ⟨240866284380548428289825041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321155045840731237719766721 240866284380548428289825041)
        ·
          refine ⟨180649713285411321217368781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240866284380548428289825041 180649713285411321217368781)
          ·
            refine ⟨67743642482029245456513293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180649713285411321217368781 67743642482029245456513293)
            ·
              refine ⟨25403865930760967046192485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67743642482029245456513293 25403865930760967046192485)
              ·
                refine ⟨4763224862017681321161091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25403865930760967046192485 4763224862017681321161091)
                ·
                  refine ⟨7144837293026521981741637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4763224862017681321161091 7144837293026521981741637)
                  ·
                    refine ⟨1339656992442472871576557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7144837293026521981741637 1339656992442472871576557)
                    ·
                      rfl

theorem cell22_3913459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 4].length) (baseStart_3913459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3913459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3913459 prefixEnd_3913459 := by exact prefixLift 3913459
  have htrace : WordTrace (prefixWord ++ tailWord_3913459) baseStart_3913459 baseEnd_3913459 := by
    simpa [prefixWord, tailWord_3913459, baseEnd_3913459] using wordTrace_append hprefix tailTrace_3913459
  have hstable : (prefixWord ++ tailWord_3913459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913459).length < 2 ^ (prefixWord ++ tailWord_3913459).sum := by decide
  have hdescent : baseEnd_3913459 < baseStart_3913459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913476 : List Nat := [2, 3, 2, 2, 1, 2, 2, 3, 1, 4]
def baseStart_3913476 : Nat := 118140960795 + 3913476 * 2 ^ 59
def prefixEnd_3913476 : Nat := 4983230072969 + 3 ^ 40 * 3913476 * 2
def baseEnd_3913476 : Nat := 1339662811889890493901505

theorem tailTrace_3913476 : CollatzResearch.WordTrace tailWord_3913476 prefixEnd_3913476 1339662811889890493901505 := by
  unfold tailWord_3913476
  simp only [CollatzResearch.WordTrace]
  refine ⟨71368097985076147667188141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95157463980101530222917521 71368097985076147667188141)
  ·
    refine ⟨26763036744403555375195553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71368097985076147667188141 26763036744403555375195553)
    ·
      refine ⟨20072277558302666531396665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26763036744403555375195553 20072277558302666531396665)
      ·
        refine ⟨15054208168726999898547499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20072277558302666531396665 15054208168726999898547499)
        ·
          refine ⟨22581312253090499847821249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15054208168726999898547499 22581312253090499847821249)
          ·
            refine ⟨16935984189817874885865937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22581312253090499847821249 16935984189817874885865937)
            ·
              refine ⟨12701988142363406164399453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16935984189817874885865937 12701988142363406164399453)
              ·
                refine ⟨4763245553386277311649795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12701988142363406164399453 4763245553386277311649795)
                ·
                  refine ⟨7144868330079415967474693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4763245553386277311649795 7144868330079415967474693)
                  ·
                    refine ⟨1339662811889890493901505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7144868330079415967474693 1339662811889890493901505)
                    ·
                      rfl

theorem cell22_3913476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_3913476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3913476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3913476 prefixEnd_3913476 := by exact prefixLift 3913476
  have htrace : WordTrace (prefixWord ++ tailWord_3913476) baseStart_3913476 baseEnd_3913476 := by
    simpa [prefixWord, tailWord_3913476, baseEnd_3913476] using wordTrace_append hprefix tailTrace_3913476
  have hstable : (prefixWord ++ tailWord_3913476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913476).length < 2 ^ (prefixWord ++ tailWord_3913476).sum := by decide
  have hdescent : baseEnd_3913476 < baseStart_3913476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913487 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 3, 6]
def baseStart_3913487 : Nat := 118140960795 + 3913487 * 2 ^ 59
def prefixEnd_3913487 : Nat := 4983230072969 + 3 ^ 40 * 3913487 * 2
def baseEnd_3913487 : Nat := 1339666577414690131876471

theorem tailTrace_3913487 : CollatzResearch.WordTrace tailWord_3913487 prefixEnd_3913487 1339666577414690131876471 := by
  unfold tailWord_3913487
  simp only [CollatzResearch.WordTrace]
  refine ⟨142736597173112444213026715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95157731448741629475351143 142736597173112444213026715)
  ·
    refine ⟨214104895759668666319540073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142736597173112444213026715 214104895759668666319540073)
    ·
      refine ⟨160578671819751499739655055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214104895759668666319540073 160578671819751499739655055)
      ·
        refine ⟨240868007729627249609482583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160578671819751499739655055 240868007729627249609482583)
        ·
          refine ⟨361302011594440874414223875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240868007729627249609482583 361302011594440874414223875)
          ·
            refine ⟨541953017391661311621335813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361302011594440874414223875 541953017391661311621335813)
            ·
              refine ⟨101616190760936495929000465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 541953017391661311621335813 101616190760936495929000465)
              ·
                refine ⟨76212143070702371946750349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101616190760936495929000465 76212143070702371946750349)
                ·
                  refine ⟨28579553651513389480031381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76212143070702371946750349 28579553651513389480031381)
                  ·
                    refine ⟨1339666577414690131876471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28579553651513389480031381 1339666577414690131876471)
                    ·
                      rfl

theorem cell22_3913487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 6].length) (baseStart_3913487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3913487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3913487 prefixEnd_3913487 := by exact prefixLift 3913487
  have htrace : WordTrace (prefixWord ++ tailWord_3913487) baseStart_3913487 baseEnd_3913487 := by
    simpa [prefixWord, tailWord_3913487, baseEnd_3913487] using wordTrace_append hprefix tailTrace_3913487
  have hstable : (prefixWord ++ tailWord_3913487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913487).length < 2 ^ (prefixWord ++ tailWord_3913487).sum := by decide
  have hdescent : baseEnd_3913487 < baseStart_3913487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913504 : List Nat := [2, 1, 1, 5, 1, 1, 1, 2, 4, 4]
def baseStart_3913504 : Nat := 118140960795 + 3913504 * 2 ^ 59
def prefixEnd_3913504 : Nat := 4983230072969 + 3 ^ 40 * 3913504 * 2
def baseEnd_3913504 : Nat := 1339672396862107754201419

theorem tailTrace_3913504 : CollatzResearch.WordTrace tailWord_3913504 prefixEnd_3913504 1339672396862107754201419 := by
  unfold tailWord_3913504
  simp only [CollatzResearch.WordTrace]
  refine ⟨71368608607025428058197783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95158144809367237410930377 71368608607025428058197783)
  ·
    refine ⟨107052912910538142087296675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71368608607025428058197783 107052912910538142087296675)
    ·
      refine ⟨160579369365807213130945013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107052912910538142087296675 160579369365807213130945013)
      ·
        refine ⟨15054315878044426231026095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160579369365807213130945013 15054315878044426231026095)
        ·
          refine ⟨22581473817066639346539143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15054315878044426231026095 22581473817066639346539143)
          ·
            refine ⟨33872210725599959019808715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22581473817066639346539143 33872210725599959019808715)
            ·
              refine ⟨50808316088399938529713073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33872210725599959019808715 50808316088399938529713073)
              ·
                refine ⟨38106237066299953897284805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50808316088399938529713073 38106237066299953897284805)
                ·
                  refine ⟨7144919449931241355740901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38106237066299953897284805 7144919449931241355740901)
                  ·
                    refine ⟨1339672396862107754201419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7144919449931241355740901 1339672396862107754201419)
                    ·
                      rfl

theorem cell22_3913504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 4, 4].length) (baseStart_3913504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3913504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3913504 prefixEnd_3913504 := by exact prefixLift 3913504
  have htrace : WordTrace (prefixWord ++ tailWord_3913504) baseStart_3913504 baseEnd_3913504 := by
    simpa [prefixWord, tailWord_3913504, baseEnd_3913504] using wordTrace_append hprefix tailTrace_3913504
  have hstable : (prefixWord ++ tailWord_3913504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913504).length < 2 ^ (prefixWord ++ tailWord_3913504).sum := by decide
  have hdescent : baseEnd_3913504 < baseStart_3913504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913521 : List Nat := [1, 2, 2, 3, 2, 3, 2, 1, 2, 4]
def baseStart_3913521 : Nat := 118140960795 + 3913521 * 2 ^ 59
def prefixEnd_3913521 : Nat := 4983230072969 + 3 ^ 40 * 3913521 * 2
def baseEnd_3913521 : Nat := 1339678216309525376526367

theorem tailTrace_3913521 : CollatzResearch.WordTrace tailWord_3913521 prefixEnd_3913521 1339678216309525376526367 := by
  unfold tailWord_3913521
  simp only [CollatzResearch.WordTrace]
  refine ⟨142737837254989268019764417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95158558169992845346509611 142737837254989268019764417)
  ·
    refine ⟨107053377941241951014823313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142737837254989268019764417 107053377941241951014823313)
    ·
      refine ⟨80290033455931463261117485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107053377941241951014823313 80290033455931463261117485)
      ·
        refine ⟨30108762545974298722919057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80290033455931463261117485 30108762545974298722919057)
        ·
          refine ⟨22581571909480724042189293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30108762545974298722919057 22581571909480724042189293)
          ·
            refine ⟨8468089466055271515820985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22581571909480724042189293 8468089466055271515820985)
            ·
              refine ⟨6351067099541453636865739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8468089466055271515820985 6351067099541453636865739)
              ·
                refine ⟨9526600649312180455298609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6351067099541453636865739 9526600649312180455298609)
                ·
                  refine ⟨7144950486984135341473957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9526600649312180455298609 7144950486984135341473957)
                  ·
                    refine ⟨1339678216309525376526367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7144950486984135341473957 1339678216309525376526367)
                    ·
                      rfl

theorem cell22_3913521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 4].length) (baseStart_3913521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3913521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3913521 prefixEnd_3913521 := by exact prefixLift 3913521
  have htrace : WordTrace (prefixWord ++ tailWord_3913521) baseStart_3913521 baseEnd_3913521 := by
    simpa [prefixWord, tailWord_3913521, baseEnd_3913521] using wordTrace_append hprefix tailTrace_3913521
  have hstable : (prefixWord ++ tailWord_3913521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913521).length < 2 ^ (prefixWord ++ tailWord_3913521).sum := by decide
  have hdescent : baseEnd_3913521 < baseStart_3913521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913542 : List Nat := [6, 1, 1, 2, 1, 1, 4, 2, 4]
def baseStart_3913542 : Nat := 118140960795 + 3913542 * 2 ^ 59
def prefixEnd_3913542 : Nat := 4983230072969 + 3 ^ 40 * 3913542 * 2
def baseEnd_3913542 : Nat := 446561801679562773917101

theorem tailTrace_3913542 : CollatzResearch.WordTrace tailWord_3913542 prefixEnd_3913542 446561801679562773917101 := by
  unfold tailWord_3913542
  simp only [CollatzResearch.WordTrace]
  refine ⟨4460581349622287143946215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 95159068791942125737519253 4460581349622287143946215)
  ·
    refine ⟨6690872024433430715919323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4460581349622287143946215 6690872024433430715919323)
    ·
      refine ⟨10036308036650146073878985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6690872024433430715919323 10036308036650146073878985)
      ·
        refine ⟨7527231027487609555409239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10036308036650146073878985 7527231027487609555409239)
        ·
          refine ⟨11290846541231414333113859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7527231027487609555409239 11290846541231414333113859)
          ·
            refine ⟨16936269811847121499670789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11290846541231414333113859 16936269811847121499670789)
            ·
              refine ⟨3175550589721335281188273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16936269811847121499670789 3175550589721335281188273)
              ·
                refine ⟨2381662942291001460891205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3175550589721335281188273 2381662942291001460891205)
                ·
                  refine ⟨446561801679562773917101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2381662942291001460891205 446561801679562773917101)
                  ·
                    rfl

theorem cell22_3913542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_3913542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3913542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3913542 prefixEnd_3913542 := by exact prefixLift 3913542
  have htrace : WordTrace (prefixWord ++ tailWord_3913542) baseStart_3913542 baseEnd_3913542 := by
    simpa [prefixWord, tailWord_3913542, baseEnd_3913542] using wordTrace_append hprefix tailTrace_3913542
  have hstable : (prefixWord ++ tailWord_3913542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913542).length < 2 ^ (prefixWord ++ tailWord_3913542).sum := by decide
  have hdescent : baseEnd_3913542 < baseStart_3913542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913598 : List Nat := [4, 2, 3, 1, 1, 2, 1, 1, 7]
def baseStart_3913598 : Nat := 118140960795 + 3913598 * 2 ^ 59
def prefixEnd_3913598 : Nat := 4983230072969 + 3 ^ 40 * 3913598 * 2
def baseEnd_3913598 : Nat := 446568191661040947450377

theorem tailTrace_3913598 : CollatzResearch.WordTrace tailWord_3913598 prefixEnd_3913598 446568191661040947450377 := by
  unfold tailWord_3913598
  simp only [CollatzResearch.WordTrace]
  refine ⟨17842580709463788771289681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95160430450473540113544965 17842580709463788771289681)
  ·
    refine ⟨13381935532097841578467261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17842580709463788771289681 13381935532097841578467261)
    ·
      refine ⟨5018225824536690591925223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13381935532097841578467261 5018225824536690591925223)
      ·
        refine ⟨7527338736805035887887835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5018225824536690591925223 7527338736805035887887835)
        ·
          refine ⟨11291008105207553831831753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7527338736805035887887835 11291008105207553831831753)
          ·
            refine ⟨8468256078905665373873815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11291008105207553831831753 8468256078905665373873815)
            ·
              refine ⟨12702384118358498060810723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8468256078905665373873815 12702384118358498060810723)
              ·
                refine ⟨19053576177537747091216085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12702384118358498060810723 19053576177537747091216085)
                ·
                  refine ⟨446568191661040947450377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19053576177537747091216085 446568191661040947450377)
                  ·
                    rfl

theorem cell22_3913598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_3913598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3913598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3913598 prefixEnd_3913598 := by exact prefixLift 3913598
  have htrace : WordTrace (prefixWord ++ tailWord_3913598) baseStart_3913598 baseEnd_3913598 := by
    simpa [prefixWord, tailWord_3913598, baseEnd_3913598] using wordTrace_append hprefix tailTrace_3913598
  have hstable : (prefixWord ++ tailWord_3913598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913598).length < 2 ^ (prefixWord ++ tailWord_3913598).sum := by decide
  have hdescent : baseEnd_3913598 < baseStart_3913598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913626 : List Nat := [3, 1, 1, 4, 2, 1, 2, 2, 6]
def baseStart_3913626 : Nat := 118140960795 + 3913626 * 2 ^ 59
def prefixEnd_3913626 : Nat := 4983230072969 + 3 ^ 40 * 3913626 * 2
def baseEnd_3913626 : Nat := 446571386651780034217015

theorem tailTrace_3913626 : CollatzResearch.WordTrace tailWord_3913626 prefixEnd_3913626 446571386651780034217015 := by
  unfold tailWord_3913626
  simp only [CollatzResearch.WordTrace]
  refine ⟨35685416729902217738084183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95161111279739247301557821 35685416729902217738084183)
  ·
    refine ⟨53528125094853326607126275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35685416729902217738084183 53528125094853326607126275)
    ·
      refine ⟨80292187642279989910689413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53528125094853326607126275 80292187642279989910689413)
      ·
        refine ⟨15054785182927498108254265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80292187642279989910689413 15054785182927498108254265)
        ·
          refine ⟨11291088887195623581190699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15054785182927498108254265 11291088887195623581190699)
          ·
            refine ⟨16936633330793435371786049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11291088887195623581190699 16936633330793435371786049)
            ·
              refine ⟨12702474998095076528839537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16936633330793435371786049 12702474998095076528839537)
              ·
                refine ⟨9526856248571307396629653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12702474998095076528839537 9526856248571307396629653)
                ·
                  refine ⟨446571386651780034217015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9526856248571307396629653 446571386651780034217015)
                  ·
                    rfl

theorem cell22_3913626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 6].length) (baseStart_3913626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3913626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3913626 prefixEnd_3913626 := by exact prefixLift 3913626
  have htrace : WordTrace (prefixWord ++ tailWord_3913626) baseStart_3913626 baseEnd_3913626 := by
    simpa [prefixWord, tailWord_3913626, baseEnd_3913626] using wordTrace_append hprefix tailTrace_3913626
  have hstable : (prefixWord ++ tailWord_3913626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913626).length < 2 ^ (prefixWord ++ tailWord_3913626).sum := by decide
  have hdescent : baseEnd_3913626 < baseStart_3913626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913628 : List Nat := [2, 2, 3, 3, 1, 1, 1, 4, 1, 4]
def baseStart_3913628 : Nat := 118140960795 + 3913628 * 2 ^ 59
def prefixEnd_3913628 : Nat := 4983230072969 + 3 ^ 40 * 3913628 * 2
def baseEnd_3913628 : Nat := 1339714844596212764101039

theorem tailTrace_3913628 : CollatzResearch.WordTrace tailWord_3913628 prefixEnd_3913628 1339714844596212764101039 := by
  unfold tailWord_3913628
  simp only [CollatzResearch.WordTrace]
  refine ⟨71370869932800812646954769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95161159910401083529273025 71370869932800812646954769)
  ·
    refine ⟨53528152449600609485216077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71370869932800812646954769 53528152449600609485216077)
    ·
      refine ⟨20073057168600228556956029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53528152449600609485216077 20073057168600228556956029)
      ·
        refine ⟨7527396438225085708858511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20073057168600228556956029 7527396438225085708858511)
        ·
          refine ⟨11291094657337628563287767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7527396438225085708858511 11291094657337628563287767)
          ·
            refine ⟨16936641986006442844931651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11291094657337628563287767 16936641986006442844931651)
            ·
              refine ⟨25404962979009664267397477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16936641986006442844931651 25404962979009664267397477)
              ·
                refine ⟨4763430558564312050137027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25404962979009664267397477 4763430558564312050137027)
                ·
                  refine ⟨7145145837846468075205541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4763430558564312050137027 7145145837846468075205541)
                  ·
                    refine ⟨1339714844596212764101039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7145145837846468075205541 1339714844596212764101039)
                    ·
                      rfl

theorem cell22_3913628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_3913628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3913628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3913628 prefixEnd_3913628 := by exact prefixLift 3913628
  have htrace : WordTrace (prefixWord ++ tailWord_3913628) baseStart_3913628 baseEnd_3913628 := by
    simpa [prefixWord, tailWord_3913628, baseEnd_3913628] using wordTrace_append hprefix tailTrace_3913628
  have hstable : (prefixWord ++ tailWord_3913628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913628).length < 2 ^ (prefixWord ++ tailWord_3913628).sum := by decide
  have hdescent : baseEnd_3913628 < baseStart_3913628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913656 : List Nat := [2, 1, 2, 1, 2, 3, 3, 2, 2, 4]
def baseStart_3913656 : Nat := 118140960795 + 3913656 * 2 ^ 59
def prefixEnd_3913656 : Nat := 4983230072969 + 3 ^ 40 * 3913656 * 2
def baseEnd_3913656 : Nat := 1339724429568430024400953

theorem tailTrace_3913656 : CollatzResearch.WordTrace tailWord_3913656 prefixEnd_3913656 1339724429568430024400953 := by
  unfold tailWord_3913656
  simp only [CollatzResearch.WordTrace]
  refine ⟨71371380554750093037964411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95161840739666790717285881 71371380554750093037964411)
  ·
    refine ⟨107057070832125139556946617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71371380554750093037964411 107057070832125139556946617)
    ·
      refine ⟨80292803124093854667709963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107057070832125139556946617 80292803124093854667709963)
      ·
        refine ⟨120439204686140782001564945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80292803124093854667709963 120439204686140782001564945)
        ·
          refine ⟨90329403514605586501173709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120439204686140782001564945 90329403514605586501173709)
          ·
            refine ⟨33873526317977094937940141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90329403514605586501173709 33873526317977094937940141)
            ·
              refine ⟨12702572369241410601727553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33873526317977094937940141 12702572369241410601727553)
              ·
                refine ⟨9526929276931057951295665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12702572369241410601727553 9526929276931057951295665)
                ·
                  refine ⟨7145196957698293463471749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9526929276931057951295665 7145196957698293463471749)
                  ·
                    refine ⟨1339724429568430024400953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7145196957698293463471749 1339724429568430024400953)
                    ·
                      rfl

theorem cell22_3913656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_3913656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3913656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3913656 prefixEnd_3913656 := by exact prefixLift 3913656
  have htrace : WordTrace (prefixWord ++ tailWord_3913656) baseStart_3913656 baseEnd_3913656 := by
    simpa [prefixWord, tailWord_3913656, baseEnd_3913656] using wordTrace_append hprefix tailTrace_3913656
  have hstable : (prefixWord ++ tailWord_3913656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913656).length < 2 ^ (prefixWord ++ tailWord_3913656).sum := by decide
  have hdescent : baseEnd_3913656 < baseStart_3913656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913660 : List Nat := [2, 2, 2, 5, 1, 2, 1, 1, 6]
def baseStart_3913660 : Nat := 118140960795 + 3913660 * 2 ^ 59
def prefixEnd_3913660 : Nat := 4983230072969 + 3 ^ 40 * 3913660 * 2
def baseEnd_3913660 : Nat := 446575266283391782433647

theorem tailTrace_3913660 : CollatzResearch.WordTrace tailWord_3913660 prefixEnd_3913660 446575266283391782433647 := by
  unfold tailWord_3913660
  simp only [CollatzResearch.WordTrace]
  refine ⟨71371453500742847379537217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95161938000990463172716289 71371453500742847379537217)
  ·
    refine ⟨53528590125557135534652913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71371453500742847379537217 53528590125557135534652913)
    ·
      refine ⟨40146442594167851650989685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53528590125557135534652913 40146442594167851650989685)
      ·
        refine ⟨3763728993203236092280283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40146442594167851650989685 3763728993203236092280283)
        ·
          refine ⟨5645593489804854138420425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3763728993203236092280283 5645593489804854138420425)
          ·
            refine ⟨4234195117353640603815319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5645593489804854138420425 4234195117353640603815319)
            ·
              refine ⟨6351292676030460905722979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4234195117353640603815319 6351292676030460905722979)
              ·
                refine ⟨9526939014045691358584469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6351292676030460905722979 9526939014045691358584469)
                ·
                  refine ⟨446575266283391782433647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9526939014045691358584469 446575266283391782433647)
                  ·
                    rfl

theorem cell22_3913660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 6].length) (baseStart_3913660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3913660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3913660 prefixEnd_3913660 := by exact prefixLift 3913660
  have htrace : WordTrace (prefixWord ++ tailWord_3913660) baseStart_3913660 baseEnd_3913660 := by
    simpa [prefixWord, tailWord_3913660, baseEnd_3913660] using wordTrace_append hprefix tailTrace_3913660
  have hstable : (prefixWord ++ tailWord_3913660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913660).length < 2 ^ (prefixWord ++ tailWord_3913660).sum := by decide
  have hdescent : baseEnd_3913660 < baseStart_3913660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913669 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 2, 7]
def baseStart_3913669 : Nat := 118140960795 + 3913669 * 2 ^ 59
def prefixEnd_3913669 : Nat := 4983230072969 + 3 ^ 40 * 3913669 * 2
def baseEnd_3913669 : Nat := 1339728879734102323825913

theorem tailTrace_3913669 : CollatzResearch.WordTrace tailWord_3913669 prefixEnd_3913669 1339728879734102323825913 := by
  unfold tailWord_3913669
  simp only [CollatzResearch.WordTrace]
  refine ⟨142743235258453089296152061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95162156838968726197434707 142743235258453089296152061)
  ·
    refine ⟨53528713221919908486057023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142743235258453089296152061 53528713221919908486057023)
    ·
      refine ⟨80293069832879862729085535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53528713221919908486057023 80293069832879862729085535)
      ·
        refine ⟨120439604749319794093628303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80293069832879862729085535 120439604749319794093628303)
        ·
          refine ⟨180659407123979691140442455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120439604749319794093628303 180659407123979691140442455)
          ·
            refine ⟨270989110685969536710663683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180659407123979691140442455 270989110685969536710663683)
            ·
              refine ⟨406483666028954305065995525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270989110685969536710663683 406483666028954305065995525)
              ·
                refine ⟨76215687380428932199874161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 406483666028954305065995525 76215687380428932199874161)
                ·
                  refine ⟨57161765535321699149905621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76215687380428932199874161 57161765535321699149905621)
                  ·
                    refine ⟨1339728879734102323825913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57161765535321699149905621 1339728879734102323825913)
                    ·
                      rfl

theorem cell22_3913669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_3913669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3913669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3913669 prefixEnd_3913669 := by exact prefixLift 3913669
  have htrace : WordTrace (prefixWord ++ tailWord_3913669) baseStart_3913669 baseEnd_3913669 := by
    simpa [prefixWord, tailWord_3913669, baseEnd_3913669] using wordTrace_append hprefix tailTrace_3913669
  have hstable : (prefixWord ++ tailWord_3913669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913669).length < 2 ^ (prefixWord ++ tailWord_3913669).sum := by decide
  have hdescent : baseEnd_3913669 < baseStart_3913669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913692 : List Nat := [2, 2, 6, 1, 1, 1, 1, 2, 1, 5]
def baseStart_3913692 : Nat := 118140960795 + 3913692 * 2 ^ 59
def prefixEnd_3913692 : Nat := 4983230072969 + 3 ^ 40 * 3913692 * 2
def baseEnd_3913692 : Nat := 1339736753104137930500843

theorem tailTrace_3913692 : CollatzResearch.WordTrace tailWord_3913692 prefixEnd_3913692 1339736753104137930500843 := by
  unfold tailWord_3913692
  simp only [CollatzResearch.WordTrace]
  refine ⟨71372037068684882112119665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95162716091579842816159553 71372037068684882112119665)
  ·
    refine ⟨53529027801513661584089749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71372037068684882112119665 53529027801513661584089749)
    ·
      refine ⟨2509173178195952886754207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53529027801513661584089749 2509173178195952886754207)
      ·
        refine ⟨3763759767293929330131311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2509173178195952886754207 3763759767293929330131311)
        ·
          refine ⟨5645639650940893995196967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3763759767293929330131311 5645639650940893995196967)
          ·
            refine ⟨8468459476411340992795451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5645639650940893995196967 8468459476411340992795451)
            ·
              refine ⟨12702689214617011489193177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8468459476411340992795451 12702689214617011489193177)
              ·
                refine ⟨9527016910962758616894883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12702689214617011489193177 9527016910962758616894883)
                ·
                  refine ⟨14290525366444137925342325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9527016910962758616894883 14290525366444137925342325)
                  ·
                    refine ⟨1339736753104137930500843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14290525366444137925342325 1339736753104137930500843)
                    ·
                      rfl

theorem cell22_3913692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_3913692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3913692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3913692 prefixEnd_3913692 := by exact prefixLift 3913692
  have htrace : WordTrace (prefixWord ++ tailWord_3913692) baseStart_3913692 baseEnd_3913692 := by
    simpa [prefixWord, tailWord_3913692, baseEnd_3913692] using wordTrace_append hprefix tailTrace_3913692
  have hstable : (prefixWord ++ tailWord_3913692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913692).length < 2 ^ (prefixWord ++ tailWord_3913692).sum := by decide
  have hdescent : baseEnd_3913692 < baseStart_3913692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913741 : List Nat := [1, 7, 1, 2, 2, 1, 1, 1, 2, 4]
def baseStart_3913741 : Nat := 118140960795 + 3913741 * 2 ^ 59
def prefixEnd_3913741 : Nat := 4983230072969 + 3 ^ 40 * 3913741 * 2
def baseEnd_3913741 : Nat := 1339753526805518136025693

theorem tailTrace_3913741 : CollatzResearch.WordTrace tailWord_3913741 prefixEnd_3913741 1339753526805518136025693 := by
  unfold tailWord_3913741
  simp only [CollatzResearch.WordTrace]
  refine ⟨142745861314192245592773077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95163907542794830395182051 142745861314192245592773077)
  ·
    refine ⟨3345606124551380756080619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 142745861314192245592773077 3345606124551380756080619)
    ·
      refine ⟨5018409186827071134120929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3345606124551380756080619 5018409186827071134120929)
      ·
        refine ⟨3763806890120303350590697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5018409186827071134120929 3763806890120303350590697)
        ·
          refine ⟨2822855167590227512943023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3763806890120303350590697 2822855167590227512943023)
          ·
            refine ⟨4234282751385341269414535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2822855167590227512943023 4234282751385341269414535)
            ·
              refine ⟨6351424127078011904121803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4234282751385341269414535 6351424127078011904121803)
              ·
                refine ⟨9527136190617017856182705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6351424127078011904121803 9527136190617017856182705)
                ·
                  refine ⟨7145352142962763392137029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9527136190617017856182705 7145352142962763392137029)
                  ·
                    refine ⟨1339753526805518136025693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7145352142962763392137029 1339753526805518136025693)
                    ·
                      rfl

theorem cell22_3913741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_3913741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3913741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3913741 prefixEnd_3913741 := by exact prefixLift 3913741
  have htrace : WordTrace (prefixWord ++ tailWord_3913741) baseStart_3913741 baseEnd_3913741 := by
    simpa [prefixWord, tailWord_3913741, baseEnd_3913741] using wordTrace_append hprefix tailTrace_3913741
  have hstable : (prefixWord ++ tailWord_3913741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913741).length < 2 ^ (prefixWord ++ tailWord_3913741).sum := by decide
  have hdescent : baseEnd_3913741 < baseStart_3913741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913763 : List Nat := [1, 1, 1, 4, 3, 1, 3, 3, 1, 4]
def baseStart_3913763 : Nat := 118140960795 + 3913763 * 2 ^ 59
def prefixEnd_3913763 : Nat := 4983230072969 + 3 ^ 40 * 3913763 * 2
def baseEnd_3913763 : Nat := 1339761057855117411975625

theorem tailTrace_3913763 : CollatzResearch.WordTrace tailWord_3913763 prefixEnd_3913763 1339761057855117411975625 := by
  unfold tailWord_3913763
  simp only [CollatzResearch.WordTrace]
  refine ⟨142746663720112543350073943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95164442480075028900049295 142746663720112543350073943)
  ·
    refine ⟨214119995580168815025110915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142746663720112543350073943 214119995580168815025110915)
    ·
      refine ⟨321179993370253222537666373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214119995580168815025110915 321179993370253222537666373)
      ·
        refine ⟨60221248756922479225812445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 321179993370253222537666373 60221248756922479225812445)
        ·
          refine ⟨22582968283845929709679667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60221248756922479225812445 22582968283845929709679667)
          ·
            refine ⟨33874452425768894564519501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22582968283845929709679667 33874452425768894564519501)
            ·
              refine ⟨12702919659663335461694813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33874452425768894564519501 12702919659663335461694813)
              ·
                refine ⟨4763594872373750798135555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12702919659663335461694813 4763594872373750798135555)
                ·
                  refine ⟨7145392308560626197203333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4763594872373750798135555 7145392308560626197203333)
                  ·
                    refine ⟨1339761057855117411975625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7145392308560626197203333 1339761057855117411975625)
                    ·
                      rfl

theorem cell22_3913763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 4].length) (baseStart_3913763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3913763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3913763 prefixEnd_3913763 := by exact prefixLift 3913763
  have htrace : WordTrace (prefixWord ++ tailWord_3913763) baseStart_3913763 baseEnd_3913763 := by
    simpa [prefixWord, tailWord_3913763, baseEnd_3913763] using wordTrace_append hprefix tailTrace_3913763
  have hstable : (prefixWord ++ tailWord_3913763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913763).length < 2 ^ (prefixWord ++ tailWord_3913763).sum := by decide
  have hdescent : baseEnd_3913763 < baseStart_3913763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913767 : List Nat := [1, 1, 7, 1, 2, 2, 1, 2, 5]
def baseStart_3913767 : Nat := 118140960795 + 3913767 * 2 ^ 59
def prefixEnd_3913767 : Nat := 4983230072969 + 3 ^ 40 * 3913767 * 2
def baseEnd_3913767 : Nat := 446587475712287578291871

theorem tailTrace_3913767 : CollatzResearch.WordTrace tailWord_3913767 prefixEnd_3913767 446587475712287578291871 := by
  unfold tailWord_3913767
  simp only [CollatzResearch.WordTrace]
  refine ⟨142746809612098052033219555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95164539741398701355479703 142746809612098052033219555)
  ·
    refine ⟨214120214418147078049829333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142746809612098052033219555 214120214418147078049829333)
    ·
      refine ⟨5018442525425322141792875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 214120214418147078049829333 5018442525425322141792875)
      ·
        refine ⟨7527663788137983212689313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5018442525425322141792875 7527663788137983212689313)
        ·
          refine ⟨5645747841103487409516985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7527663788137983212689313 5645747841103487409516985)
          ·
            refine ⟨4234310880827615557137739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5645747841103487409516985 4234310880827615557137739)
            ·
              refine ⟨6351466321241423335706609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4234310880827615557137739 6351466321241423335706609)
              ·
                refine ⟨4763599740931067501779957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6351466321241423335706609 4763599740931067501779957)
                ·
                  refine ⟨446587475712287578291871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4763599740931067501779957 446587475712287578291871)
                  ·
                    rfl

theorem cell22_3913767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 5].length) (baseStart_3913767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3913767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3913767 prefixEnd_3913767 := by exact prefixLift 3913767
  have htrace : WordTrace (prefixWord ++ tailWord_3913767) baseStart_3913767 baseEnd_3913767 := by
    simpa [prefixWord, tailWord_3913767, baseEnd_3913767] using wordTrace_append hprefix tailTrace_3913767
  have hstable : (prefixWord ++ tailWord_3913767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913767).length < 2 ^ (prefixWord ++ tailWord_3913767).sum := by decide
  have hdescent : baseEnd_3913767 < baseStart_3913767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913778 : List Nat := [3, 2, 1, 1, 2, 4, 2, 1, 6]
def baseStart_3913778 : Nat := 118140960795 + 3913778 * 2 ^ 59
def prefixEnd_3913778 : Nat := 4983230072969 + 3 ^ 40 * 3913778 * 2
def baseEnd_3913778 : Nat := 446588730887220790950193

theorem tailTrace_3913778 : CollatzResearch.WordTrace tailWord_3913778 prefixEnd_3913778 446588730887220790950193 := by
  unfold tailWord_3913778
  simp only [CollatzResearch.WordTrace]
  refine ⟨35686802703764550227967497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95164807210038800607913325 35686802703764550227967497)
  ·
    refine ⟨26765102027823412670975623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35686802703764550227967497 26765102027823412670975623)
    ·
      refine ⟨40147653041735119006463435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26765102027823412670975623 40147653041735119006463435)
      ·
        refine ⟨60221479562602678509695153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40147653041735119006463435 60221479562602678509695153)
        ·
          refine ⟨45166109671952008882271365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60221479562602678509695153 45166109671952008882271365)
          ·
            refine ⟨8468645563491001665425881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45166109671952008882271365 8468645563491001665425881)
            ·
              refine ⟨6351484172618251249069411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8468645563491001665425881 6351484172618251249069411)
              ·
                refine ⟨9527226258927376873604117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6351484172618251249069411 9527226258927376873604117)
                ·
                  refine ⟨446588730887220790950193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9527226258927376873604117 446588730887220790950193)
                  ·
                    rfl

theorem cell22_3913778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_3913778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3913778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3913778 prefixEnd_3913778 := by exact prefixLift 3913778
  have htrace : WordTrace (prefixWord ++ tailWord_3913778) baseStart_3913778 baseEnd_3913778 := by
    simpa [prefixWord, tailWord_3913778, baseEnd_3913778] using wordTrace_append hprefix tailTrace_3913778
  have hstable : (prefixWord ++ tailWord_3913778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913778).length < 2 ^ (prefixWord ++ tailWord_3913778).sum := by decide
  have hdescent : baseEnd_3913778 < baseStart_3913778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913791 : List Nat := [1, 1, 2, 2, 3, 1, 3, 2, 1, 6]
def baseStart_3913791 : Nat := 118140960795 + 3913791 * 2 ^ 59
def prefixEnd_3913791 : Nat := 4983230072969 + 3 ^ 40 * 3913791 * 2
def baseEnd_3913791 : Nat := 1339770642827334672275539

theorem tailTrace_3913791 : CollatzResearch.WordTrace tailWord_3913791 prefixEnd_3913791 1339770642827334672275539 := by
  unfold tailWord_3913791
  simp only [CollatzResearch.WordTrace]
  refine ⟨142747684964011104132093227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95165123309340736088062151 142747684964011104132093227)
  ·
    refine ⟨214121527446016656198139841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142747684964011104132093227 214121527446016656198139841)
    ·
      refine ⟨160591145584512492148604881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214121527446016656198139841 160591145584512492148604881)
      ·
        refine ⟨120443359188384369111453661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160591145584512492148604881 120443359188384369111453661)
        ·
          refine ⟨45166259695644138416795123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120443359188384369111453661 45166259695644138416795123)
          ·
            refine ⟨67749389543466207625192685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45166259695644138416795123 67749389543466207625192685)
            ·
              refine ⟨25406021078799827859447257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67749389543466207625192685 25406021078799827859447257)
              ·
                refine ⟨19054515809099870894585443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25406021078799827859447257 19054515809099870894585443)
                ·
                  refine ⟨28581773713649806341878165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19054515809099870894585443 28581773713649806341878165)
                  ·
                    refine ⟨1339770642827334672275539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28581773713649806341878165 1339770642827334672275539)
                    ·
                      rfl

theorem cell22_3913791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 6].length) (baseStart_3913791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3913791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3913791 prefixEnd_3913791 := by exact prefixLift 3913791
  have htrace : WordTrace (prefixWord ++ tailWord_3913791) baseStart_3913791 baseEnd_3913791 := by
    simpa [prefixWord, tailWord_3913791, baseEnd_3913791] using wordTrace_append hprefix tailTrace_3913791
  have hstable : (prefixWord ++ tailWord_3913791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913791).length < 2 ^ (prefixWord ++ tailWord_3913791).sum := by decide
  have hdescent : baseEnd_3913791 < baseStart_3913791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913885 : List Nat := [1, 4, 2, 1, 1, 4, 2, 2, 5]
def baseStart_3913885 : Nat := 118140960795 + 3913885 * 2 ^ 59
def prefixEnd_3913885 : Nat := 4983230072969 + 3 ^ 40 * 3913885 * 2
def baseEnd_3913885 : Nat := 446600940316116586808417

theorem tailTrace_3913885 : CollatzResearch.WordTrace tailWord_3913885 prefixEnd_3913885 446600940316116586808417 := by
  unfold tailWord_3913885
  simp only [CollatzResearch.WordTrace]
  refine ⟨142751113425670558186015109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95167408950447038790676739 142751113425670558186015109)
  ·
    refine ⟨26765833767313229659877833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142751113425670558186015109 26765833767313229659877833)
    ·
      refine ⟨20074375325484922244908375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26765833767313229659877833 20074375325484922244908375)
      ·
        refine ⟨30111562988227383367362563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20074375325484922244908375 30111562988227383367362563)
        ·
          refine ⟨45167344482341075051043845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30111562988227383367362563 45167344482341075051043845)
          ·
            refine ⟨8468877090438951572070721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45167344482341075051043845 8468877090438951572070721)
            ·
              refine ⟨6351657817829213679053041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8468877090438951572070721 6351657817829213679053041)
              ·
                refine ⟨4763743363371910259289781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6351657817829213679053041 4763743363371910259289781)
                ·
                  refine ⟨446600940316116586808417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4763743363371910259289781 446600940316116586808417)
                  ·
                    rfl

theorem cell22_3913885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_3913885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3913885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3913885 prefixEnd_3913885 := by exact prefixLift 3913885
  have htrace : WordTrace (prefixWord ++ tailWord_3913885) baseStart_3913885 baseEnd_3913885 := by
    simpa [prefixWord, tailWord_3913885, baseEnd_3913885] using wordTrace_append hprefix tailTrace_3913885
  have hstable : (prefixWord ++ tailWord_3913885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913885).length < 2 ^ (prefixWord ++ tailWord_3913885).sum := by decide
  have hdescent : baseEnd_3913885 < baseStart_3913885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913889 : List Nat := [1, 2, 3, 3, 1, 2, 4, 2, 1, 3]
def baseStart_3913889 : Nat := 118140960795 + 3913889 * 2 ^ 59
def prefixEnd_3913889 : Nat := 4983230072969 + 3 ^ 40 * 3913889 * 2
def baseEnd_3913889 : Nat := 1339804190230095083325239

theorem tailTrace_3913889 : CollatzResearch.WordTrace tailWord_3913889 prefixEnd_3913889 1339804190230095083325239 := by
  unfold tailWord_3913889
  simp only [CollatzResearch.WordTrace]
  refine ⟨142751259317656066869160721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95167506211770711246107147 142751259317656066869160721)
  ·
    refine ⟨107063444488242050151870541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142751259317656066869160721 107063444488242050151870541)
    ·
      refine ⟨40148791683090768806951453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107063444488242050151870541 40148791683090768806951453)
      ·
        refine ⟨15055796881159038302606795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40148791683090768806951453 15055796881159038302606795)
        ·
          refine ⟨22583695321738557453910193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15055796881159038302606795 22583695321738557453910193)
          ·
            refine ⟨16937771491303918090432645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22583695321738557453910193 16937771491303918090432645)
            ·
              refine ⟨3175832154619484641956121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16937771491303918090432645 3175832154619484641956121)
              ·
                refine ⟨2381874115964613481467091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3175832154619484641956121 2381874115964613481467091)
                ·
                  refine ⟨3572811173946920222200637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2381874115964613481467091 3572811173946920222200637)
                  ·
                    refine ⟨1339804190230095083325239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3572811173946920222200637 1339804190230095083325239)
                    ·
                      rfl

theorem cell22_3913889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 2, 1, 3].length) (baseStart_3913889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3913889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3913889 prefixEnd_3913889 := by exact prefixLift 3913889
  have htrace : WordTrace (prefixWord ++ tailWord_3913889) baseStart_3913889 baseEnd_3913889 := by
    simpa [prefixWord, tailWord_3913889, baseEnd_3913889] using wordTrace_append hprefix tailTrace_3913889
  have hstable : (prefixWord ++ tailWord_3913889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913889).length < 2 ^ (prefixWord ++ tailWord_3913889).sum := by decide
  have hdescent : baseEnd_3913889 < baseStart_3913889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913913 : List Nat := [1, 2, 1, 4, 1, 2, 3, 2, 6]
def baseStart_3913913 : Nat := 118140960795 + 3913913 * 2 ^ 59
def prefixEnd_3913913 : Nat := 4983230072969 + 3 ^ 40 * 3913913 * 2
def baseEnd_3913913 : Nat := 446604135306855673575055

theorem tailTrace_3913913 : CollatzResearch.WordTrace tailWord_3913913 prefixEnd_3913913 446604135306855673575055 := by
  unfold tailWord_3913913
  simp only [CollatzResearch.WordTrace]
  refine ⟨142752134669569118968034393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95168089779712745978689595 142752134669569118968034393)
  ·
    refine ⟨107064101002176839226025795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142752134669569118968034393 107064101002176839226025795)
    ·
      refine ⟨160596151503265258839038693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107064101002176839226025795 160596151503265258839038693)
      ·
        refine ⟨30111778406862236032319755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160596151503265258839038693 30111778406862236032319755)
        ·
          refine ⟨45167667610293354048479633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30111778406862236032319755 45167667610293354048479633)
          ·
            refine ⟨33875750707720015536359725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45167667610293354048479633 33875750707720015536359725)
            ·
              refine ⟨12703406515395005826134897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33875750707720015536359725 12703406515395005826134897)
              ·
                refine ⟨9527554886546254369601173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12703406515395005826134897 9527554886546254369601173)
                ·
                  refine ⟨446604135306855673575055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9527554886546254369601173 446604135306855673575055)
                  ·
                    rfl

theorem cell22_3913913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 6].length) (baseStart_3913913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3913913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3913913 prefixEnd_3913913 := by exact prefixLift 3913913
  have htrace : WordTrace (prefixWord ++ tailWord_3913913) baseStart_3913913 baseEnd_3913913 := by
    simpa [prefixWord, tailWord_3913913, baseEnd_3913913] using wordTrace_append hprefix tailTrace_3913913
  have hstable : (prefixWord ++ tailWord_3913913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913913).length < 2 ^ (prefixWord ++ tailWord_3913913).sum := by decide
  have hdescent : baseEnd_3913913 < baseStart_3913913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913943 : List Nat := [1, 1, 3, 2, 1, 2, 1, 3, 4, 4]
def baseStart_3913943 : Nat := 118140960795 + 3913943 * 2 ^ 59
def prefixEnd_3913943 : Nat := 4983230072969 + 3 ^ 40 * 3913943 * 2
def baseEnd_3913943 : Nat := 1339822675533656942475073

theorem tailTrace_3913943 : CollatzResearch.WordTrace tailWord_3913943 prefixEnd_3913943 1339822675533656942475073 := by
  unfold tailWord_3913943
  simp only [CollatzResearch.WordTrace]
  refine ⟨142753228859460434091626483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95168819239640289394417655 142753228859460434091626483)
  ·
    refine ⟨214129843289190651137439725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142753228859460434091626483 214129843289190651137439725)
    ·
      refine ⟨80298691233446494176539897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214129843289190651137439725 80298691233446494176539897)
      ·
        refine ⟨60224018425084870632404923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80298691233446494176539897 60224018425084870632404923)
        ·
          refine ⟨90336027637627305948607385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60224018425084870632404923 90336027637627305948607385)
          ·
            refine ⟨67752020728220479461455539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90336027637627305948607385 67752020728220479461455539)
            ·
              refine ⟨101628031092330719192183309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67752020728220479461455539 101628031092330719192183309)
              ·
                refine ⟨38110511659624019697068741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101628031092330719192183309 38110511659624019697068741)
                ·
                  refine ⟨7145720936179503693200389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38110511659624019697068741 7145720936179503693200389)
                  ·
                    refine ⟨1339822675533656942475073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7145720936179503693200389 1339822675533656942475073)
                    ·
                      rfl

theorem cell22_3913943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_3913943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3913943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3913943 prefixEnd_3913943 := by exact prefixLift 3913943
  have htrace : WordTrace (prefixWord ++ tailWord_3913943) baseStart_3913943 baseEnd_3913943 := by
    simpa [prefixWord, tailWord_3913943, baseEnd_3913943] using wordTrace_append hprefix tailTrace_3913943
  have hstable : (prefixWord ++ tailWord_3913943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913943).length < 2 ^ (prefixWord ++ tailWord_3913943).sum := by decide
  have hdescent : baseEnd_3913943 < baseStart_3913943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914007 : List Nat := [1, 1, 3, 4, 1, 2, 3, 1, 3, 3]
def baseStart_3914007 : Nat := 118140960795 + 3914007 * 2 ^ 59
def prefixEnd_3914007 : Nat := 4983230072969 + 3 ^ 40 * 3914007 * 2
def baseEnd_3914007 : Nat := 1339844584041582108874877

theorem tailTrace_3914007 : CollatzResearch.WordTrace tailWord_3914007 prefixEnd_3914007 1339844584041582108874877 := by
  unfold tailWord_3914007
  simp only [CollatzResearch.WordTrace]
  refine ⟨142755563131228573021956275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95170375420819048681304183 142755563131228573021956275)
  ·
    refine ⟨214133344696842859532934413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142755563131228573021956275 214133344696842859532934413)
    ·
      refine ⟨80300004261316072324850405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214133344696842859532934413 80300004261316072324850405)
      ·
        refine ⟨15056250798996763560909451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80300004261316072324850405 15056250798996763560909451)
        ·
          refine ⟨22584376198495145341364177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15056250798996763560909451 22584376198495145341364177)
          ·
            refine ⟨16938282148871359006023133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22584376198495145341364177 16938282148871359006023133)
            ·
              refine ⟨6351855805826759627258675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16938282148871359006023133 6351855805826759627258675)
              ·
                refine ⟨9527783708740139440888013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6351855805826759627258675 9527783708740139440888013)
                ·
                  refine ⟨3572918890777552290333005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9527783708740139440888013 3572918890777552290333005)
                  ·
                    refine ⟨1339844584041582108874877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3572918890777552290333005 1339844584041582108874877)
                    ·
                      rfl

theorem cell22_3914007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 3, 3].length) (baseStart_3914007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914007 prefixEnd_3914007 := by exact prefixLift 3914007
  have htrace : WordTrace (prefixWord ++ tailWord_3914007) baseStart_3914007 baseEnd_3914007 := by
    simpa [prefixWord, tailWord_3914007, baseEnd_3914007] using wordTrace_append hprefix tailTrace_3914007
  have hstable : (prefixWord ++ tailWord_3914007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914007).length < 2 ^ (prefixWord ++ tailWord_3914007).sum := by decide
  have hdescent : baseEnd_3914007 < baseStart_3914007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914013 : List Nat := [1, 4, 2, 3, 3, 1, 2, 1, 2, 3]
def baseStart_3914013 : Nat := 118140960795 + 3914013 * 2 ^ 59
def prefixEnd_3914013 : Nat := 4983230072969 + 3 ^ 40 * 3914013 * 2
def baseEnd_3914013 : Nat := 1339846637964200093224859

theorem tailTrace_3914013 : CollatzResearch.WordTrace tailWord_3914013 prefixEnd_3914013 1339846637964200093224859 := by
  unfold tailWord_3914013
  simp only [CollatzResearch.WordTrace]
  refine ⟨142755781969206836046674693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95170521312804557364449795 142755781969206836046674693)
  ·
    refine ⟨26766709119226281758751505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142755781969206836046674693 26766709119226281758751505)
    ·
      refine ⟨20075031839419711319063629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26766709119226281758751505 20075031839419711319063629)
      ·
        refine ⟨7528136939782391744648861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20075031839419711319063629 7528136939782391744648861)
        ·
          refine ⟨2823051352418396904243323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7528136939782391744648861 2823051352418396904243323)
          ·
            refine ⟨4234577028627595356364985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2823051352418396904243323 4234577028627595356364985)
            ·
              refine ⟨3175932771470696517273739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4234577028627595356364985 3175932771470696517273739)
              ·
                refine ⟨4763899157206044775910609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3175932771470696517273739 4763899157206044775910609)
                ·
                  refine ⟨3572924367904533581932957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4763899157206044775910609 3572924367904533581932957)
                  ·
                    refine ⟨1339846637964200093224859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3572924367904533581932957 1339846637964200093224859)
                    ·
                      rfl

theorem cell22_3914013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_3914013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914013 prefixEnd_3914013 := by exact prefixLift 3914013
  have htrace : WordTrace (prefixWord ++ tailWord_3914013) baseStart_3914013 baseEnd_3914013 := by
    simpa [prefixWord, tailWord_3914013, baseEnd_3914013] using wordTrace_append hprefix tailTrace_3914013
  have hstable : (prefixWord ++ tailWord_3914013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914013).length < 2 ^ (prefixWord ++ tailWord_3914013).sum := by decide
  have hdescent : baseEnd_3914013 < baseStart_3914013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914048 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 10]
def baseStart_3914048 : Nat := 118140960795 + 3914048 * 2 ^ 59
def prefixEnd_3914048 : Nat := 4983230072969 + 3 ^ 40 * 3914048 * 2
def baseEnd_3914048 : Nat := 446619539726490556199917

theorem tailTrace_3914048 : CollatzResearch.WordTrace tailWord_3914048 prefixEnd_3914048 446619539726490556199917 := by
  unfold tailWord_3914048
  simp only [CollatzResearch.WordTrace]
  refine ⟨71378529262040018512099399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95171372349386691349465865 71378529262040018512099399)
  ·
    refine ⟨107067793893060027768149099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71378529262040018512099399 107067793893060027768149099)
    ·
      refine ⟨160601690839590041652223649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107067793893060027768149099 160601690839590041652223649)
      ·
        refine ⟨120451268129692531239167737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160601690839590041652223649 120451268129692531239167737)
        ·
          refine ⟨90338451097269398429375803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120451268129692531239167737 90338451097269398429375803)
          ·
            refine ⟨135507676645904097644063705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90338451097269398429375803 135507676645904097644063705)
            ·
              refine ⟨101630757484428073233047779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135507676645904097644063705 101630757484428073233047779)
              ·
                refine ⟨152446136226642109849571669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101630757484428073233047779 152446136226642109849571669)
                ·
                  refine ⟨446619539726490556199917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 152446136226642109849571669 446619539726490556199917)
                  ·
                    rfl

theorem cell22_3914048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 10].length) (baseStart_3914048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914048 prefixEnd_3914048 := by exact prefixLift 3914048
  have htrace : WordTrace (prefixWord ++ tailWord_3914048) baseStart_3914048 baseEnd_3914048 := by
    simpa [prefixWord, tailWord_3914048, baseEnd_3914048] using wordTrace_append hprefix tailTrace_3914048
  have hstable : (prefixWord ++ tailWord_3914048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914048).length < 2 ^ (prefixWord ++ tailWord_3914048).sum := by decide
  have hdescent : baseEnd_3914048 < baseStart_3914048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914082 : List Nat := [3, 3, 2, 1, 1, 3, 1, 2, 6]
def baseStart_3914082 : Nat := 118140960795 + 3914082 * 2 ^ 59
def prefixEnd_3914082 : Nat := 4983230072969 + 3 ^ 40 * 3914082 * 2
def baseEnd_3914082 : Nat := 446623419358102304416549

theorem tailTrace_3914082 : CollatzResearch.WordTrace tailWord_3914082 prefixEnd_3914082 446623419358102304416549 := by
  unfold tailWord_3914082
  simp only [CollatzResearch.WordTrace]
  refine ⟨35689574651489215207734125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95172199070637907220624333 35689574651489215207734125)
  ·
    refine ⟨13383590494308455702900297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35689574651489215207734125 13383590494308455702900297)
    ·
      refine ⟨10037692870731341777175223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13383590494308455702900297 10037692870731341777175223)
      ·
        refine ⟨15056539306097012665762835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10037692870731341777175223 15056539306097012665762835)
        ·
          refine ⟨22584808959145518998644253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15056539306097012665762835 22584808959145518998644253)
          ·
            refine ⟨8469303359679569624491595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22584808959145518998644253 8469303359679569624491595)
            ·
              refine ⟨12703955039519354436737393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8469303359679569624491595 12703955039519354436737393)
              ·
                refine ⟨9527966279639515827553045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12703955039519354436737393 9527966279639515827553045)
                ·
                  refine ⟨446623419358102304416549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9527966279639515827553045 446623419358102304416549)
                  ·
                    rfl

theorem cell22_3914082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_3914082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914082 prefixEnd_3914082 := by exact prefixLift 3914082
  have htrace : WordTrace (prefixWord ++ tailWord_3914082) baseStart_3914082 baseEnd_3914082 := by
    simpa [prefixWord, tailWord_3914082, baseEnd_3914082] using wordTrace_append hprefix tailTrace_3914082
  have hstable : (prefixWord ++ tailWord_3914082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914082).length < 2 ^ (prefixWord ++ tailWord_3914082).sum := by decide
  have hdescent : baseEnd_3914082 < baseStart_3914082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914095 : List Nat := [1, 1, 2, 1, 3, 1, 2, 5, 2, 4]
def baseStart_3914095 : Nat := 118140960795 + 3914095 * 2 ^ 59
def prefixEnd_3914095 : Nat := 4983230072969 + 3 ^ 40 * 3914095 * 2
def baseEnd_3914095 : Nat := 1339874708239979212674607

theorem tailTrace_3914095 : CollatzResearch.WordTrace tailWord_3914095 prefixEnd_3914095 1339874708239979212674607 := by
  unfold tailWord_3914095
  simp only [CollatzResearch.WordTrace]
  refine ⟨142758772754909764051159739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95172515169939842700773159 142758772754909764051159739)
  ·
    refine ⟨214138159132364646076739609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142758772754909764051159739 214138159132364646076739609)
    ·
      refine ⟨160603619349273484557554707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214138159132364646076739609 160603619349273484557554707)
      ·
        refine ⟨240905429023910226836332061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160603619349273484557554707 240905429023910226836332061)
        ·
          refine ⟨90339535883966335063624523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240905429023910226836332061 90339535883966335063624523)
          ·
            refine ⟨135509303825949502595436785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90339535883966335063624523 135509303825949502595436785)
            ·
              refine ⟨101631977869462126946577589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135509303825949502595436785 101631977869462126946577589)
              ·
                refine ⟨9527997925262074401241649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101631977869462126946577589 9527997925262074401241649)
                ·
                  refine ⟨7145998443946555800931237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9527997925262074401241649 7145998443946555800931237)
                  ·
                    refine ⟨1339874708239979212674607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7145998443946555800931237 1339874708239979212674607)
                    ·
                      rfl

theorem cell22_3914095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 4].length) (baseStart_3914095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914095 prefixEnd_3914095 := by exact prefixLift 3914095
  have htrace : WordTrace (prefixWord ++ tailWord_3914095) baseStart_3914095 baseEnd_3914095 := by
    simpa [prefixWord, tailWord_3914095, baseEnd_3914095] using wordTrace_append hprefix tailTrace_3914095
  have hstable : (prefixWord ++ tailWord_3914095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914095).length < 2 ^ (prefixWord ++ tailWord_3914095).sum := by decide
  have hdescent : baseEnd_3914095 < baseStart_3914095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914101 : List Nat := [1, 3, 4, 1, 2, 3, 2, 1, 1, 4]
def baseStart_3914101 : Nat := 118140960795 + 3914101 * 2 ^ 59
def prefixEnd_3914101 : Nat := 4983230072969 + 3 ^ 40 * 3914101 * 2
def baseEnd_3914101 : Nat := 1339876762162597197024589

theorem tailTrace_3914101 : CollatzResearch.WordTrace tailWord_3914101 prefixEnd_3914101 1339876762162597197024589 := by
  unfold tailWord_3914101
  simp only [CollatzResearch.WordTrace]
  refine ⟨142758991592888027075878157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95172661061925351383918771 142758991592888027075878157)
  ·
    refine ⟨53534621847333010153454309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142758991592888027075878157 53534621847333010153454309)
    ·
      refine ⟨10037741596374939403772683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53534621847333010153454309 10037741596374939403772683)
      ·
        refine ⟨15056612394562409105659025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10037741596374939403772683 15056612394562409105659025)
        ·
          refine ⟨11292459295921806829244269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15056612394562409105659025 11292459295921806829244269)
          ·
            refine ⟨4234672235970677560966601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11292459295921806829244269 4234672235970677560966601)
            ·
              refine ⟨3176004176978008170724951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4234672235970677560966601 3176004176978008170724951)
              ·
                refine ⟨4764006265467012256087427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3176004176978008170724951 4764006265467012256087427)
                ·
                  refine ⟨7146009398200518384131141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4764006265467012256087427 7146009398200518384131141)
                  ·
                    refine ⟨1339876762162597197024589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7146009398200518384131141 1339876762162597197024589)
                    ·
                      rfl

theorem cell22_3914101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_3914101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914101 prefixEnd_3914101 := by exact prefixLift 3914101
  have htrace : WordTrace (prefixWord ++ tailWord_3914101) baseStart_3914101 baseEnd_3914101 := by
    simpa [prefixWord, tailWord_3914101, baseEnd_3914101] using wordTrace_append hprefix tailTrace_3914101
  have hstable : (prefixWord ++ tailWord_3914101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914101).length < 2 ^ (prefixWord ++ tailWord_3914101).sum := by decide
  have hdescent : baseEnd_3914101 < baseStart_3914101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914170 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 4, 5]
def baseStart_3914170 : Nat := 118140960795 + 3914170 * 2 ^ 59
def prefixEnd_3914170 : Nat := 4983230072969 + 3 ^ 40 * 3914170 * 2
def baseEnd_3914170 : Nat := 1339900382272704017049377

theorem tailTrace_3914170 : CollatzResearch.WordTrace tailWord_3914170 prefixEnd_3914170 1339900382272704017049377 := by
  unfold tailWord_3914170
  simp only [CollatzResearch.WordTrace]
  refine ⟨35690377057409512965034991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95174338819758701240093309 35690377057409512965034991)
  ·
    refine ⟨53535565586114269447552487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35690377057409512965034991 53535565586114269447552487)
    ·
      refine ⟨80303348379171404171328731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53535565586114269447552487 80303348379171404171328731)
      ·
        refine ⟨120455022568757106256993097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80303348379171404171328731 120455022568757106256993097)
        ·
          refine ⟨90341266926567829692744823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120455022568757106256993097 90341266926567829692744823)
          ·
            refine ⟨135511900389851744539117235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90341266926567829692744823 135511900389851744539117235)
            ·
              refine ⟨203267850584777616808675853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135511900389851744539117235 203267850584777616808675853)
              ·
                refine ⟨76225443969291606303253445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203267850584777616808675853 76225443969291606303253445)
                ·
                  refine ⟨14292270744242176181860021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76225443969291606303253445 14292270744242176181860021)
                  ·
                    refine ⟨1339900382272704017049377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14292270744242176181860021 1339900382272704017049377)
                    ·
                      rfl

theorem cell22_3914170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_3914170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914170 prefixEnd_3914170 := by exact prefixLift 3914170
  have htrace : WordTrace (prefixWord ++ tailWord_3914170) baseStart_3914170 baseEnd_3914170 := by
    simpa [prefixWord, tailWord_3914170, baseEnd_3914170] using wordTrace_append hprefix tailTrace_3914170
  have hstable : (prefixWord ++ tailWord_3914170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914170).length < 2 ^ (prefixWord ++ tailWord_3914170).sum := by decide
  have hdescent : baseEnd_3914170 < baseStart_3914170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914172 : List Nat := [2, 2, 2, 4, 1, 1, 2, 1, 7]
def baseStart_3914172 : Nat := 118140960795 + 3914172 * 2 ^ 59
def prefixEnd_3914172 : Nat := 4983230072969 + 3 ^ 40 * 3914172 * 2
def baseEnd_3914172 : Nat := 446633688971192226166457

theorem tailTrace_3914172 : CollatzResearch.WordTrace tailWord_3914172 prefixEnd_3914172 446633688971192226166457 := by
  unfold tailWord_3914172
  simp only [CollatzResearch.WordTrace]
  refine ⟨71380790587815403100856385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95174387450420537467808513 71380790587815403100856385)
  ·
    refine ⟨53535592940861552325642289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71380790587815403100856385 53535592940861552325642289)
    ·
      refine ⟨40151694705646164244231717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53535592940861552325642289 40151694705646164244231717)
      ·
        refine ⟨7528442757308655795793447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40151694705646164244231717 7528442757308655795793447)
        ·
          refine ⟨11292664135962983693690171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7528442757308655795793447 11292664135962983693690171)
          ·
            refine ⟨16938996203944475540535257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11292664135962983693690171 16938996203944475540535257)
            ·
              refine ⟨12704247152958356655401443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16938996203944475540535257 12704247152958356655401443)
              ·
                refine ⟨19056370729437534983102165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12704247152958356655401443 19056370729437534983102165)
                ·
                  refine ⟨446633688971192226166457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19056370729437534983102165 446633688971192226166457)
                  ·
                    rfl

theorem cell22_3914172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 7].length) (baseStart_3914172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914172 prefixEnd_3914172 := by exact prefixLift 3914172
  have htrace : WordTrace (prefixWord ++ tailWord_3914172) baseStart_3914172 baseEnd_3914172 := by
    simpa [prefixWord, tailWord_3914172, baseEnd_3914172] using wordTrace_append hprefix tailTrace_3914172
  have hstable : (prefixWord ++ tailWord_3914172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914172).length < 2 ^ (prefixWord ++ tailWord_3914172).sum := by decide
  have hdescent : baseEnd_3914172 < baseStart_3914172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914200 : List Nat := [2, 1, 2, 2, 2, 1, 1, 3, 8]
def baseStart_3914200 : Nat := 118140960795 + 3914200 * 2 ^ 59
def prefixEnd_3914200 : Nat := 4983230072969 + 3 ^ 40 * 3914200 * 2
def baseEnd_3914200 : Nat := 446636883961931312933095

theorem tailTrace_3914200 : CollatzResearch.WordTrace tailWord_3914200 prefixEnd_3914200 446636883961931312933095 := by
  unfold tailWord_3914200
  simp only [CollatzResearch.WordTrace]
  refine ⟨71381301209764683491866027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95175068279686244655821369 71381301209764683491866027)
  ·
    refine ⟨107071951814647025237799041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71381301209764683491866027 107071951814647025237799041)
    ·
      refine ⟨80303963860985268928349281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107071951814647025237799041 80303963860985268928349281)
      ·
        refine ⟨60227972895738951696261961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80303963860985268928349281 60227972895738951696261961)
        ·
          refine ⟨45170979671804213772196471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60227972895738951696261961 45170979671804213772196471)
          ·
            refine ⟨67756469507706320658294707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45170979671804213772196471 67756469507706320658294707)
            ·
              refine ⟨101634704261559480987442061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67756469507706320658294707 101634704261559480987442061)
              ·
                refine ⟨38113014098084805370290773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101634704261559480987442061 38113014098084805370290773)
                ·
                  refine ⟨446636883961931312933095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38113014098084805370290773 446636883961931312933095)
                  ·
                    rfl

theorem cell22_3914200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 8].length) (baseStart_3914200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914200 prefixEnd_3914200 := by exact prefixLift 3914200
  have htrace : WordTrace (prefixWord ++ tailWord_3914200) baseStart_3914200 baseEnd_3914200 := by
    simpa [prefixWord, tailWord_3914200, baseEnd_3914200] using wordTrace_append hprefix tailTrace_3914200
  have hstable : (prefixWord ++ tailWord_3914200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914200).length < 2 ^ (prefixWord ++ tailWord_3914200).sum := by decide
  have hdescent : baseEnd_3914200 < baseStart_3914200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914202 : List Nat := [3, 1, 1, 2, 3, 1, 3, 1, 3, 4]
def baseStart_3914202 : Nat := 118140960795 + 3914202 * 2 ^ 59
def prefixEnd_3914202 : Nat := 4983230072969 + 3 ^ 40 * 3914202 * 2
def baseEnd_3914202 : Nat := 1339911336526666600249279

theorem tailTrace_3914202 : CollatzResearch.WordTrace tailWord_3914202 prefixEnd_3914202 1339911336526666600249279 := by
  unfold tailWord_3914202
  simp only [CollatzResearch.WordTrace]
  refine ⟨35690668841380530331326215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95175116910348080883536573 35690668841380530331326215)
  ·
    refine ⟨53536003262070795496989323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35690668841380530331326215 53536003262070795496989323)
    ·
      refine ⟨80304004893106193245483985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53536003262070795496989323 80304004893106193245483985)
      ·
        refine ⟨60228003669829644934112989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80304004893106193245483985 60228003669829644934112989)
        ·
          refine ⟨22585501376186116850292371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60228003669829644934112989 22585501376186116850292371)
          ·
            refine ⟨33878252064279175275438557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22585501376186116850292371 33878252064279175275438557)
            ·
              refine ⟨12704344524104690728289459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33878252064279175275438557 12704344524104690728289459)
              ·
                refine ⟨19056516786157036092434189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12704344524104690728289459 19056516786157036092434189)
                ·
                  refine ⟨7146193794808888534662821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19056516786157036092434189 7146193794808888534662821)
                  ·
                    refine ⟨1339911336526666600249279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7146193794808888534662821 1339911336526666600249279)
                    ·
                      rfl

theorem cell22_3914202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_3914202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914202 prefixEnd_3914202 := by exact prefixLift 3914202
  have htrace : WordTrace (prefixWord ++ tailWord_3914202) baseStart_3914202 baseEnd_3914202 := by
    simpa [prefixWord, tailWord_3914202, baseEnd_3914202] using wordTrace_append hprefix tailTrace_3914202
  have hstable : (prefixWord ++ tailWord_3914202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914202).length < 2 ^ (prefixWord ++ tailWord_3914202).sum := by decide
  have hdescent : baseEnd_3914202 < baseStart_3914202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914219 : List Nat := [1, 1, 1, 1, 2, 3, 7, 1, 1, 4]
def baseStart_3914219 : Nat := 118140960795 + 3914219 * 2 ^ 59
def prefixEnd_3914219 : Nat := 4983230072969 + 3 ^ 40 * 3914219 * 2
def baseEnd_3914219 : Nat := 1339917155974084222574227

theorem tailTrace_3914219 : CollatzResearch.WordTrace tailWord_3914219 prefixEnd_3914219 1339917155974084222574227 := by
  unfold tailWord_3914219
  simp only [CollatzResearch.WordTrace]
  refine ⟨142763295406460533228673711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95175530270973688819115807 142763295406460533228673711)
  ·
    refine ⟨214144943109690799843010567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142763295406460533228673711 214144943109690799843010567)
    ·
      refine ⟨321217414664536199764515851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214144943109690799843010567 321217414664536199764515851)
      ·
        refine ⟨481826121996804299646773777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321217414664536199764515851 481826121996804299646773777)
        ·
          refine ⟨361369591497603224735080333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481826121996804299646773777 361369591497603224735080333)
          ·
            refine ⟨135513596811601209275655125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 361369591497603224735080333 135513596811601209275655125)
            ·
              refine ⟨3176099925271903342398167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 135513596811601209275655125 3176099925271903342398167)
              ·
                refine ⟨4764149887907855013597251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3176099925271903342398167 4764149887907855013597251)
                ·
                  refine ⟨7146224831861782520395877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4764149887907855013597251 7146224831861782520395877)
                  ·
                    refine ⟨1339917155974084222574227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7146224831861782520395877 1339917155974084222574227)
                    ·
                      rfl

theorem cell22_3914219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 1, 4].length) (baseStart_3914219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914219 prefixEnd_3914219 := by exact prefixLift 3914219
  have htrace : WordTrace (prefixWord ++ tailWord_3914219) baseStart_3914219 baseEnd_3914219 := by
    simpa [prefixWord, tailWord_3914219, baseEnd_3914219] using wordTrace_append hprefix tailTrace_3914219
  have hstable : (prefixWord ++ tailWord_3914219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914219).length < 2 ^ (prefixWord ++ tailWord_3914219).sum := by decide
  have hdescent : baseEnd_3914219 < baseStart_3914219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3914264 : List Nat := [2, 1, 2, 3, 3, 1, 3, 1, 2, 4]
def baseStart_3914264 : Nat := 118140960795 + 3914264 * 2 ^ 59
def prefixEnd_3914264 : Nat := 4983230072969 + 3 ^ 40 * 3914264 * 2
def baseEnd_3914264 : Nat := 1339932560393719105199089

theorem tailTrace_3914264 : CollatzResearch.WordTrace tailWord_3914264 prefixEnd_3914264 1339932560393719105199089 := by
  unfold tailWord_3914264
  simp only [CollatzResearch.WordTrace]
  refine ⟨71382468345648752957030923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95176624460865003942707897 71382468345648752957030923)
  ·
    refine ⟨107073702518473129435546385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71382468345648752957030923 107073702518473129435546385)
    ·
      refine ⟨80305276888854847076659789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107073702518473129435546385 80305276888854847076659789)
      ·
        refine ⟨30114478833320567653747421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80305276888854847076659789 30114478833320567653747421)
        ·
          refine ⟨11292929562495212870155283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30114478833320567653747421 11292929562495212870155283)
          ·
            refine ⟨16939394343742819305232925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11292929562495212870155283 16939394343742819305232925)
            ·
              refine ⟨6352272878903557239462347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16939394343742819305232925 6352272878903557239462347)
              ·
                refine ⟨9528409318355335859193521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6352272878903557239462347 9528409318355335859193521)
                ·
                  refine ⟨7146306988766501894395141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9528409318355335859193521 7146306988766501894395141)
                  ·
                    refine ⟨1339932560393719105199089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7146306988766501894395141 1339932560393719105199089)
                    ·
                      rfl

theorem cell22_3914264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 2, 4].length) (baseStart_3914264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3914264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3914264 prefixEnd_3914264 := by exact prefixLift 3914264
  have htrace : WordTrace (prefixWord ++ tailWord_3914264) baseStart_3914264 baseEnd_3914264 := by
    simpa [prefixWord, tailWord_3914264, baseEnd_3914264] using wordTrace_append hprefix tailTrace_3914264
  have hstable : (prefixWord ++ tailWord_3914264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3914264).length < 2 ^ (prefixWord ++ tailWord_3914264).sum := by decide
  have hdescent : baseEnd_3914264 < baseStart_3914264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3914264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
