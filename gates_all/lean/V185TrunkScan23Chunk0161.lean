import V185TrunkScan23Chunk0160

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_952211 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 7, 5]
def baseStart_952211 : Nat := 118140960795 + 952211 * 2 ^ 59
def prefixEnd_952211 : Nat := 4983230072969 + 3 ^ 40 * 952211 * 2
def baseEnd_952211 : Nat := 162980642499493067927789

theorem tailTrace_952211 : CollatzResearch.WordTrace tailWord_952211 prefixEnd_952211 162980642499493067927789 := by
  unfold tailWord_952211
  simp only [CollatzResearch.WordTrace]
  refine ⟨34729988353309646536696487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23153325568873097691130991 34729988353309646536696487)
  ·
    refine ⟨52094982529964469805044731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34729988353309646536696487 52094982529964469805044731)
    ·
      refine ⟨78142473794946704707567097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52094982529964469805044731 78142473794946704707567097)
      ·
        refine ⟨58606855346210028530675323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78142473794946704707567097 58606855346210028530675323)
        ·
          refine ⟨87910283019315042796012985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58606855346210028530675323 87910283019315042796012985)
          ·
            refine ⟨65932712264486282097009739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87910283019315042796012985 65932712264486282097009739)
            ·
              refine ⟨98899068396729423145514609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65932712264486282097009739 98899068396729423145514609)
              ·
                refine ⟨74174301297547067359135957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98899068396729423145514609 74174301297547067359135957)
                ·
                  refine ⟨1738460186661259391229749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 74174301297547067359135957 1738460186661259391229749)
                  ·
                    refine ⟨162980642499493067927789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1738460186661259391229749 162980642499493067927789)
                    ·
                      rfl

theorem cell23_952211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 7, 5].length) (baseStart_952211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952211 prefixEnd_952211 := by exact prefixLift 952211
  have htrace : WordTrace (prefixWord ++ tailWord_952211) baseStart_952211 baseEnd_952211 := by
    simpa [prefixWord, tailWord_952211, baseEnd_952211] using wordTrace_append hprefix tailTrace_952211
  have hstable : (prefixWord ++ tailWord_952211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952211).length < 2 ^ (prefixWord ++ tailWord_952211).sum := by decide
  have hdescent : baseEnd_952211 < baseStart_952211 := by decide
  rcases family_descends (prefixWord ++ tailWord_952211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952242 : List Nat := [3, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3]
def baseStart_952242 : Nat := 118140960795 + 952242 * 2 ^ 59
def prefixEnd_952242 : Nat := 4983230072969 + 3 ^ 40 * 952242 * 2
def baseEnd_952242 : Nat := 488957845398768582495725

theorem tailTrace_952242 : CollatzResearch.WordTrace tailWord_952242 prefixEnd_952242 488957845398768582495725 := by
  unfold tailWord_952242
  simp only [CollatzResearch.WordTrace]
  refine ⟨8682779754049334707768745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23154079344131559220716653 8682779754049334707768745)
  ·
    refine ⟨6512084815537001030826559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8682779754049334707768745 6512084815537001030826559)
    ·
      refine ⟨9768127223305501546239839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6512084815537001030826559 9768127223305501546239839)
      ·
        refine ⟨14652190834958252319359759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9768127223305501546239839 14652190834958252319359759)
        ·
          refine ⟨21978286252437378479039639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14652190834958252319359759 21978286252437378479039639)
          ·
            refine ⟨32967429378656067718559459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21978286252437378479039639 32967429378656067718559459)
            ·
              refine ⟨49451144067984101577839189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32967429378656067718559459 49451144067984101577839189)
              ·
                refine ⟨579505594546688690365303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 49451144067984101577839189 579505594546688690365303)
                ·
                  refine ⟨869258391820033035547955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 579505594546688690365303 869258391820033035547955)
                  ·
                    refine ⟨1303887587730049553321933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 869258391820033035547955 1303887587730049553321933)
                    ·
                      refine ⟨488957845398768582495725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1303887587730049553321933 488957845398768582495725)
                      ·
                        rfl

theorem cell23_952242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3].length) (baseStart_952242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952242 prefixEnd_952242 := by exact prefixLift 952242
  have htrace : WordTrace (prefixWord ++ tailWord_952242) baseStart_952242 baseEnd_952242 := by
    simpa [prefixWord, tailWord_952242, baseEnd_952242] using wordTrace_append hprefix tailTrace_952242
  have hstable : (prefixWord ++ tailWord_952242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952242).length < 2 ^ (prefixWord ++ tailWord_952242).sum := by decide
  have hdescent : baseEnd_952242 < baseStart_952242 := by decide
  rcases family_descends (prefixWord ++ tailWord_952242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952248 : List Nat := [2, 1, 2, 1, 2, 3, 2, 2, 3, 1, 4]
def baseStart_952248 : Nat := 118140960795 + 952248 * 2 ^ 59
def prefixEnd_952248 : Nat := 4983230072969 + 3 ^ 40 * 952248 * 2
def baseEnd_952248 : Nat := 488960926282695559020697

theorem tailTrace_952248 : CollatzResearch.WordTrace tailWord_952248 prefixEnd_952248 488960926282695559020697 := by
  unfold tailWord_952248
  simp only [CollatzResearch.WordTrace]
  refine ⟨17365668927087800927896699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23154225236117067903862265 17365668927087800927896699)
  ·
    refine ⟨26048503390631701391845049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17365668927087800927896699 26048503390631701391845049)
    ·
      refine ⟨19536377542973776043883787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26048503390631701391845049 19536377542973776043883787)
      ·
        refine ⟨29304566314460664065825681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19536377542973776043883787 29304566314460664065825681)
        ·
          refine ⟨21978424735845498049369261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29304566314460664065825681 21978424735845498049369261)
          ·
            refine ⟨8241909275942061768513473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21978424735845498049369261 8241909275942061768513473)
            ·
              refine ⟨6181431956956546326385105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8241909275942061768513473 6181431956956546326385105)
              ·
                refine ⟨4636073967717409744788829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6181431956956546326385105 4636073967717409744788829)
                ·
                  refine ⟨1738527737894028654295811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4636073967717409744788829 1738527737894028654295811)
                  ·
                    refine ⟨2607791606841042981443717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1738527737894028654295811 2607791606841042981443717)
                    ·
                      refine ⟨488960926282695559020697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2607791606841042981443717 488960926282695559020697)
                      ·
                        rfl

theorem cell23_952248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 3, 1, 4].length) (baseStart_952248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952248 prefixEnd_952248 := by exact prefixLift 952248
  have htrace : WordTrace (prefixWord ++ tailWord_952248) baseStart_952248 baseEnd_952248 := by
    simpa [prefixWord, tailWord_952248, baseEnd_952248] using wordTrace_append hprefix tailTrace_952248
  have hstable : (prefixWord ++ tailWord_952248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952248).length < 2 ^ (prefixWord ++ tailWord_952248).sum := by decide
  have hdescent : baseEnd_952248 < baseStart_952248 := by decide
  rcases family_descends (prefixWord ++ tailWord_952248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952271 : List Nat := [1, 1, 2, 1, 1, 5, 1, 11]
def baseStart_952271 : Nat := 118140960795 + 952271 * 2 ^ 59
def prefixEnd_952271 : Nat := 4983230072969 + 3 ^ 40 * 952271 * 2
def baseEnd_952271 : Nat := 18110101345842554408633

theorem tailTrace_952271 : CollatzResearch.WordTrace tailWord_952271 prefixEnd_952271 18110101345842554408633 := by
  unfold tailWord_952271
  simp only [CollatzResearch.WordTrace]
  refine ⟨34732176733092276783880667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23154784488728184522587111 34732176733092276783880667)
  ·
    refine ⟨52098265099638415175821001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34732176733092276783880667 52098265099638415175821001)
    ·
      refine ⟨39073698824728811381865751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52098265099638415175821001 39073698824728811381865751)
      ·
        refine ⟨58610548237093217072798627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39073698824728811381865751 58610548237093217072798627)
        ·
          refine ⟨87915822355639825609197941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58610548237093217072798627 87915822355639825609197941)
          ·
            refine ⟨8242108345841233650862307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87915822355639825609197941 8242108345841233650862307)
            ·
              refine ⟨12363162518761850476293461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8242108345841233650862307 12363162518761850476293461)
              ·
                refine ⟨18110101345842554408633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 12363162518761850476293461 18110101345842554408633)
                ·
                  rfl

theorem cell23_952271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 11].length) (baseStart_952271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952271 prefixEnd_952271 := by exact prefixLift 952271
  have htrace : WordTrace (prefixWord ++ tailWord_952271) baseStart_952271 baseEnd_952271 := by
    simpa [prefixWord, tailWord_952271, baseEnd_952271] using wordTrace_append hprefix tailTrace_952271
  have hstable : (prefixWord ++ tailWord_952271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952271).length < 2 ^ (prefixWord ++ tailWord_952271).sum := by decide
  have hdescent : baseEnd_952271 < baseStart_952271 := by decide
  rcases family_descends (prefixWord ++ tailWord_952271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952305 : List Nat := [1, 2, 2, 2, 5, 2, 1, 8]
def baseStart_952305 : Nat := 118140960795 + 952305 * 2 ^ 59
def prefixEnd_952305 : Nat := 4983230072969 + 3 ^ 40 * 952305 * 2
def baseEnd_952305 : Nat := 18110747951111179111405

theorem tailTrace_952305 : CollatzResearch.WordTrace tailWord_952305 prefixEnd_952305 18110747951111179111405 := by
  unfold tailWord_952305
  simp only [CollatzResearch.WordTrace]
  refine ⟨34733416814969100590618369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23155611209979400393745579 34733416814969100590618369)
  ·
    refine ⟨26050062611226825442963777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34733416814969100590618369 26050062611226825442963777)
    ·
      refine ⟨19537546958420119082222833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26050062611226825442963777 19537546958420119082222833)
      ·
        refine ⟨14653160218815089311667125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19537546958420119082222833 14653160218815089311667125)
        ·
          refine ⟨1373733770513914622968793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14653160218815089311667125 1373733770513914622968793)
          ·
            refine ⟨1030300327885435967226595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1373733770513914622968793 1030300327885435967226595)
            ·
              refine ⟨1545450491828153950839893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1030300327885435967226595 1545450491828153950839893)
              ·
                refine ⟨18110747951111179111405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1545450491828153950839893 18110747951111179111405)
                ·
                  rfl

theorem cell23_952305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 8].length) (baseStart_952305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952305 prefixEnd_952305 := by exact prefixLift 952305
  have htrace : WordTrace (prefixWord ++ tailWord_952305) baseStart_952305 baseEnd_952305 := by
    simpa [prefixWord, tailWord_952305, baseEnd_952305] using wordTrace_append hprefix tailTrace_952305
  have hstable : (prefixWord ++ tailWord_952305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952305).length < 2 ^ (prefixWord ++ tailWord_952305).sum := by decide
  have hdescent : baseEnd_952305 < baseStart_952305 := by decide
  rcases family_descends (prefixWord ++ tailWord_952305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952328 : List Nat := [2, 1, 3, 2, 1, 2, 2, 1, 2, 2, 5]
def baseStart_952328 : Nat := 118140960795 + 952328 * 2 ^ 59
def prefixEnd_952328 : Nat := 4983230072969 + 3 ^ 40 * 952328 * 2
def baseEnd_952328 : Nat := 489002004735055246020329

theorem tailTrace_952328 : CollatzResearch.WordTrace tailWord_952328 prefixEnd_952328 489002004735055246020329 := by
  unfold tailWord_952328
  simp only [CollatzResearch.WordTrace]
  refine ⟨17367127846942887759352819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23156170462590517012470425 17367127846942887759352819)
  ·
    refine ⟨26050691770414331639029229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17367127846942887759352819 26050691770414331639029229)
    ·
      refine ⟨9769009413905374364635961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26050691770414331639029229 9769009413905374364635961)
      ·
        refine ⟨7326757060429030773476971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9769009413905374364635961 7326757060429030773476971)
        ·
          refine ⟨10990135590643546160215457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7326757060429030773476971 10990135590643546160215457)
          ·
            refine ⟨8242601692982659620161593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10990135590643546160215457 8242601692982659620161593)
            ·
              refine ⟨6181951269736994715121195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8242601692982659620161593 6181951269736994715121195)
              ·
                refine ⟨9272926904605492072681793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6181951269736994715121195 9272926904605492072681793)
                ·
                  refine ⟨6954695178454119054511345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9272926904605492072681793 6954695178454119054511345)
                  ·
                    refine ⟨5216021383840589290883509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6954695178454119054511345 5216021383840589290883509)
                    ·
                      refine ⟨489002004735055246020329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5216021383840589290883509 489002004735055246020329)
                      ·
                        rfl

theorem cell23_952328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_952328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952328 prefixEnd_952328 := by exact prefixLift 952328
  have htrace : WordTrace (prefixWord ++ tailWord_952328) baseStart_952328 baseEnd_952328 := by
    simpa [prefixWord, tailWord_952328, baseEnd_952328] using wordTrace_append hprefix tailTrace_952328
  have hstable : (prefixWord ++ tailWord_952328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952328).length < 2 ^ (prefixWord ++ tailWord_952328).sum := by decide
  have hdescent : baseEnd_952328 < baseStart_952328 := by decide
  rcases family_descends (prefixWord ++ tailWord_952328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952349 : List Nat := [1, 4, 2, 2, 2, 1, 3, 2, 2, 1, 3]
def baseStart_952349 : Nat := 118140960795 + 952349 * 2 ^ 59
def prefixEnd_952349 : Nat := 4983230072969 + 3 ^ 40 * 952349 * 2
def baseEnd_952349 : Nat := 489012787828799663857733

theorem tailTrace_952349 : CollatzResearch.WordTrace tailWord_952349 prefixEnd_952349 489012787828799663857733 := by
  unfold tailWord_952349
  simp only [CollatzResearch.WordTrace]
  refine ⟨34735021626809696105220101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23156681084539797403480067 34735021626809696105220101)
  ·
    refine ⟨6512816555026818019728769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34735021626809696105220101 6512816555026818019728769)
    ·
      refine ⟨4884612416270113514796577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6512816555026818019728769 4884612416270113514796577)
      ·
        refine ⟨3663459312202585136097433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4884612416270113514796577 3663459312202585136097433)
        ·
          refine ⟨2747594484151938852073075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3663459312202585136097433 2747594484151938852073075)
          ·
            refine ⟨4121391726227908278109613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2747594484151938852073075 4121391726227908278109613)
            ·
              refine ⟨1545521897335465604291105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4121391726227908278109613 1545521897335465604291105)
              ·
                refine ⟨1159141423001599203218329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1545521897335465604291105 1159141423001599203218329)
                ·
                  refine ⟨869356067251199402413747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1159141423001599203218329 869356067251199402413747)
                  ·
                    refine ⟨1304034100876799103620621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 869356067251199402413747 1304034100876799103620621)
                    ·
                      refine ⟨489012787828799663857733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1304034100876799103620621 489012787828799663857733)
                      ·
                        rfl

theorem cell23_952349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_952349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952349 prefixEnd_952349 := by exact prefixLift 952349
  have htrace : WordTrace (prefixWord ++ tailWord_952349) baseStart_952349 baseEnd_952349 := by
    simpa [prefixWord, tailWord_952349, baseEnd_952349] using wordTrace_append hprefix tailTrace_952349
  have hstable : (prefixWord ++ tailWord_952349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952349).length < 2 ^ (prefixWord ++ tailWord_952349).sum := by decide
  have hdescent : baseEnd_952349 < baseStart_952349 := by decide
  rcases family_descends (prefixWord ++ tailWord_952349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952366 : List Nat := [4, 1, 3, 1, 1, 3, 3, 1, 2, 1, 3]
def baseStart_952366 : Nat := 118140960795 + 952366 * 2 ^ 59
def prefixEnd_952366 : Nat := 4983230072969 + 3 ^ 40 * 952366 * 2
def baseEnd_952366 : Nat := 489021516999926097345155

theorem tailTrace_952366 : CollatzResearch.WordTrace tailWord_952366 prefixEnd_952366 489021516999926097345155 := by
  unfold tailWord_952366
  simp only [CollatzResearch.WordTrace]
  refine ⟨4341955208468513501073619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23157094445165405339059301 4341955208468513501073619)
  ·
    refine ⟨6512932812702770251610429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4341955208468513501073619 6512932812702770251610429)
    ·
      refine ⟨2442349804763538844353911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6512932812702770251610429 2442349804763538844353911)
      ·
        refine ⟨3663524707145308266530867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2442349804763538844353911 3663524707145308266530867)
        ·
          refine ⟨5495287060717962399796301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3663524707145308266530867 5495287060717962399796301)
          ·
            refine ⟨2060732647769235899923613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5495287060717962399796301 2060732647769235899923613)
            ·
              refine ⟨772774742913463462471355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2060732647769235899923613 772774742913463462471355)
              ·
                refine ⟨1159162114370195193707033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 772774742913463462471355 1159162114370195193707033)
                ·
                  refine ⟨869371585777646395280275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1159162114370195193707033 869371585777646395280275)
                  ·
                    refine ⟨1304057378666469592920413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 869371585777646395280275 1304057378666469592920413)
                    ·
                      refine ⟨489021516999926097345155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1304057378666469592920413 489021516999926097345155)
                      ·
                        rfl

theorem cell23_952366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_952366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952366 prefixEnd_952366 := by exact prefixLift 952366
  have htrace : WordTrace (prefixWord ++ tailWord_952366) baseStart_952366 baseEnd_952366 := by
    simpa [prefixWord, tailWord_952366, baseEnd_952366] using wordTrace_append hprefix tailTrace_952366
  have hstable : (prefixWord ++ tailWord_952366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952366).length < 2 ^ (prefixWord ++ tailWord_952366).sum := by decide
  have hdescent : baseEnd_952366 < baseStart_952366 := by decide
  rcases family_descends (prefixWord ++ tailWord_952366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952412 : List Nat := [2, 2, 4, 1, 1, 4, 1, 1, 7]
def baseStart_952412 : Nat := 118140960795 + 952412 * 2 ^ 59
def prefixEnd_952412 : Nat := 4983230072969 + 3 ^ 40 * 952412 * 2
def baseEnd_952412 : Nat := 54338348567781435263327

theorem tailTrace_952412 : CollatzResearch.WordTrace tailWord_952412 prefixEnd_952412 54338348567781435263327 := by
  unfold tailWord_952412
  simp only [CollatzResearch.WordTrace]
  refine ⟨17368659712790728932381745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23158212950387638576508993 17368659712790728932381745)
  ·
    refine ⟨13026494784593046699286309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17368659712790728932381745 13026494784593046699286309)
    ·
      refine ⟨2442467772111196256116183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13026494784593046699286309 2442467772111196256116183)
      ·
        refine ⟨3663701658166794384174275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2442467772111196256116183 3663701658166794384174275)
        ·
          refine ⟨5495552487250191576261413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3663701658166794384174275 5495552487250191576261413)
          ·
            refine ⟨1030416091359410920549015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5495552487250191576261413 1030416091359410920549015)
            ·
              refine ⟨1545624137039116380823523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1030416091359410920549015 1545624137039116380823523)
              ·
                refine ⟨2318436205558674571235285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1545624137039116380823523 2318436205558674571235285)
                ·
                  refine ⟨54338348567781435263327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2318436205558674571235285 54338348567781435263327)
                  ·
                    rfl

theorem cell23_952412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 7].length) (baseStart_952412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952412 prefixEnd_952412 := by exact prefixLift 952412
  have htrace : WordTrace (prefixWord ++ tailWord_952412) baseStart_952412 baseEnd_952412 := by
    simpa [prefixWord, tailWord_952412, baseEnd_952412] using wordTrace_append hprefix tailTrace_952412
  have hstable : (prefixWord ++ tailWord_952412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952412).length < 2 ^ (prefixWord ++ tailWord_952412).sum := by decide
  have hdescent : baseEnd_952412 < baseStart_952412 := by decide
  rcases family_descends (prefixWord ++ tailWord_952412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952479 : List Nat := [1, 1, 2, 6, 1, 2, 1, 1, 2, 4, 2]
def baseStart_952479 : Nat := 118140960795 + 952479 * 2 ^ 59
def prefixEnd_952479 : Nat := 4983230072969 + 3 ^ 40 * 952479 * 2
def baseEnd_952479 : Nat := 489079540313884155232135

theorem tailTrace_952479 : CollatzResearch.WordTrace tailWord_952479 prefixEnd_952479 489079540313884155232135 := by
  unfold tailWord_952479
  simp only [CollatzResearch.WordTrace]
  refine ⟨34739763116338728307452491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23159842077559152204968327 34739763116338728307452491)
  ·
    refine ⟨52109644674508092461178737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34739763116338728307452491 52109644674508092461178737)
    ·
      refine ⟨39082233505881069345884053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52109644674508092461178737 39082233505881069345884053)
      ·
        refine ⟨1831979695588175125588315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39082233505881069345884053 1831979695588175125588315)
        ·
          refine ⟨2747969543382262688382473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1831979695588175125588315 2747969543382262688382473)
          ·
            refine ⟨2060977157536697016286855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2747969543382262688382473 2060977157536697016286855)
            ·
              refine ⟨3091465736305045524430283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2060977157536697016286855 3091465736305045524430283)
              ·
                refine ⟨4637198604457568286645425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3091465736305045524430283 4637198604457568286645425)
                ·
                  refine ⟨3477898953343176214984069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4637198604457568286645425 3477898953343176214984069)
                  ·
                    refine ⟨652106053751845540309513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3477898953343176214984069 652106053751845540309513)
                    ·
                      refine ⟨489079540313884155232135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 652106053751845540309513 489079540313884155232135)
                      ·
                        rfl

theorem cell23_952479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_952479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952479 prefixEnd_952479 := by exact prefixLift 952479
  have htrace : WordTrace (prefixWord ++ tailWord_952479) baseStart_952479 baseEnd_952479 := by
    simpa [prefixWord, tailWord_952479, baseEnd_952479] using wordTrace_append hprefix tailTrace_952479
  have hstable : (prefixWord ++ tailWord_952479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952479).length < 2 ^ (prefixWord ++ tailWord_952479).sum := by decide
  have hdescent : baseEnd_952479 < baseStart_952479 := by decide
  rcases family_descends (prefixWord ++ tailWord_952479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952485 : List Nat := [1, 3, 1, 2, 1, 3, 1, 5, 6]
def baseStart_952485 : Nat := 118140960795 + 952485 * 2 ^ 59
def prefixEnd_952485 : Nat := 4983230072969 + 3 ^ 40 * 952485 * 2
def baseEnd_952485 : Nat := 54342513466423459084123

theorem tailTrace_952485 : CollatzResearch.WordTrace tailWord_952485 prefixEnd_952485 54342513466423459084123 := by
  unfold tailWord_952485
  simp only [CollatzResearch.WordTrace]
  refine ⟨34739981954316991332170909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23159987969544660888113939 34739981954316991332170909)
  ·
    refine ⟨13027493232868871749564091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34739981954316991332170909 13027493232868871749564091)
    ·
      refine ⟨19541239849303307624346137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13027493232868871749564091 19541239849303307624346137)
      ·
        refine ⟨14655929886977480718259603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19541239849303307624346137 14655929886977480718259603)
        ·
          refine ⟨21983894830466221077389405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14655929886977480718259603 21983894830466221077389405)
          ·
            refine ⟨8243960561424832904021027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21983894830466221077389405 8243960561424832904021027)
            ·
              refine ⟨12365940842137249356031541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8243960561424832904021027 12365940842137249356031541)
              ·
                refine ⟨1159306953950367127127957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12365940842137249356031541 1159306953950367127127957)
                ·
                  refine ⟨54342513466423459084123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1159306953950367127127957 54342513466423459084123)
                  ·
                    rfl

theorem cell23_952485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 6].length) (baseStart_952485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952485 prefixEnd_952485 := by exact prefixLift 952485
  have htrace : WordTrace (prefixWord ++ tailWord_952485) baseStart_952485 baseEnd_952485 := by
    simpa [prefixWord, tailWord_952485, baseEnd_952485] using wordTrace_append hprefix tailTrace_952485
  have hstable : (prefixWord ++ tailWord_952485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952485).length < 2 ^ (prefixWord ++ tailWord_952485).sum := by decide
  have hdescent : baseEnd_952485 < baseStart_952485 := by decide
  rcases family_descends (prefixWord ++ tailWord_952485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952549 : List Nat := [1, 3, 1, 4, 2, 2, 2, 2, 1, 5]
def baseStart_952549 : Nat := 118140960795 + 952549 * 2 ^ 59
def prefixEnd_952549 : Nat := 4983230072969 + 3 ^ 40 * 952549 * 2
def baseEnd_952549 : Nat := 163038494653232960452271

theorem tailTrace_952549 : CollatzResearch.WordTrace tailWord_952549 prefixEnd_952549 163038494653232960452271 := by
  unfold tailWord_952549
  simp only [CollatzResearch.WordTrace]
  refine ⟨34742316226085130262500701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23161544150723420175000467 34742316226085130262500701)
  ·
    refine ⟨13028368584781923848437763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34742316226085130262500701 13028368584781923848437763)
    ·
      refine ⟨19542552877172885772656645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13028368584781923848437763 19542552877172885772656645)
      ·
        refine ⟨3664228664469916082373121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19542552877172885772656645 3664228664469916082373121)
        ·
          refine ⟨2748171498352437061779841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3664228664469916082373121 2748171498352437061779841)
          ·
            refine ⟨2061128623764327796334881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2748171498352437061779841 2061128623764327796334881)
            ·
              refine ⟨1545846467823245847251161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2061128623764327796334881 1545846467823245847251161)
              ·
                refine ⟨1159384850867434385438371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1545846467823245847251161 1159384850867434385438371)
                ·
                  refine ⟨1739077276301151578157557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1159384850867434385438371 1739077276301151578157557)
                  ·
                    refine ⟨163038494653232960452271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1739077276301151578157557 163038494653232960452271)
                    ·
                      rfl

theorem cell23_952549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 5].length) (baseStart_952549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952549 prefixEnd_952549 := by exact prefixLift 952549
  have htrace : WordTrace (prefixWord ++ tailWord_952549) baseStart_952549 baseEnd_952549 := by
    simpa [prefixWord, tailWord_952549, baseEnd_952549] using wordTrace_append hprefix tailTrace_952549
  have hstable : (prefixWord ++ tailWord_952549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952549).length < 2 ^ (prefixWord ++ tailWord_952549).sum := by decide
  have hdescent : baseEnd_952549 < baseStart_952549 := by decide
  rcases family_descends (prefixWord ++ tailWord_952549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952555 : List Nat := [1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 5]
def baseStart_952555 : Nat := 118140960795 + 952555 * 2 ^ 59
def prefixEnd_952555 : Nat := 4983230072969 + 3 ^ 40 * 952555 * 2
def baseEnd_952555 : Nat := 489118564843625857881785

theorem tailTrace_952555 : CollatzResearch.WordTrace tailWord_952555 prefixEnd_952555 489118564843625857881785 := by
  unfold tailWord_952555
  simp only [CollatzResearch.WordTrace]
  refine ⟨34742535064063393287219119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23161690042708928858146079 34742535064063393287219119)
  ·
    refine ⟨52113802596095089930828679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34742535064063393287219119 52113802596095089930828679)
    ·
      refine ⟨78170703894142634896243019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52113802596095089930828679 78170703894142634896243019)
      ·
        refine ⟨117256055841213952344364529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78170703894142634896243019 117256055841213952344364529)
        ·
          refine ⟨87942041880910464258273397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117256055841213952344364529 87942041880910464258273397)
          ·
            refine ⟨8244566426335356024213131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87942041880910464258273397 8244566426335356024213131)
            ·
              refine ⟨12366849639503034036319697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8244566426335356024213131 12366849639503034036319697)
              ·
                refine ⟨9275137229627275527239773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12366849639503034036319697 9275137229627275527239773)
                ·
                  refine ⟨3478176461110228322714915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9275137229627275527239773 3478176461110228322714915)
                  ·
                    refine ⟨5217264691665342484072373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3478176461110228322714915 5217264691665342484072373)
                    ·
                      refine ⟨489118564843625857881785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5217264691665342484072373 489118564843625857881785)
                      ·
                        rfl

theorem cell23_952555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 5].length) (baseStart_952555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952555 prefixEnd_952555 := by exact prefixLift 952555
  have htrace : WordTrace (prefixWord ++ tailWord_952555) baseStart_952555 baseEnd_952555 := by
    simpa [prefixWord, tailWord_952555, baseEnd_952555] using wordTrace_append hprefix tailTrace_952555
  have hstable : (prefixWord ++ tailWord_952555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952555).length < 2 ^ (prefixWord ++ tailWord_952555).sum := by decide
  have hdescent : baseEnd_952555 < baseStart_952555 := by decide
  rcases family_descends (prefixWord ++ tailWord_952555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952572 : List Nat := [2, 2, 2, 1, 4, 1, 1, 3, 1, 1, 5]
def baseStart_952572 : Nat := 118140960795 + 952572 * 2 ^ 59
def prefixEnd_952572 : Nat := 4983230072969 + 3 ^ 40 * 952572 * 2
def baseEnd_952572 : Nat := 489127294014752291369207

theorem tailTrace_952572 : CollatzResearch.WordTrace tailWord_952572 prefixEnd_952572 489127294014752291369207 := by
  unfold tailWord_952572
  simp only [CollatzResearch.WordTrace]
  refine ⟨17371577552500902595293985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23162103403334536793725313 17371577552500902595293985)
  ·
    refine ⟨13028683164375676946470489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17371577552500902595293985 13028683164375676946470489)
    ·
      refine ⟨9771512373281757709852867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13028683164375676946470489 9771512373281757709852867)
      ·
        refine ⟨14657268559922636564779301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9771512373281757709852867 14657268559922636564779301)
        ·
          refine ⟨2748237854985494355896119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14657268559922636564779301 2748237854985494355896119)
          ·
            refine ⟨4122356782478241533844179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2748237854985494355896119 4122356782478241533844179)
            ·
              refine ⟨6183535173717362300766269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4122356782478241533844179 6183535173717362300766269)
              ·
                refine ⟨2318825690144010862787351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6183535173717362300766269 2318825690144010862787351)
                ·
                  refine ⟨3478238535216016294181027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2318825690144010862787351 3478238535216016294181027)
                  ·
                    refine ⟨5217357802824024441271541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3478238535216016294181027 5217357802824024441271541)
                    ·
                      refine ⟨489127294014752291369207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5217357802824024441271541 489127294014752291369207)
                      ·
                        rfl

theorem cell23_952572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_952572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952572 prefixEnd_952572 := by exact prefixLift 952572
  have htrace : WordTrace (prefixWord ++ tailWord_952572) baseStart_952572 baseEnd_952572 := by
    simpa [prefixWord, tailWord_952572, baseEnd_952572] using wordTrace_append hprefix tailTrace_952572
  have hstable : (prefixWord ++ tailWord_952572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952572).length < 2 ^ (prefixWord ++ tailWord_952572).sum := by decide
  have hdescent : baseEnd_952572 < baseStart_952572 := by decide
  rcases family_descends (prefixWord ++ tailWord_952572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952580 : List Nat := [2, 3, 2, 2, 3, 1, 3, 2, 1, 1, 3]
def baseStart_952580 : Nat := 118140960795 + 952580 * 2 ^ 59
def prefixEnd_952580 : Nat := 4983230072969 + 3 ^ 40 * 952580 * 2
def baseEnd_952580 : Nat := 489131401859988260069171

theorem tailTrace_952580 : CollatzResearch.WordTrace tailWord_952580 prefixEnd_952580 489131401859988260069171 := by
  unfold tailWord_952580
  simp only [CollatzResearch.WordTrace]
  refine ⟨17371723444486411278439597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23162297925981881704586129 17371723444486411278439597)
  ·
    refine ⟨6514396291682404229414849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17371723444486411278439597 6514396291682404229414849)
    ·
      refine ⟨4885797218761803172061137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6514396291682404229414849 4885797218761803172061137)
      ·
        refine ⟨3664347914071352379045853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4885797218761803172061137 3664347914071352379045853)
        ·
          refine ⟨1374130467776757142142195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3664347914071352379045853 1374130467776757142142195)
          ·
            refine ⟨2061195701665135713213293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1374130467776757142142195 2061195701665135713213293)
            ·
              refine ⟨772948388124425892454985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2061195701665135713213293 772948388124425892454985)
              ·
                refine ⟨579711291093319419341239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 772948388124425892454985 579711291093319419341239)
                ·
                  refine ⟨869566936639979129011859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 579711291093319419341239 869566936639979129011859)
                  ·
                    refine ⟨1304350404959968693517789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 869566936639979129011859 1304350404959968693517789)
                    ·
                      refine ⟨489131401859988260069171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1304350404959968693517789 489131401859988260069171)
                      ·
                        rfl

theorem cell23_952580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_952580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952580 prefixEnd_952580 := by exact prefixLift 952580
  have htrace : WordTrace (prefixWord ++ tailWord_952580) baseStart_952580 baseEnd_952580 := by
    simpa [prefixWord, tailWord_952580, baseEnd_952580] using wordTrace_append hprefix tailTrace_952580
  have hstable : (prefixWord ++ tailWord_952580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952580).length < 2 ^ (prefixWord ++ tailWord_952580).sum := by decide
  have hdescent : baseEnd_952580 < baseStart_952580 := by decide
  rcases family_descends (prefixWord ++ tailWord_952580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952586 : List Nat := [3, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2]
def baseStart_952586 : Nat := 118140960795 + 952586 * 2 ^ 59
def prefixEnd_952586 : Nat := 4983230072969 + 3 ^ 40 * 952586 * 2
def baseEnd_952586 : Nat := 489134482743915236594143

theorem tailTrace_952586 : CollatzResearch.WordTrace tailWord_952586 prefixEnd_952586 489134482743915236594143 := by
  unfold tailWord_952586
  simp only [CollatzResearch.WordTrace]
  refine ⟨8685916431737771395399403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23162443817967390387731741 8685916431737771395399403)
  ·
    refine ⟨13028874647606657093099105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8685916431737771395399403 13028874647606657093099105)
    ·
      refine ⟨9771655985704992819824329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13028874647606657093099105 9771655985704992819824329)
      ·
        refine ⟨7328741989278744614868247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9771655985704992819824329 7328741989278744614868247)
        ·
          refine ⟨10993112983918116922302371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7328741989278744614868247 10993112983918116922302371)
          ·
            refine ⟨16489669475877175383453557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10993112983918116922302371 16489669475877175383453557)
            ·
              refine ⟨1545906513363485192198771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16489669475877175383453557 1545906513363485192198771)
              ·
                refine ⟨2318859770045227788298157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1545906513363485192198771 2318859770045227788298157)
                ·
                  refine ⟨869572413766960420611809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2318859770045227788298157 869572413766960420611809)
                  ·
                    refine ⟨652179310325220315458857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 869572413766960420611809 652179310325220315458857)
                    ·
                      refine ⟨489134482743915236594143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 652179310325220315458857 489134482743915236594143)
                      ·
                        rfl

theorem cell23_952586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_952586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952586 prefixEnd_952586 := by exact prefixLift 952586
  have htrace : WordTrace (prefixWord ++ tailWord_952586) baseStart_952586 baseEnd_952586 := by
    simpa [prefixWord, tailWord_952586, baseEnd_952586] using wordTrace_append hprefix tailTrace_952586
  have hstable : (prefixWord ++ tailWord_952586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952586).length < 2 ^ (prefixWord ++ tailWord_952586).sum := by decide
  have hdescent : baseEnd_952586 < baseStart_952586 := by decide
  rcases family_descends (prefixWord ++ tailWord_952586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952636 : List Nat := [2, 2, 2, 2, 1, 2, 4, 2, 2, 1, 3]
def baseStart_952636 : Nat := 118140960795 + 952636 * 2 ^ 59
def prefixEnd_952636 : Nat := 4983230072969 + 3 ^ 40 * 952636 * 2
def baseEnd_952636 : Nat := 489160156776640040968913

theorem tailTrace_952636 : CollatzResearch.WordTrace tailWord_952636 prefixEnd_952636 489160156776640040968913 := by
  unfold tailWord_952636
  simp only [CollatzResearch.WordTrace]
  refine ⟨17372744688384972060458881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23163659584513296080611841 17372744688384972060458881)
  ·
    refine ⟨13029558516288729045344161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17372744688384972060458881 13029558516288729045344161)
    ·
      refine ⟨9772168887216546784008121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13029558516288729045344161 9772168887216546784008121)
      ·
        refine ⟨7329126665412410088006091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9772168887216546784008121 7329126665412410088006091)
        ·
          refine ⟨10993689998118615132009137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7329126665412410088006091 10993689998118615132009137)
          ·
            refine ⟨8245267498588961349006853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10993689998118615132009137 8245267498588961349006853)
            ·
              refine ⟨1545987655985430252938785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8245267498588961349006853 1545987655985430252938785)
              ·
                refine ⟨1159490741989072689704089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1545987655985430252938785 1159490741989072689704089)
                ·
                  refine ⟨869618056491804517278067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1159490741989072689704089 869618056491804517278067)
                  ·
                    refine ⟨1304427084737706775917101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 869618056491804517278067 1304427084737706775917101)
                    ·
                      refine ⟨489160156776640040968913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1304427084737706775917101 489160156776640040968913)
                      ·
                        rfl

theorem cell23_952636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_952636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952636 prefixEnd_952636 := by exact prefixLift 952636
  have htrace : WordTrace (prefixWord ++ tailWord_952636) baseStart_952636 baseEnd_952636 := by
    simpa [prefixWord, tailWord_952636, baseEnd_952636] using wordTrace_append hprefix tailTrace_952636
  have hstable : (prefixWord ++ tailWord_952636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952636).length < 2 ^ (prefixWord ++ tailWord_952636).sum := by decide
  have hdescent : baseEnd_952636 < baseStart_952636 := by decide
  rcases family_descends (prefixWord ++ tailWord_952636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952652 : List Nat := [2, 2, 1, 3, 2, 1, 3, 1, 2, 6]
def baseStart_952652 : Nat := 118140960795 + 952652 * 2 ^ 59
def prefixEnd_952652 : Nat := 4983230072969 + 3 ^ 40 * 952652 * 2
def baseEnd_952652 : Nat := 163056124155703992789613

theorem tailTrace_952652 : CollatzResearch.WordTrace tailWord_952652 prefixEnd_952652 163056124155703992789613 := by
  unfold tailWord_952652
  simp only [CollatzResearch.WordTrace]
  refine ⟨17373036472355989426750105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23164048629807985902333473 17373036472355989426750105)
  ·
    refine ⟨13029777354266992070062579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17373036472355989426750105 13029777354266992070062579)
    ·
      refine ⟨19544666031400488105093869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13029777354266992070062579 19544666031400488105093869)
      ·
        refine ⟨7329249761775183039410201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19544666031400488105093869 7329249761775183039410201)
        ·
          refine ⟨5496937321331387279557651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7329249761775183039410201 5496937321331387279557651)
          ·
            refine ⟨8245405981997080919336477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5496937321331387279557651 8245405981997080919336477)
            ·
              refine ⟨3092027243248905344751179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8245405981997080919336477 3092027243248905344751179)
              ·
                refine ⟨4638040864873358017126769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3092027243248905344751179 4638040864873358017126769)
                ·
                  refine ⟨3478530648655018512845077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4638040864873358017126769 3478530648655018512845077)
                  ·
                    refine ⟨163056124155703992789613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3478530648655018512845077 163056124155703992789613)
                    ·
                      rfl

theorem cell23_952652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 2, 6].length) (baseStart_952652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952652 prefixEnd_952652 := by exact prefixLift 952652
  have htrace : WordTrace (prefixWord ++ tailWord_952652) baseStart_952652 baseEnd_952652 := by
    simpa [prefixWord, tailWord_952652, baseEnd_952652] using wordTrace_append hprefix tailTrace_952652
  have hstable : (prefixWord ++ tailWord_952652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952652).length < 2 ^ (prefixWord ++ tailWord_952652).sum := by decide
  have hdescent : baseEnd_952652 < baseStart_952652 := by decide
  rcases family_descends (prefixWord ++ tailWord_952652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952676 : List Nat := [2, 3, 1, 1, 3, 1, 2, 2, 4, 2, 2]
def baseStart_952676 : Nat := 118140960795 + 952676 * 2 ^ 59
def prefixEnd_952676 : Nat := 4983230072969 + 3 ^ 40 * 952676 * 2
def baseEnd_952676 : Nat := 489180696002819884468729

theorem tailTrace_952676 : CollatzResearch.WordTrace tailWord_952676 prefixEnd_952676 489180696002819884468729 := by
  unfold tailWord_952676
  simp only [CollatzResearch.WordTrace]
  refine ⟨17373474148312515476186941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23164632197750020634915921 17373474148312515476186941)
  ·
    refine ⟨6515052805617193303570103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17373474148312515476186941 6515052805617193303570103)
    ·
      refine ⟨9772579208425789955355155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6515052805617193303570103 9772579208425789955355155)
      ·
        refine ⟨14658868812638684933032733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9772579208425789955355155 14658868812638684933032733)
        ·
          refine ⟨5497075804739506849887275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14658868812638684933032733 5497075804739506849887275)
          ·
            refine ⟨8245613707109260274830913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5497075804739506849887275 8245613707109260274830913)
            ·
              refine ⟨6184210280331945206123185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8245613707109260274830913 6184210280331945206123185)
              ·
                refine ⟨4638157710248958904592389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6184210280331945206123185 4638157710248958904592389)
                ·
                  refine ⟨869654570671679794611073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4638157710248958904592389 869654570671679794611073)
                  ·
                    refine ⟨652240928003759845958305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 869654570671679794611073 652240928003759845958305)
                    ·
                      refine ⟨489180696002819884468729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 652240928003759845958305 489180696002819884468729)
                      ·
                        rfl

theorem cell23_952676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 4, 2, 2].length) (baseStart_952676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952676 prefixEnd_952676 := by exact prefixLift 952676
  have htrace : WordTrace (prefixWord ++ tailWord_952676) baseStart_952676 baseEnd_952676 := by
    simpa [prefixWord, tailWord_952676, baseEnd_952676] using wordTrace_append hprefix tailTrace_952676
  have hstable : (prefixWord ++ tailWord_952676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952676).length < 2 ^ (prefixWord ++ tailWord_952676).sum := by decide
  have hdescent : baseEnd_952676 < baseStart_952676 := by decide
  rcases family_descends (prefixWord ++ tailWord_952676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952680 : List Nat := [2, 1, 4, 2, 2, 3, 2, 1, 1, 3, 2]
def baseStart_952680 : Nat := 118140960795 + 952680 * 2 ^ 59
def prefixEnd_952680 : Nat := 4983230072969 + 3 ^ 40 * 952680 * 2
def baseEnd_952680 : Nat := 489182749925437868818711

theorem tailTrace_952680 : CollatzResearch.WordTrace tailWord_952680 prefixEnd_952680 489182749925437868818711 := by
  unfold tailWord_952680
  simp only [CollatzResearch.WordTrace]
  refine ⟨17373547094305269817759747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23164729459073693090346329 17373547094305269817759747)
  ·
    refine ⟨26060320641457904726639621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17373547094305269817759747 26060320641457904726639621)
    ·
      refine ⟨4886310120273357136244929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26060320641457904726639621 4886310120273357136244929)
      ·
        refine ⟨3664732590205017852183697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4886310120273357136244929 3664732590205017852183697)
        ·
          refine ⟨2748549442653763389137773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3664732590205017852183697 2748549442653763389137773)
          ·
            refine ⟨1030706040995161270926665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2748549442653763389137773 1030706040995161270926665)
            ·
              refine ⟨773029530746370953194999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1030706040995161270926665 773029530746370953194999)
              ·
                refine ⟨1159544296119556429792499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 773029530746370953194999 1159544296119556429792499)
                ·
                  refine ⟨1739316444179334644688749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1159544296119556429792499 1739316444179334644688749)
                  ·
                    refine ⟨652243666567250491758281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1739316444179334644688749 652243666567250491758281)
                    ·
                      refine ⟨489182749925437868818711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 652243666567250491758281 489182749925437868818711)
                      ·
                        rfl

theorem cell23_952680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_952680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952680 prefixEnd_952680 := by exact prefixLift 952680
  have htrace : WordTrace (prefixWord ++ tailWord_952680) baseStart_952680 baseEnd_952680 := by
    simpa [prefixWord, tailWord_952680, baseEnd_952680] using wordTrace_append hprefix tailTrace_952680
  have hstable : (prefixWord ++ tailWord_952680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952680).length < 2 ^ (prefixWord ++ tailWord_952680).sum := by decide
  have hdescent : baseEnd_952680 < baseStart_952680 := by decide
  rcases family_descends (prefixWord ++ tailWord_952680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952693 : List Nat := [1, 3, 4, 1, 2, 2, 1, 1, 4, 2, 2]
def baseStart_952693 : Nat := 118140960795 + 952693 * 2 ^ 59
def prefixEnd_952693 : Nat := 4983230072969 + 3 ^ 40 * 952693 * 2
def baseEnd_952693 : Nat := 489189425173946317956151

theorem tailTrace_952693 : CollatzResearch.WordTrace tailWord_952693 prefixEnd_952693 489189425173946317956151 := by
  unfold tailWord_952693
  simp only [CollatzResearch.WordTrace]
  refine ⟨34747568337563442855742733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23165045558375628570495155 34747568337563442855742733)
  ·
    refine ⟨13030338126586291070903525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34747568337563442855742733 13030338126586291070903525)
    ·
      refine ⟨2443188398734929575794411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13030338126586291070903525 2443188398734929575794411)
      ·
        refine ⟨3664782598102394363691617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2443188398734929575794411 3664782598102394363691617)
        ·
          refine ⟨2748586948576795772768713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3664782598102394363691617 2748586948576795772768713)
          ·
            refine ⟨2061440211432596829576535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2748586948576795772768713 2061440211432596829576535)
            ·
              refine ⟨3092160317148895244364803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2061440211432596829576535 3092160317148895244364803)
              ·
                refine ⟨4638240475723342866547205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3092160317148895244364803 4638240475723342866547205)
                ·
                  refine ⟨869670089198126787477601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4638240475723342866547205 869670089198126787477601)
                  ·
                    refine ⟨652252566898595090608201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 869670089198126787477601 652252566898595090608201)
                    ·
                      refine ⟨489189425173946317956151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 652252566898595090608201 489189425173946317956151)
                      ·
                        rfl

theorem cell23_952693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_952693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952693 prefixEnd_952693 := by exact prefixLift 952693
  have htrace : WordTrace (prefixWord ++ tailWord_952693) baseStart_952693 baseEnd_952693 := by
    simpa [prefixWord, tailWord_952693, baseEnd_952693] using wordTrace_append hprefix tailTrace_952693
  have hstable : (prefixWord ++ tailWord_952693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952693).length < 2 ^ (prefixWord ++ tailWord_952693).sum := by decide
  have hdescent : baseEnd_952693 < baseStart_952693 := by decide
  rcases family_descends (prefixWord ++ tailWord_952693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952699 : List Nat := [1, 1, 1, 1, 1, 7, 2, 4, 5]
def baseStart_952699 : Nat := 118140960795 + 952699 * 2 ^ 59
def prefixEnd_952699 : Nat := 4983230072969 + 3 ^ 40 * 952699 * 2
def baseEnd_952699 : Nat := 54354722895319254942347

theorem tailTrace_952699 : CollatzResearch.WordTrace tailWord_952699 prefixEnd_952699 54354722895319254942347 := by
  unfold tailWord_952699
  simp only [CollatzResearch.WordTrace]
  refine ⟨34747787175541705880461151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23165191450361137253640767 34747787175541705880461151)
  ·
    refine ⟨52121680763312558820691727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34747787175541705880461151 52121680763312558820691727)
    ·
      refine ⟨78182521144968838231037591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52121680763312558820691727 78182521144968838231037591)
      ·
        refine ⟨117273781717453257346556387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78182521144968838231037591 117273781717453257346556387)
        ·
          refine ⟨175910672576179886019834581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117273781717453257346556387 175910672576179886019834581)
          ·
            refine ⟨4122906388504216078589873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 175910672576179886019834581 4122906388504216078589873)
            ·
              refine ⟨3092179791378162058942405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4122906388504216078589873 3092179791378162058942405)
              ·
                refine ⟨579783710883405386051701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3092179791378162058942405 579783710883405386051701)
                ·
                  refine ⟨54354722895319254942347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 579783710883405386051701 54354722895319254942347)
                  ·
                    rfl

theorem cell23_952699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 4, 5].length) (baseStart_952699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952699 prefixEnd_952699 := by exact prefixLift 952699
  have htrace : WordTrace (prefixWord ++ tailWord_952699) baseStart_952699 baseEnd_952699 := by
    simpa [prefixWord, tailWord_952699, baseEnd_952699] using wordTrace_append hprefix tailTrace_952699
  have hstable : (prefixWord ++ tailWord_952699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952699).length < 2 ^ (prefixWord ++ tailWord_952699).sum := by decide
  have hdescent : baseEnd_952699 < baseStart_952699 := by decide
  rcases family_descends (prefixWord ++ tailWord_952699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952712 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 3, 7]
def baseStart_952712 : Nat := 118140960795 + 952712 * 2 ^ 59
def prefixEnd_952712 : Nat := 4983230072969 + 3 ^ 40 * 952712 * 2
def baseEnd_952712 : Nat := 163066393768793914539521

theorem tailTrace_952712 : CollatzResearch.WordTrace tailWord_952712 prefixEnd_952712 163066393768793914539521 := by
  unfold tailWord_952712
  simp only [CollatzResearch.WordTrace]
  refine ⟨17374130662247304550342195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23165507549663072733789593 17374130662247304550342195)
  ·
    refine ⟨26061195993370956825513293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17374130662247304550342195 26061195993370956825513293)
    ·
      refine ⟨9772948497514108809567485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26061195993370956825513293 9772948497514108809567485)
      ·
        refine ⟨3664855686567790803587807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9772948497514108809567485 3664855686567790803587807)
        ·
          refine ⟨5497283529851686205381711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3664855686567790803587807 5497283529851686205381711)
          ·
            refine ⟨8245925294777529308072567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5497283529851686205381711 8245925294777529308072567)
            ·
              refine ⟨12368887942166293962108851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8245925294777529308072567 12368887942166293962108851)
              ·
                refine ⟨18553331913249440943163277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12368887942166293962108851 18553331913249440943163277)
                ·
                  refine ⟨6957499467468540353686229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18553331913249440943163277 6957499467468540353686229)
                  ·
                    refine ⟨163066393768793914539521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6957499467468540353686229 163066393768793914539521)
                    ·
                      rfl

theorem cell23_952712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_952712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952712 prefixEnd_952712 := by exact prefixLift 952712
  have htrace : WordTrace (prefixWord ++ tailWord_952712) baseStart_952712 baseEnd_952712 := by
    simpa [prefixWord, tailWord_952712, baseEnd_952712] using wordTrace_append hprefix tailTrace_952712
  have hstable : (prefixWord ++ tailWord_952712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952712).length < 2 ^ (prefixWord ++ tailWord_952712).sum := by decide
  have hdescent : baseEnd_952712 < baseStart_952712 := by decide
  rcases family_descends (prefixWord ++ tailWord_952712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952733 : List Nat := [1, 4, 2, 1, 4, 2, 1, 3, 5]
def baseStart_952733 : Nat := 118140960795 + 952733 * 2 ^ 59
def prefixEnd_952733 : Nat := 4983230072969 + 3 ^ 40 * 952733 * 2
def baseEnd_952733 : Nat := 54356662711125129050663

theorem tailTrace_952733 : CollatzResearch.WordTrace tailWord_952733 prefixEnd_952733 54356662711125129050663 := by
  unfold tailWord_952733
  simp only [CollatzResearch.WordTrace]
  refine ⟨34749027257418529687198853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23166018171612353124799235 34749027257418529687198853)
  ·
    refine ⟨6515442610765974316349785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34749027257418529687198853 6515442610765974316349785)
    ·
      refine ⟨4886581958074480737262339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6515442610765974316349785 4886581958074480737262339)
      ·
        refine ⟨7329872937111721105893509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4886581958074480737262339 7329872937111721105893509)
        ·
          refine ⟨1374351175708447707355033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7329872937111721105893509 1374351175708447707355033)
          ·
            refine ⟨1030763381781335780516275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1374351175708447707355033 1030763381781335780516275)
            ·
              refine ⟨1546145072672003670774413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1030763381781335780516275 1546145072672003670774413)
              ·
                refine ⟨579804402252001376540405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1546145072672003670774413 579804402252001376540405)
                ·
                  refine ⟨54356662711125129050663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 579804402252001376540405 54356662711125129050663)
                  ·
                    rfl

theorem cell23_952733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 3, 5].length) (baseStart_952733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952733 prefixEnd_952733 := by exact prefixLift 952733
  have htrace : WordTrace (prefixWord ++ tailWord_952733) baseStart_952733 baseEnd_952733 := by
    simpa [prefixWord, tailWord_952733, baseEnd_952733] using wordTrace_append hprefix tailTrace_952733
  have hstable : (prefixWord ++ tailWord_952733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952733).length < 2 ^ (prefixWord ++ tailWord_952733).sum := by decide
  have hdescent : baseEnd_952733 < baseStart_952733 := by decide
  rcases family_descends (prefixWord ++ tailWord_952733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952762 : List Nat := [3, 1, 1, 1, 2, 1, 1, 4, 2, 1, 6]
def baseStart_952762 : Nat := 118140960795 + 952762 * 2 ^ 59
def prefixEnd_952762 : Nat := 4983230072969 + 3 ^ 40 * 952762 * 2
def baseEnd_952762 : Nat := 489224855339106547993333

theorem tailTrace_952762 : CollatzResearch.WordTrace tailWord_952762 prefixEnd_952762 489224855339106547993333 := by
  unfold tailWord_952762
  simp only [CollatzResearch.WordTrace]
  refine ⟨8687521243578366910001135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23166723316208978426669693 8687521243578366910001135)
  ·
    refine ⟨13031281865367550365001703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8687521243578366910001135 13031281865367550365001703)
    ·
      refine ⟨19546922798051325547502555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13031281865367550365001703 19546922798051325547502555)
      ·
        refine ⟨29320384197076988321253833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19546922798051325547502555 29320384197076988321253833)
        ·
          refine ⟨21990288147807741240940375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29320384197076988321253833 21990288147807741240940375)
          ·
            refine ⟨32985432221711611861410563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21990288147807741240940375 32985432221711611861410563)
            ·
              refine ⟨49478148332567417792115845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32985432221711611861410563 49478148332567417792115845)
              ·
                refine ⟨9277152812356390836021721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49478148332567417792115845 9277152812356390836021721)
                ·
                  refine ⟨6957864609267293127016291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9277152812356390836021721 6957864609267293127016291)
                  ·
                    refine ⟨10436796913900939690524437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6957864609267293127016291 10436796913900939690524437)
                    ·
                      refine ⟨489224855339106547993333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10436796913900939690524437 489224855339106547993333)
                      ·
                        rfl

theorem cell23_952762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_952762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952762 prefixEnd_952762 := by exact prefixLift 952762
  have htrace : WordTrace (prefixWord ++ tailWord_952762) baseStart_952762 baseEnd_952762 := by
    simpa [prefixWord, tailWord_952762, baseEnd_952762] using wordTrace_append hprefix tailTrace_952762
  have hstable : (prefixWord ++ tailWord_952762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952762).length < 2 ^ (prefixWord ++ tailWord_952762).sum := by decide
  have hdescent : baseEnd_952762 < baseStart_952762 := by decide
  rcases family_descends (prefixWord ++ tailWord_952762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952766 : List Nat := [4, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2]
def baseStart_952766 : Nat := 118140960795 + 952766 * 2 ^ 59
def prefixEnd_952766 : Nat := 4983230072969 + 3 ^ 40 * 952766 * 2
def baseEnd_952766 : Nat := 489226909261724532343315

theorem tailTrace_952766 : CollatzResearch.WordTrace tailWord_952766 prefixEnd_952766 489226909261724532343315 := by
  unfold tailWord_952766
  simp only [CollatzResearch.WordTrace]
  refine ⟨4343778858287372040393769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23166820577532650882100101 4343778858287372040393769)
  ·
    refine ⟨3257834143715529030295327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4343778858287372040393769 3257834143715529030295327)
    ·
      refine ⟨4886751215573293545442991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3257834143715529030295327 4886751215573293545442991)
      ·
        refine ⟨7330126823359940318164487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4886751215573293545442991 7330126823359940318164487)
        ·
          refine ⟨10995190235039910477246731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7330126823359940318164487 10995190235039910477246731)
          ·
            refine ⟨16492785352559865715870097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10995190235039910477246731 16492785352559865715870097)
            ·
              refine ⟨12369589014419899286902573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16492785352559865715870097 12369589014419899286902573)
              ·
                refine ⟨4638595880407462232588465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12369589014419899286902573 4638595880407462232588465)
                ·
                  refine ⟨3478946910305596674441349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4638595880407462232588465 3478946910305596674441349)
                  ·
                    refine ⟨652302545682299376457753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3478946910305596674441349 652302545682299376457753)
                    ·
                      refine ⟨489226909261724532343315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 652302545682299376457753 489226909261724532343315)
                      ·
                        rfl

theorem cell23_952766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_952766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952766 prefixEnd_952766 := by exact prefixLift 952766
  have htrace : WordTrace (prefixWord ++ tailWord_952766) baseStart_952766 baseEnd_952766 := by
    simpa [prefixWord, tailWord_952766, baseEnd_952766] using wordTrace_append hprefix tailTrace_952766
  have hstable : (prefixWord ++ tailWord_952766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952766).length < 2 ^ (prefixWord ++ tailWord_952766).sum := by decide
  have hdescent : baseEnd_952766 < baseStart_952766 := by decide
  rcases family_descends (prefixWord ++ tailWord_952766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952792 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 1, 1, 8]
def baseStart_952792 : Nat := 118140960795 + 952792 * 2 ^ 59
def prefixEnd_952792 : Nat := 4983230072969 + 3 ^ 40 * 952792 * 2
def baseEnd_952792 : Nat := 489240259758741430618195

theorem tailTrace_952792 : CollatzResearch.WordTrace tailWord_952792 prefixEnd_952792 489240259758741430618195 := by
  unfold tailWord_952792
  simp only [CollatzResearch.WordTrace]
  refine ⟨17375589582102391381798315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23167452776136521842397753 17375589582102391381798315)
  ·
    refine ⟨26063384373153587072697473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17375589582102391381798315 26063384373153587072697473)
    ·
      refine ⟨19547538279865190304523105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26063384373153587072697473 19547538279865190304523105)
      ·
        refine ⟨14660653709898892728392329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19547538279865190304523105 14660653709898892728392329)
        ·
          refine ⟨10995490282424169546294247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14660653709898892728392329 10995490282424169546294247)
          ·
            refine ⟨16493235423636254319441371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10995490282424169546294247 16493235423636254319441371)
            ·
              refine ⟨24739853135454381479162057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16493235423636254319441371 24739853135454381479162057)
              ·
                refine ⟨18554889851590786109371543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24739853135454381479162057 18554889851590786109371543)
                ·
                  refine ⟨27832334777386179164057315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18554889851590786109371543 27832334777386179164057315)
                  ·
                    refine ⟨41748502166079268746085973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27832334777386179164057315 41748502166079268746085973)
                    ·
                      refine ⟨489240259758741430618195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 41748502166079268746085973 489240259758741430618195)
                      ·
                        rfl

theorem cell23_952792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_952792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952792 prefixEnd_952792 := by exact prefixLift 952792
  have htrace : WordTrace (prefixWord ++ tailWord_952792) baseStart_952792 baseEnd_952792 := by
    simpa [prefixWord, tailWord_952792, baseEnd_952792] using wordTrace_append hprefix tailTrace_952792
  have hstable : (prefixWord ++ tailWord_952792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952792).length < 2 ^ (prefixWord ++ tailWord_952792).sum := by decide
  have hdescent : baseEnd_952792 < baseStart_952792 := by decide
  rcases family_descends (prefixWord ++ tailWord_952792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952810 : List Nat := [3, 1, 3, 1, 3, 1, 4, 2, 1, 4]
def baseStart_952810 : Nat := 118140960795 + 952810 * 2 ^ 59
def prefixEnd_952810 : Nat := 4983230072969 + 3 ^ 40 * 952810 * 2
def baseEnd_952810 : Nat := 163083167470174120064371

theorem tailTrace_952810 : CollatzResearch.WordTrace tailWord_952810 prefixEnd_952810 163083167470174120064371 := by
  unfold tailWord_952810
  simp only [CollatzResearch.WordTrace]
  refine ⟨8687958919534892959437971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23167890452093047891834589 8687958919534892959437971)
  ·
    refine ⟨13031938379302339439156957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8687958919534892959437971 13031938379302339439156957)
    ·
      refine ⟨4886976892238377289683859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13031938379302339439156957 4886976892238377289683859)
      ·
        refine ⟨7330465338357565934525789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4886976892238377289683859 7330465338357565934525789)
        ·
          refine ⟨2748924501884087225447171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7330465338357565934525789 2748924501884087225447171)
          ·
            refine ⟨4123386752826130838170757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2748924501884087225447171 4123386752826130838170757)
            ·
              refine ⟨773135016154899532157017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4123386752826130838170757 773135016154899532157017)
              ·
                refine ⟨579851262116174649117763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 773135016154899532157017 579851262116174649117763)
                ·
                  refine ⟨869776893174261973676645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 579851262116174649117763 869776893174261973676645)
                  ·
                    refine ⟨163083167470174120064371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 869776893174261973676645 163083167470174120064371)
                    ·
                      rfl

theorem cell23_952810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_952810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952810 prefixEnd_952810 := by exact prefixLift 952810
  have htrace : WordTrace (prefixWord ++ tailWord_952810) baseStart_952810 baseEnd_952810 := by
    simpa [prefixWord, tailWord_952810, baseEnd_952810] using wordTrace_append hprefix tailTrace_952810
  have hstable : (prefixWord ++ tailWord_952810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952810).length < 2 ^ (prefixWord ++ tailWord_952810).sum := by decide
  have hdescent : baseEnd_952810 < baseStart_952810 := by decide
  rcases family_descends (prefixWord ++ tailWord_952810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952816 : List Nat := [2, 1, 1, 1, 3, 3, 2, 3, 3, 1, 3]
def baseStart_952816 : Nat := 118140960795 + 952816 * 2 ^ 59
def prefixEnd_952816 : Nat := 4983230072969 + 3 ^ 40 * 952816 * 2
def baseEnd_952816 : Nat := 489252583294449336718085

theorem tailTrace_952816 : CollatzResearch.WordTrace tailWord_952816 prefixEnd_952816 489252583294449336718085 := by
  unfold tailWord_952816
  simp only [CollatzResearch.WordTrace]
  refine ⟨17376027258058917431235151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23168036344078556574980201 17376027258058917431235151)
  ·
    refine ⟨26064040887088376146852727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17376027258058917431235151 26064040887088376146852727)
    ·
      refine ⟨39096061330632564220279091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26064040887088376146852727 39096061330632564220279091)
      ·
        refine ⟨58644091995948846330418637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39096061330632564220279091 58644091995948846330418637)
        ·
          refine ⟨21991534498480817373906989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58644091995948846330418637 21991534498480817373906989)
          ·
            refine ⟨8246825436930306515215121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21991534498480817373906989 8246825436930306515215121)
            ·
              refine ⟨6185119077697729886411341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8246825436930306515215121 6185119077697729886411341)
              ·
                refine ⟨2319419654136648707404253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6185119077697729886411341 2319419654136648707404253)
                ·
                  refine ⟨869782370301243265276595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2319419654136648707404253 869782370301243265276595)
                  ·
                    refine ⟨1304673555451864897914893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 869782370301243265276595 1304673555451864897914893)
                    ·
                      refine ⟨489252583294449336718085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1304673555451864897914893 489252583294449336718085)
                      ·
                        rfl

theorem cell23_952816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 3, 1, 3].length) (baseStart_952816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952816 prefixEnd_952816 := by exact prefixLift 952816
  have htrace : WordTrace (prefixWord ++ tailWord_952816) baseStart_952816 baseEnd_952816 := by
    simpa [prefixWord, tailWord_952816, baseEnd_952816] using wordTrace_append hprefix tailTrace_952816
  have hstable : (prefixWord ++ tailWord_952816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952816).length < 2 ^ (prefixWord ++ tailWord_952816).sum := by decide
  have hdescent : baseEnd_952816 < baseStart_952816 := by decide
  rcases family_descends (prefixWord ++ tailWord_952816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952833 : List Nat := [1, 2, 4, 1, 3, 2, 1, 2, 3, 1, 3]
def baseStart_952833 : Nat := 118140960795 + 952833 * 2 ^ 59
def prefixEnd_952833 : Nat := 4983230072969 + 3 ^ 40 * 952833 * 2
def baseEnd_952833 : Nat := 489261312465575770205507

theorem tailTrace_952833 : CollatzResearch.WordTrace tailWord_952833 prefixEnd_952833 489261312465575770205507 := by
  unfold tailWord_952833
  simp only [CollatzResearch.WordTrace]
  refine ⟨34752674557056246765839153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23168449704704164510559435 34752674557056246765839153)
  ·
    refine ⟨26064505917792185074379365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34752674557056246765839153 26064505917792185074379365)
    ·
      refine ⟨4887094859586034701446131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26064505917792185074379365 4887094859586034701446131)
      ·
        refine ⟨7330642289379052052169197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4887094859586034701446131 7330642289379052052169197)
        ·
          refine ⟨2748990858517144519563449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7330642289379052052169197 2748990858517144519563449)
          ·
            refine ⟨2061743143887858389672587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2748990858517144519563449 2061743143887858389672587)
            ·
              refine ⟨3092614715831787584508881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2061743143887858389672587 3092614715831787584508881)
              ·
                refine ⟨2319461036873840688381661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3092614715831787584508881 2319461036873840688381661)
                ·
                  refine ⟨869797888827690258143123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2319461036873840688381661 869797888827690258143123)
                  ·
                    refine ⟨1304696833241535387214685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 869797888827690258143123 1304696833241535387214685)
                    ·
                      refine ⟨489261312465575770205507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1304696833241535387214685 489261312465575770205507)
                      ·
                        rfl

theorem cell23_952833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_952833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952833 prefixEnd_952833 := by exact prefixLift 952833
  have htrace : WordTrace (prefixWord ++ tailWord_952833) baseStart_952833 baseEnd_952833 := by
    simpa [prefixWord, tailWord_952833, baseEnd_952833] using wordTrace_append hprefix tailTrace_952833
  have hstable : (prefixWord ++ tailWord_952833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952833).length < 2 ^ (prefixWord ++ tailWord_952833).sum := by decide
  have hdescent : baseEnd_952833 < baseStart_952833 := by decide
  rcases family_descends (prefixWord ++ tailWord_952833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952836 : List Nat := [2, 3, 2, 3, 1, 1, 2, 1, 3, 5]
def baseStart_952836 : Nat := 118140960795 + 952836 * 2 ^ 59
def prefixEnd_952836 : Nat := 4983230072969 + 3 ^ 40 * 952836 * 2
def baseEnd_952836 : Nat := 163087617635846419489331

theorem tailTrace_952836 : CollatzResearch.WordTrace tailWord_952836 prefixEnd_952836 163087617635846419489331 := by
  unfold tailWord_952836
  simp only [CollatzResearch.WordTrace]
  refine ⟨17376391988022689139099181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23168522650696918852132241 17376391988022689139099181)
  ·
    refine ⟨6516146995508508427162193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17376391988022689139099181 6516146995508508427162193)
    ·
      refine ⟨4887110246631381320371645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6516146995508508427162193 4887110246631381320371645)
      ·
        refine ⟨1832666342486767995139367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4887110246631381320371645 1832666342486767995139367)
        ·
          refine ⟨2748999513730151992709051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1832666342486767995139367 2748999513730151992709051)
          ·
            refine ⟨4123499270595227989063577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2748999513730151992709051 4123499270595227989063577)
            ·
              refine ⟨3092624452946420991797683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4123499270595227989063577 3092624452946420991797683)
              ·
                refine ⟨4638936679419631487696525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3092624452946420991797683 4638936679419631487696525)
                ·
                  refine ⟨1739601254782361807886197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4638936679419631487696525 1739601254782361807886197)
                  ·
                    refine ⟨163087617635846419489331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1739601254782361807886197 163087617635846419489331)
                    ·
                      rfl

theorem cell23_952836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_952836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952836 prefixEnd_952836 := by exact prefixLift 952836
  have htrace : WordTrace (prefixWord ++ tailWord_952836) baseStart_952836 baseEnd_952836 := by
    simpa [prefixWord, tailWord_952836, baseEnd_952836] using wordTrace_append hprefix tailTrace_952836
  have hstable : (prefixWord ++ tailWord_952836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952836).length < 2 ^ (prefixWord ++ tailWord_952836).sum := by decide
  have hdescent : baseEnd_952836 < baseStart_952836 := by decide
  rcases family_descends (prefixWord ++ tailWord_952836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952843 : List Nat := [1, 1, 1, 1, 7, 1, 3, 1, 2, 3, 2]
def baseStart_952843 : Nat := 118140960795 + 952843 * 2 ^ 59
def prefixEnd_952843 : Nat := 4983230072969 + 3 ^ 40 * 952843 * 2
def baseEnd_952843 : Nat := 489266447272120731080461

theorem tailTrace_952843 : CollatzResearch.WordTrace tailWord_952843 prefixEnd_952843 489266447272120731080461 := by
  unfold tailWord_952843
  simp only [CollatzResearch.WordTrace]
  refine ⟨34753039287020018473703183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23168692858013345649135455 34753039287020018473703183)
  ·
    refine ⟨52129558930530027710554775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34753039287020018473703183 52129558930530027710554775)
    ·
      refine ⟨78194338395795041565832163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52129558930530027710554775 78194338395795041565832163)
      ·
        refine ⟨117291507593692562348748245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78194338395795041565832163 117291507593692562348748245)
        ·
          refine ⟨2749019709227169430048787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 117291507593692562348748245 2749019709227169430048787)
          ·
            refine ⟨4123529563840754145073181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2749019709227169430048787 4123529563840754145073181)
            ·
              refine ⟨1546323586440282804402443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4123529563840754145073181 1546323586440282804402443)
              ·
                refine ⟨2319485379660424206603665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1546323586440282804402443 2319485379660424206603665)
                ·
                  refine ⟨1739614034745318154952749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2319485379660424206603665 1739614034745318154952749)
                  ·
                    refine ⟨652355263029494308107281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1739614034745318154952749 652355263029494308107281)
                    ·
                      refine ⟨489266447272120731080461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 652355263029494308107281 489266447272120731080461)
                      ·
                        rfl

theorem cell23_952843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 3, 2].length) (baseStart_952843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952843 prefixEnd_952843 := by exact prefixLift 952843
  have htrace : WordTrace (prefixWord ++ tailWord_952843) baseStart_952843 baseEnd_952843 := by
    simpa [prefixWord, tailWord_952843, baseEnd_952843] using wordTrace_append hprefix tailTrace_952843
  have hstable : (prefixWord ++ tailWord_952843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952843).length < 2 ^ (prefixWord ++ tailWord_952843).sum := by decide
  have hdescent : baseEnd_952843 < baseStart_952843 := by decide
  rcases family_descends (prefixWord ++ tailWord_952843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952869 : List Nat := [1, 3, 1, 2, 2, 1, 2, 2, 3, 2, 4]
def baseStart_952869 : Nat := 118140960795 + 952869 * 2 ^ 59
def prefixEnd_952869 : Nat := 4983230072969 + 3 ^ 40 * 952869 * 2
def baseEnd_952869 : Nat := 489279797769137629355341

theorem tailTrace_952869 : CollatzResearch.WordTrace tailWord_952869 prefixEnd_952869 489279797769137629355341 := by
  unfold tailWord_952869
  simp only [CollatzResearch.WordTrace]
  refine ⟨34753987584925824914149661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23169325056617216609433107 34753987584925824914149661)
  ·
    refine ⟨13032745344347184342806123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34753987584925824914149661 13032745344347184342806123)
    ·
      refine ⟨19549118016520776514209185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13032745344347184342806123 19549118016520776514209185)
      ·
        refine ⟨14661838512390582385656889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19549118016520776514209185 14661838512390582385656889)
        ·
          refine ⟨10996378884292936789242667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14661838512390582385656889 10996378884292936789242667)
          ·
            refine ⟨16494568326439405183864001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10996378884292936789242667 16494568326439405183864001)
            ·
              refine ⟨12370926244829553887898001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16494568326439405183864001 12370926244829553887898001)
              ·
                refine ⟨9278194683622165415923501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12370926244829553887898001 9278194683622165415923501)
                ·
                  refine ⟨3479323006358312030971313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9278194683622165415923501 3479323006358312030971313)
                  ·
                    refine ⟨2609492254768734023228485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3479323006358312030971313 2609492254768734023228485)
                    ·
                      refine ⟨489279797769137629355341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2609492254768734023228485 489279797769137629355341)
                      ·
                        rfl

theorem cell23_952869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_952869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952869 prefixEnd_952869 := by exact prefixLift 952869
  have htrace : WordTrace (prefixWord ++ tailWord_952869) baseStart_952869 baseEnd_952869 := by
    simpa [prefixWord, tailWord_952869, baseEnd_952869] using wordTrace_append hprefix tailTrace_952869
  have hstable : (prefixWord ++ tailWord_952869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952869).length < 2 ^ (prefixWord ++ tailWord_952869).sum := by decide
  have hdescent : baseEnd_952869 < baseStart_952869 := by decide
  rcases family_descends (prefixWord ++ tailWord_952869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952883 : List Nat := [1, 1, 1, 2, 4, 2, 5, 1, 2, 4]
def baseStart_952883 : Nat := 118140960795 + 952883 * 2 ^ 59
def prefixEnd_952883 : Nat := 4983230072969 + 3 ^ 40 * 952883 * 2
def baseEnd_952883 : Nat := 163095662166100191526759

theorem tailTrace_952883 : CollatzResearch.WordTrace tailWord_952883 prefixEnd_952883 163095662166100191526759 := by
  unfold tailWord_952883
  simp only [CollatzResearch.WordTrace]
  refine ⟨34754498206875105305159303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23169665471250070203439535 34754498206875105305159303)
  ·
    refine ⟨52131747310312657957738955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34754498206875105305159303 52131747310312657957738955)
    ·
      refine ⟨78197620965468986936608433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52131747310312657957738955 78197620965468986936608433)
      ·
        refine ⟨58648215724101740202456325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78197620965468986936608433 58648215724101740202456325)
        ·
          refine ⟨10996540448269076287960561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58648215724101740202456325 10996540448269076287960561)
          ·
            refine ⟨8247405336201807215970421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10996540448269076287960561 8247405336201807215970421)
            ·
              refine ⟨773194250268919426497227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8247405336201807215970421 773194250268919426497227)
              ·
                refine ⟨1159791375403379139745841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 773194250268919426497227 1159791375403379139745841)
                ·
                  refine ⟨869843531552534354809381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1159791375403379139745841 869843531552534354809381)
                  ·
                    refine ⟨163095662166100191526759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 869843531552534354809381 163095662166100191526759)
                    ·
                      rfl

theorem cell23_952883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 2, 4].length) (baseStart_952883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952883 prefixEnd_952883 := by exact prefixLift 952883
  have htrace : WordTrace (prefixWord ++ tailWord_952883) baseStart_952883 baseEnd_952883 := by
    simpa [prefixWord, tailWord_952883, baseEnd_952883] using wordTrace_append hprefix tailTrace_952883
  have hstable : (prefixWord ++ tailWord_952883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952883).length < 2 ^ (prefixWord ++ tailWord_952883).sum := by decide
  have hdescent : baseEnd_952883 < baseStart_952883 := by decide
  rcases family_descends (prefixWord ++ tailWord_952883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952893 : List Nat := [1, 4, 1, 3, 2, 1, 1, 4, 1, 2, 3]
def baseStart_952893 : Nat := 118140960795 + 952893 * 2 ^ 59
def prefixEnd_952893 : Nat := 4983230072969 + 3 ^ 40 * 952893 * 2
def baseEnd_952893 : Nat := 489292121304845535455231

theorem tailTrace_952893 : CollatzResearch.WordTrace tailWord_952893 prefixEnd_952893 489292121304845535455231 := by
  unfold tailWord_952893
  simp only [CollatzResearch.WordTrace]
  refine ⟨34754862936838877013023333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23169908624559251342015555 34754862936838877013023333)
  ·
    refine ⟨6516536800657289439941875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34754862936838877013023333 6516536800657289439941875)
    ·
      refine ⟨9774805200985934159912813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6516536800657289439941875 9774805200985934159912813)
      ·
        refine ⟨3665551950369725309967305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9774805200985934159912813 3665551950369725309967305)
        ·
          refine ⟨2749163962777293982475479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3665551950369725309967305 2749163962777293982475479)
          ·
            refine ⟨4123745944165940973713219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2749163962777293982475479 4123745944165940973713219)
            ·
              refine ⟨6185618916248911460569829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4123745944165940973713219 6185618916248911460569829)
              ·
                refine ⟨1159803546796670898856843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6185618916248911460569829 1159803546796670898856843)
                ·
                  refine ⟨1739705320195006348285265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1159803546796670898856843 1739705320195006348285265)
                  ·
                    refine ⟨1304778990146254761213949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1739705320195006348285265 1304778990146254761213949)
                    ·
                      refine ⟨489292121304845535455231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1304778990146254761213949 489292121304845535455231)
                      ·
                        rfl

theorem cell23_952893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_952893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952893 prefixEnd_952893 := by exact prefixLift 952893
  have htrace : WordTrace (prefixWord ++ tailWord_952893) baseStart_952893 baseEnd_952893 := by
    simpa [prefixWord, tailWord_952893, baseEnd_952893] using wordTrace_append hprefix tailTrace_952893
  have hstable : (prefixWord ++ tailWord_952893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952893).length < 2 ^ (prefixWord ++ tailWord_952893).sum := by decide
  have hdescent : baseEnd_952893 < baseStart_952893 := by decide
  rcases family_descends (prefixWord ++ tailWord_952893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952919 : List Nat := [1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 5]
def baseStart_952919 : Nat := 118140960795 + 952919 * 2 ^ 59
def prefixEnd_952919 : Nat := 4983230072969 + 3 ^ 40 * 952919 * 2
def baseEnd_952919 : Nat := 489305471801862433730111

theorem tailTrace_952919 : CollatzResearch.WordTrace tailWord_952919 prefixEnd_952919 489305471801862433730111 := by
  unfold tailWord_952919
  simp only [CollatzResearch.WordTrace]
  refine ⟨34755811234744683453469811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23170540823163122302313207 34755811234744683453469811)
  ·
    refine ⟨52133716852117025180204717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34755811234744683453469811 52133716852117025180204717)
    ·
      refine ⟨19550143819543884442576769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52133716852117025180204717 19550143819543884442576769)
      ·
        refine ⟨14662607864657913331932577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19550143819543884442576769 14662607864657913331932577)
        ·
          refine ⟨10996955898493434998949433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14662607864657913331932577 10996955898493434998949433)
          ·
            refine ⟨8247716923870076249212075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10996955898493434998949433 8247716923870076249212075)
            ·
              refine ⟨12371575385805114373818113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8247716923870076249212075 12371575385805114373818113)
              ·
                refine ⟨9278681539353835780363585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12371575385805114373818113 9278681539353835780363585)
                ·
                  refine ⟨6959011154515376835272689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9278681539353835780363585 6959011154515376835272689)
                  ·
                    refine ⟨5219258365886532626454517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6959011154515376835272689 5219258365886532626454517)
                    ·
                      refine ⟨489305471801862433730111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5219258365886532626454517 489305471801862433730111)
                      ·
                        rfl

theorem cell23_952919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_952919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952919 prefixEnd_952919 := by exact prefixLift 952919
  have htrace : WordTrace (prefixWord ++ tailWord_952919) baseStart_952919 baseEnd_952919 := by
    simpa [prefixWord, tailWord_952919, baseEnd_952919] using wordTrace_append hprefix tailTrace_952919
  have hstable : (prefixWord ++ tailWord_952919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952919).length < 2 ^ (prefixWord ++ tailWord_952919).sum := by decide
  have hdescent : baseEnd_952919 < baseStart_952919 := by decide
  rcases family_descends (prefixWord ++ tailWord_952919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952924 : List Nat := [2, 2, 4, 1, 4, 1, 1, 1, 3, 2, 2]
def baseStart_952924 : Nat := 118140960795 + 952924 * 2 ^ 59
def prefixEnd_952924 : Nat := 4983230072969 + 3 ^ 40 * 952924 * 2
def baseEnd_952924 : Nat := 489308039205134914167589

theorem tailTrace_952924 : CollatzResearch.WordTrace tailWord_952924 prefixEnd_952924 489308039205134914167589 := by
  unfold tailWord_952924
  simp only [CollatzResearch.WordTrace]
  refine ⟨17377996799863284653700913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23170662399817712871601217 17377996799863284653700913)
  ·
    refine ⟨13033497599897463490275685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17377996799863284653700913 13033497599897463490275685)
    ·
      refine ⟨2443780799980774404426691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13033497599897463490275685 2443780799980774404426691)
      ·
        refine ⟨3665671199971161606640037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2443780799980774404426691 3665671199971161606640037)
        ·
          refine ⟨687313349994592801245007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3665671199971161606640037 687313349994592801245007)
          ·
            refine ⟨1030970024991889201867511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 687313349994592801245007 1030970024991889201867511)
            ·
              refine ⟨1546455037487833802801267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1030970024991889201867511 1546455037487833802801267)
              ·
                refine ⟨2319682556231750704201901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1546455037487833802801267 2319682556231750704201901)
                ·
                  refine ⟨869880958586906514075713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2319682556231750704201901 869880958586906514075713)
                  ·
                    refine ⟨652410718940179885556785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 869880958586906514075713 652410718940179885556785)
                    ·
                      refine ⟨489308039205134914167589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 652410718940179885556785 489308039205134914167589)
                      ·
                        rfl

theorem cell23_952924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_952924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952924 prefixEnd_952924 := by exact prefixLift 952924
  have htrace : WordTrace (prefixWord ++ tailWord_952924) baseStart_952924 baseEnd_952924 := by
    simpa [prefixWord, tailWord_952924, baseEnd_952924] using wordTrace_append hprefix tailTrace_952924
  have hstable : (prefixWord ++ tailWord_952924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952924).length < 2 ^ (prefixWord ++ tailWord_952924).sum := by decide
  have hdescent : baseEnd_952924 < baseStart_952924 := by decide
  rcases family_descends (prefixWord ++ tailWord_952924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952940 : List Nat := [2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 3]
def baseStart_952940 : Nat := 118140960795 + 952940 * 2 ^ 59
def prefixEnd_952940 : Nat := 4983230072969 + 3 ^ 40 * 952940 * 2
def baseEnd_952940 : Nat := 489316254895606851567515

theorem tailTrace_952940 : CollatzResearch.WordTrace tailWord_952940 prefixEnd_952940 489316254895606851567515 := by
  unfold tailWord_952940
  simp only [CollatzResearch.WordTrace]
  refine ⟨17378288583834302019992137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23171051445112402693322849 17378288583834302019992137)
  ·
    refine ⟨13033716437875726514994103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17378288583834302019992137 13033716437875726514994103)
    ·
      refine ⟨19550574656813589772491155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13033716437875726514994103 19550574656813589772491155)
      ·
        refine ⟨29325861985220384658736733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19550574656813589772491155 29325861985220384658736733)
        ·
          refine ⟨10997198244457644247026275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29325861985220384658736733 10997198244457644247026275)
          ·
            refine ⟨16495797366686466370539413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10997198244457644247026275 16495797366686466370539413)
            ·
              refine ⟨773240501563428111119035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16495797366686466370539413 773240501563428111119035)
              ·
                refine ⟨1159860752345142166678553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 773240501563428111119035 1159860752345142166678553)
                ·
                  refine ⟨869895564258856625008915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1159860752345142166678553 869895564258856625008915)
                  ·
                    refine ⟨1304843346388284937513373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 869895564258856625008915 1304843346388284937513373)
                    ·
                      refine ⟨489316254895606851567515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1304843346388284937513373 489316254895606851567515)
                      ·
                        rfl

theorem cell23_952940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 3].length) (baseStart_952940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952940 prefixEnd_952940 := by exact prefixLift 952940
  have htrace : WordTrace (prefixWord ++ tailWord_952940) baseStart_952940 baseEnd_952940 := by
    simpa [prefixWord, tailWord_952940, baseEnd_952940] using wordTrace_append hprefix tailTrace_952940
  have hstable : (prefixWord ++ tailWord_952940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952940).length < 2 ^ (prefixWord ++ tailWord_952940).sum := by decide
  have hdescent : baseEnd_952940 < baseStart_952940 := by decide
  rcases family_descends (prefixWord ++ tailWord_952940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952959 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 4]
def baseStart_952959 : Nat := 118140960795 + 952959 * 2 ^ 59
def prefixEnd_952959 : Nat := 4983230072969 + 3 ^ 40 * 952959 * 2
def baseEnd_952959 : Nat := 489326011028042277229927

theorem tailTrace_952959 : CollatzResearch.WordTrace tailWord_952959 prefixEnd_952959 489326011028042277229927 := by
  unfold tailWord_952959
  simp only [CollatzResearch.WordTrace]
  refine ⟨34757270154599770284925931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23171513436399846856617287 34757270154599770284925931)
  ·
    refine ⟨52135905231899655427388897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34757270154599770284925931 52135905231899655427388897)
    ·
      refine ⟨39101928923924741570541673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52135905231899655427388897 39101928923924741570541673)
      ·
        refine ⟨29326446692943556177906255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39101928923924741570541673 29326446692943556177906255)
        ·
          refine ⟨43989670039415334266859383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29326446692943556177906255 43989670039415334266859383)
          ·
            refine ⟨65984505059123001400289075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43989670039415334266859383 65984505059123001400289075)
            ·
              refine ⟨98976757588684502100433613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65984505059123001400289075 98976757588684502100433613)
              ·
                refine ⟨37116284095756688287662605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98976757588684502100433613 37116284095756688287662605)
                ·
                  refine ⟨13918606535908758107873477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37116284095756688287662605 13918606535908758107873477)
                  ·
                    refine ⟨2609738725482892145226277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13918606535908758107873477 2609738725482892145226277)
                    ·
                      refine ⟨489326011028042277229927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2609738725482892145226277 489326011028042277229927)
                      ·
                        rfl

theorem cell23_952959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_952959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952959 prefixEnd_952959 := by exact prefixLift 952959
  have htrace : WordTrace (prefixWord ++ tailWord_952959) baseStart_952959 baseEnd_952959 := by
    simpa [prefixWord, tailWord_952959, baseEnd_952959] using wordTrace_append hprefix tailTrace_952959
  have hstable : (prefixWord ++ tailWord_952959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952959).length < 2 ^ (prefixWord ++ tailWord_952959).sum := by decide
  have hdescent : baseEnd_952959 < baseStart_952959 := by decide
  rcases family_descends (prefixWord ++ tailWord_952959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952963 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 6, 2, 2]
def baseStart_952963 : Nat := 118140960795 + 952963 * 2 ^ 59
def prefixEnd_952963 : Nat := 4983230072969 + 3 ^ 40 * 952963 * 2
def baseEnd_952963 : Nat := 489328064950660261579909

theorem tailTrace_952963 : CollatzResearch.WordTrace tailWord_952963 prefixEnd_952963 489328064950660261579909 := by
  unfold tailWord_952963
  simp only [CollatzResearch.WordTrace]
  refine ⟨34757416046585278968071543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23171610697723519312047695 34757416046585278968071543)
  ·
    refine ⟨52136124069877918452107315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34757416046585278968071543 52136124069877918452107315)
    ·
      refine ⟨78204186104816877678160973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52136124069877918452107315 78204186104816877678160973)
      ·
        refine ⟨29326569789306329129310365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78204186104816877678160973 29326569789306329129310365)
        ·
          refine ⟨10997463670989873423491387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29326569789306329129310365 10997463670989873423491387)
          ·
            refine ⟨16496195506484810135237081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10997463670989873423491387 16496195506484810135237081)
            ·
              refine ⟨12372146629863607601427811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16496195506484810135237081 12372146629863607601427811)
              ·
                refine ⟨18558219944795411402141717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12372146629863607601427811 18558219944795411402141717)
                ·
                  refine ⟨869916559912284909475393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 18558219944795411402141717 869916559912284909475393)
                  ·
                    refine ⟨652437419934213682106545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 869916559912284909475393 652437419934213682106545)
                    ·
                      refine ⟨489328064950660261579909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 652437419934213682106545 489328064950660261579909)
                      ·
                        rfl

theorem cell23_952963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 6, 2, 2].length) (baseStart_952963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952963 prefixEnd_952963 := by exact prefixLift 952963
  have htrace : WordTrace (prefixWord ++ tailWord_952963) baseStart_952963 baseEnd_952963 := by
    simpa [prefixWord, tailWord_952963, baseEnd_952963] using wordTrace_append hprefix tailTrace_952963
  have hstable : (prefixWord ++ tailWord_952963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952963).length < 2 ^ (prefixWord ++ tailWord_952963).sum := by decide
  have hdescent : baseEnd_952963 < baseStart_952963 := by decide
  rcases family_descends (prefixWord ++ tailWord_952963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_952993 : List Nat := [1, 2, 3, 3, 3, 1, 1, 1, 2, 2, 4]
def baseStart_952993 : Nat := 118140960795 + 952993 * 2 ^ 59
def prefixEnd_952993 : Nat := 4983230072969 + 3 ^ 40 * 952993 * 2
def baseEnd_952993 : Nat := 489343469370295144204771

theorem tailTrace_952993 : CollatzResearch.WordTrace tailWord_952993 prefixEnd_952993 489343469370295144204771 := by
  unfold tailWord_952993
  simp only [CollatzResearch.WordTrace]
  refine ⟨34758510236476594091663633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23172340157651062727775755 34758510236476594091663633)
  ·
    refine ⟨26068882677357445568747725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34758510236476594091663633 26068882677357445568747725)
    ·
      refine ⟨9775831004009042088280397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26068882677357445568747725 9775831004009042088280397)
      ·
        refine ⟨3665936626503390783105149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9775831004009042088280397 3665936626503390783105149)
        ·
          refine ⟨1374726234938771543664431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3665936626503390783105149 1374726234938771543664431)
          ·
            refine ⟨2062089352408157315496647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1374726234938771543664431 2062089352408157315496647)
            ·
              refine ⟨3093134028612235973244971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2062089352408157315496647 3093134028612235973244971)
              ·
                refine ⟨4639701042918353959867457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3093134028612235973244971 4639701042918353959867457)
                ·
                  refine ⟨3479775782188765469900593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4639701042918353959867457 3479775782188765469900593)
                  ·
                    refine ⟨2609831836641574102425445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3479775782188765469900593 2609831836641574102425445)
                    ·
                      refine ⟨489343469370295144204771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2609831836641574102425445 489343469370295144204771)
                      ·
                        rfl

theorem cell23_952993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_952993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_952993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_952993 prefixEnd_952993 := by exact prefixLift 952993
  have htrace : WordTrace (prefixWord ++ tailWord_952993) baseStart_952993 baseEnd_952993 := by
    simpa [prefixWord, tailWord_952993, baseEnd_952993] using wordTrace_append hprefix tailTrace_952993
  have hstable : (prefixWord ++ tailWord_952993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_952993).length < 2 ^ (prefixWord ++ tailWord_952993).sum := by decide
  have hdescent : baseEnd_952993 < baseStart_952993 := by decide
  rcases family_descends (prefixWord ++ tailWord_952993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953066 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 1, 6, 4]
def baseStart_953066 : Nat := 118140960795 + 953066 * 2 ^ 59
def prefixEnd_953066 : Nat := 4983230072969 + 3 ^ 40 * 953066 * 2
def baseEnd_953066 : Nat := 489380953458073358591935

theorem tailTrace_953066 : CollatzResearch.WordTrace tailWord_953066 prefixEnd_953066 489380953458073358591935 := by
  unfold tailWord_953066
  simp only [CollatzResearch.WordTrace]
  refine ⟨8690293191303031889767763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23174115176808085039380701 8690293191303031889767763)
  ·
    refine ⟨13035439786954547834651645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8690293191303031889767763 13035439786954547834651645)
    ·
      refine ⟨4888289920107955437994367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13035439786954547834651645 4888289920107955437994367)
      ·
        refine ⟨7332434880161933156991551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4888289920107955437994367 7332434880161933156991551)
        ·
          refine ⟨10998652320242899735487327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7332434880161933156991551 10998652320242899735487327)
          ·
            refine ⟨16497978480364349603230991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10998652320242899735487327 16497978480364349603230991)
            ·
              refine ⟨24746967720546524404846487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16497978480364349603230991 24746967720546524404846487)
              ·
                refine ⟨37120451580819786607269731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24746967720546524404846487 37120451580819786607269731)
                ·
                  refine ⟨55680677371229679910904597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37120451580819786607269731 55680677371229679910904597)
                  ·
                    refine ⟨2610031751776391245823653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55680677371229679910904597 2610031751776391245823653)
                    ·
                      refine ⟨489380953458073358591935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2610031751776391245823653 489380953458073358591935)
                      ·
                        rfl

theorem cell23_953066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_953066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953066 prefixEnd_953066 := by exact prefixLift 953066
  have htrace : WordTrace (prefixWord ++ tailWord_953066) baseStart_953066 baseEnd_953066 := by
    simpa [prefixWord, tailWord_953066, baseEnd_953066] using wordTrace_append hprefix tailTrace_953066
  have hstable : (prefixWord ++ tailWord_953066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953066).length < 2 ^ (prefixWord ++ tailWord_953066).sum := by decide
  have hdescent : baseEnd_953066 < baseStart_953066 := by decide
  rcases family_descends (prefixWord ++ tailWord_953066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953073 : List Nat := [1, 2, 2, 2, 2, 2, 2, 3, 2, 2, 3]
def baseStart_953073 : Nat := 118140960795 + 953073 * 2 ^ 59
def prefixEnd_953073 : Nat := 4983230072969 + 3 ^ 40 * 953073 * 2
def baseEnd_953073 : Nat := 489384547822654831204403

theorem tailTrace_953073 : CollatzResearch.WordTrace tailWord_953073 prefixEnd_953073 489384547822654831204403 := by
  unfold tailWord_953073
  simp only [CollatzResearch.WordTrace]
  refine ⟨34761428076186767754575873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23174285384124511836383915 34761428076186767754575873)
  ·
    refine ⟨26071071057140075815931905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34761428076186767754575873 26071071057140075815931905)
    ·
      refine ⟨19553303292855056861948929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26071071057140075815931905 19553303292855056861948929)
      ·
        refine ⟨14664977469641292646461697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19553303292855056861948929 14664977469641292646461697)
        ·
          refine ⟨10998733102230969484846273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14664977469641292646461697 10998733102230969484846273)
          ·
            refine ⟨8249049826673227113634705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10998733102230969484846273 8249049826673227113634705)
            ·
              refine ⟨6186787370004920335226029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8249049826673227113634705 6186787370004920335226029)
              ·
                refine ⟨2320045263751845125709761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6186787370004920335226029 2320045263751845125709761)
                ·
                  refine ⟨1740033947813883844282321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2320045263751845125709761 1740033947813883844282321)
                  ·
                    refine ⟨1305025460860412883211741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1740033947813883844282321 1305025460860412883211741)
                    ·
                      refine ⟨489384547822654831204403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1305025460860412883211741 489384547822654831204403)
                      ·
                        rfl

theorem cell23_953073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_953073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953073 prefixEnd_953073 := by exact prefixLift 953073
  have htrace : WordTrace (prefixWord ++ tailWord_953073) baseStart_953073 baseEnd_953073 := by
    simpa [prefixWord, tailWord_953073, baseEnd_953073] using wordTrace_append hprefix tailTrace_953073
  have hstable : (prefixWord ++ tailWord_953073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953073).length < 2 ^ (prefixWord ++ tailWord_953073).sum := by decide
  have hdescent : baseEnd_953073 < baseStart_953073 := by decide
  rcases family_descends (prefixWord ++ tailWord_953073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953090 : List Nat := [3, 4, 1, 1, 1, 2, 1, 1, 4, 2, 3]
def baseStart_953090 : Nat := 118140960795 + 953090 * 2 ^ 59
def prefixEnd_953090 : Nat := 4983230072969 + 3 ^ 40 * 953090 * 2
def baseEnd_953090 : Nat := 489393276993781264691825

theorem tailTrace_953090 : CollatzResearch.WordTrace tailWord_953090 prefixEnd_953090 489393276993781264691825 := by
  unfold tailWord_953090
  simp only [CollatzResearch.WordTrace]
  refine ⟨8690512029281294914486181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23174698744750119771963149 8690512029281294914486181)
  ·
    refine ⟨1629471005490242796466159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8690512029281294914486181 1629471005490242796466159)
    ·
      refine ⟨2444206508235364194699239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1629471005490242796466159 2444206508235364194699239)
      ·
        refine ⟨3666309762353046292048859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2444206508235364194699239 3666309762353046292048859)
        ·
          refine ⟨5499464643529569438073289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3666309762353046292048859 5499464643529569438073289)
          ·
            refine ⟨4124598482647177078554967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5499464643529569438073289 4124598482647177078554967)
            ·
              refine ⟨6186897723970765617832451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4124598482647177078554967 6186897723970765617832451)
              ·
                refine ⟨9280346585956148426748677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6186897723970765617832451 9280346585956148426748677)
                ·
                  refine ⟨1740064984866777830015377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9280346585956148426748677 1740064984866777830015377)
                  ·
                    refine ⟨1305048738650083372511533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1740064984866777830015377 1305048738650083372511533)
                    ·
                      refine ⟨489393276993781264691825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1305048738650083372511533 489393276993781264691825)
                      ·
                        rfl

theorem cell23_953090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_953090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953090 prefixEnd_953090 := by exact prefixLift 953090
  have htrace : WordTrace (prefixWord ++ tailWord_953090) baseStart_953090 baseEnd_953090 := by
    simpa [prefixWord, tailWord_953090, baseEnd_953090] using wordTrace_append hprefix tailTrace_953090
  have hstable : (prefixWord ++ tailWord_953090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953090).length < 2 ^ (prefixWord ++ tailWord_953090).sum := by decide
  have hdescent : baseEnd_953090 < baseStart_953090 := by decide
  rcases family_descends (prefixWord ++ tailWord_953090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953113 : List Nat := [1, 2, 1, 2, 1, 1, 1, 6, 1, 5, 2]
def baseStart_953113 : Nat := 118140960795 + 953113 * 2 ^ 59
def prefixEnd_953113 : Nat := 4983230072969 + 3 ^ 40 * 953113 * 2
def baseEnd_953113 : Nat := 489405087048834674704219

theorem tailTrace_953113 : CollatzResearch.WordTrace tailWord_953113 prefixEnd_953113 489405087048834674704219 := by
  unfold tailWord_953113
  simp only [CollatzResearch.WordTrace]
  refine ⟨34762886996041854586031993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23175257997361236390687995 34762886996041854586031993)
  ·
    refine ⟨26072165247031390939523995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34762886996041854586031993 26072165247031390939523995)
    ·
      refine ⟨39108247870547086409285993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26072165247031390939523995 39108247870547086409285993)
      ·
        refine ⟨29331185902910314806964495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39108247870547086409285993 29331185902910314806964495)
        ·
          refine ⟨43996778854365472210446743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29331185902910314806964495 43996778854365472210446743)
          ·
            refine ⟨65995168281548208315670115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43996778854365472210446743 65995168281548208315670115)
            ·
              refine ⟨98992752422322312473505173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65995168281548208315670115 98992752422322312473505173)
              ·
                refine ⟨4640285269796358397195555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98992752422322312473505173 4640285269796358397195555)
                ·
                  refine ⟨6960427904694537595793333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4640285269796358397195555 6960427904694537595793333)
                  ·
                    refine ⟨652540116065112899605625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6960427904694537595793333 652540116065112899605625)
                    ·
                      refine ⟨489405087048834674704219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 652540116065112899605625 489405087048834674704219)
                      ·
                        rfl

theorem cell23_953113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 5, 2].length) (baseStart_953113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953113 prefixEnd_953113 := by exact prefixLift 953113
  have htrace : WordTrace (prefixWord ++ tailWord_953113) baseStart_953113 baseEnd_953113 := by
    simpa [prefixWord, tailWord_953113, baseEnd_953113] using wordTrace_append hprefix tailTrace_953113
  have hstable : (prefixWord ++ tailWord_953113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953113).length < 2 ^ (prefixWord ++ tailWord_953113).sum := by decide
  have hdescent : baseEnd_953113 < baseStart_953113 := by decide
  rcases family_descends (prefixWord ++ tailWord_953113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953137 : List Nat := [1, 2, 2, 3, 2, 1, 2, 5, 1, 1, 3]
def baseStart_953137 : Nat := 118140960795 + 953137 * 2 ^ 59
def prefixEnd_953137 : Nat := 4983230072969 + 3 ^ 40 * 953137 * 2
def baseEnd_953137 : Nat := 489417410584542580804109

theorem tailTrace_953137 : CollatzResearch.WordTrace tailWord_953137 prefixEnd_953137 489417410584542580804109 := by
  unfold tailWord_953137
  simp only [CollatzResearch.WordTrace]
  refine ⟨34763762347954906684905665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23175841565303271123270443 34763762347954906684905665)
  ·
    refine ⟨26072821760966180013679249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34763762347954906684905665 26072821760966180013679249)
    ·
      refine ⟨19554616320724635010259437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26072821760966180013679249 19554616320724635010259437)
      ·
        refine ⟨7332981120271738128847289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19554616320724635010259437 7332981120271738128847289)
        ·
          refine ⟨5499735840203803596635467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7332981120271738128847289 5499735840203803596635467)
          ·
            refine ⟨8249603760305705394953201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5499735840203803596635467 8249603760305705394953201)
            ·
              refine ⟨6187202820229279046214901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8249603760305705394953201 6187202820229279046214901)
              ·
                refine ⟨580050264396494910582647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6187202820229279046214901 580050264396494910582647)
                ·
                  refine ⟨870075396594742365873971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 580050264396494910582647 870075396594742365873971)
                  ·
                    refine ⟨1305113094892113548810957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 870075396594742365873971 1305113094892113548810957)
                    ·
                      refine ⟨489417410584542580804109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1305113094892113548810957 489417410584542580804109)
                      ·
                        rfl

theorem cell23_953137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_953137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953137 prefixEnd_953137 := by exact prefixLift 953137
  have htrace : WordTrace (prefixWord ++ tailWord_953137) baseStart_953137 baseEnd_953137 := by
    simpa [prefixWord, tailWord_953137, baseEnd_953137] using wordTrace_append hprefix tailTrace_953137
  have hstable : (prefixWord ++ tailWord_953137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953137).length < 2 ^ (prefixWord ++ tailWord_953137).sum := by decide
  have hdescent : baseEnd_953137 < baseStart_953137 := by decide
  rcases family_descends (prefixWord ++ tailWord_953137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953170 : List Nat := [3, 2, 2, 1, 1, 2, 1, 5, 2, 4]
def baseStart_953170 : Nat := 118140960795 + 953170 * 2 ^ 59
def prefixEnd_953170 : Nat := 4983230072969 + 3 ^ 40 * 953170 * 2
def baseEnd_953170 : Nat := 163144785148713650563819

theorem tailTrace_953170 : CollatzResearch.WordTrace tailWord_953170 prefixEnd_953170 163144785148713650563819 := by
  unfold tailWord_953170
  simp only [CollatzResearch.WordTrace]
  refine ⟨8691241489208838330214241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23176643971223568880571309 8691241489208838330214241)
  ·
    refine ⟨6518431116906628747660681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8691241489208838330214241 6518431116906628747660681)
    ·
      refine ⟨4888823337679971560745511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6518431116906628747660681 4888823337679971560745511)
      ·
        refine ⟨7333235006519957341118267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4888823337679971560745511 7333235006519957341118267)
        ·
          refine ⟨10999852509779936011677401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7333235006519957341118267 10999852509779936011677401)
          ·
            refine ⟨8249889382334952008758051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10999852509779936011677401 8249889382334952008758051)
            ·
              refine ⟨12374834073502428013137077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8249889382334952008758051 12374834073502428013137077)
              ·
                refine ⟨1160140694390852626231601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12374834073502428013137077 1160140694390852626231601)
                ·
                  refine ⟨870105520793139469673701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1160140694390852626231601 870105520793139469673701)
                  ·
                    refine ⟨163144785148713650563819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 870105520793139469673701 163144785148713650563819)
                    ·
                      rfl

theorem cell23_953170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_953170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953170 prefixEnd_953170 := by exact prefixLift 953170
  have htrace : WordTrace (prefixWord ++ tailWord_953170) baseStart_953170 baseEnd_953170 := by
    simpa [prefixWord, tailWord_953170, baseEnd_953170] using wordTrace_append hprefix tailTrace_953170
  have hstable : (prefixWord ++ tailWord_953170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953170).length < 2 ^ (prefixWord ++ tailWord_953170).sum := by decide
  have hdescent : baseEnd_953170 < baseStart_953170 := by decide
  rcases family_descends (prefixWord ++ tailWord_953170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953176 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 2, 2, 7]
def baseStart_953176 : Nat := 118140960795 + 953176 * 2 ^ 59
def prefixEnd_953176 : Nat := 4983230072969 + 3 ^ 40 * 953176 * 2
def baseEnd_953176 : Nat := 489437436330067928216429

theorem tailTrace_953176 : CollatzResearch.WordTrace tailWord_953176 prefixEnd_953176 489437436330067928216429 := by
  unfold tailWord_953176
  simp only [CollatzResearch.WordTrace]
  refine ⟨17382592397406808172787691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23176789863209077563716921 17382592397406808172787691)
  ·
    refine ⟨26073888596110212259181537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17382592397406808172787691 26073888596110212259181537)
    ·
      refine ⟨19555416447082659194386153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26073888596110212259181537 19555416447082659194386153)
      ·
        refine ⟨14666562335311994395789615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19555416447082659194386153 14666562335311994395789615)
        ·
          refine ⟨21999843502967991593684423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14666562335311994395789615 21999843502967991593684423)
          ·
            refine ⟨32999765254451987390526635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21999843502967991593684423 32999765254451987390526635)
            ·
              refine ⟨49499647881677981085789953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32999765254451987390526635 49499647881677981085789953)
              ·
                refine ⟨37124735911258485814342465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49499647881677981085789953 37124735911258485814342465)
                ·
                  refine ⟨27843551933443864360756849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37124735911258485814342465 27843551933443864360756849)
                  ·
                    refine ⟨20882663950082898270567637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27843551933443864360756849 20882663950082898270567637)
                    ·
                      refine ⟨489437436330067928216429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 20882663950082898270567637 489437436330067928216429)
                      ·
                        rfl

theorem cell23_953176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_953176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953176 prefixEnd_953176 := by exact prefixLift 953176
  have htrace : WordTrace (prefixWord ++ tailWord_953176) baseStart_953176 baseEnd_953176 := by
    simpa [prefixWord, tailWord_953176, baseEnd_953176] using wordTrace_append hprefix tailTrace_953176
  have hstable : (prefixWord ++ tailWord_953176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953176).length < 2 ^ (prefixWord ++ tailWord_953176).sum := by decide
  have hdescent : baseEnd_953176 < baseStart_953176 := by decide
  rcases family_descends (prefixWord ++ tailWord_953176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953177 : List Nat := [1, 2, 1, 2, 2, 5, 1, 2, 3, 2, 2]
def baseStart_953177 : Nat := 118140960795 + 953177 * 2 ^ 59
def prefixEnd_953177 : Nat := 4983230072969 + 3 ^ 40 * 953177 * 2
def baseEnd_953177 : Nat := 489437949810722424303925

theorem tailTrace_953177 : CollatzResearch.WordTrace tailWord_953177 prefixEnd_953177 489437949810722424303925 := by
  unfold tailWord_953177
  simp only [CollatzResearch.WordTrace]
  refine ⟨34765221267809993516361785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23176814178539995677574523 34765221267809993516361785)
  ·
    refine ⟨26073915950857495137271339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34765221267809993516361785 26073915950857495137271339)
    ·
      refine ⟨39110873926286242705907009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26073915950857495137271339 39110873926286242705907009)
      ·
        refine ⟨29333155444714682029430257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39110873926286242705907009 29333155444714682029430257)
        ·
          refine ⟨21999866583536011522072693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29333155444714682029430257 21999866583536011522072693)
          ·
            refine ⟨2062487492206501080194315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21999866583536011522072693 2062487492206501080194315)
            ·
              refine ⟨3093731238309751620291473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2062487492206501080194315 3093731238309751620291473)
              ·
                refine ⟨2320298428732313715218605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3093731238309751620291473 2320298428732313715218605)
                ·
                  refine ⟨870111910774617643206977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2320298428732313715218605 870111910774617643206977)
                  ·
                    refine ⟨652583933080963232405233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 870111910774617643206977 652583933080963232405233)
                    ·
                      refine ⟨489437949810722424303925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 652583933080963232405233 489437949810722424303925)
                      ·
                        rfl

theorem cell23_953177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 3, 2, 2].length) (baseStart_953177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953177 prefixEnd_953177 := by exact prefixLift 953177
  have htrace : WordTrace (prefixWord ++ tailWord_953177) baseStart_953177 baseEnd_953177 := by
    simpa [prefixWord, tailWord_953177, baseEnd_953177] using wordTrace_append hprefix tailTrace_953177
  have hstable : (prefixWord ++ tailWord_953177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953177).length < 2 ^ (prefixWord ++ tailWord_953177).sum := by decide
  have hdescent : baseEnd_953177 < baseStart_953177 := by decide
  rcases family_descends (prefixWord ++ tailWord_953177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953183 : List Nat := [1, 1, 2, 3, 1, 3, 5, 7]
def baseStart_953183 : Nat := 118140960795 + 953183 * 2 ^ 59
def prefixEnd_953183 : Nat := 4983230072969 + 3 ^ 40 * 953183 * 2
def baseEnd_953183 : Nat := 18127445581283311141811

theorem tailTrace_953183 : CollatzResearch.WordTrace tailWord_953183 prefixEnd_953183 18127445581283311141811 := by
  unfold tailWord_953183
  simp only [CollatzResearch.WordTrace]
  refine ⟨34765440105788256541080203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23176960070525504360720135 34765440105788256541080203)
  ·
    refine ⟨52148160158682384811620305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34765440105788256541080203 52148160158682384811620305)
    ·
      refine ⟨39111120119011788608715229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52148160158682384811620305 39111120119011788608715229)
      ·
        refine ⟨14666670044629420728268211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39111120119011788608715229 14666670044629420728268211)
        ·
          refine ⟨22000005066944131092402317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14666670044629420728268211 22000005066944131092402317)
          ·
            refine ⟨8250001900104049159650869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22000005066944131092402317 8250001900104049159650869)
            ·
              refine ⟨773437678134754608717269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8250001900104049159650869 773437678134754608717269)
              ·
                refine ⟨18127445581283311141811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 773437678134754608717269 18127445581283311141811)
                ·
                  rfl

theorem cell23_953183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 7].length) (baseStart_953183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953183 prefixEnd_953183 := by exact prefixLift 953183
  have htrace : WordTrace (prefixWord ++ tailWord_953183) baseStart_953183 baseEnd_953183 := by
    simpa [prefixWord, tailWord_953183, baseEnd_953183] using wordTrace_append hprefix tailTrace_953183
  have hstable : (prefixWord ++ tailWord_953183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953183).length < 2 ^ (prefixWord ++ tailWord_953183).sum := by decide
  have hdescent : baseEnd_953183 < baseStart_953183 := by decide
  rcases family_descends (prefixWord ++ tailWord_953183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953234 : List Nat := [3, 2, 3, 2, 3, 1, 2, 7]
def baseStart_953234 : Nat := 118140960795 + 953234 * 2 ^ 59
def prefixEnd_953234 : Nat := 4983230072969 + 3 ^ 40 * 953234 * 2
def baseEnd_953234 : Nat := 18128415489186248195969

theorem tailTrace_953234 : CollatzResearch.WordTrace tailWord_953234 prefixEnd_953234 18128415489186248195969 := by
  unfold tailWord_953234
  simp only [CollatzResearch.WordTrace]
  refine ⟨8691825057150873062796689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23178200152402328167457837 8691825057150873062796689)
  ·
    refine ⟨6518868792863154797097517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8691825057150873062796689 6518868792863154797097517)
    ·
      refine ⟨2444575797323683048911569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6518868792863154797097517 2444575797323683048911569)
      ·
        refine ⟨1833431847992762286683677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2444575797323683048911569 1833431847992762286683677)
        ·
          refine ⟨687536942997285857506379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1833431847992762286683677 687536942997285857506379)
          ·
            refine ⟨1031305414495928786259569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 687536942997285857506379 1031305414495928786259569)
            ·
              refine ⟨773479060871946589694677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1031305414495928786259569 773479060871946589694677)
              ·
                refine ⟨18128415489186248195969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 773479060871946589694677 18128415489186248195969)
                ·
                  rfl

theorem cell23_953234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 7].length) (baseStart_953234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953234 prefixEnd_953234 := by exact prefixLift 953234
  have htrace : WordTrace (prefixWord ++ tailWord_953234) baseStart_953234 baseEnd_953234 := by
    simpa [prefixWord, tailWord_953234, baseEnd_953234] using wordTrace_append hprefix tailTrace_953234
  have hstable : (prefixWord ++ tailWord_953234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953234).length < 2 ^ (prefixWord ++ tailWord_953234).sum := by decide
  have hdescent : baseEnd_953234 < baseStart_953234 := by decide
  rcases family_descends (prefixWord ++ tailWord_953234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953237 : List Nat := [1, 3, 2, 1, 1, 4, 1, 4, 1, 3, 2]
def baseStart_953237 : Nat := 118140960795 + 953237 * 2 ^ 59
def prefixEnd_953237 : Nat := 4983230072969 + 3 ^ 40 * 953237 * 2
def baseEnd_953237 : Nat := 489468758649992189553649

theorem tailTrace_953237 : CollatzResearch.WordTrace tailWord_953237 prefixEnd_953237 489468758649992189553649 := by
  unfold tailWord_953237
  simp only [CollatzResearch.WordTrace]
  refine ⟨34767409647592623763545965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23178273098395082509030643 34767409647592623763545965)
  ·
    refine ⟨13037778617847233911329737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34767409647592623763545965 13037778617847233911329737)
    ·
      refine ⟨9778333963385425433497303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13037778617847233911329737 9778333963385425433497303)
      ·
        refine ⟨14667500945078138150245955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9778333963385425433497303 14667500945078138150245955)
        ·
          refine ⟨22001251417617207225368933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14667500945078138150245955 22001251417617207225368933)
          ·
            refine ⟨4125234640803226354756675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22001251417617207225368933 4125234640803226354756675)
            ·
              refine ⟨6187851961204839532135013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4125234640803226354756675 6187851961204839532135013)
              ·
                refine ⟨1160222242725907412275315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6187851961204839532135013 1160222242725907412275315)
                ·
                  refine ⟨1740333364088861118412973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1160222242725907412275315 1740333364088861118412973)
                  ·
                    refine ⟨652625011533322919404865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1740333364088861118412973 652625011533322919404865)
                    ·
                      refine ⟨489468758649992189553649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 652625011533322919404865 489468758649992189553649)
                      ·
                        rfl

theorem cell23_953237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 3, 2].length) (baseStart_953237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953237 prefixEnd_953237 := by exact prefixLift 953237
  have htrace : WordTrace (prefixWord ++ tailWord_953237) baseStart_953237 baseEnd_953237 := by
    simpa [prefixWord, tailWord_953237, baseEnd_953237] using wordTrace_append hprefix tailTrace_953237
  have hstable : (prefixWord ++ tailWord_953237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953237).length < 2 ^ (prefixWord ++ tailWord_953237).sum := by decide
  have hdescent : baseEnd_953237 < baseStart_953237 := by decide
  rcases family_descends (prefixWord ++ tailWord_953237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953253 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 3, 6, 3]
def baseStart_953253 : Nat := 118140960795 + 953253 * 2 ^ 59
def prefixEnd_953253 : Nat := 4983230072969 + 3 ^ 40 * 953253 * 2
def baseEnd_953253 : Nat := 489476974340464126953575

theorem tailTrace_953253 : CollatzResearch.WordTrace tailWord_953253 prefixEnd_953253 489476974340464126953575 := by
  unfold tailWord_953253
  simp only [CollatzResearch.WordTrace]
  refine ⟨34767993215534658496128413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23178662143689772330752275 34767993215534658496128413)
  ·
    refine ⟨13037997455825496936048155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34767993215534658496128413 13037997455825496936048155)
    ·
      refine ⟨19556996183738245404072233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13037997455825496936048155 19556996183738245404072233)
      ·
        refine ⟨14667747137803684053054175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19556996183738245404072233 14667747137803684053054175)
        ·
          refine ⟨22001620706705526079581263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14667747137803684053054175 22001620706705526079581263)
          ·
            refine ⟨33002431060058289119371895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22001620706705526079581263 33002431060058289119371895)
            ·
              refine ⟨49503646590087433679057843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33002431060058289119371895 49503646590087433679057843)
              ·
                refine ⟨74255469885131150518586765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49503646590087433679057843 74255469885131150518586765)
                ·
                  refine ⟨27845801206924181444470037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74255469885131150518586765 27845801206924181444470037)
                  ·
                    refine ⟨1305271931574571005209533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27845801206924181444470037 1305271931574571005209533)
                    ·
                      refine ⟨489476974340464126953575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1305271931574571005209533 489476974340464126953575)
                      ·
                        rfl

theorem cell23_953253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_953253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953253 prefixEnd_953253 := by exact prefixLift 953253
  have htrace : WordTrace (prefixWord ++ tailWord_953253) baseStart_953253 baseEnd_953253 := by
    simpa [prefixWord, tailWord_953253, baseEnd_953253] using wordTrace_append hprefix tailTrace_953253
  have hstable : (prefixWord ++ tailWord_953253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953253).length < 2 ^ (prefixWord ++ tailWord_953253).sum := by decide
  have hdescent : baseEnd_953253 < baseStart_953253 := by decide
  rcases family_descends (prefixWord ++ tailWord_953253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953263 : List Nat := [1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 4]
def baseStart_953263 : Nat := 118140960795 + 953263 * 2 ^ 59
def prefixEnd_953263 : Nat := 4983230072969 + 3 ^ 40 * 953263 * 2
def baseEnd_953263 : Nat := 489482109147009087828529

theorem tailTrace_953263 : CollatzResearch.WordTrace tailWord_953263 prefixEnd_953263 489482109147009087828529 := by
  unfold tailWord_953263
  simp only [CollatzResearch.WordTrace]
  refine ⟨34768357945498430203992443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23178905296998953469328295 34768357945498430203992443)
  ·
    refine ⟨52152536918247645305988665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34768357945498430203992443 52152536918247645305988665)
    ·
      refine ⟨39114402688685733979491499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52152536918247645305988665 39114402688685733979491499)
      ·
        refine ⟨58671604033028600969237249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39114402688685733979491499 58671604033028600969237249)
        ·
          refine ⟨44003703024771450726927937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58671604033028600969237249 44003703024771450726927937)
          ·
            refine ⟨33002777268578588045195953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44003703024771450726927937 33002777268578588045195953)
            ·
              refine ⟨24752082951433941033896965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33002777268578588045195953 24752082951433941033896965)
              ·
                refine ⟨4641015553393863943855681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24752082951433941033896965 4641015553393863943855681)
                ·
                  refine ⟨3480761665045397957891761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4641015553393863943855681 3480761665045397957891761)
                  ·
                    refine ⟨2610571248784048468418821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3480761665045397957891761 2610571248784048468418821)
                    ·
                      refine ⟨489482109147009087828529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2610571248784048468418821 489482109147009087828529)
                      ·
                        rfl

theorem cell23_953263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 4].length) (baseStart_953263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953263 prefixEnd_953263 := by exact prefixLift 953263
  have htrace : WordTrace (prefixWord ++ tailWord_953263) baseStart_953263 baseEnd_953263 := by
    simpa [prefixWord, tailWord_953263, baseEnd_953263] using wordTrace_append hprefix tailTrace_953263
  have hstable : (prefixWord ++ tailWord_953263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953263).length < 2 ^ (prefixWord ++ tailWord_953263).sum := by decide
  have hdescent : baseEnd_953263 < baseStart_953263 := by decide
  rcases family_descends (prefixWord ++ tailWord_953263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953320 : List Nat := [2, 1, 4, 1, 1, 1, 4, 2, 2, 5]
def baseStart_953320 : Nat := 118140960795 + 953320 * 2 ^ 59
def prefixEnd_953320 : Nat := 4983230072969 + 3 ^ 40 * 953320 * 2
def baseEnd_953320 : Nat := 163170459181438454938589

theorem tailTrace_953320 : CollatzResearch.WordTrace tailWord_953320 prefixEnd_953320 163170459181438454938589 := by
  unfold tailWord_953320
  simp only [CollatzResearch.WordTrace]
  refine ⟨17385218453145964469408707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23180291270861285959211609 17385218453145964469408707)
  ·
    refine ⟨26077827679718946704113061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17385218453145964469408707 26077827679718946704113061)
    ·
      refine ⟨4889592689947302507021199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26077827679718946704113061 4889592689947302507021199)
      ·
        refine ⟨7334389034920953760531799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4889592689947302507021199 7334389034920953760531799)
        ·
          refine ⟨11001583552381430640797699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7334389034920953760531799 11001583552381430640797699)
          ·
            refine ⟨16502375328572145961196549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11001583552381430640797699 16502375328572145961196549)
            ·
              refine ⟨3094195374107277367724353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16502375328572145961196549 3094195374107277367724353)
              ·
                refine ⟨2320646530580458025793265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3094195374107277367724353 2320646530580458025793265)
                ·
                  refine ⟨1740484897935343519344949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2320646530580458025793265 1740484897935343519344949)
                  ·
                    refine ⟨163170459181438454938589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1740484897935343519344949 163170459181438454938589)
                    ·
                      rfl

theorem cell23_953320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_953320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953320 prefixEnd_953320 := by exact prefixLift 953320
  have htrace : WordTrace (prefixWord ++ tailWord_953320) baseStart_953320 baseEnd_953320 := by
    simpa [prefixWord, tailWord_953320, baseEnd_953320] using wordTrace_append hprefix tailTrace_953320
  have hstable : (prefixWord ++ tailWord_953320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953320).length < 2 ^ (prefixWord ++ tailWord_953320).sum := by decide
  have hdescent : baseEnd_953320 < baseStart_953320 := by decide
  rcases family_descends (prefixWord ++ tailWord_953320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953323 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 4]
def baseStart_953323 : Nat := 118140960795 + 953323 * 2 ^ 59
def prefixEnd_953323 : Nat := 4983230072969 + 3 ^ 40 * 953323 * 2
def baseEnd_953323 : Nat := 489512917986278853078253

theorem tailTrace_953323 : CollatzResearch.WordTrace tailWord_953323 prefixEnd_953323 489512917986278853078253 := by
  unfold tailWord_953323
  simp only [CollatzResearch.WordTrace]
  refine ⟨34770546325281060451176623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23180364216854040300784415 34770546325281060451176623)
  ·
    refine ⟨52155819487921590676764935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34770546325281060451176623 52155819487921590676764935)
    ·
      refine ⟨78233729231882386015147403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52155819487921590676764935 78233729231882386015147403)
      ·
        refine ⟨117350593847823579022721105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78233729231882386015147403 117350593847823579022721105)
        ·
          refine ⟨88012945385867684267040829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117350593847823579022721105 88012945385867684267040829)
          ·
            refine ⟨33004854519700381600140311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88012945385867684267040829 33004854519700381600140311)
            ·
              refine ⟨49507281779550572400210467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33004854519700381600140311 49507281779550572400210467)
              ·
                refine ⟨74260922669325858600315701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49507281779550572400210467 74260922669325858600315701)
                ·
                  refine ⟨6961961500249299243779597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74260922669325858600315701 6961961500249299243779597)
                  ·
                    refine ⟨2610735562593487216417349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6961961500249299243779597 2610735562593487216417349)
                    ·
                      refine ⟨489512917986278853078253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2610735562593487216417349 489512917986278853078253)
                      ·
                        rfl

theorem cell23_953323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 4].length) (baseStart_953323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953323 prefixEnd_953323 := by exact prefixLift 953323
  have htrace : WordTrace (prefixWord ++ tailWord_953323) baseStart_953323 baseEnd_953323 := by
    simpa [prefixWord, tailWord_953323, baseEnd_953323] using wordTrace_append hprefix tailTrace_953323
  have hstable : (prefixWord ++ tailWord_953323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953323).length < 2 ^ (prefixWord ++ tailWord_953323).sum := by decide
  have hdescent : baseEnd_953323 < baseStart_953323 := by decide
  rcases family_descends (prefixWord ++ tailWord_953323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953353 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 4, 1, 6]
def baseStart_953353 : Nat := 118140960795 + 953353 * 2 ^ 59
def prefixEnd_953353 : Nat := 4983230072969 + 3 ^ 40 * 953353 * 2
def baseEnd_953353 : Nat := 489528322405913735703115

theorem tailTrace_953353 : CollatzResearch.WordTrace tailWord_953353 prefixEnd_953353 489528322405913735703115 := by
  unfold tailWord_953353
  simp only [CollatzResearch.WordTrace]
  refine ⟨34771640515172375574768713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23181093676781583716512475 34771640515172375574768713)
  ·
    refine ⟨26078730386379281681076535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34771640515172375574768713 26078730386379281681076535)
    ·
      refine ⟨39118095579568922521614803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26078730386379281681076535 39118095579568922521614803)
      ·
        refine ⟨58677143369353383782422205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39118095579568922521614803 58677143369353383782422205)
        ·
          refine ⟨22003928763507518918408327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58677143369353383782422205 22003928763507518918408327)
          ·
            refine ⟨33005893145261278377612491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22003928763507518918408327 33005893145261278377612491)
            ·
              refine ⟨49508839717891917566418737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33005893145261278377612491 49508839717891917566418737)
              ·
                refine ⟨37131629788418938174814053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49508839717891917566418737 37131629788418938174814053)
                ·
                  refine ⟨6962180585328550907777635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37131629788418938174814053 6962180585328550907777635)
                  ·
                    refine ⟨10443270877992826361666453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6962180585328550907777635 10443270877992826361666453)
                    ·
                      refine ⟨489528322405913735703115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10443270877992826361666453 489528322405913735703115)
                      ·
                        rfl

theorem cell23_953353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 1, 6].length) (baseStart_953353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953353 prefixEnd_953353 := by exact prefixLift 953353
  have htrace : WordTrace (prefixWord ++ tailWord_953353) baseStart_953353 baseEnd_953353 := by
    simpa [prefixWord, tailWord_953353, baseEnd_953353] using wordTrace_append hprefix tailTrace_953353
  have hstable : (prefixWord ++ tailWord_953353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953353).length < 2 ^ (prefixWord ++ tailWord_953353).sum := by decide
  have hdescent : baseEnd_953353 < baseStart_953353 := by decide
  rcases family_descends (prefixWord ++ tailWord_953353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953363 : List Nat := [1, 1, 1, 2, 1, 4, 1, 4, 8]
def baseStart_953363 : Nat := 118140960795 + 953363 * 2 ^ 59
def prefixEnd_953363 : Nat := 4983230072969 + 3 ^ 40 * 953363 * 2
def baseEnd_953363 : Nat := 54392606356939855175341

theorem tailTrace_953363 : CollatzResearch.WordTrace tailWord_953363 prefixEnd_953363 54392606356939855175341 := by
  unfold tailWord_953363
  simp only [CollatzResearch.WordTrace]
  refine ⟨34772005245136147282632743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23181336830090764855088495 34772005245136147282632743)
  ·
    refine ⟨52158007867704220923949115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34772005245136147282632743 52158007867704220923949115)
    ·
      refine ⟨78237011801556331385923673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52158007867704220923949115 78237011801556331385923673)
      ·
        refine ⟨58677758851167248539442755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78237011801556331385923673 58677758851167248539442755)
        ·
          refine ⟨88016638276750872809164133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58677758851167248539442755 88016638276750872809164133)
          ·
            refine ⟨16503119676890788651718275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88016638276750872809164133 16503119676890788651718275)
            ·
              refine ⟨24754679515336182977577413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16503119676890788651718275 24754679515336182977577413)
              ·
                refine ⟨4641502409125534308295765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24754679515336182977577413 4641502409125534308295765)
                ·
                  refine ⟨54392606356939855175341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4641502409125534308295765 54392606356939855175341)
                  ·
                    rfl

theorem cell23_953363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 8].length) (baseStart_953363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953363 prefixEnd_953363 := by exact prefixLift 953363
  have htrace : WordTrace (prefixWord ++ tailWord_953363) baseStart_953363 baseEnd_953363 := by
    simpa [prefixWord, tailWord_953363, baseEnd_953363] using wordTrace_append hprefix tailTrace_953363
  have hstable : (prefixWord ++ tailWord_953363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953363).length < 2 ^ (prefixWord ++ tailWord_953363).sum := by decide
  have hdescent : baseEnd_953363 < baseStart_953363 := by decide
  rcases family_descends (prefixWord ++ tailWord_953363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953448 : List Nat := [2, 1, 4, 4, 2, 1, 2, 1, 6]
def baseStart_953448 : Nat := 118140960795 + 953448 * 2 ^ 59
def prefixEnd_953448 : Nat := 4983230072969 + 3 ^ 40 * 953448 * 2
def baseEnd_953448 : Nat := 54397455896454540446131

theorem tailTrace_953448 : CollatzResearch.WordTrace tailWord_953448 prefixEnd_953448 54397455896454540446131 := by
  unfold tailWord_953448
  simp only [CollatzResearch.WordTrace]
  refine ⟨17387552724914103399738499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23183403633218804532984665 17387552724914103399738499)
  ·
    refine ⟨26081329087371155099607749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17387552724914103399738499 26081329087371155099607749)
    ·
      refine ⟨4890249203882091581176453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26081329087371155099607749 4890249203882091581176453)
      ·
        refine ⟨916921725727892171470585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4890249203882091581176453 916921725727892171470585)
        ·
          refine ⟨687691294295919128602939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 916921725727892171470585 687691294295919128602939)
          ·
            refine ⟨1031536941443878692904409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 687691294295919128602939 1031536941443878692904409)
            ·
              refine ⟨773652706082909019678307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1031536941443878692904409 773652706082909019678307)
              ·
                refine ⟨1160479059124363529517461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 773652706082909019678307 1160479059124363529517461)
                ·
                  refine ⟨54397455896454540446131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1160479059124363529517461 54397455896454540446131)
                  ·
                    rfl

theorem cell23_953448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 6].length) (baseStart_953448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953448 prefixEnd_953448 := by exact prefixLift 953448
  have htrace : WordTrace (prefixWord ++ tailWord_953448) baseStart_953448 baseEnd_953448 := by
    simpa [prefixWord, tailWord_953448, baseEnd_953448] using wordTrace_append hprefix tailTrace_953448
  have hstable : (prefixWord ++ tailWord_953448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953448).length < 2 ^ (prefixWord ++ tailWord_953448).sum := by decide
  have hdescent : baseEnd_953448 < baseStart_953448 := by decide
  rcases family_descends (prefixWord ++ tailWord_953448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953464 : List Nat := [2, 1, 2, 1, 1, 1, 4, 4, 3, 2, 2]
def baseStart_953464 : Nat := 118140960795 + 953464 * 2 ^ 59
def prefixEnd_953464 : Nat := 4983230072969 + 3 ^ 40 * 953464 * 2
def baseEnd_953464 : Nat := 489585318758562801415105

theorem tailTrace_953464 : CollatzResearch.WordTrace tailWord_953464 prefixEnd_953464 489585318758562801415105 := by
  unfold tailWord_953464
  simp only [CollatzResearch.WordTrace]
  refine ⟨17387844508885120766029723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23183792678513494354706297 17387844508885120766029723)
  ·
    refine ⟨26081766763327681149044585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17387844508885120766029723 26081766763327681149044585)
    ·
      refine ⟨19561325072495760861783439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26081766763327681149044585 19561325072495760861783439)
      ·
        refine ⟨29341987608743641292675159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19561325072495760861783439 29341987608743641292675159)
        ·
          refine ⟨44012981413115461939012739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29341987608743641292675159 44012981413115461939012739)
          ·
            refine ⟨66019472119673192908519109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44012981413115461939012739 66019472119673192908519109)
            ·
              refine ⟨12378651022438723670347333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66019472119673192908519109 12378651022438723670347333)
              ·
                refine ⟨2320997066707260688190125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12378651022438723670347333 2320997066707260688190125)
                ·
                  refine ⟨870373900015222758071297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2320997066707260688190125 870373900015222758071297)
                  ·
                    refine ⟨652780425011417068553473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 870373900015222758071297 652780425011417068553473)
                    ·
                      refine ⟨489585318758562801415105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 652780425011417068553473 489585318758562801415105)
                      ·
                        rfl

theorem cell23_953464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 3, 2, 2].length) (baseStart_953464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953464 prefixEnd_953464 := by exact prefixLift 953464
  have htrace : WordTrace (prefixWord ++ tailWord_953464) baseStart_953464 baseEnd_953464 := by
    simpa [prefixWord, tailWord_953464, baseEnd_953464] using wordTrace_append hprefix tailTrace_953464
  have hstable : (prefixWord ++ tailWord_953464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953464).length < 2 ^ (prefixWord ++ tailWord_953464).sum := by decide
  have hdescent : baseEnd_953464 < baseStart_953464 := by decide
  rcases family_descends (prefixWord ++ tailWord_953464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953530 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 3, 8]
def baseStart_953530 : Nat := 118140960795 + 953530 * 2 ^ 59
def prefixEnd_953530 : Nat := 4983230072969 + 3 ^ 40 * 953530 * 2
def baseEnd_953530 : Nat := 163206402827253181063267

theorem tailTrace_953530 : CollatzResearch.WordTrace tailWord_953530 prefixEnd_953530 163206402827253181063267 := by
  unfold tailWord_953530
  simp only [CollatzResearch.WordTrace]
  refine ⟨8694524058882783700990511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23185397490354089869308029 8694524058882783700990511)
  ·
    refine ⟨13041786088324175551485767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8694524058882783700990511 13041786088324175551485767)
    ·
      refine ⟨19562679132486263327228651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13041786088324175551485767 19562679132486263327228651)
      ·
        refine ⟨29344018698729394990842977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19562679132486263327228651 29344018698729394990842977)
        ·
          refine ⟨22008014024047046243132233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29344018698729394990842977 22008014024047046243132233)
          ·
            refine ⟨16506010518035284682349175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22008014024047046243132233 16506010518035284682349175)
            ·
              refine ⟨24759015777052927023523763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16506010518035284682349175 24759015777052927023523763)
              ·
                refine ⟨37138523665579390535285645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24759015777052927023523763 37138523665579390535285645)
                ·
                  refine ⟨13926946374592271450732117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37138523665579390535285645 13926946374592271450732117)
                  ·
                    refine ⟨163206402827253181063267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13926946374592271450732117 163206402827253181063267)
                    ·
                      rfl

theorem cell23_953530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 3, 8].length) (baseStart_953530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953530 prefixEnd_953530 := by exact prefixLift 953530
  have htrace : WordTrace (prefixWord ++ tailWord_953530) baseStart_953530 baseEnd_953530 := by
    simpa [prefixWord, tailWord_953530, baseEnd_953530] using wordTrace_append hprefix tailTrace_953530
  have hstable : (prefixWord ++ tailWord_953530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953530).length < 2 ^ (prefixWord ++ tailWord_953530).sum := by decide
  have hdescent : baseEnd_953530 < baseStart_953530 := by decide
  rcases family_descends (prefixWord ++ tailWord_953530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953542 : List Nat := [6, 1, 2, 2, 1, 2, 1, 2, 2, 4]
def baseStart_953542 : Nat := 118140960795 + 953542 * 2 ^ 59
def prefixEnd_953542 : Nat := 4983230072969 + 3 ^ 40 * 953542 * 2
def baseEnd_953542 : Nat := 163208456749871165413249

theorem tailTrace_953542 : CollatzResearch.WordTrace tailWord_953542 prefixEnd_953542 163208456749871165413249 := by
  unfold tailWord_953542
  simp only [CollatzResearch.WordTrace]
  refine ⟨1086829184733989401668715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23185689274325107235599253 1086829184733989401668715)
  ·
    refine ⟨1630243777100984102503073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1086829184733989401668715 1630243777100984102503073)
    ·
      refine ⟨1222682832825738076877305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1630243777100984102503073 1222682832825738076877305)
      ·
        refine ⟨917012124619303557657979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1222682832825738076877305 917012124619303557657979)
        ·
          refine ⟨1375518186928955336486969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 917012124619303557657979 1375518186928955336486969)
          ·
            refine ⟨1031638640196716502365227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1375518186928955336486969 1031638640196716502365227)
            ·
              refine ⟨1547457960295074753547841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1031638640196716502365227 1547457960295074753547841)
              ·
                refine ⟨1160593470221306065160881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1547457960295074753547841 1160593470221306065160881)
                ·
                  refine ⟨870445102665979548870661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1160593470221306065160881 870445102665979548870661)
                  ·
                    refine ⟨163208456749871165413249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 870445102665979548870661 163208456749871165413249)
                    ·
                      rfl

theorem cell23_953542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_953542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953542 prefixEnd_953542 := by exact prefixLift 953542
  have htrace : WordTrace (prefixWord ++ tailWord_953542) baseStart_953542 baseEnd_953542 := by
    simpa [prefixWord, tailWord_953542, baseEnd_953542] using wordTrace_append hprefix tailTrace_953542
  have hstable : (prefixWord ++ tailWord_953542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953542).length < 2 ^ (prefixWord ++ tailWord_953542).sum := by decide
  have hdescent : baseEnd_953542 < baseStart_953542 := by decide
  rcases family_descends (prefixWord ++ tailWord_953542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953565 : List Nat := [1, 4, 3, 2, 2, 1, 3, 1, 2, 1, 3]
def baseStart_953565 : Nat := 118140960795 + 953565 * 2 ^ 59
def prefixEnd_953565 : Nat := 4983230072969 + 3 ^ 40 * 953565 * 2
def baseEnd_953565 : Nat := 489637180304666906252141

theorem tailTrace_953565 : CollatzResearch.WordTrace tailWord_953565 prefixEnd_953565 489637180304666906252141 := by
  unfold tailWord_953565
  simp only [CollatzResearch.WordTrace]
  refine ⟨34779372790404335781486149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23186248526936223854324099 34779372790404335781486149)
  ·
    refine ⟨6521132398200812959028653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34779372790404335781486149 6521132398200812959028653)
    ·
      refine ⟨2445424649325304859635745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6521132398200812959028653 2445424649325304859635745)
      ·
        refine ⟨1834068486993978644726809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2445424649325304859635745 1834068486993978644726809)
        ·
          refine ⟨1375551365245483983545107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1834068486993978644726809 1375551365245483983545107)
          ·
            refine ⟨2063327047868225975317661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1375551365245483983545107 2063327047868225975317661)
            ·
              refine ⟨773747642950584740744123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2063327047868225975317661 773747642950584740744123)
              ·
                refine ⟨1160621464425877111116185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 773747642950584740744123 1160621464425877111116185)
                ·
                  refine ⟨870466098319407833337139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1160621464425877111116185 870466098319407833337139)
                  ·
                    refine ⟨1305699147479111750005709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 870466098319407833337139 1305699147479111750005709)
                    ·
                      refine ⟨489637180304666906252141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1305699147479111750005709 489637180304666906252141)
                      ·
                        rfl

theorem cell23_953565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_953565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953565 prefixEnd_953565 := by exact prefixLift 953565
  have htrace : WordTrace (prefixWord ++ tailWord_953565) baseStart_953565 baseEnd_953565 := by
    simpa [prefixWord, tailWord_953565, baseEnd_953565] using wordTrace_append hprefix tailTrace_953565
  have hstable : (prefixWord ++ tailWord_953565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953565).length < 2 ^ (prefixWord ++ tailWord_953565).sum := by decide
  have hdescent : baseEnd_953565 < baseStart_953565 := by decide
  rcases family_descends (prefixWord ++ tailWord_953565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953567 : List Nat := [1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 4]
def baseStart_953567 : Nat := 118140960795 + 953567 * 2 ^ 59
def prefixEnd_953567 : Nat := 4983230072969 + 3 ^ 40 * 953567 * 2
def baseEnd_953567 : Nat := 489638207265975898427131

theorem tailTrace_953567 : CollatzResearch.WordTrace tailWord_953567 prefixEnd_953567 489638207265975898427131 := by
  unfold tailWord_953567
  simp only [CollatzResearch.WordTrace]
  refine ⟨34779445736397090123058955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23186297157598060082039303 34779445736397090123058955)
  ·
    refine ⟨52169168604595635184588433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34779445736397090123058955 52169168604595635184588433)
    ·
      refine ⟨39126876453446726388441325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52169168604595635184588433 39126876453446726388441325)
      ·
        refine ⟨14672578670042522395665497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39126876453446726388441325 14672578670042522395665497)
        ·
          refine ⟨11004434002531891796749123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14672578670042522395665497 11004434002531891796749123)
          ·
            refine ⟨16506651003797837695123685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11004434002531891796749123 16506651003797837695123685)
            ·
              refine ⟨3094997063212094567835691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16506651003797837695123685 3094997063212094567835691)
              ·
                refine ⟨4642495594818141851753537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3094997063212094567835691 4642495594818141851753537)
                ·
                  refine ⟨3481871696113606388815153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4642495594818141851753537 3481871696113606388815153)
                  ·
                    refine ⟨2611403772085204791611365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3481871696113606388815153 2611403772085204791611365)
                    ·
                      refine ⟨489638207265975898427131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2611403772085204791611365 489638207265975898427131)
                      ·
                        rfl

theorem cell23_953567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_953567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953567 prefixEnd_953567 := by exact prefixLift 953567
  have htrace : WordTrace (prefixWord ++ tailWord_953567) baseStart_953567 baseEnd_953567 := by
    simpa [prefixWord, tailWord_953567, baseEnd_953567] using wordTrace_append hprefix tailTrace_953567
  have hstable : (prefixWord ++ tailWord_953567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953567).length < 2 ^ (prefixWord ++ tailWord_953567).sum := by decide
  have hdescent : baseEnd_953567 < baseStart_953567 := by decide
  rcases family_descends (prefixWord ++ tailWord_953567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953611 : List Nat := [1, 1, 1, 1, 5, 4, 3, 2, 5]
def baseStart_953611 : Nat := 118140960795 + 953611 * 2 ^ 59
def prefixEnd_953611 : Nat := 4983230072969 + 3 ^ 40 * 953611 * 2
def baseEnd_953611 : Nat := 54406755601641525141881

theorem tailTrace_953611 : CollatzResearch.WordTrace tailWord_953611 prefixEnd_953611 54406755601641525141881 := by
  unfold tailWord_953611
  simp only [CollatzResearch.WordTrace]
  refine ⟨34781050548237685637660687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23187367032158457091773791 34781050548237685637660687)
  ·
    refine ⟨52171575822356528456491031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34781050548237685637660687 52171575822356528456491031)
    ·
      refine ⟨78257363733534792684736547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52171575822356528456491031 78257363733534792684736547)
      ·
        refine ⟨117386045600302189027104821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78257363733534792684736547 117386045600302189027104821)
        ·
          refine ⟨11004941775028330221291077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117386045600302189027104821 11004941775028330221291077)
          ·
            refine ⟨2063426582817811916492077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11004941775028330221291077 2063426582817811916492077)
            ·
              refine ⟨773784968556679468684529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2063426582817811916492077 773784968556679468684529)
              ·
                refine ⟨580338726417509601513397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 773784968556679468684529 580338726417509601513397)
                ·
                  refine ⟨54406755601641525141881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 580338726417509601513397 54406755601641525141881)
                  ·
                    rfl

theorem cell23_953611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 2, 5].length) (baseStart_953611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953611 prefixEnd_953611 := by exact prefixLift 953611
  have htrace : WordTrace (prefixWord ++ tailWord_953611) baseStart_953611 baseEnd_953611 := by
    simpa [prefixWord, tailWord_953611, baseEnd_953611] using wordTrace_append hprefix tailTrace_953611
  have hstable : (prefixWord ++ tailWord_953611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953611).length < 2 ^ (prefixWord ++ tailWord_953611).sum := by decide
  have hdescent : baseEnd_953611 < baseStart_953611 := by decide
  rcases family_descends (prefixWord ++ tailWord_953611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953617 : List Nat := [1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 5]
def baseStart_953617 : Nat := 118140960795 + 953617 * 2 ^ 59
def prefixEnd_953617 : Nat := 4983230072969 + 3 ^ 40 * 953617 * 2
def baseEnd_953617 : Nat := 489663881298700702801901

theorem tailTrace_953617 : CollatzResearch.WordTrace tailWord_953617 prefixEnd_953617 489663881298700702801901 := by
  unfold tailWord_953617
  simp only [CollatzResearch.WordTrace]
  refine ⟨34781269386215948662379105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23187512924143965774919403 34781269386215948662379105)
  ·
    refine ⟨26085952039661961496784329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34781269386215948662379105 26085952039661961496784329)
    ·
      refine ⟨19564464029746471122588247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26085952039661961496784329 19564464029746471122588247)
      ·
        refine ⟨29346696044619706683882371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19564464029746471122588247 29346696044619706683882371)
        ·
          refine ⟨44020044066929560025823557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29346696044619706683882371 44020044066929560025823557)
          ·
            refine ⟨8253758262549292504841917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44020044066929560025823557 8253758262549292504841917)
            ·
              refine ⟨3095159348455984689315719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8253758262549292504841917 3095159348455984689315719)
              ·
                refine ⟨4642739022683977033973579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3095159348455984689315719 4642739022683977033973579)
                ·
                  refine ⟨6964108534025965550960369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4642739022683977033973579 6964108534025965550960369)
                  ·
                    refine ⟨5223081400519474163220277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6964108534025965550960369 5223081400519474163220277)
                    ·
                      refine ⟨489663881298700702801901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5223081400519474163220277 489663881298700702801901)
                      ·
                        rfl

theorem cell23_953617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_953617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953617 prefixEnd_953617 := by exact prefixLift 953617
  have htrace : WordTrace (prefixWord ++ tailWord_953617) baseStart_953617 baseEnd_953617 := by
    simpa [prefixWord, tailWord_953617, baseEnd_953617] using wordTrace_append hprefix tailTrace_953617
  have hstable : (prefixWord ++ tailWord_953617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953617).length < 2 ^ (prefixWord ++ tailWord_953617).sum := by decide
  have hdescent : baseEnd_953617 < baseStart_953617 := by decide
  rcases family_descends (prefixWord ++ tailWord_953617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953627 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 4]
def baseStart_953627 : Nat := 118140960795 + 953627 * 2 ^ 59
def prefixEnd_953627 : Nat := 4983230072969 + 3 ^ 40 * 953627 * 2
def baseEnd_953627 : Nat := 489669016105245663676855

theorem tailTrace_953627 : CollatzResearch.WordTrace tailWord_953627 prefixEnd_953627 489669016105245663676855 := by
  unfold tailWord_953627
  simp only [CollatzResearch.WordTrace]
  refine ⟨34781634116179720370243135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23187756077453146913495423 34781634116179720370243135)
  ·
    refine ⟨52172451174269580555364703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34781634116179720370243135 52172451174269580555364703)
    ·
      refine ⟨78258676761404370833047055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52172451174269580555364703 78258676761404370833047055)
      ·
        refine ⟨117388015142106556249570583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78258676761404370833047055 117388015142106556249570583)
        ·
          refine ⟨176082022713159834374355875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117388015142106556249570583 176082022713159834374355875)
          ·
            refine ⟨264123034069739751561533813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176082022713159834374355875 264123034069739751561533813)
            ·
              refine ⟨24761534444038101708893795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 264123034069739751561533813 24761534444038101708893795)
              ·
                refine ⟨37142301666057152563340693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24761534444038101708893795 37142301666057152563340693)
                ·
                  refine ⟨1741045390596429026406595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37142301666057152563340693 1741045390596429026406595)
                  ·
                    refine ⟨2611568085894643539609893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1741045390596429026406595 2611568085894643539609893)
                    ·
                      refine ⟨489669016105245663676855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2611568085894643539609893 489669016105245663676855)
                      ·
                        rfl

theorem cell23_953627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 4].length) (baseStart_953627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953627 prefixEnd_953627 := by exact prefixLift 953627
  have htrace : WordTrace (prefixWord ++ tailWord_953627) baseStart_953627 baseEnd_953627 := by
    simpa [prefixWord, tailWord_953627, baseEnd_953627] using wordTrace_append hprefix tailTrace_953627
  have hstable : (prefixWord ++ tailWord_953627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953627).length < 2 ^ (prefixWord ++ tailWord_953627).sum := by decide
  have hdescent : baseEnd_953627 < baseStart_953627 := by decide
  rcases family_descends (prefixWord ++ tailWord_953627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953644 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 4, 4, 2]
def baseStart_953644 : Nat := 118140960795 + 953644 * 2 ^ 59
def prefixEnd_953644 : Nat := 4983230072969 + 3 ^ 40 * 953644 * 2
def baseEnd_953644 : Nat := 489677745276372097164277

theorem tailTrace_953644 : CollatzResearch.WordTrace tailWord_953644 prefixEnd_953644 489677745276372097164277 := by
  unfold tailWord_953644
  simp only [CollatzResearch.WordTrace]
  refine ⟨17391127078559066136805993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23188169438078754849074657 17391127078559066136805993)
  ·
    refine ⟨13043345308919299602604495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17391127078559066136805993 13043345308919299602604495)
    ·
      refine ⟨19565017963378949403906743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13043345308919299602604495 19565017963378949403906743)
      ·
        refine ⟨29347526945068424105860115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19565017963378949403906743 29347526945068424105860115)
        ·
          refine ⟨44021290417602636158790173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29347526945068424105860115 44021290417602636158790173)
          ·
            refine ⟨16507983906600988559546315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44021290417602636158790173 16507983906600988559546315)
            ·
              refine ⟨24761975859901482839319473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16507983906600988559546315 24761975859901482839319473)
              ·
                refine ⟨18571481894926112129489605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24761975859901482839319473 18571481894926112129489605)
                ·
                  refine ⟨3482152855298646024279301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18571481894926112129489605 3482152855298646024279301)
                  ·
                    refine ⟨652903660368496129552369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3482152855298646024279301 652903660368496129552369)
                    ·
                      refine ⟨489677745276372097164277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 652903660368496129552369 489677745276372097164277)
                      ·
                        rfl

theorem cell23_953644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 4, 2].length) (baseStart_953644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953644 prefixEnd_953644 := by exact prefixLift 953644
  have htrace : WordTrace (prefixWord ++ tailWord_953644) baseStart_953644 baseEnd_953644 := by
    simpa [prefixWord, tailWord_953644, baseEnd_953644] using wordTrace_append hprefix tailTrace_953644
  have hstable : (prefixWord ++ tailWord_953644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953644).length < 2 ^ (prefixWord ++ tailWord_953644).sum := by decide
  have hdescent : baseEnd_953644 < baseStart_953644 := by decide
  rcases family_descends (prefixWord ++ tailWord_953644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953664 : List Nat := [2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 3]
def baseStart_953664 : Nat := 118140960795 + 953664 * 2 ^ 59
def prefixEnd_953664 : Nat := 4983230072969 + 3 ^ 40 * 953664 * 2
def baseEnd_953664 : Nat := 489688014889462018914185

theorem tailTrace_953664 : CollatzResearch.WordTrace tailWord_953664 prefixEnd_953664 489688014889462018914185 := by
  unfold tailWord_953664
  simp only [CollatzResearch.WordTrace]
  refine ⟨17391491808522837844670023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23188655744697117126226697 17391491808522837844670023)
  ·
    refine ⟨26087237712784256767005035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17391491808522837844670023 26087237712784256767005035)
    ·
      refine ⟨39130856569176385150507553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26087237712784256767005035 39130856569176385150507553)
      ·
        refine ⟨29348142426882288862880665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39130856569176385150507553 29348142426882288862880665)
        ·
          refine ⟨22011106820161716647160499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29348142426882288862880665 22011106820161716647160499)
          ·
            refine ⟨33016660230242574970740749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22011106820161716647160499 33016660230242574970740749)
            ·
              refine ⟨12381247586340965614027781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33016660230242574970740749 12381247586340965614027781)
              ·
                refine ⟨2321483922438931052630209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12381247586340965614027781 2321483922438931052630209)
                ·
                  refine ⟨1741112941829198289472657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2321483922438931052630209 1741112941829198289472657)
                  ·
                    refine ⟨1305834706371898717104493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1741112941829198289472657 1305834706371898717104493)
                    ·
                      refine ⟨489688014889462018914185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1305834706371898717104493 489688014889462018914185)
                      ·
                        rfl

theorem cell23_953664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 3].length) (baseStart_953664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953664 prefixEnd_953664 := by exact prefixLift 953664
  have htrace : WordTrace (prefixWord ++ tailWord_953664) baseStart_953664 baseEnd_953664 := by
    simpa [prefixWord, tailWord_953664, baseEnd_953664] using wordTrace_append hprefix tailTrace_953664
  have hstable : (prefixWord ++ tailWord_953664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953664).length < 2 ^ (prefixWord ++ tailWord_953664).sum := by decide
  have hdescent : baseEnd_953664 < baseStart_953664 := by decide
  rcases family_descends (prefixWord ++ tailWord_953664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953684 : List Nat := [2, 4, 1, 1, 2, 1, 1, 5, 6]
def baseStart_953684 : Nat := 118140960795 + 953684 * 2 ^ 59
def prefixEnd_953684 : Nat := 4983230072969 + 3 ^ 40 * 953684 * 2
def baseEnd_953684 : Nat := 54410920500283548962677

theorem tailTrace_953684 : CollatzResearch.WordTrace tailWord_953684 prefixEnd_953684 54410920500283548962677 := by
  unfold tailWord_953684
  simp only [CollatzResearch.WordTrace]
  refine ⟨17391856538486609552534053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23189142051315479403378737 17391856538486609552534053)
  ·
    refine ⟨3260973100966239291100135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17391856538486609552534053 3260973100966239291100135)
    ·
      refine ⟨4891459651449358936650203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3260973100966239291100135 4891459651449358936650203)
      ·
        refine ⟨7337189477174038404975305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4891459651449358936650203 7337189477174038404975305)
        ·
          refine ⟨5502892107880528803731479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7337189477174038404975305 5502892107880528803731479)
          ·
            refine ⟨8254338161820793205597219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5502892107880528803731479 8254338161820793205597219)
            ·
              refine ⟨12381507242731189808395829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8254338161820793205597219 12381507242731189808395829)
              ·
                refine ⟨1160766304006049044537109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12381507242731189808395829 1160766304006049044537109)
                ·
                  refine ⟨54410920500283548962677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1160766304006049044537109 54410920500283548962677)
                  ·
                    rfl

theorem cell23_953684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_953684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953684 prefixEnd_953684 := by exact prefixLift 953684
  have htrace : WordTrace (prefixWord ++ tailWord_953684) baseStart_953684 baseEnd_953684 := by
    simpa [prefixWord, tailWord_953684, baseEnd_953684] using wordTrace_append hprefix tailTrace_953684
  have hstable : (prefixWord ++ tailWord_953684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953684).length < 2 ^ (prefixWord ++ tailWord_953684).sum := by decide
  have hdescent : baseEnd_953684 < baseStart_953684 := by decide
  rcases family_descends (prefixWord ++ tailWord_953684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953721 : List Nat := [1, 2, 1, 3, 2, 1, 2, 4, 2, 3, 2]
def baseStart_953721 : Nat := 118140960795 + 953721 * 2 ^ 59
def prefixEnd_953721 : Nat := 4983230072969 + 3 ^ 40 * 953721 * 2
def baseEnd_953721 : Nat := 489717283286768295901423

theorem tailTrace_953721 : CollatzResearch.WordTrace tailWord_953721 prefixEnd_953721 489717283286768295901423 := by
  unfold tailWord_953721
  simp only [CollatzResearch.WordTrace]
  refine ⟨34785062577839174424165017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23190041718559449616110011 34785062577839174424165017)
  ·
    refine ⟨26088796933379380818123763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34785062577839174424165017 26088796933379380818123763)
    ·
      refine ⟨39133195400069071227185645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26088796933379380818123763 39133195400069071227185645)
      ·
        refine ⟨14674948275025901710194617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39133195400069071227185645 14674948275025901710194617)
        ·
          refine ⟨11006211206269426282645963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14674948275025901710194617 11006211206269426282645963)
          ·
            refine ⟨16509316809404139423968945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11006211206269426282645963 16509316809404139423968945)
            ·
              refine ⟨12381987607053104567976709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16509316809404139423968945 12381987607053104567976709)
              ·
                refine ⟨2321622676322457106495633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12381987607053104567976709 2321622676322457106495633)
                ·
                  refine ⟨1741217007241842829871725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2321622676322457106495633 1741217007241842829871725)
                  ·
                    refine ⟨652956377715691061201897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1741217007241842829871725 652956377715691061201897)
                    ·
                      refine ⟨489717283286768295901423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 652956377715691061201897 489717283286768295901423)
                      ·
                        rfl

theorem cell23_953721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 3, 2].length) (baseStart_953721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953721 prefixEnd_953721 := by exact prefixLift 953721
  have htrace : WordTrace (prefixWord ++ tailWord_953721) baseStart_953721 baseEnd_953721 := by
    simpa [prefixWord, tailWord_953721, baseEnd_953721] using wordTrace_append hprefix tailTrace_953721
  have hstable : (prefixWord ++ tailWord_953721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953721).length < 2 ^ (prefixWord ++ tailWord_953721).sum := by decide
  have hdescent : baseEnd_953721 < baseStart_953721 := by decide
  rcases family_descends (prefixWord ++ tailWord_953721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953748 : List Nat := [2, 4, 2, 1, 2, 2, 2, 2, 1, 5]
def baseStart_953748 : Nat := 118140960795 + 953748 * 2 ^ 59
def prefixEnd_953748 : Nat := 4983230072969 + 3 ^ 40 * 953748 * 2
def baseEnd_953748 : Nat := 163243715754813230087933

theorem tailTrace_953748 : CollatzResearch.WordTrace tailWord_953748 prefixEnd_953748 163243715754813230087933 := by
  unfold tailWord_953748
  simp only [CollatzResearch.WordTrace]
  refine ⟨17393023674370679017698949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23190698232494238690265265 17393023674370679017698949)
  ·
    refine ⟨3261191938944502315818553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17393023674370679017698949 3261191938944502315818553)
    ·
      refine ⟨2445893954208376736863915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3261191938944502315818553 2445893954208376736863915)
      ·
        refine ⟨3668840931312565105295873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2445893954208376736863915 3668840931312565105295873)
        ·
          refine ⟨2751630698484423828971905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3668840931312565105295873 2751630698484423828971905)
          ·
            refine ⟨2063723023863317871728929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2751630698484423828971905 2063723023863317871728929)
            ·
              refine ⟨1547792267897488403796697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2063723023863317871728929 1547792267897488403796697)
              ·
                refine ⟨1160844200923116302847523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1547792267897488403796697 1160844200923116302847523)
                ·
                  refine ⟨1741266301384674454271285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1160844200923116302847523 1741266301384674454271285)
                  ·
                    refine ⟨163243715754813230087933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1741266301384674454271285 163243715754813230087933)
                    ·
                      rfl

theorem cell23_953748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_953748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953748 prefixEnd_953748 := by exact prefixLift 953748
  have htrace : WordTrace (prefixWord ++ tailWord_953748) baseStart_953748 baseEnd_953748 := by
    simpa [prefixWord, tailWord_953748, baseEnd_953748] using wordTrace_append hprefix tailTrace_953748
  have hstable : (prefixWord ++ tailWord_953748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953748).length < 2 ^ (prefixWord ++ tailWord_953748).sum := by decide
  have hdescent : baseEnd_953748 < baseStart_953748 := by decide
  rcases family_descends (prefixWord ++ tailWord_953748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953754 : List Nat := [3, 1, 1, 4, 1, 1, 1, 2, 3, 1, 5]
def baseStart_953754 : Nat := 118140960795 + 953754 * 2 ^ 59
def prefixEnd_953754 : Nat := 4983230072969 + 3 ^ 40 * 953754 * 2
def baseEnd_953754 : Nat := 489734228148366666788771

theorem tailTrace_953754 : CollatzResearch.WordTrace tailWord_953754 prefixEnd_953754 489734228148366666788771 := by
  unfold tailWord_953754
  simp only [CollatzResearch.WordTrace]
  refine ⟨8696566546679905265029079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23190844124479747373410877 8696566546679905265029079)
  ·
    refine ⟨13044849820019857897543619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8696566546679905265029079 13044849820019857897543619)
    ·
      refine ⟨19567274730029786846315429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13044849820019857897543619 19567274730029786846315429)
      ·
        refine ⟨3668864011880585033684143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19567274730029786846315429 3668864011880585033684143)
        ·
          refine ⟨5503296017820877550526215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3668864011880585033684143 5503296017820877550526215)
          ·
            refine ⟨8254944026731316325789323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5503296017820877550526215 8254944026731316325789323)
            ·
              refine ⟨12382416040096974488683985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8254944026731316325789323 12382416040096974488683985)
              ·
                refine ⟨9286812030072730866512989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12382416040096974488683985 9286812030072730866512989)
                ·
                  refine ⟨3482554511277274074942371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9286812030072730866512989 3482554511277274074942371)
                  ·
                    refine ⟨5223831766915911112413557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3482554511277274074942371 5223831766915911112413557)
                    ·
                      refine ⟨489734228148366666788771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5223831766915911112413557 489734228148366666788771)
                      ·
                        rfl

theorem cell23_953754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_953754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953754 prefixEnd_953754 := by exact prefixLift 953754
  have htrace : WordTrace (prefixWord ++ tailWord_953754) baseStart_953754 baseEnd_953754 := by
    simpa [prefixWord, tailWord_953754, baseEnd_953754] using wordTrace_append hprefix tailTrace_953754
  have hstable : (prefixWord ++ tailWord_953754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953754).length < 2 ^ (prefixWord ++ tailWord_953754).sum := by decide
  have hdescent : baseEnd_953754 < baseStart_953754 := by decide
  rcases family_descends (prefixWord ++ tailWord_953754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953762 : List Nat := [3, 3, 1, 2, 1, 4, 1, 3, 1, 1, 3]
def baseStart_953762 : Nat := 118140960795 + 953762 * 2 ^ 59
def prefixEnd_953762 : Nat := 4983230072969 + 3 ^ 40 * 953762 * 2
def baseEnd_953762 : Nat := 489738335993602635488735

theorem tailTrace_953762 : CollatzResearch.WordTrace tailWord_953762 prefixEnd_953762 489738335993602635488735 := by
  unfold tailWord_953762
  simp only [CollatzResearch.WordTrace]
  refine ⟨8696639492672659606601885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23191038647127092284271693 8696639492672659606601885)
  ·
    refine ⟨3261239809752247352475707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8696639492672659606601885 3261239809752247352475707)
    ·
      refine ⟨4891859714628371028713561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3261239809752247352475707 4891859714628371028713561)
      ·
        refine ⟨3668894785971278271535171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4891859714628371028713561 3668894785971278271535171)
        ·
          refine ⟨5503342178956917407302757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3668894785971278271535171 5503342178956917407302757)
          ·
            refine ⟨1031876658554422013869267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5503342178956917407302757 1031876658554422013869267)
            ·
              refine ⟨1547814987831633020803901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1031876658554422013869267 1547814987831633020803901)
              ·
                refine ⟨580430620436862382801463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1547814987831633020803901 580430620436862382801463)
                ·
                  refine ⟨870645930655293574202195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 580430620436862382801463 870645930655293574202195)
                  ·
                    refine ⟨1305968895982940361303293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 870645930655293574202195 1305968895982940361303293)
                    ·
                      refine ⟨489738335993602635488735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1305968895982940361303293 489738335993602635488735)
                      ·
                        rfl

theorem cell23_953762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_953762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953762 prefixEnd_953762 := by exact prefixLift 953762
  have htrace : WordTrace (prefixWord ++ tailWord_953762) baseStart_953762 baseEnd_953762 := by
    simpa [prefixWord, tailWord_953762, baseEnd_953762] using wordTrace_append hprefix tailTrace_953762
  have hstable : (prefixWord ++ tailWord_953762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953762).length < 2 ^ (prefixWord ++ tailWord_953762).sum := by decide
  have hdescent : baseEnd_953762 < baseStart_953762 := by decide
  rcases family_descends (prefixWord ++ tailWord_953762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953764 : List Nat := [2, 3, 1, 2, 1, 1, 1, 3, 3, 2, 4]
def baseStart_953764 : Nat := 118140960795 + 953764 * 2 ^ 59
def prefixEnd_953764 : Nat := 4983230072969 + 3 ^ 40 * 953764 * 2
def baseEnd_953764 : Nat := 489739362954911627663725

theorem tailTrace_953764 : CollatzResearch.WordTrace tailWord_953764 prefixEnd_953764 489739362954911627663725 := by
  unfold tailWord_953764
  simp only [CollatzResearch.WordTrace]
  refine ⟨17393315458341696383990173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23191087277788928511986897 17393315458341696383990173)
  ·
    refine ⟨6522493296878136143996315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17393315458341696383990173 6522493296878136143996315)
    ·
      refine ⟨9783739945317204215994473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6522493296878136143996315 9783739945317204215994473)
      ·
        refine ⟨7337804958987903161995855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9783739945317204215994473 7337804958987903161995855)
        ·
          refine ⟨11006707438481854742993783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7337804958987903161995855 11006707438481854742993783)
          ·
            refine ⟨16510061157722782114490675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11006707438481854742993783 16510061157722782114490675)
            ·
              refine ⟨24765091736584173171736013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16510061157722782114490675 24765091736584173171736013)
              ·
                refine ⟨9286909401219064939401005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24765091736584173171736013 9286909401219064939401005)
                ·
                  refine ⟨3482591025457149352275377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9286909401219064939401005 3482591025457149352275377)
                  ·
                    refine ⟨2611943269092862014206533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3482591025457149352275377 2611943269092862014206533)
                    ·
                      refine ⟨489739362954911627663725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2611943269092862014206533 489739362954911627663725)
                      ·
                        rfl

theorem cell23_953764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_953764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953764 prefixEnd_953764 := by exact prefixLift 953764
  have htrace : WordTrace (prefixWord ++ tailWord_953764) baseStart_953764 baseEnd_953764 := by
    simpa [prefixWord, tailWord_953764, baseEnd_953764] using wordTrace_append hprefix tailTrace_953764
  have hstable : (prefixWord ++ tailWord_953764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953764).length < 2 ^ (prefixWord ++ tailWord_953764).sum := by decide
  have hdescent : baseEnd_953764 < baseStart_953764 := by decide
  rcases family_descends (prefixWord ++ tailWord_953764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953828 : List Nat := [2, 3, 1, 1, 1, 1, 1, 7, 1, 3, 2]
def baseStart_953828 : Nat := 118140960795 + 953828 * 2 ^ 59
def prefixEnd_953828 : Nat := 4983230072969 + 3 ^ 40 * 953828 * 2
def baseEnd_953828 : Nat := 489772225716799377263431

theorem tailTrace_953828 : CollatzResearch.WordTrace tailWord_953828 prefixEnd_953828 489772225716799377263431 := by
  unfold tailWord_953828
  simp only [CollatzResearch.WordTrace]
  refine ⟨17394482594225765849155069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23192643458967687798873425 17394482594225765849155069)
  ·
    refine ⟨6522930972834662193433151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17394482594225765849155069 6522930972834662193433151)
    ·
      refine ⟨9784396459251993290149727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6522930972834662193433151 9784396459251993290149727)
      ·
        refine ⟨14676594688877989935224591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9784396459251993290149727 14676594688877989935224591)
        ·
          refine ⟨22014892033316984902836887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14676594688877989935224591 22014892033316984902836887)
          ·
            refine ⟨33022338049975477354255331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22014892033316984902836887 33022338049975477354255331)
            ·
              refine ⟨49533507074963216031382997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33022338049975477354255331 49533507074963216031382997)
              ·
                refine ⟨1160941572069450375735539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 49533507074963216031382997 1160941572069450375735539)
                ·
                  refine ⟨1741412358104175563603309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1160941572069450375735539 1741412358104175563603309)
                  ·
                    refine ⟨653029634289065836351241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1741412358104175563603309 653029634289065836351241)
                    ·
                      refine ⟨489772225716799377263431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 653029634289065836351241 489772225716799377263431)
                      ·
                        rfl

theorem cell23_953828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 1, 3, 2].length) (baseStart_953828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953828 prefixEnd_953828 := by exact prefixLift 953828
  have htrace : WordTrace (prefixWord ++ tailWord_953828) baseStart_953828 baseEnd_953828 := by
    simpa [prefixWord, tailWord_953828, baseEnd_953828] using wordTrace_append hprefix tailTrace_953828
  have hstable : (prefixWord ++ tailWord_953828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953828).length < 2 ^ (prefixWord ++ tailWord_953828).sum := by decide
  have hdescent : baseEnd_953828 < baseStart_953828 := by decide
  rcases family_descends (prefixWord ++ tailWord_953828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953845 : List Nat := [1, 3, 5, 1, 1, 1, 1, 2, 3, 3, 2]
def baseStart_953845 : Nat := 118140960795 + 953845 * 2 ^ 59
def prefixEnd_953845 : Nat := 4983230072969 + 3 ^ 40 * 953845 * 2
def baseEnd_953845 : Nat := 489780954887925810750853

theorem tailTrace_953845 : CollatzResearch.WordTrace tailWord_953845 prefixEnd_953845 489780954887925810750853 := by
  unfold tailWord_953845
  simp only [CollatzResearch.WordTrace]
  refine ⟨34789585229389943601678989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23193056819593295734452659 34789585229389943601678989)
  ·
    refine ⟨13046094461021228850629621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34789585229389943601678989 13046094461021228850629621)
    ·
      refine ⟨1223071355720740204746527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13046094461021228850629621 1223071355720740204746527)
      ·
        refine ⟨1834607033581110307119791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1223071355720740204746527 1834607033581110307119791)
        ·
          refine ⟨2751910550371665460679687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1834607033581110307119791 2751910550371665460679687)
          ·
            refine ⟨4127865825557498191019531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2751910550371665460679687 4127865825557498191019531)
            ·
              refine ⟨6191798738336247286529297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4127865825557498191019531 6191798738336247286529297)
              ·
                refine ⟨4643849053752185464896973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6191798738336247286529297 4643849053752185464896973)
                ·
                  refine ⟨1741443395157069549336365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4643849053752185464896973 1741443395157069549336365)
                  ·
                    refine ⟨653041273183901081001137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1741443395157069549336365 653041273183901081001137)
                    ·
                      refine ⟨489780954887925810750853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 653041273183901081001137 489780954887925810750853)
                      ·
                        rfl

theorem cell23_953845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_953845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953845 prefixEnd_953845 := by exact prefixLift 953845
  have htrace : WordTrace (prefixWord ++ tailWord_953845) baseStart_953845 baseEnd_953845 := by
    simpa [prefixWord, tailWord_953845, baseEnd_953845] using wordTrace_append hprefix tailTrace_953845
  have hstable : (prefixWord ++ tailWord_953845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953845).length < 2 ^ (prefixWord ++ tailWord_953845).sum := by decide
  have hdescent : baseEnd_953845 < baseStart_953845 := by decide
  rcases family_descends (prefixWord ++ tailWord_953845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953864 : List Nat := [2, 1, 3, 2, 1, 1, 3, 1, 9]
def baseStart_953864 : Nat := 118140960795 + 953864 * 2 ^ 59
def prefixEnd_953864 : Nat := 4983230072969 + 3 ^ 40 * 953864 * 2
def baseEnd_953864 : Nat := 54421190113373470712585

theorem tailTrace_953864 : CollatzResearch.WordTrace tailWord_953864 prefixEnd_953864 54421190113373470712585 := by
  unfold tailWord_953864
  simp only [CollatzResearch.WordTrace]
  refine ⟨17395139108160554923310323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23193518810880739897747097 17395139108160554923310323)
  ·
    refine ⟨26092708662240832384965485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17395139108160554923310323 26092708662240832384965485)
    ·
      refine ⟨9784765748340312144362057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26092708662240832384965485 9784765748340312144362057)
      ·
        refine ⟨7338574311255234108271543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9784765748340312144362057 7338574311255234108271543)
        ·
          refine ⟨11007861466882851162407315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7338574311255234108271543 11007861466882851162407315)
          ·
            refine ⟨16511792200324276743610973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11007861466882851162407315 16511792200324276743610973)
            ·
              refine ⟨6191922075121603778854115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16511792200324276743610973 6191922075121603778854115)
              ·
                refine ⟨9287883112682405668281173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6191922075121603778854115 9287883112682405668281173)
                ·
                  refine ⟨54421190113373470712585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9287883112682405668281173 54421190113373470712585)
                  ·
                    rfl

theorem cell23_953864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 9].length) (baseStart_953864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953864 prefixEnd_953864 := by exact prefixLift 953864
  have htrace : WordTrace (prefixWord ++ tailWord_953864) baseStart_953864 baseEnd_953864 := by
    simpa [prefixWord, tailWord_953864, baseEnd_953864] using wordTrace_append hprefix tailTrace_953864
  have hstable : (prefixWord ++ tailWord_953864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953864).length < 2 ^ (prefixWord ++ tailWord_953864).sum := by decide
  have hdescent : baseEnd_953864 < baseStart_953864 := by decide
  rcases family_descends (prefixWord ++ tailWord_953864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953898 : List Nat := [3, 1, 4, 1, 1, 1, 1, 6, 5]
def baseStart_953898 : Nat := 118140960795 + 953898 * 2 ^ 59
def prefixEnd_953898 : Nat := 4983230072969 + 3 ^ 40 * 953898 * 2
def baseEnd_953898 : Nat := 54423129929179344820901

theorem tailTrace_953898 : CollatzResearch.WordTrace tailWord_953898 prefixEnd_953898 54423129929179344820901 := by
  unfold tailWord_953898
  simp only [CollatzResearch.WordTrace]
  refine ⟨8697879574549483413339587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23194345532131955768905565 8697879574549483413339587)
  ·
    refine ⟨13046819361824225120009381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8697879574549483413339587 13046819361824225120009381)
    ·
      refine ⟨2446278630342042210001759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13046819361824225120009381 2446278630342042210001759)
      ·
        refine ⟨3669417945513063315002639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2446278630342042210001759 3669417945513063315002639)
        ·
          refine ⟨5504126918269594972503959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3669417945513063315002639 5504126918269594972503959)
          ·
            refine ⟨8256190377404392458755939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5504126918269594972503959 8256190377404392458755939)
            ·
              refine ⟨12384285566106588688133909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8256190377404392458755939 12384285566106588688133909)
              ·
                refine ⟨580513385911246344756277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12384285566106588688133909 580513385911246344756277)
                ·
                  refine ⟨54423129929179344820901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 580513385911246344756277 54423129929179344820901)
                  ·
                    rfl

theorem cell23_953898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 6, 5].length) (baseStart_953898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953898 prefixEnd_953898 := by exact prefixLift 953898
  have htrace : WordTrace (prefixWord ++ tailWord_953898) baseStart_953898 baseEnd_953898 := by
    simpa [prefixWord, tailWord_953898, baseEnd_953898] using wordTrace_append hprefix tailTrace_953898
  have hstable : (prefixWord ++ tailWord_953898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953898).length < 2 ^ (prefixWord ++ tailWord_953898).sum := by decide
  have hdescent : baseEnd_953898 < baseStart_953898 := by decide
  rcases family_descends (prefixWord ++ tailWord_953898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953904 : List Nat := [2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 7]
def baseStart_953904 : Nat := 118140960795 + 953904 * 2 ^ 59
def prefixEnd_953904 : Nat := 4983230072969 + 3 ^ 40 * 953904 * 2
def baseEnd_953904 : Nat := 489811250246541079913081

theorem tailTrace_953904 : CollatzResearch.WordTrace tailWord_953904 prefixEnd_953904 489811250246541079913081 := by
  unfold tailWord_953904
  simp only [CollatzResearch.WordTrace]
  refine ⟨17395868568088098339038383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23194491424117464452051177 17395868568088098339038383)
  ·
    refine ⟨26093802852132147508557575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17395868568088098339038383 26093802852132147508557575)
    ·
      refine ⟨39140704278198221262836363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26093802852132147508557575 39140704278198221262836363)
      ·
        refine ⟨58711056417297331894254545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39140704278198221262836363 58711056417297331894254545)
        ·
          refine ⟨44033292312972998920690909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58711056417297331894254545 44033292312972998920690909)
          ·
            refine ⟨16512484617364874595259091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44033292312972998920690909 16512484617364874595259091)
            ·
              refine ⟨24768726926047311892888637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16512484617364874595259091 24768726926047311892888637)
              ·
                refine ⟨9288272597267741959833239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24768726926047311892888637 9288272597267741959833239)
                ·
                  refine ⟨13932408895901612939749859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9288272597267741959833239 13932408895901612939749859)
                  ·
                    refine ⟨20898613343852419409624789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13932408895901612939749859 20898613343852419409624789)
                    ·
                      refine ⟨489811250246541079913081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 20898613343852419409624789 489811250246541079913081)
                      ·
                        rfl

theorem cell23_953904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 7].length) (baseStart_953904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953904 prefixEnd_953904 := by exact prefixLift 953904
  have htrace : WordTrace (prefixWord ++ tailWord_953904) baseStart_953904 baseEnd_953904 := by
    simpa [prefixWord, tailWord_953904, baseEnd_953904] using wordTrace_append hprefix tailTrace_953904
  have hstable : (prefixWord ++ tailWord_953904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953904).length < 2 ^ (prefixWord ++ tailWord_953904).sum := by decide
  have hdescent : baseEnd_953904 < baseStart_953904 := by decide
  rcases family_descends (prefixWord ++ tailWord_953904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953931 : List Nat := [1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 4]
def baseStart_953931 : Nat := 118140960795 + 953931 * 2 ^ 59
def prefixEnd_953931 : Nat := 4983230072969 + 3 ^ 40 * 953931 * 2
def baseEnd_953931 : Nat := 489825114224212474275457

theorem tailTrace_953931 : CollatzResearch.WordTrace tailWord_953931 prefixEnd_953931 489825114224212474275457 := by
  unfold tailWord_953931
  simp only [CollatzResearch.WordTrace]
  refine ⟨34792721907078380289309647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23195147938052253526206431 34792721907078380289309647)
  ·
    refine ⟨52189082860617570433964471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34792721907078380289309647 52189082860617570433964471)
    ·
      refine ⟨78283624290926355650946707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52189082860617570433964471 78283624290926355650946707)
      ·
        refine ⟨117425436436389533476420061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78283624290926355650946707 117425436436389533476420061)
        ·
          refine ⟨44034538663646075053657523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117425436436389533476420061 44034538663646075053657523)
          ·
            refine ⟨66051807995469112580486285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44034538663646075053657523 66051807995469112580486285)
            ·
              refine ⟨24769427998300917217682357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66051807995469112580486285 24769427998300917217682357)
              ·
                refine ⟨2322133874840710989157721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24769427998300917217682357 2322133874840710989157721)
                ·
                  refine ⟨1741600406130533241868291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2322133874840710989157721 1741600406130533241868291)
                  ·
                    refine ⟨2612400609195799862802437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1741600406130533241868291 2612400609195799862802437)
                    ·
                      refine ⟨489825114224212474275457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2612400609195799862802437 489825114224212474275457)
                      ·
                        rfl

theorem cell23_953931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 4].length) (baseStart_953931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953931 prefixEnd_953931 := by exact prefixLift 953931
  have htrace : WordTrace (prefixWord ++ tailWord_953931) baseStart_953931 baseEnd_953931 := by
    simpa [prefixWord, tailWord_953931, baseEnd_953931] using wordTrace_append hprefix tailTrace_953931
  have hstable : (prefixWord ++ tailWord_953931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953931).length < 2 ^ (prefixWord ++ tailWord_953931).sum := by decide
  have hdescent : baseEnd_953931 < baseStart_953931 := by decide
  rcases family_descends (prefixWord ++ tailWord_953931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953948 : List Nat := [2, 2, 4, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_953948 : Nat := 118140960795 + 953948 * 2 ^ 59
def prefixEnd_953948 : Nat := 4983230072969 + 3 ^ 40 * 953948 * 2
def baseEnd_953948 : Nat := 489833843395338907762879

theorem tailTrace_953948 : CollatzResearch.WordTrace tailWord_953948 prefixEnd_953948 489833843395338907762879 := by
  unfold tailWord_953948
  simp only [CollatzResearch.WordTrace]
  refine ⟨17396670974008396096339249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23195561298677861461785665 17396670974008396096339249)
  ·
    refine ⟨13047503230506297072254437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17396670974008396096339249 13047503230506297072254437)
    ·
      refine ⟨2446406855719930701047707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13047503230506297072254437 2446406855719930701047707)
      ·
        refine ⟨3669610283579896051571561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2446406855719930701047707 3669610283579896051571561)
        ·
          refine ⟨2752207712684922038678671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3669610283579896051571561 2752207712684922038678671)
          ·
            refine ⟨4128311569027383058018007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2752207712684922038678671 4128311569027383058018007)
            ·
              refine ⟨6192467353541074587027011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4128311569027383058018007 6192467353541074587027011)
              ·
                refine ⟨9288701030311611880540517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6192467353541074587027011 9288701030311611880540517)
                ·
                  refine ⟨1741631443183427227601347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9288701030311611880540517 1741631443183427227601347)
                  ·
                    refine ⟨2612447164775140841402021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1741631443183427227601347 2612447164775140841402021)
                    ·
                      refine ⟨489833843395338907762879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2612447164775140841402021 489833843395338907762879)
                      ·
                        rfl

theorem cell23_953948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_953948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953948 prefixEnd_953948 := by exact prefixLift 953948
  have htrace : WordTrace (prefixWord ++ tailWord_953948) baseStart_953948 baseEnd_953948 := by
    simpa [prefixWord, tailWord_953948, baseEnd_953948] using wordTrace_append hprefix tailTrace_953948
  have hstable : (prefixWord ++ tailWord_953948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953948).length < 2 ^ (prefixWord ++ tailWord_953948).sum := by decide
  have hdescent : baseEnd_953948 < baseStart_953948 := by decide
  rcases family_descends (prefixWord ++ tailWord_953948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953949 : List Nat := [1, 4, 4, 2, 1, 1, 3, 2, 5]
def baseStart_953949 : Nat := 118140960795 + 953949 * 2 ^ 59
def prefixEnd_953949 : Nat := 4983230072969 + 3 ^ 40 * 953949 * 2
def baseEnd_953949 : Nat := 54426039652888155983375

theorem tailTrace_953949 : CollatzResearch.WordTrace tailWord_953949 prefixEnd_953949 54426039652888155983375 := by
  unfold tailWord_953949
  simp only [CollatzResearch.WordTrace]
  refine ⟨34793378421013169363464901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23195585614008779575643267 34793378421013169363464901)
  ·
    refine ⟨6523758453939969255649669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34793378421013169363464901 6523758453939969255649669)
    ·
      refine ⟨1223204710113744235434313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6523758453939969255649669 1223204710113744235434313)
      ·
        refine ⟨917403532585308176575735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1223204710113744235434313 917403532585308176575735)
        ·
          refine ⟨1376105298877962264863603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 917403532585308176575735 1376105298877962264863603)
          ·
            refine ⟨2064157948316943397295405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1376105298877962264863603 2064157948316943397295405)
            ·
              refine ⟨774059230618853773985777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2064157948316943397295405 774059230618853773985777)
              ·
                refine ⟨580544422964140330489333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 774059230618853773985777 580544422964140330489333)
                ·
                  refine ⟨54426039652888155983375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 580544422964140330489333 54426039652888155983375)
                  ·
                    rfl

theorem cell23_953949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 2, 5].length) (baseStart_953949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953949 prefixEnd_953949 := by exact prefixLift 953949
  have htrace : WordTrace (prefixWord ++ tailWord_953949) baseStart_953949 baseEnd_953949 := by
    simpa [prefixWord, tailWord_953949, baseEnd_953949] using wordTrace_append hprefix tailTrace_953949
  have hstable : (prefixWord ++ tailWord_953949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953949).length < 2 ^ (prefixWord ++ tailWord_953949).sum := by decide
  have hdescent : baseEnd_953949 < baseStart_953949 := by decide
  rcases family_descends (prefixWord ++ tailWord_953949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_953985 : List Nat := [1, 2, 4, 2, 1, 3, 2, 1, 2, 2, 3]
def baseStart_953985 : Nat := 118140960795 + 953985 * 2 ^ 59
def prefixEnd_953985 : Nat := 4983230072969 + 3 ^ 40 * 953985 * 2
def baseEnd_953985 : Nat := 489852842179555263000209

theorem tailTrace_953985 : CollatzResearch.WordTrace tailWord_953985 prefixEnd_953985 489852842179555263000209 := by
  unfold tailWord_953985
  simp only [CollatzResearch.WordTrace]
  refine ⟨34794691448882747511775409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23196460965921831674516939 34794691448882747511775409)
  ·
    refine ⟨26096018586662060633831557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34794691448882747511775409 26096018586662060633831557)
    ·
      refine ⟨4893003484999136368843417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26096018586662060633831557 4893003484999136368843417)
      ·
        refine ⟨3669752613749352276632563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4893003484999136368843417 3669752613749352276632563)
        ·
          refine ⟨5504628920624028414948845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3669752613749352276632563 5504628920624028414948845)
          ·
            refine ⟨2064235845234010655605817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5504628920624028414948845 2064235845234010655605817)
            ·
              refine ⟨1548176883925507991704363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2064235845234010655605817 1548176883925507991704363)
              ·
                refine ⟨2322265325888261987556545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1548176883925507991704363 2322265325888261987556545)
                ·
                  refine ⟨1741698994416196490667409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2322265325888261987556545 1741698994416196490667409)
                  ·
                    refine ⟨1306274245812147368000557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1741698994416196490667409 1306274245812147368000557)
                    ·
                      refine ⟨489852842179555263000209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1306274245812147368000557 489852842179555263000209)
                      ·
                        rfl

theorem cell23_953985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_953985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_953985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_953985 prefixEnd_953985 := by exact prefixLift 953985
  have htrace : WordTrace (prefixWord ++ tailWord_953985) baseStart_953985 baseEnd_953985 := by
    simpa [prefixWord, tailWord_953985, baseEnd_953985] using wordTrace_append hprefix tailTrace_953985
  have hstable : (prefixWord ++ tailWord_953985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_953985).length < 2 ^ (prefixWord ++ tailWord_953985).sum := by decide
  have hdescent : baseEnd_953985 < baseStart_953985 := by decide
  rcases family_descends (prefixWord ++ tailWord_953985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954042 : List Nat := [3, 1, 1, 1, 2, 6, 1, 1, 2, 3, 2]
def baseStart_954042 : Nat := 118140960795 + 954042 * 2 ^ 59
def prefixEnd_954042 : Nat := 4983230072969 + 3 ^ 40 * 954042 * 2
def baseEnd_954042 : Nat := 489882110576861539987447

theorem tailTrace_954042 : CollatzResearch.WordTrace tailWord_954042 prefixEnd_954042 489882110576861539987447 := by
  unfold tailWord_954042
  simp only [CollatzResearch.WordTrace]
  refine ⟨8699192602419061561650095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23197846939784164164400253 8699192602419061561650095)
  ·
    refine ⟨13048788903628592342475143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8699192602419061561650095 13048788903628592342475143)
    ·
      refine ⟨19573183355442888513712715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13048788903628592342475143 19573183355442888513712715)
      ·
        refine ⟨29359775033164332770569073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19573183355442888513712715 29359775033164332770569073)
        ·
          refine ⟨22019831274873249577926805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29359775033164332770569073 22019831274873249577926805)
          ·
            refine ⟨1032179591009683573965319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22019831274873249577926805 1032179591009683573965319)
            ·
              refine ⟨1548269386514525360947979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1032179591009683573965319 1548269386514525360947979)
              ·
                refine ⟨2322404079771788041421969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1548269386514525360947979 2322404079771788041421969)
                ·
                  refine ⟨1741803059828841031066477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2322404079771788041421969 1741803059828841031066477)
                  ·
                    refine ⟨653176147435815386649929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1741803059828841031066477 653176147435815386649929)
                    ·
                      refine ⟨489882110576861539987447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 653176147435815386649929 489882110576861539987447)
                      ·
                        rfl

theorem cell23_954042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 2, 3, 2].length) (baseStart_954042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954042 prefixEnd_954042 := by exact prefixLift 954042
  have htrace : WordTrace (prefixWord ++ tailWord_954042) baseStart_954042 baseEnd_954042 := by
    simpa [prefixWord, tailWord_954042, baseEnd_954042] using wordTrace_append hprefix tailTrace_954042
  have hstable : (prefixWord ++ tailWord_954042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954042).length < 2 ^ (prefixWord ++ tailWord_954042).sum := by decide
  have hdescent : baseEnd_954042 < baseStart_954042 := by decide
  rcases family_descends (prefixWord ++ tailWord_954042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954048 : List Nat := [2, 1, 1, 2, 4, 1, 2, 2, 4, 4]
def baseStart_954048 : Nat := 118140960795 + 954048 * 2 ^ 59
def prefixEnd_954048 : Nat := 4983230072969 + 3 ^ 40 * 954048 * 2
def baseEnd_954048 : Nat := 163295063820262838837473

theorem tailTrace_954048 : CollatzResearch.WordTrace tailWord_954048 prefixEnd_954048 163295063820262838837473 := by
  unfold tailWord_954048
  simp only [CollatzResearch.WordTrace]
  refine ⟨17398494623827254635659399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23197992831769672847545865 17398494623827254635659399)
  ·
    refine ⟨26097741935740881953489099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17398494623827254635659399 26097741935740881953489099)
    ·
      refine ⟨39146612903611322930233649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26097741935740881953489099 39146612903611322930233649)
      ·
        refine ⟨29359959677708492197675237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39146612903611322930233649 29359959677708492197675237)
        ·
          refine ⟨5504992439570342287064107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29359959677708492197675237 5504992439570342287064107)
          ·
            refine ⟨8257488659355513430596161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5504992439570342287064107 8257488659355513430596161)
            ·
              refine ⟨6193116494516635072947121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8257488659355513430596161 6193116494516635072947121)
              ·
                refine ⟨4644837370887476304710341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6193116494516635072947121 4644837370887476304710341)
                ·
                  refine ⟨870907007041401807133189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4644837370887476304710341 870907007041401807133189)
                  ·
                    refine ⟨163295063820262838837473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 870907007041401807133189 163295063820262838837473)
                    ·
                      rfl

theorem cell23_954048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 4, 4].length) (baseStart_954048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954048 prefixEnd_954048 := by exact prefixLift 954048
  have htrace : WordTrace (prefixWord ++ tailWord_954048) baseStart_954048 baseEnd_954048 := by
    simpa [prefixWord, tailWord_954048, baseEnd_954048] using wordTrace_append hprefix tailTrace_954048
  have hstable : (prefixWord ++ tailWord_954048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954048).length < 2 ^ (prefixWord ++ tailWord_954048).sum := by decide
  have hdescent : baseEnd_954048 < baseStart_954048 := by decide
  rcases family_descends (prefixWord ++ tailWord_954048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954055 : List Nat := [1, 1, 4, 1, 1, 1, 3, 2, 5, 2, 2]
def baseStart_954055 : Nat := 118140960795 + 954055 * 2 ^ 59
def prefixEnd_954055 : Nat := 4983230072969 + 3 ^ 40 * 954055 * 2
def baseEnd_954055 : Nat := 489888785825369989124887

theorem tailTrace_954055 : CollatzResearch.WordTrace tailWord_954055 prefixEnd_954055 489888785825369989124887 := by
  unfold tailWord_954055
  simp only [CollatzResearch.WordTrace]
  refine ⟨34797244558629149466823619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23198163039086099644549079 34797244558629149466823619)
  ·
    refine ⟨52195866837943724200235429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34797244558629149466823619 52195866837943724200235429)
    ·
      refine ⟨9786725032114448287544143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52195866837943724200235429 9786725032114448287544143)
      ·
        refine ⟨14680087548171672431316215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9786725032114448287544143 14680087548171672431316215)
        ·
          refine ⟨22020131322257508646974323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14680087548171672431316215 22020131322257508646974323)
          ·
            refine ⟨33030196983386262970461485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22020131322257508646974323 33030196983386262970461485)
            ·
              refine ⟨12386323868769848613923057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33030196983386262970461485 12386323868769848613923057)
              ·
                refine ⟨9289742901577386460442293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12386323868769848613923057 9289742901577386460442293)
                ·
                  refine ⟨870913397022879980666465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9289742901577386460442293 870913397022879980666465)
                  ·
                    refine ⟨653185047767159985499849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 870913397022879980666465 653185047767159985499849)
                    ·
                      refine ⟨489888785825369989124887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 653185047767159985499849 489888785825369989124887)
                      ·
                        rfl

theorem cell23_954055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 5, 2, 2].length) (baseStart_954055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954055 prefixEnd_954055 := by exact prefixLift 954055
  have htrace : WordTrace (prefixWord ++ tailWord_954055) baseStart_954055 baseEnd_954055 := by
    simpa [prefixWord, tailWord_954055, baseEnd_954055] using wordTrace_append hprefix tailTrace_954055
  have hstable : (prefixWord ++ tailWord_954055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954055).length < 2 ^ (prefixWord ++ tailWord_954055).sum := by decide
  have hdescent : baseEnd_954055 < baseStart_954055 := by decide
  rcases family_descends (prefixWord ++ tailWord_954055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954065 : List Nat := [1, 2, 2, 1, 2, 4, 3, 2, 2, 4]
def baseStart_954065 : Nat := 118140960795 + 954065 * 2 ^ 59
def prefixEnd_954065 : Nat := 4983230072969 + 3 ^ 40 * 954065 * 2
def baseEnd_954065 : Nat := 163297973543971649999947

theorem tailTrace_954065 : CollatzResearch.WordTrace tailWord_954065 prefixEnd_954065 163297973543971649999947 := by
  unfold tailWord_954065
  simp only [CollatzResearch.WordTrace]
  refine ⟨34797609288592921174687649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23198406192395280783125099 34797609288592921174687649)
  ·
    refine ⟨26098206966444690881015737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34797609288592921174687649 26098206966444690881015737)
    ·
      refine ⟨19573655224833518160761803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26098206966444690881015737 19573655224833518160761803)
      ·
        refine ⟨29360482837250277241142705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19573655224833518160761803 29360482837250277241142705)
        ·
          refine ⟨22020362127937707930857029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29360482837250277241142705 22020362127937707930857029)
          ·
            refine ⟨4128817898988320237035693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22020362127937707930857029 4128817898988320237035693)
            ·
              refine ⟨1548306712120620088888385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4128817898988320237035693 1548306712120620088888385)
              ·
                refine ⟨1161230034090465066666289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1548306712120620088888385 1161230034090465066666289)
                ·
                  refine ⟨870922525567848799999717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1161230034090465066666289 870922525567848799999717)
                  ·
                    refine ⟨163297973543971649999947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 870922525567848799999717 163297973543971649999947)
                    ·
                      rfl

theorem cell23_954065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 2, 4].length) (baseStart_954065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954065 prefixEnd_954065 := by exact prefixLift 954065
  have htrace : WordTrace (prefixWord ++ tailWord_954065) baseStart_954065 baseEnd_954065 := by
    simpa [prefixWord, tailWord_954065, baseEnd_954065] using wordTrace_append hprefix tailTrace_954065
  have hstable : (prefixWord ++ tailWord_954065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954065).length < 2 ^ (prefixWord ++ tailWord_954065).sum := by decide
  have hdescent : baseEnd_954065 < baseStart_954065 := by decide
  rcases family_descends (prefixWord ++ tailWord_954065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954072 : List Nat := [2, 1, 2, 2, 3, 1, 4, 1, 3, 2, 2]
def baseStart_954072 : Nat := 118140960795 + 954072 * 2 ^ 59
def prefixEnd_954072 : Nat := 4983230072969 + 3 ^ 40 * 954072 * 2
def baseEnd_954072 : Nat := 489897514996496422612309

theorem tailTrace_954072 : CollatzResearch.WordTrace tailWord_954072 prefixEnd_954072 489897514996496422612309 := by
  unfold tailWord_954072
  simp only [CollatzResearch.WordTrace]
  refine ⟨17398932299783780685096235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23198576399711707580128313 17398932299783780685096235)
  ·
    refine ⟨26098398449675671027644353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17398932299783780685096235 26098398449675671027644353)
    ·
      refine ⟨19573798837256753270733265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26098398449675671027644353 19573798837256753270733265)
      ·
        refine ⟨14680349127942564953049949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19573798837256753270733265 14680349127942564953049949)
        ·
          refine ⟨5505130922978461857393731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14680349127942564953049949 5505130922978461857393731)
          ·
            refine ⟨8257696384467692786090597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5505130922978461857393731 8257696384467692786090597)
            ·
              refine ⟨1548318072087692397391987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8257696384467692786090597 1548318072087692397391987)
              ·
                refine ⟨2322477108131538596087981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1548318072087692397391987 2322477108131538596087981)
                ·
                  refine ⟨870928915549326973532993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2322477108131538596087981 870928915549326973532993)
                  ·
                    refine ⟨653196686661995230149745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 870928915549326973532993 653196686661995230149745)
                    ·
                      refine ⟨489897514996496422612309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 653196686661995230149745 489897514996496422612309)
                      ·
                        rfl

theorem cell23_954072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 3, 2, 2].length) (baseStart_954072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954072 prefixEnd_954072 := by exact prefixLift 954072
  have htrace : WordTrace (prefixWord ++ tailWord_954072) baseStart_954072 baseEnd_954072 := by
    simpa [prefixWord, tailWord_954072, baseEnd_954072] using wordTrace_append hprefix tailTrace_954072
  have hstable : (prefixWord ++ tailWord_954072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954072).length < 2 ^ (prefixWord ++ tailWord_954072).sum := by decide
  have hdescent : baseEnd_954072 < baseStart_954072 := by decide
  rcases family_descends (prefixWord ++ tailWord_954072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954091 : List Nat := [1, 1, 1, 1, 2, 4, 2, 2, 2, 7]
def baseStart_954091 : Nat := 118140960795 + 954091 * 2 ^ 59
def prefixEnd_954091 : Nat := 4983230072969 + 3 ^ 40 * 954091 * 2
def baseEnd_954091 : Nat := 163302423709643949424907

theorem tailTrace_954091 : CollatzResearch.WordTrace tailWord_954091 prefixEnd_954091 163302423709643949424907 := by
  unfold tailWord_954091
  simp only [CollatzResearch.WordTrace]
  refine ⟨34798557586498727615134127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23199038390999151743422751 34798557586498727615134127)
  ·
    refine ⟨52197836379748091422701191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34798557586498727615134127 52197836379748091422701191)
    ·
      refine ⟨78296754569622137134051787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52197836379748091422701191 78296754569622137134051787)
      ·
        refine ⟨117445131854433205701077681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78296754569622137134051787 117445131854433205701077681)
        ·
          refine ⟨88083848890824904275808261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117445131854433205701077681 88083848890824904275808261)
          ·
            refine ⟨16515721667029669551714049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88083848890824904275808261 16515721667029669551714049)
            ·
              refine ⟨12386791250272252163785537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16515721667029669551714049 12386791250272252163785537)
              ·
                refine ⟨9290093437704189122839153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12386791250272252163785537 9290093437704189122839153)
                ·
                  refine ⟨6967570078278141842129365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9290093437704189122839153 6967570078278141842129365)
                  ·
                    refine ⟨163302423709643949424907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6967570078278141842129365 163302423709643949424907)
                    ·
                      rfl

theorem cell23_954091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 7].length) (baseStart_954091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954091 prefixEnd_954091 := by exact prefixLift 954091
  have htrace : WordTrace (prefixWord ++ tailWord_954091) baseStart_954091 baseEnd_954091 := by
    simpa [prefixWord, tailWord_954091, baseEnd_954091] using wordTrace_append hprefix tailTrace_954091
  have hstable : (prefixWord ++ tailWord_954091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954091).length < 2 ^ (prefixWord ++ tailWord_954091).sum := by decide
  have hdescent : baseEnd_954091 < baseStart_954091 := by decide
  rcases family_descends (prefixWord ++ tailWord_954091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954149 : List Nat := [1, 3, 1, 2, 3, 4, 1, 2, 1, 3, 2]
def baseStart_954149 : Nat := 118140960795 + 954149 * 2 ^ 59
def prefixEnd_954149 : Nat := 4983230072969 + 3 ^ 40 * 954149 * 2
def baseEnd_954149 : Nat := 489937053006892621349455

theorem tailTrace_954149 : CollatzResearch.WordTrace tailWord_954149 prefixEnd_954149 489937053006892621349455 := by
  unfold tailWord_954149
  simp only [CollatzResearch.WordTrace]
  refine ⟨34800673020288603520745501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23200448680192402347163667 34800673020288603520745501)
  ·
    refine ⟨13050252382608226320279563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34800673020288603520745501 13050252382608226320279563)
    ·
      refine ⟨19575378573912339480419345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13050252382608226320279563 19575378573912339480419345)
      ·
        refine ⟨14681533930434254610314509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19575378573912339480419345 14681533930434254610314509)
        ·
          refine ⟨5505575223912845478867941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14681533930434254610314509 5505575223912845478867941)
          ·
            refine ⟨1032295354483658527287739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5505575223912845478867941 1032295354483658527287739)
            ·
              refine ⟨1548443031725487790931609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1032295354483658527287739 1548443031725487790931609)
              ·
                refine ⟨1161332273794115843198707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1548443031725487790931609 1161332273794115843198707)
                ·
                  refine ⟨1741998410691173764798061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1161332273794115843198707 1741998410691173764798061)
                  ·
                    refine ⟨653249404009190161799273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1741998410691173764798061 653249404009190161799273)
                    ·
                      refine ⟨489937053006892621349455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 653249404009190161799273 489937053006892621349455)
                      ·
                        rfl

theorem cell23_954149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 3, 2].length) (baseStart_954149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954149 prefixEnd_954149 := by exact prefixLift 954149
  have htrace : WordTrace (prefixWord ++ tailWord_954149) baseStart_954149 baseEnd_954149 := by
    simpa [prefixWord, tailWord_954149, baseEnd_954149] using wordTrace_append hprefix tailTrace_954149
  have hstable : (prefixWord ++ tailWord_954149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954149).length < 2 ^ (prefixWord ++ tailWord_954149).sum := by decide
  have hdescent : baseEnd_954149 < baseStart_954149 := by decide
  rcases family_descends (prefixWord ++ tailWord_954149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954162 : List Nat := [3, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2]
def baseStart_954162 : Nat := 118140960795 + 954162 * 2 ^ 59
def prefixEnd_954162 : Nat := 4983230072969 + 3 ^ 40 * 954162 * 2
def baseEnd_954162 : Nat := 489943728255401070486895

theorem tailTrace_954162 : CollatzResearch.WordTrace tailWord_954162 prefixEnd_954162 489943728255401070486895 := by
  unfold tailWord_954162
  simp only [CollatzResearch.WordTrace]
  refine ⟨8700286792310376685242185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23200764779494337827312493 8700286792310376685242185)
  ·
    refine ⟨6525215094232782513931639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8700286792310376685242185 6525215094232782513931639)
    ·
      refine ⟨9787822641349173770897459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6525215094232782513931639 9787822641349173770897459)
      ·
        refine ⟨14681733962023760656346189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9787822641349173770897459 14681733962023760656346189)
        ·
          refine ⟨5505650235758910246129821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14681733962023760656346189 5505650235758910246129821)
          ·
            refine ⟨2064618838409591342298683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5505650235758910246129821 2064618838409591342298683)
            ·
              refine ⟨3096928257614387013448025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2064618838409591342298683 3096928257614387013448025)
              ·
                refine ⟨2322696193210790260086019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3096928257614387013448025 2322696193210790260086019)
                ·
                  refine ⟨3484044289816185390129029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2322696193210790260086019 3484044289816185390129029)
                  ·
                    refine ⟨653258304340534760649193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3484044289816185390129029 653258304340534760649193)
                    ·
                      refine ⟨489943728255401070486895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 653258304340534760649193 489943728255401070486895)
                      ·
                        rfl

theorem cell23_954162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2].length) (baseStart_954162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954162 prefixEnd_954162 := by exact prefixLift 954162
  have htrace : WordTrace (prefixWord ++ tailWord_954162) baseStart_954162 baseEnd_954162 := by
    simpa [prefixWord, tailWord_954162, baseEnd_954162] using wordTrace_append hprefix tailTrace_954162
  have hstable : (prefixWord ++ tailWord_954162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954162).length < 2 ^ (prefixWord ++ tailWord_954162).sum := by decide
  have hdescent : baseEnd_954162 < baseStart_954162 := by decide
  rcases family_descends (prefixWord ++ tailWord_954162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954179 : List Nat := [1, 1, 1, 3, 1, 6, 2, 2, 2, 2, 2]
def baseStart_954179 : Nat := 118140960795 + 954179 * 2 ^ 59
def prefixEnd_954179 : Nat := 4983230072969 + 3 ^ 40 * 954179 * 2
def baseEnd_954179 : Nat := 489952457426527503974317

theorem tailTrace_954179 : CollatzResearch.WordTrace tailWord_954179 prefixEnd_954179 489952457426527503974317 := by
  unfold tailWord_954179
  simp only [CollatzResearch.WordTrace]
  refine ⟨34801767210179918644337591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23201178140119945762891727 34801767210179918644337591)
  ·
    refine ⟨52202650815269877966506387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34801767210179918644337591 52202650815269877966506387)
    ·
      refine ⟨78303976222904816949759581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52202650815269877966506387 78303976222904816949759581)
      ·
        refine ⟨29363991083589306356159843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78303976222904816949759581 29363991083589306356159843)
        ·
          refine ⟨44045986625383959534239765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29363991083589306356159843 44045986625383959534239765)
          ·
            refine ⟨2064655623064873103167489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 44045986625383959534239765 2064655623064873103167489)
            ·
              refine ⟨1548491717298654827375617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2064655623064873103167489 1548491717298654827375617)
              ·
                refine ⟨1161368787973991120531713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1548491717298654827375617 1161368787973991120531713)
                ·
                  refine ⟨871026590980493340398785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1161368787973991120531713 871026590980493340398785)
                  ·
                    refine ⟨653269943235370005299089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 871026590980493340398785 653269943235370005299089)
                    ·
                      refine ⟨489952457426527503974317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 653269943235370005299089 489952457426527503974317)
                      ·
                        rfl

theorem cell23_954179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 2, 2, 2].length) (baseStart_954179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954179 prefixEnd_954179 := by exact prefixLift 954179
  have htrace : WordTrace (prefixWord ++ tailWord_954179) baseStart_954179 baseEnd_954179 := by
    simpa [prefixWord, tailWord_954179, baseEnd_954179] using wordTrace_append hprefix tailTrace_954179
  have hstable : (prefixWord ++ tailWord_954179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954179).length < 2 ^ (prefixWord ++ tailWord_954179).sum := by decide
  have hdescent : baseEnd_954179 < baseStart_954179 := by decide
  rcases family_descends (prefixWord ++ tailWord_954179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954185 : List Nat := [1, 2, 1, 1, 2, 4, 3, 4, 5]
def baseStart_954185 : Nat := 118140960795 + 954185 * 2 ^ 59
def prefixEnd_954185 : Nat := 4983230072969 + 3 ^ 40 * 954185 * 2
def baseEnd_954185 : Nat := 54439504256717164499921

theorem tailTrace_954185 : CollatzResearch.WordTrace tailWord_954185 prefixEnd_954185 54439504256717164499921 := by
  unfold tailWord_954185
  simp only [CollatzResearch.WordTrace]
  refine ⟨34801986048158181669056009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23201324032105454446037339 34801986048158181669056009)
  ·
    refine ⟨26101489536118636251792007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34801986048158181669056009 26101489536118636251792007)
    ·
      refine ⟨39152234304177954377688011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26101489536118636251792007 39152234304177954377688011)
      ·
        refine ⟨58728351456266931566532017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39152234304177954377688011 58728351456266931566532017)
        ·
          refine ⟨44046263592200198674899013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58728351456266931566532017 44046263592200198674899013)
          ·
            refine ⟨8258674423537537251543565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44046263592200198674899013 8258674423537537251543565)
            ·
              refine ⟨3097002908826576469328837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8258674423537537251543565 3097002908826576469328837)
              ·
                refine ⟨580688045404983087999157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3097002908826576469328837 580688045404983087999157)
                ·
                  refine ⟨54439504256717164499921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 580688045404983087999157 54439504256717164499921)
                  ·
                    rfl

theorem cell23_954185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 4, 5].length) (baseStart_954185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954185 prefixEnd_954185 := by exact prefixLift 954185
  have htrace : WordTrace (prefixWord ++ tailWord_954185) baseStart_954185 baseEnd_954185 := by
    simpa [prefixWord, tailWord_954185, baseEnd_954185] using wordTrace_append hprefix tailTrace_954185
  have hstable : (prefixWord ++ tailWord_954185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954185).length < 2 ^ (prefixWord ++ tailWord_954185).sum := by decide
  have hdescent : baseEnd_954185 < baseStart_954185 := by decide
  rcases family_descends (prefixWord ++ tailWord_954185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954230 : List Nat := [5, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2]
def baseStart_954230 : Nat := 118140960795 + 954230 * 2 ^ 59
def prefixEnd_954230 : Nat := 4983230072969 + 3 ^ 40 * 954230 * 2
def baseEnd_954230 : Nat := 489978644939906804436583

theorem tailTrace_954230 : CollatzResearch.WordTrace tailWord_954230 prefixEnd_954230 489978644939906804436583 := by
  unfold tailWord_954230
  simp only [CollatzResearch.WordTrace]
  refine ⟨2175226708312197147152759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23202418221996769569629429 2175226708312197147152759)
  ·
    refine ⟨3262840062468295720729139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2175226708312197147152759 3262840062468295720729139)
    ·
      refine ⟨4894260093702443581093709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3262840062468295720729139 4894260093702443581093709)
      ·
        refine ⟨1835347535138416342910141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4894260093702443581093709 1835347535138416342910141)
        ·
          refine ⟨688255325676906128591303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1835347535138416342910141 688255325676906128591303)
          ·
            refine ⟨1032382988515359192886955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688255325676906128591303 1032382988515359192886955)
            ·
              refine ⟨1548574482773038789330433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1032382988515359192886955 1548574482773038789330433)
              ·
                refine ⟨1161430862079779091997825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1548574482773038789330433 1161430862079779091997825)
                ·
                  refine ⟨871073146559834318998369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1161430862079779091997825 871073146559834318998369)
                  ·
                    refine ⟨653304859919875739248777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 871073146559834318998369 653304859919875739248777)
                    ·
                      refine ⟨489978644939906804436583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 653304859919875739248777 489978644939906804436583)
                      ·
                        rfl

theorem cell23_954230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_954230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954230 prefixEnd_954230 := by exact prefixLift 954230
  have htrace : WordTrace (prefixWord ++ tailWord_954230) baseStart_954230 baseEnd_954230 := by
    simpa [prefixWord, tailWord_954230, baseEnd_954230] using wordTrace_append hprefix tailTrace_954230
  have hstable : (prefixWord ++ tailWord_954230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954230).length < 2 ^ (prefixWord ++ tailWord_954230).sum := by decide
  have hdescent : baseEnd_954230 < baseStart_954230 := by decide
  rcases family_descends (prefixWord ++ tailWord_954230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954335 : List Nat := [1, 1, 2, 3, 4, 1, 1, 1, 3, 6]
def baseStart_954335 : Nat := 118140960795 + 954335 * 2 ^ 59
def prefixEnd_954335 : Nat := 4983230072969 + 3 ^ 40 * 954335 * 2
def baseEnd_954335 : Nat := 163344186802876297874533

theorem tailTrace_954335 : CollatzResearch.WordTrace tailWord_954335 prefixEnd_954335 163344186802876297874533 := by
  unfold tailWord_954335
  simp only [CollatzResearch.WordTrace]
  refine ⟨34807456997614757287016459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23204971331743171524677639 34807456997614757287016459)
  ·
    refine ⟨52211185496422135930524689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34807456997614757287016459 52211185496422135930524689)
    ·
      refine ⟨39158389122316601947893517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52211185496422135930524689 39158389122316601947893517)
      ·
        refine ⟨14684395920868725730460069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39158389122316601947893517 14684395920868725730460069)
        ·
          refine ⟨2753324235162886074461263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14684395920868725730460069 2753324235162886074461263)
          ·
            refine ⟨4129986352744329111691895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2753324235162886074461263 4129986352744329111691895)
            ·
              refine ⟨6194979529116493667537843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4129986352744329111691895 6194979529116493667537843)
              ·
                refine ⟨9292469293674740501306765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6194979529116493667537843 9292469293674740501306765)
                ·
                  refine ⟨3484675985128027687990037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9292469293674740501306765 3484675985128027687990037)
                  ·
                    refine ⟨163344186802876297874533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3484675985128027687990037 163344186802876297874533)
                    ·
                      rfl

theorem cell23_954335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 6].length) (baseStart_954335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954335 prefixEnd_954335 := by exact prefixLift 954335
  have htrace : WordTrace (prefixWord ++ tailWord_954335) baseStart_954335 baseEnd_954335 := by
    simpa [prefixWord, tailWord_954335, baseEnd_954335] using wordTrace_append hprefix tailTrace_954335
  have hstable : (prefixWord ++ tailWord_954335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954335).length < 2 ^ (prefixWord ++ tailWord_954335).sum := by decide
  have hdescent : baseEnd_954335 < baseStart_954335 := by decide
  rcases family_descends (prefixWord ++ tailWord_954335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954339 : List Nat := [1, 1, 1, 6, 1, 3, 3, 1, 1, 5]
def baseStart_954339 : Nat := 118140960795 + 954339 * 2 ^ 59
def prefixEnd_954339 : Nat := 4983230072969 + 3 ^ 40 * 954339 * 2
def baseEnd_954339 : Nat := 163344871443748959324527

theorem tailTrace_954339 : CollatzResearch.WordTrace tailWord_954339 prefixEnd_954339 163344871443748959324527 := by
  unfold tailWord_954339
  simp only [CollatzResearch.WordTrace]
  refine ⟨34807602889600265970162071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23205068593066843980108047 34807602889600265970162071)
  ·
    refine ⟨52211404334400398955243107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34807602889600265970162071 52211404334400398955243107)
    ·
      refine ⟨78317106501600598432864661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52211404334400398955243107 78317106501600598432864661)
      ·
        refine ⟨3671114367262528051540531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 78317106501600598432864661 3671114367262528051540531)
        ·
          refine ⟨5506671550893792077310797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3671114367262528051540531 5506671550893792077310797)
          ·
            refine ⟨2065001831585172028991549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5506671550893792077310797 2065001831585172028991549)
            ·
              refine ⟨774375686844439510871831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2065001831585172028991549 774375686844439510871831)
              ·
                refine ⟨1161563530266659266307747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 774375686844439510871831 1161563530266659266307747)
                ·
                  refine ⟨1742345295399988899461621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1161563530266659266307747 1742345295399988899461621)
                  ·
                    refine ⟨163344871443748959324527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1742345295399988899461621 163344871443748959324527)
                    ·
                      rfl

theorem cell23_954339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 1, 5].length) (baseStart_954339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954339 prefixEnd_954339 := by exact prefixLift 954339
  have htrace : WordTrace (prefixWord ++ tailWord_954339) baseStart_954339 baseEnd_954339 := by
    simpa [prefixWord, tailWord_954339, baseEnd_954339] using wordTrace_append hprefix tailTrace_954339
  have hstable : (prefixWord ++ tailWord_954339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954339).length < 2 ^ (prefixWord ++ tailWord_954339).sum := by decide
  have hdescent : baseEnd_954339 < baseStart_954339 := by decide
  rcases family_descends (prefixWord ++ tailWord_954339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954352 : List Nat := [2, 1, 1, 1, 3, 2, 3, 4, 2, 4]
def baseStart_954352 : Nat := 118140960795 + 954352 * 2 ^ 59
def prefixEnd_954352 : Nat := 4983230072969 + 3 ^ 40 * 954352 * 2
def baseEnd_954352 : Nat := 163347096526585109037007

theorem tailTrace_954352 : CollatzResearch.WordTrace tailWord_954352 prefixEnd_954352 163347096526585109037007 := by
  unfold tailWord_954352
  simp only [CollatzResearch.WordTrace]
  refine ⟨17404038519276584595192655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23205384692368779460256873 17404038519276584595192655)
  ·
    refine ⟨26106057778914876892788983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17404038519276584595192655 26106057778914876892788983)
    ·
      refine ⟨39159086668372315339183475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26106057778914876892788983 39159086668372315339183475)
      ·
        refine ⟨58738630002558473008775213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39159086668372315339183475 58738630002558473008775213)
        ·
          refine ⟨22026986250959427378290705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58738630002558473008775213 22026986250959427378290705)
          ·
            refine ⟨16520239688219570533718029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22026986250959427378290705 16520239688219570533718029)
            ·
              refine ⟨6195089883082338950144261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16520239688219570533718029 6195089883082338950144261)
              ·
                refine ⟨1161579353077938553152049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6195089883082338950144261 1161579353077938553152049)
                ·
                  refine ⟨871184514808453914864037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1161579353077938553152049 871184514808453914864037)
                  ·
                    refine ⟨163347096526585109037007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 871184514808453914864037 163347096526585109037007)
                    ·
                      rfl

theorem cell23_954352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 2, 4].length) (baseStart_954352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954352 prefixEnd_954352 := by exact prefixLift 954352
  have htrace : WordTrace (prefixWord ++ tailWord_954352) baseStart_954352 baseEnd_954352 := by
    simpa [prefixWord, tailWord_954352, baseEnd_954352] using wordTrace_append hprefix tailTrace_954352
  have hstable : (prefixWord ++ tailWord_954352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954352).length < 2 ^ (prefixWord ++ tailWord_954352).sum := by decide
  have hdescent : baseEnd_954352 < baseStart_954352 := by decide
  rcases family_descends (prefixWord ++ tailWord_954352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954365 : List Nat := [1, 4, 1, 1, 1, 2, 5, 8]
def baseStart_954365 : Nat := 118140960795 + 954365 * 2 ^ 59
def prefixEnd_954365 : Nat := 4983230072969 + 3 ^ 40 * 954365 * 2
def baseEnd_954365 : Nat := 18149924623269028749943

theorem tailTrace_954365 : CollatzResearch.WordTrace tailWord_954365 prefixEnd_954365 18149924623269028749943 := by
  unfold tailWord_954365
  simp only [CollatzResearch.WordTrace]
  refine ⟨34808551187506072410608549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23205700791670714940405699 34808551187506072410608549)
  ·
    refine ⟨6526603347657388576989103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34808551187506072410608549 6526603347657388576989103)
    ·
      refine ⟨9789905021486082865483655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6526603347657388576989103 9789905021486082865483655)
      ·
        refine ⟨14684857532229124298225483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9789905021486082865483655 14684857532229124298225483)
        ·
          refine ⟨22027286298343686447338225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14684857532229124298225483 22027286298343686447338225)
          ·
            refine ⟨16520464723757764835503669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22027286298343686447338225 16520464723757764835503669)
            ·
              refine ⟨1548793567852290453328469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16520464723757764835503669 1548793567852290453328469)
              ·
                refine ⟨18149924623269028749943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1548793567852290453328469 18149924623269028749943)
                ·
                  rfl

theorem cell23_954365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 8].length) (baseStart_954365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954365 prefixEnd_954365 := by exact prefixLift 954365
  have htrace : WordTrace (prefixWord ++ tailWord_954365) baseStart_954365 baseEnd_954365 := by
    simpa [prefixWord, tailWord_954365, baseEnd_954365] using wordTrace_append hprefix tailTrace_954365
  have hstable : (prefixWord ++ tailWord_954365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954365).length < 2 ^ (prefixWord ++ tailWord_954365).sum := by decide
  have hdescent : baseEnd_954365 < baseStart_954365 := by decide
  rcases family_descends (prefixWord ++ tailWord_954365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954382 : List Nat := [4, 1, 1, 2, 2, 1, 5, 7]
def baseStart_954382 : Nat := 118140960795 + 954382 * 2 ^ 59
def prefixEnd_954382 : Nat := 4983230072969 + 3 ^ 40 * 954382 * 2
def baseEnd_954382 : Nat := 18150247925903341101329

theorem tailTrace_954382 : CollatzResearch.WordTrace tailWord_954382 prefixEnd_954382 18150247925903341101329 := by
  unfold tailWord_954382
  simp only [CollatzResearch.WordTrace]
  refine ⟨4351146403555560539247175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23206114152296322875984933 4351146403555560539247175)
  ·
    refine ⟨6526719605333340808870763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4351146403555560539247175 6526719605333340808870763)
    ·
      refine ⟨9790079408000011213306145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6526719605333340808870763 9790079408000011213306145)
      ·
        refine ⟨7342559556000008409979609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9790079408000011213306145 7342559556000008409979609)
        ·
          refine ⟨5506919667000006307484707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7342559556000008409979609 5506919667000006307484707)
          ·
            refine ⟨8260379500500009461227061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5506919667000006307484707 8260379500500009461227061)
            ·
              refine ⟨774410578171875886990037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8260379500500009461227061 774410578171875886990037)
              ·
                refine ⟨18150247925903341101329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 774410578171875886990037 18150247925903341101329)
                ·
                  rfl

theorem cell23_954382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 7].length) (baseStart_954382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954382 prefixEnd_954382 := by exact prefixLift 954382
  have htrace : WordTrace (prefixWord ++ tailWord_954382) baseStart_954382 baseEnd_954382 := by
    simpa [prefixWord, tailWord_954382, baseEnd_954382] using wordTrace_append hprefix tailTrace_954382
  have hstable : (prefixWord ++ tailWord_954382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954382).length < 2 ^ (prefixWord ++ tailWord_954382).sum := by decide
  have hdescent : baseEnd_954382 < baseStart_954382 := by decide
  rcases family_descends (prefixWord ++ tailWord_954382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954392 : List Nat := [2, 1, 2, 3, 2, 1, 1, 4, 1, 3, 3]
def baseStart_954392 : Nat := 118140960795 + 954392 * 2 ^ 59
def prefixEnd_954392 : Nat := 4983230072969 + 3 ^ 40 * 954392 * 2
def baseEnd_954392 : Nat := 490061828805935170610837

theorem tailTrace_954392 : CollatzResearch.WordTrace tailWord_954392 prefixEnd_954392 490061828805935170610837 := by
  unfold tailWord_954392
  simp only [CollatzResearch.WordTrace]
  refine ⟨17404767979204128010920715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23206357305605504014560953 17404767979204128010920715)
  ·
    refine ⟨26107151968806192016381073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17404767979204128010920715 26107151968806192016381073)
    ·
      refine ⟨19580363976604644012285805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26107151968806192016381073 19580363976604644012285805)
      ·
        refine ⟨7342636491226741504607177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19580363976604644012285805 7342636491226741504607177)
        ·
          refine ⟨5506977368420056128455383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7342636491226741504607177 5506977368420056128455383)
          ·
            refine ⟨8260466052630084192683075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5506977368420056128455383 8260466052630084192683075)
            ·
              refine ⟨12390699078945126289024613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8260466052630084192683075 12390699078945126289024613)
              ·
                refine ⟨2323256077302211179192115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12390699078945126289024613 2323256077302211179192115)
                ·
                  refine ⟨3484884115953316768788173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2323256077302211179192115 3484884115953316768788173)
                  ·
                    refine ⟨1306831543482493788295565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3484884115953316768788173 1306831543482493788295565)
                    ·
                      refine ⟨490061828805935170610837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1306831543482493788295565 490061828805935170610837)
                      ·
                        rfl

theorem cell23_954392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_954392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954392 prefixEnd_954392 := by exact prefixLift 954392
  have htrace : WordTrace (prefixWord ++ tailWord_954392) baseStart_954392 baseEnd_954392 := by
    simpa [prefixWord, tailWord_954392, baseEnd_954392] using wordTrace_append hprefix tailTrace_954392
  have hstable : (prefixWord ++ tailWord_954392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954392).length < 2 ^ (prefixWord ++ tailWord_954392).sum := by decide
  have hdescent : baseEnd_954392 < baseStart_954392 := by decide
  rcases family_descends (prefixWord ++ tailWord_954392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954396 : List Nat := [2, 2, 3, 1, 3, 1, 4, 1, 1, 2, 3]
def baseStart_954396 : Nat := 118140960795 + 954396 * 2 ^ 59
def prefixEnd_954396 : Nat := 4983230072969 + 3 ^ 40 * 954396 * 2
def baseEnd_954396 : Nat := 490063882728553154960819

theorem tailTrace_954396 : CollatzResearch.WordTrace tailWord_954396 prefixEnd_954396 490063882728553154960819 := by
  unfold tailWord_954396
  simp only [CollatzResearch.WordTrace]
  refine ⟨17404840925196882352493521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23206454566929176469991361 17404840925196882352493521)
  ·
    refine ⟨13053630693897661764370141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17404840925196882352493521 13053630693897661764370141)
    ·
      refine ⟨4895111510211623161638803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13053630693897661764370141 4895111510211623161638803)
      ·
        refine ⟨7342667265317434742458205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4895111510211623161638803 7342667265317434742458205)
        ·
          refine ⟨2753500224494038028421827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7342667265317434742458205 2753500224494038028421827)
          ·
            refine ⟨4130250336741057042632741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2753500224494038028421827 4130250336741057042632741)
            ·
              refine ⟨774421938138948195493639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4130250336741057042632741 774421938138948195493639)
              ·
                refine ⟨1161632907208422293240459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 774421938138948195493639 1161632907208422293240459)
                ·
                  refine ⟨1742449360812633439860689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1161632907208422293240459 1742449360812633439860689)
                  ·
                    refine ⟨1306837020609475079895517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1742449360812633439860689 1306837020609475079895517)
                    ·
                      refine ⟨490063882728553154960819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1306837020609475079895517 490063882728553154960819)
                      ·
                        rfl

theorem cell23_954396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_954396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954396 prefixEnd_954396 := by exact prefixLift 954396
  have htrace : WordTrace (prefixWord ++ tailWord_954396) baseStart_954396 baseEnd_954396 := by
    simpa [prefixWord, tailWord_954396, baseEnd_954396] using wordTrace_append hprefix tailTrace_954396
  have hstable : (prefixWord ++ tailWord_954396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954396).length < 2 ^ (prefixWord ++ tailWord_954396).sum := by decide
  have hdescent : baseEnd_954396 < baseStart_954396 := by decide
  rcases family_descends (prefixWord ++ tailWord_954396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954415 : List Nat := [1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 4]
def baseStart_954415 : Nat := 118140960795 + 954415 * 2 ^ 59
def prefixEnd_954415 : Nat := 4983230072969 + 3 ^ 40 * 954415 * 2
def baseEnd_954415 : Nat := 490073638860988580623231

theorem tailTrace_954415 : CollatzResearch.WordTrace tailWord_954415 prefixEnd_954415 490073638860988580623231 := by
  unfold tailWord_954415
  simp only [CollatzResearch.WordTrace]
  refine ⟨34810374837324930949928699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23206916558216620633285799 34810374837324930949928699)
  ·
    refine ⟨52215562255987396424893049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34810374837324930949928699 52215562255987396424893049)
    ·
      refine ⟨39161671691990547318669787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52215562255987396424893049 39161671691990547318669787)
      ·
        refine ⟨58742507537985820978004681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39161671691990547318669787 58742507537985820978004681)
        ·
          refine ⟨44056880653489365733503511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58742507537985820978004681 44056880653489365733503511)
          ·
            refine ⟨66085320980234048600255267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44056880653489365733503511 66085320980234048600255267)
            ·
              refine ⟨99127981470351072900382901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66085320980234048600255267 99127981470351072900382901)
              ·
                refine ⟨9293248262845413084410897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99127981470351072900382901 9293248262845413084410897)
                ·
                  refine ⟨6969936197134059813308173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9293248262845413084410897 6969936197134059813308173)
                  ·
                    refine ⟨2613726073925272429990565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6969936197134059813308173 2613726073925272429990565)
                    ·
                      refine ⟨490073638860988580623231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2613726073925272429990565 490073638860988580623231)
                      ·
                        rfl

theorem cell23_954415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 4].length) (baseStart_954415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954415 prefixEnd_954415 := by exact prefixLift 954415
  have htrace : WordTrace (prefixWord ++ tailWord_954415) baseStart_954415 baseEnd_954415 := by
    simpa [prefixWord, tailWord_954415, baseEnd_954415] using wordTrace_append hprefix tailTrace_954415
  have hstable : (prefixWord ++ tailWord_954415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954415).length < 2 ^ (prefixWord ++ tailWord_954415).sum := by decide
  have hdescent : baseEnd_954415 < baseStart_954415 := by decide
  rcases family_descends (prefixWord ++ tailWord_954415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954452 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 1, 6, 3]
def baseStart_954452 : Nat := 118140960795 + 954452 * 2 ^ 59
def prefixEnd_954452 : Nat := 4983230072969 + 3 ^ 40 * 954452 * 2
def baseEnd_954452 : Nat := 490092637645204935860561

theorem tailTrace_954452 : CollatzResearch.WordTrace tailWord_954452 prefixEnd_954452 490092637645204935860561 := by
  unfold tailWord_954452
  simp only [CollatzResearch.WordTrace]
  refine ⟨17405862169095443134512805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23207816225460590846017073 17405862169095443134512805)
  ·
    refine ⟨3263599156705395587721151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17405862169095443134512805 3263599156705395587721151)
    ·
      refine ⟨4895398735058093381581727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3263599156705395587721151 4895398735058093381581727)
      ·
        refine ⟨7343098102587140072372591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4895398735058093381581727 7343098102587140072372591)
        ·
          refine ⟨11014647153880710108558887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7343098102587140072372591 11014647153880710108558887)
          ·
            refine ⟨16521970730821065162838331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11014647153880710108558887 16521970730821065162838331)
            ·
              refine ⟨24782956096231597744257497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16521970730821065162838331 24782956096231597744257497)
              ·
                refine ⟨18587217072173698308193123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24782956096231597744257497 18587217072173698308193123)
                ·
                  refine ⟨27880825608260547462289685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18587217072173698308193123 27880825608260547462289685)
                  ·
                    refine ⟨1306913700387213162294829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27880825608260547462289685 1306913700387213162294829)
                    ·
                      refine ⟨490092637645204935860561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1306913700387213162294829 490092637645204935860561)
                      ·
                        rfl

theorem cell23_954452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_954452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954452 prefixEnd_954452 := by exact prefixLift 954452
  have htrace : WordTrace (prefixWord ++ tailWord_954452) baseStart_954452 baseEnd_954452 := by
    simpa [prefixWord, tailWord_954452, baseEnd_954452] using wordTrace_append hprefix tailTrace_954452
  have hstable : (prefixWord ++ tailWord_954452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954452).length < 2 ^ (prefixWord ++ tailWord_954452).sum := by decide
  have hdescent : baseEnd_954452 < baseStart_954452 := by decide
  rcases family_descends (prefixWord ++ tailWord_954452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954455 : List Nat := [1, 1, 3, 2, 2, 1, 2, 2, 9]
def baseStart_954455 : Nat := 118140960795 + 954455 * 2 ^ 59
def prefixEnd_954455 : Nat := 4983230072969 + 3 ^ 40 * 954455 * 2
def baseEnd_954455 : Nat := 54454908676352047124783

theorem tailTrace_954455 : CollatzResearch.WordTrace tailWord_954455 prefixEnd_954455 54454908676352047124783 := by
  unfold tailWord_954455
  simp only [CollatzResearch.WordTrace]
  refine ⟨34811833757180017781384819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23207889171453345187589879 34811833757180017781384819)
  ·
    refine ⟨52217750635770026672077229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34811833757180017781384819 52217750635770026672077229)
    ·
      refine ⟨19581656488413760002028961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52217750635770026672077229 19581656488413760002028961)
      ·
        refine ⟨14686242366310320001521721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19581656488413760002028961 14686242366310320001521721)
        ·
          refine ⟨11014681774732740001141291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14686242366310320001521721 11014681774732740001141291)
          ·
            refine ⟨16522022662099110001711937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11014681774732740001141291 16522022662099110001711937)
            ·
              refine ⟨12391516996574332501283953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16522022662099110001711937 12391516996574332501283953)
              ·
                refine ⟨9293637747430749375962965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12391516996574332501283953 9293637747430749375962965)
                ·
                  refine ⟨54454908676352047124783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9293637747430749375962965 54454908676352047124783)
                  ·
                    rfl

theorem cell23_954455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 9].length) (baseStart_954455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954455 prefixEnd_954455 := by exact prefixLift 954455
  have htrace : WordTrace (prefixWord ++ tailWord_954455) baseStart_954455 baseEnd_954455 := by
    simpa [prefixWord, tailWord_954455, baseEnd_954455] using wordTrace_append hprefix tailTrace_954455
  have hstable : (prefixWord ++ tailWord_954455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954455).length < 2 ^ (prefixWord ++ tailWord_954455).sum := by decide
  have hdescent : baseEnd_954455 < baseStart_954455 := by decide
  rcases family_descends (prefixWord ++ tailWord_954455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954465 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 1, 1, 9]
def baseStart_954465 : Nat := 118140960795 + 954465 * 2 ^ 59
def prefixEnd_954465 : Nat := 4983230072969 + 3 ^ 40 * 954465 * 2
def baseEnd_954465 : Nat := 490099312893713384998001

theorem tailTrace_954465 : CollatzResearch.WordTrace tailWord_954465 prefixEnd_954465 490099312893713384998001 := by
  unfold tailWord_954465
  simp only [CollatzResearch.WordTrace]
  refine ⟨34812198487143789489248849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23208132324762526326165899 34812198487143789489248849)
  ·
    refine ⟨26109148865357842116936637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34812198487143789489248849 26109148865357842116936637)
    ·
      refine ⟨9790930824509190793851239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26109148865357842116936637 9790930824509190793851239)
      ·
        refine ⟨14686396236763786190776859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9790930824509190793851239 14686396236763786190776859)
        ·
          refine ⟨22029594355145679286165289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14686396236763786190776859 22029594355145679286165289)
          ·
            refine ⟨16522195766359259464623967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22029594355145679286165289 16522195766359259464623967)
            ·
              refine ⟨24783293649538889196935951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16522195766359259464623967 24783293649538889196935951)
              ·
                refine ⟨37174940474308333795403927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24783293649538889196935951 37174940474308333795403927)
                ·
                  refine ⟨55762410711462500693105891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37174940474308333795403927 55762410711462500693105891)
                  ·
                    refine ⟨83643616067193751039658837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55762410711462500693105891 83643616067193751039658837)
                    ·
                      refine ⟨490099312893713384998001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 83643616067193751039658837 490099312893713384998001)
                      ·
                        rfl

theorem cell23_954465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_954465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954465 prefixEnd_954465 := by exact prefixLift 954465
  have htrace : WordTrace (prefixWord ++ tailWord_954465) baseStart_954465 baseEnd_954465 := by
    simpa [prefixWord, tailWord_954465, baseEnd_954465] using wordTrace_append hprefix tailTrace_954465
  have hstable : (prefixWord ++ tailWord_954465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954465).length < 2 ^ (prefixWord ++ tailWord_954465).sum := by decide
  have hdescent : baseEnd_954465 < baseStart_954465 := by decide
  rcases family_descends (prefixWord ++ tailWord_954465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954609 : List Nat := [1, 2, 2, 2, 2, 1, 3, 4, 1, 5]
def baseStart_954609 : Nat := 118140960795 + 954609 * 2 ^ 59
def prefixEnd_954609 : Nat := 4983230072969 + 3 ^ 40 * 954609 * 2
def baseEnd_954609 : Nat := 163391084702653607199113

theorem tailTrace_954609 : CollatzResearch.WordTrace tailWord_954609 prefixEnd_954609 163391084702653607199113 := by
  unfold tailWord_954609
  simp only [CollatzResearch.WordTrace]
  refine ⟨34817450598622102082490881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23211633732414734721660587 34817450598622102082490881)
  ·
    refine ⟨26113087948966576561868161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34817450598622102082490881 26113087948966576561868161)
    ·
      refine ⟨19584815961724932421401121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26113087948966576561868161 19584815961724932421401121)
      ·
        refine ⟨14688611971293699316050841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19584815961724932421401121 14688611971293699316050841)
        ·
          refine ⟨11016458978470274487038131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14688611971293699316050841 11016458978470274487038131)
          ·
            refine ⟨16524688467705411730557197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11016458978470274487038131 16524688467705411730557197)
            ·
              refine ⟨6196758175389529398958949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16524688467705411730557197 6196758175389529398958949)
              ·
                refine ⟨1161892157885536762304803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6196758175389529398958949 1161892157885536762304803)
                ·
                  refine ⟨1742838236828305143457205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1161892157885536762304803 1742838236828305143457205)
                  ·
                    refine ⟨163391084702653607199113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1742838236828305143457205 163391084702653607199113)
                    ·
                      rfl

theorem cell23_954609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 5].length) (baseStart_954609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954609 prefixEnd_954609 := by exact prefixLift 954609
  have htrace : WordTrace (prefixWord ++ tailWord_954609) baseStart_954609 baseEnd_954609 := by
    simpa [prefixWord, tailWord_954609, baseEnd_954609] using wordTrace_append hprefix tailTrace_954609
  have hstable : (prefixWord ++ tailWord_954609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954609).length < 2 ^ (prefixWord ++ tailWord_954609).sum := by decide
  have hdescent : baseEnd_954609 < baseStart_954609 := by decide
  rcases family_descends (prefixWord ++ tailWord_954609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954659 : List Nat := [1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 4]
def baseStart_954659 : Nat := 118140960795 + 954659 * 2 ^ 59
def prefixEnd_954659 : Nat := 4983230072969 + 3 ^ 40 * 954659 * 2
def baseEnd_954659 : Nat := 490198928140685625972109

theorem tailTrace_954659 : CollatzResearch.WordTrace tailWord_954659 prefixEnd_954659 490198928140685625972109 := by
  unfold tailWord_954659
  simp only [CollatzResearch.WordTrace]
  refine ⟨34819274248440960621811031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23212849498960640414540687 34819274248440960621811031)
  ·
    refine ⟨52228911372661440932716547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34819274248440960621811031 52228911372661440932716547)
    ·
      refine ⟨78343367058992161399074821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52228911372661440932716547 78343367058992161399074821)
      ·
        refine ⟨14689381323561030262326529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78343367058992161399074821 14689381323561030262326529)
        ·
          refine ⟨11017035992670772696744897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14689381323561030262326529 11017035992670772696744897)
          ·
            refine ⟨8262776994503079522558673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11017035992670772696744897 8262776994503079522558673)
            ·
              refine ⟨6197082745877309641919005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8262776994503079522558673 6197082745877309641919005)
              ·
                refine ⟨2323906029703991115719627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6197082745877309641919005 2323906029703991115719627)
                ·
                  refine ⟨3485859044555986673579441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2323906029703991115719627 3485859044555986673579441)
                  ·
                    refine ⟨2614394283416990005184581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3485859044555986673579441 2614394283416990005184581)
                    ·
                      refine ⟨490198928140685625972109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2614394283416990005184581 490198928140685625972109)
                      ·
                        rfl

theorem cell23_954659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_954659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954659 prefixEnd_954659 := by exact prefixLift 954659
  have htrace : WordTrace (prefixWord ++ tailWord_954659) baseStart_954659 baseEnd_954659 := by
    simpa [prefixWord, tailWord_954659, baseEnd_954659] using wordTrace_append hprefix tailTrace_954659
  have hstable : (prefixWord ++ tailWord_954659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954659).length < 2 ^ (prefixWord ++ tailWord_954659).sum := by decide
  have hdescent : baseEnd_954659 < baseStart_954659 := by decide
  rcases family_descends (prefixWord ++ tailWord_954659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954676 : List Nat := [2, 5, 1, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_954676 : Nat := 118140960795 + 954676 * 2 ^ 59
def prefixEnd_954676 : Nat := 4983230072969 + 3 ^ 40 * 954676 * 2
def baseEnd_954676 : Nat := 490207657311812059459531

theorem tailTrace_954676 : CollatzResearch.WordTrace tailWord_954676 prefixEnd_954676 490207657311812059459531 := by
  unfold tailWord_954676
  simp only [CollatzResearch.WordTrace]
  refine ⟨17409947144689686262589941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23213262859586248350119921 17409947144689686262589941)
  ·
    refine ⟨1632182544814658087117807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17409947144689686262589941 1632182544814658087117807)
    ·
      refine ⟨2448273817221987130676711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1632182544814658087117807 2448273817221987130676711)
      ·
        refine ⟨3672410725832980696015067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2448273817221987130676711 3672410725832980696015067)
        ·
          refine ⟨5508616088749471044022601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3672410725832980696015067 5508616088749471044022601)
          ·
            refine ⟨4131462066562103283016951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5508616088749471044022601 4131462066562103283016951)
            ·
              refine ⟨6197193099843154924525427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4131462066562103283016951 6197193099843154924525427)
              ·
                refine ⟨9295789649764732386788141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6197193099843154924525427 9295789649764732386788141)
                ·
                  refine ⟨3485921118661774645045553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9295789649764732386788141 3485921118661774645045553)
                  ·
                    refine ⟨2614440838996330983784165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3485921118661774645045553 2614440838996330983784165)
                    ·
                      refine ⟨490207657311812059459531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2614440838996330983784165 490207657311812059459531)
                      ·
                        rfl

theorem cell23_954676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_954676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954676 prefixEnd_954676 := by exact prefixLift 954676
  have htrace : WordTrace (prefixWord ++ tailWord_954676) baseStart_954676 baseEnd_954676 := by
    simpa [prefixWord, tailWord_954676, baseEnd_954676] using wordTrace_append hprefix tailTrace_954676
  have hstable : (prefixWord ++ tailWord_954676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954676).length < 2 ^ (prefixWord ++ tailWord_954676).sum := by decide
  have hdescent : baseEnd_954676 < baseStart_954676 := by decide
  rcases family_descends (prefixWord ++ tailWord_954676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954696 : List Nat := [2, 1, 3, 1, 1, 2, 2, 3, 4, 1, 3]
def baseStart_954696 : Nat := 118140960795 + 954696 * 2 ^ 59
def prefixEnd_954696 : Nat := 4983230072969 + 3 ^ 40 * 954696 * 2
def baseEnd_954696 : Nat := 490217926924901981209439

theorem tailTrace_954696 : CollatzResearch.WordTrace tailWord_954696 prefixEnd_954696 490217926924901981209439 := by
  unfold tailWord_954696
  simp only [CollatzResearch.WordTrace]
  refine ⟨17410311874653457970453971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23213749166204610627271961 17410311874653457970453971)
  ·
    refine ⟨26115467811980186955680957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17410311874653457970453971 26115467811980186955680957)
    ·
      refine ⟨9793300429492570108380359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26115467811980186955680957 9793300429492570108380359)
      ·
        refine ⟨14689950644238855162570539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9793300429492570108380359 14689950644238855162570539)
        ·
          refine ⟨22034925966358282743855809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14689950644238855162570539 22034925966358282743855809)
          ·
            refine ⟨16526194474768712057891857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22034925966358282743855809 16526194474768712057891857)
            ·
              refine ⟨12394645856076534043418893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16526194474768712057891857 12394645856076534043418893)
              ·
                refine ⟨4647992196028700266282085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12394645856076534043418893 4647992196028700266282085)
                ·
                  refine ⟨871498536755381299927891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4647992196028700266282085 871498536755381299927891)
                  ·
                    refine ⟨1307247805133071949891837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 871498536755381299927891 1307247805133071949891837)
                    ·
                      refine ⟨490217926924901981209439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1307247805133071949891837 490217926924901981209439)
                      ·
                        rfl

theorem cell23_954696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 4, 1, 3].length) (baseStart_954696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954696 prefixEnd_954696 := by exact prefixLift 954696
  have htrace : WordTrace (prefixWord ++ tailWord_954696) baseStart_954696 baseEnd_954696 := by
    simpa [prefixWord, tailWord_954696, baseEnd_954696] using wordTrace_append hprefix tailTrace_954696
  have hstable : (prefixWord ++ tailWord_954696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954696).length < 2 ^ (prefixWord ++ tailWord_954696).sum := by decide
  have hdescent : baseEnd_954696 < baseStart_954696 := by decide
  rcases family_descends (prefixWord ++ tailWord_954696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954718 : List Nat := [4, 4, 2, 1, 2, 1, 1, 1, 2, 3, 2]
def baseStart_954718 : Nat := 118140960795 + 954718 * 2 ^ 59
def prefixEnd_954718 : Nat := 4983230072969 + 3 ^ 40 * 954718 * 2
def baseEnd_954718 : Nat := 490229223499300895134339

theorem tailTrace_954718 : CollatzResearch.WordTrace tailWord_954718 prefixEnd_954718 490229223499300895134339 := by
  unfold tailWord_954718
  simp only [CollatzResearch.WordTrace]
  refine ⟨4352678269403401712276101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23214284103484809132139205 4352678269403401712276101)
  ·
    refine ⟨816127175513137821051769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4352678269403401712276101 816127175513137821051769)
    ·
      refine ⟨612095381634853365788827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 816127175513137821051769 612095381634853365788827)
      ·
        refine ⟨918143072452280048683241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 612095381634853365788827 918143072452280048683241)
        ·
          refine ⟨688607304339210036512431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 918143072452280048683241 688607304339210036512431)
          ·
            refine ⟨1032910956508815054768647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688607304339210036512431 1032910956508815054768647)
            ·
              refine ⟨1549366434763222582152971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1032910956508815054768647 1549366434763222582152971)
              ·
                refine ⟨2324049652144833873229457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1549366434763222582152971 2324049652144833873229457)
                ·
                  refine ⟨1743037239108625404922093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2324049652144833873229457 1743037239108625404922093)
                  ·
                    refine ⟨653638964665734526845785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1743037239108625404922093 653638964665734526845785)
                    ·
                      refine ⟨490229223499300895134339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 653638964665734526845785 490229223499300895134339)
                      ·
                        rfl

theorem cell23_954718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_954718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954718 prefixEnd_954718 := by exact prefixLift 954718
  have htrace : WordTrace (prefixWord ++ tailWord_954718) baseStart_954718 baseEnd_954718 := by
    simpa [prefixWord, tailWord_954718, baseEnd_954718] using wordTrace_append hprefix tailTrace_954718
  have hstable : (prefixWord ++ tailWord_954718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954718).length < 2 ^ (prefixWord ++ tailWord_954718).sum := by decide
  have hdescent : baseEnd_954718 < baseStart_954718 := by decide
  rcases family_descends (prefixWord ++ tailWord_954718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954723 : List Nat := [1, 1, 1, 5, 2, 1, 2, 4, 1, 3, 2]
def baseStart_954723 : Nat := 118140960795 + 954723 * 2 ^ 59
def prefixEnd_954723 : Nat := 4983230072969 + 3 ^ 40 * 954723 * 2
def baseEnd_954723 : Nat := 490231790902573375571815

theorem tailTrace_954723 : CollatzResearch.WordTrace tailWord_954723 prefixEnd_954723 490231790902573375571815 := by
  unfold tailWord_954723
  simp only [CollatzResearch.WordTrace]
  refine ⟨34821608520209099552140823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23214405680139399701427215 34821608520209099552140823)
  ·
    refine ⟨52232412780313649328211235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34821608520209099552140823 52232412780313649328211235)
    ·
      refine ⟨78348619170470473992316853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52232412780313649328211235 78348619170470473992316853)
      ·
        refine ⟨7345183047231606936779705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78348619170470473992316853 7345183047231606936779705)
        ·
          refine ⟨5508887285423705202584779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7345183047231606936779705 5508887285423705202584779)
          ·
            refine ⟨8263330928135557803877169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5508887285423705202584779 8263330928135557803877169)
            ·
              refine ⟨6197498196101668352907877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8263330928135557803877169 6197498196101668352907877)
              ·
                refine ⟨1162030911769062816170227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6197498196101668352907877 1162030911769062816170227)
                ·
                  refine ⟨1743046367653594224255341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1162030911769062816170227 1743046367653594224255341)
                  ·
                    refine ⟨653642387870097834095753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1743046367653594224255341 653642387870097834095753)
                    ·
                      refine ⟨490231790902573375571815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 653642387870097834095753 490231790902573375571815)
                      ·
                        rfl

theorem cell23_954723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_954723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954723 prefixEnd_954723 := by exact prefixLift 954723
  have htrace : WordTrace (prefixWord ++ tailWord_954723) baseStart_954723 baseEnd_954723 := by
    simpa [prefixWord, tailWord_954723, baseEnd_954723] using wordTrace_append hprefix tailTrace_954723
  have hstable : (prefixWord ++ tailWord_954723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954723).length < 2 ^ (prefixWord ++ tailWord_954723).sum := by decide
  have hdescent : baseEnd_954723 < baseStart_954723 := by decide
  rcases family_descends (prefixWord ++ tailWord_954723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954739 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 4, 4, 3]
def baseStart_954739 : Nat := 118140960795 + 954739 * 2 ^ 59
def prefixEnd_954739 : Nat := 4983230072969 + 3 ^ 40 * 954739 * 2
def baseEnd_954739 : Nat := 490240006593045312971741

theorem tailTrace_954739 : CollatzResearch.WordTrace tailWord_954739 prefixEnd_954739 490240006593045312971741 := by
  unfold tailWord_954739
  simp only [CollatzResearch.WordTrace]
  refine ⟨34822192088151134284723271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23214794725434089523148847 34822192088151134284723271)
  ·
    refine ⟨52233288132226701427084907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34822192088151134284723271 52233288132226701427084907)
    ·
      refine ⟨78349932198340052140627361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52233288132226701427084907 78349932198340052140627361)
      ·
        refine ⟨58762449148755039105470521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78349932198340052140627361 58762449148755039105470521)
        ·
          refine ⟨44071836861566279329102891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58762449148755039105470521 44071836861566279329102891)
          ·
            refine ⟨66107755292349418993654337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44071836861566279329102891 66107755292349418993654337)
            ·
              refine ⟨49580816469262064245240753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66107755292349418993654337 49580816469262064245240753)
              ·
                refine ⟨37185612351946548183930565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49580816469262064245240753 37185612351946548183930565)
                ·
                  refine ⟨6972302315989977784486981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37185612351946548183930565 6972302315989977784486981)
                  ·
                    refine ⟨1307306684248120834591309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6972302315989977784486981 1307306684248120834591309)
                    ·
                      refine ⟨490240006593045312971741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1307306684248120834591309 490240006593045312971741)
                      ·
                        rfl

theorem cell23_954739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 4, 3].length) (baseStart_954739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954739 prefixEnd_954739 := by exact prefixLift 954739
  have htrace : WordTrace (prefixWord ++ tailWord_954739) baseStart_954739 baseEnd_954739 := by
    simpa [prefixWord, tailWord_954739, baseEnd_954739] using wordTrace_append hprefix tailTrace_954739
  have hstable : (prefixWord ++ tailWord_954739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954739).length < 2 ^ (prefixWord ++ tailWord_954739).sum := by decide
  have hdescent : baseEnd_954739 < baseStart_954739 := by decide
  rcases family_descends (prefixWord ++ tailWord_954739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954776 : List Nat := [2, 1, 2, 5, 1, 1, 2, 2, 7]
def baseStart_954776 : Nat := 118140960795 + 954776 * 2 ^ 59
def prefixEnd_954776 : Nat := 4983230072969 + 3 ^ 40 * 954776 * 2
def baseEnd_954776 : Nat := 54473222819695740912119

theorem tailTrace_954776 : CollatzResearch.WordTrace tailWord_954776 prefixEnd_954776 54473222819695740912119 := by
  unfold tailWord_954776
  simp only [CollatzResearch.WordTrace]
  refine ⟨17411770794508544801910091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23215694392678059735880121 17411770794508544801910091)
  ·
    refine ⟨26117656191762817202865137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17411770794508544801910091 26117656191762817202865137)
    ·
      refine ⟨19588242143822112902148853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26117656191762817202865137 19588242143822112902148853)
      ·
        refine ⟨1836397700983323084576455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19588242143822112902148853 1836397700983323084576455)
        ·
          refine ⟨2754596551474984626864683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1836397700983323084576455 2754596551474984626864683)
          ·
            refine ⟨4131894827212476940297025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2754596551474984626864683 4131894827212476940297025)
            ·
              refine ⟨3098921120409357705222769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4131894827212476940297025 3098921120409357705222769)
              ·
                refine ⟨2324190840307018278917077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3098921120409357705222769 2324190840307018278917077)
                ·
                  refine ⟨54473222819695740912119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2324190840307018278917077 54473222819695740912119)
                  ·
                    rfl

theorem cell23_954776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 7].length) (baseStart_954776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954776 prefixEnd_954776 := by exact prefixLift 954776
  have htrace : WordTrace (prefixWord ++ tailWord_954776) baseStart_954776 baseEnd_954776 := by
    simpa [prefixWord, tailWord_954776, baseEnd_954776] using wordTrace_append hprefix tailTrace_954776
  have hstable : (prefixWord ++ tailWord_954776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954776).length < 2 ^ (prefixWord ++ tailWord_954776).sum := by decide
  have hdescent : baseEnd_954776 < baseStart_954776 := by decide
  rcases family_descends (prefixWord ++ tailWord_954776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954789 : List Nat := [1, 3, 1, 2, 1, 1, 3, 3, 1, 7]
def baseStart_954789 : Nat := 118140960795 + 954789 * 2 ^ 59
def prefixEnd_954789 : Nat := 4983230072969 + 3 ^ 40 * 954789 * 2
def baseEnd_954789 : Nat := 163421893541923372448837

theorem tailTrace_954789 : CollatzResearch.WordTrace tailWord_954789 prefixEnd_954789 163421893541923372448837 := by
  unfold tailWord_954789
  simp only [CollatzResearch.WordTrace]
  refine ⟨34824015737969992824043421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23216010491979995216028947 34824015737969992824043421)
  ·
    refine ⟨13059005901738747309016283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34824015737969992824043421 13059005901738747309016283)
    ·
      refine ⟨19588508852608120963524425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13059005901738747309016283 19588508852608120963524425)
      ·
        refine ⟨14691381639456090722643319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19588508852608120963524425 14691381639456090722643319)
        ·
          refine ⟨22037072459184136083964979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14691381639456090722643319 22037072459184136083964979)
          ·
            refine ⟨33055608688776204125947469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22037072459184136083964979 33055608688776204125947469)
            ·
              refine ⟨12395853258291076547230301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33055608688776204125947469 12395853258291076547230301)
              ·
                refine ⟨4648444971859153705211363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12395853258291076547230301 4648444971859153705211363)
                ·
                  refine ⟨6972667457788730557817045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4648444971859153705211363 6972667457788730557817045)
                  ·
                    refine ⟨163421893541923372448837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6972667457788730557817045 163421893541923372448837)
                    ·
                      rfl

theorem cell23_954789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 7].length) (baseStart_954789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954789 prefixEnd_954789 := by exact prefixLift 954789
  have htrace : WordTrace (prefixWord ++ tailWord_954789) baseStart_954789 baseEnd_954789 := by
    simpa [prefixWord, tailWord_954789, baseEnd_954789] using wordTrace_append hprefix tailTrace_954789
  have hstable : (prefixWord ++ tailWord_954789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954789).length < 2 ^ (prefixWord ++ tailWord_954789).sum := by decide
  have hdescent : baseEnd_954789 < baseStart_954789 := by decide
  rcases family_descends (prefixWord ++ tailWord_954789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954796 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 1, 7, 2]
def baseStart_954796 : Nat := 118140960795 + 954796 * 2 ^ 59
def prefixEnd_954796 : Nat := 4983230072969 + 3 ^ 40 * 954796 * 2
def baseEnd_954796 : Nat := 490269274990351589958979

theorem tailTrace_954796 : CollatzResearch.WordTrace tailWord_954796 prefixEnd_954796 490269274990351589958979 := by
  unfold tailWord_954796
  simp only [CollatzResearch.WordTrace]
  refine ⟨17412135524472316509774121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23216180699296422013032161 17412135524472316509774121)
  ·
    refine ⟨13059101643354237382330591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17412135524472316509774121 13059101643354237382330591)
    ·
      refine ⟨19588652465031356073495887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13059101643354237382330591 19588652465031356073495887)
      ·
        refine ⟨29382978697547034110243831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19588652465031356073495887 29382978697547034110243831)
        ·
          refine ⟨44074468046320551165365747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29382978697547034110243831 44074468046320551165365747)
          ·
            refine ⟨66111702069480826748048621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44074468046320551165365747 66111702069480826748048621)
            ·
              refine ⟨24791888276055310030518233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66111702069480826748048621 24791888276055310030518233)
              ·
                refine ⟨18593916207041482522888675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24791888276055310030518233 18593916207041482522888675)
                ·
                  refine ⟨27890874310562223784333013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18593916207041482522888675 27890874310562223784333013)
                  ·
                    refine ⟨653692366653802119945305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27890874310562223784333013 653692366653802119945305)
                    ·
                      refine ⟨490269274990351589958979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 653692366653802119945305 490269274990351589958979)
                      ·
                        rfl

theorem cell23_954796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 7, 2].length) (baseStart_954796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954796 prefixEnd_954796 := by exact prefixLift 954796
  have htrace : WordTrace (prefixWord ++ tailWord_954796) baseStart_954796 baseEnd_954796 := by
    simpa [prefixWord, tailWord_954796, baseEnd_954796] using wordTrace_append hprefix tailTrace_954796
  have hstable : (prefixWord ++ tailWord_954796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954796).length < 2 ^ (prefixWord ++ tailWord_954796).sum := by decide
  have hdescent : baseEnd_954796 < baseStart_954796 := by decide
  rcases family_descends (prefixWord ++ tailWord_954796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954826 : List Nat := [3, 1, 2, 1, 2, 2, 1, 2, 4, 1, 4]
def baseStart_954826 : Nat := 118140960795 + 954826 * 2 ^ 59
def prefixEnd_954826 : Nat := 4983230072969 + 3 ^ 40 * 954826 * 2
def baseEnd_954826 : Nat := 490284679409986472583841

theorem tailTrace_954826 : CollatzResearch.WordTrace tailWord_954826 prefixEnd_954826 490284679409986472583841 := by
  unfold tailWord_954826
  simp only [CollatzResearch.WordTrace]
  refine ⟨8706341309708987035785083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23216910159223965428760221 8706341309708987035785083)
  ·
    refine ⟨13059511964563480553677625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8706341309708987035785083 13059511964563480553677625)
    ·
      refine ⟨9794633973422610415258219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13059511964563480553677625 9794633973422610415258219)
      ·
        refine ⟨14691950960133915622887329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9794633973422610415258219 14691950960133915622887329)
        ·
          refine ⟨11018963220100436717165497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14691950960133915622887329 11018963220100436717165497)
          ·
            refine ⟨8264222415075327537874123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11018963220100436717165497 8264222415075327537874123)
            ·
              refine ⟨12396333622612991306811185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8264222415075327537874123 12396333622612991306811185)
              ·
                refine ⟨9297250216959743480108389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12396333622612991306811185 9297250216959743480108389)
                ·
                  refine ⟨1743234415679951902520323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9297250216959743480108389 1743234415679951902520323)
                  ·
                    refine ⟨2614851623519927853780485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1743234415679951902520323 2614851623519927853780485)
                    ·
                      refine ⟨490284679409986472583841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2614851623519927853780485 490284679409986472583841)
                      ·
                        rfl

theorem cell23_954826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_954826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954826 prefixEnd_954826 := by exact prefixLift 954826
  have htrace : WordTrace (prefixWord ++ tailWord_954826) baseStart_954826 baseEnd_954826 := by
    simpa [prefixWord, tailWord_954826, baseEnd_954826] using wordTrace_append hprefix tailTrace_954826
  have hstable : (prefixWord ++ tailWord_954826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954826).length < 2 ^ (prefixWord ++ tailWord_954826).sum := by decide
  have hdescent : baseEnd_954826 < baseStart_954826 := by decide
  rcases family_descends (prefixWord ++ tailWord_954826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954839 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 6]
def baseStart_954839 : Nat := 118140960795 + 954839 * 2 ^ 59
def prefixEnd_954839 : Nat := 4983230072969 + 3 ^ 40 * 954839 * 2
def baseEnd_954839 : Nat := 490291354658494921721281

theorem tailTrace_954839 : CollatzResearch.WordTrace tailWord_954839 prefixEnd_954839 490291354658494921721281 := by
  unfold tailWord_954839
  simp only [CollatzResearch.WordTrace]
  refine ⟨34825839387788851363363571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23217226258525900908909047 34825839387788851363363571)
  ·
    refine ⟨52238759081683277045045357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34825839387788851363363571 52238759081683277045045357)
    ·
      refine ⟨19589534655631228891892009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52238759081683277045045357 19589534655631228891892009)
      ·
        refine ⟨14692150991723421668919007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19589534655631228891892009 14692150991723421668919007)
        ·
          refine ⟨22038226487585132503378511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14692150991723421668919007 22038226487585132503378511)
          ·
            refine ⟨33057339731377698755067767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22038226487585132503378511 33057339731377698755067767)
            ·
              refine ⟨49586009597066548132601651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33057339731377698755067767 49586009597066548132601651)
              ·
                refine ⟨74379014395599822198902477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49586009597066548132601651 74379014395599822198902477)
                ·
                  refine ⟨27892130398349933324588429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74379014395599822198902477 27892130398349933324588429)
                  ·
                    refine ⟨10459548899381224996720661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27892130398349933324588429 10459548899381224996720661)
                    ·
                      refine ⟨490291354658494921721281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10459548899381224996720661 490291354658494921721281)
                      ·
                        rfl

theorem cell23_954839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_954839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954839 prefixEnd_954839 := by exact prefixLift 954839
  have htrace : WordTrace (prefixWord ++ tailWord_954839) baseStart_954839 baseEnd_954839 := by
    simpa [prefixWord, tailWord_954839, baseEnd_954839] using wordTrace_append hprefix tailTrace_954839
  have hstable : (prefixWord ++ tailWord_954839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954839).length < 2 ^ (prefixWord ++ tailWord_954839).sum := by decide
  have hdescent : baseEnd_954839 < baseStart_954839 := by decide
  rcases family_descends (prefixWord ++ tailWord_954839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954876 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 2, 5, 3]
def baseStart_954876 : Nat := 118140960795 + 954876 * 2 ^ 59
def prefixEnd_954876 : Nat := 4983230072969 + 3 ^ 40 * 954876 * 2
def baseEnd_954876 : Nat := 490310353442711276958611

theorem tailTrace_954876 : CollatzResearch.WordTrace tailWord_954876 prefixEnd_954876 490310353442711276958611 := by
  unfold tailWord_954876
  simp only [CollatzResearch.WordTrace]
  refine ⟨17413594444327403341230241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23218125925769871121640321 17413594444327403341230241)
  ·
    refine ⟨13060195833245552505922681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17413594444327403341230241 13060195833245552505922681)
    ·
      refine ⟨9795146874934164379442011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13060195833245552505922681 9795146874934164379442011)
      ·
        refine ⟨14692720312401246569163017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9795146874934164379442011 14692720312401246569163017)
        ·
          refine ⟨11019540234300934926872263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14692720312401246569163017 11019540234300934926872263)
          ·
            refine ⟨16529310351451402390308395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11019540234300934926872263 16529310351451402390308395)
            ·
              refine ⟨24793965527177103585462593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16529310351451402390308395 24793965527177103585462593)
              ·
                refine ⟨18595474145382827689096945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24793965527177103585462593 18595474145382827689096945)
                ·
                  refine ⟨13946605609037120766822709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18595474145382827689096945 13946605609037120766822709)
                  ·
                    refine ⟨1307494275847230071889629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13946605609037120766822709 1307494275847230071889629)
                    ·
                      refine ⟨490310353442711276958611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1307494275847230071889629 490310353442711276958611)
                      ·
                        rfl

theorem cell23_954876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_954876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954876 prefixEnd_954876 := by exact prefixLift 954876
  have htrace : WordTrace (prefixWord ++ tailWord_954876) baseStart_954876 baseEnd_954876 := by
    simpa [prefixWord, tailWord_954876, baseEnd_954876] using wordTrace_append hprefix tailTrace_954876
  have hstable : (prefixWord ++ tailWord_954876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954876).length < 2 ^ (prefixWord ++ tailWord_954876).sum := by decide
  have hdescent : baseEnd_954876 < baseStart_954876 := by decide
  rcases family_descends (prefixWord ++ tailWord_954876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954913 : List Nat := [1, 2, 3, 2, 2, 1, 3, 3, 1, 5]
def baseStart_954913 : Nat := 118140960795 + 954913 * 2 ^ 59
def prefixEnd_954913 : Nat := 4983230072969 + 3 ^ 40 * 954913 * 2
def baseEnd_954913 : Nat := 163443117408975877398647

theorem tailTrace_954913 : CollatzResearch.WordTrace tailWord_954913 prefixEnd_954913 163443117408975877398647 := by
  unfold tailWord_954913
  simp only [CollatzResearch.WordTrace]
  refine ⟨34828538389520762001557393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23219025593013841334371595 34828538389520762001557393)
  ·
    refine ⟨26121403792140571501168045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34828538389520762001557393 26121403792140571501168045)
    ·
      refine ⟨9795526422052714312938017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26121403792140571501168045 9795526422052714312938017)
      ·
        refine ⟨7346644816539535734703513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9795526422052714312938017 7346644816539535734703513)
        ·
          refine ⟨5509983612404651801027635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7346644816539535734703513 5509983612404651801027635)
          ·
            refine ⟨8264975418606977701541453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5509983612404651801027635 8264975418606977701541453)
            ·
              refine ⟨3099365781977616638078045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8264975418606977701541453 3099365781977616638078045)
              ·
                refine ⟨1162262168241606239279267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3099365781977616638078045 1162262168241606239279267)
                ·
                  refine ⟨1743393252362409358918901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1162262168241606239279267 1743393252362409358918901)
                  ·
                    refine ⟨163443117408975877398647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1743393252362409358918901 163443117408975877398647)
                    ·
                      rfl

theorem cell23_954913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_954913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954913 prefixEnd_954913 := by exact prefixLift 954913
  have htrace : WordTrace (prefixWord ++ tailWord_954913) baseStart_954913 baseEnd_954913 := by
    simpa [prefixWord, tailWord_954913, baseEnd_954913] using wordTrace_append hprefix tailTrace_954913
  have hstable : (prefixWord ++ tailWord_954913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954913).length < 2 ^ (prefixWord ++ tailWord_954913).sum := by decide
  have hdescent : baseEnd_954913 < baseStart_954913 := by decide
  rcases family_descends (prefixWord ++ tailWord_954913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954956 : List Nat := [2, 2, 1, 3, 1, 2, 3, 9]
def baseStart_954956 : Nat := 118140960795 + 954956 * 2 ^ 59
def prefixEnd_954956 : Nat := 4983230072969 + 3 ^ 40 * 954956 * 2
def baseEnd_954956 : Nat := 18161164144261887554009

theorem tailTrace_954956 : CollatzResearch.WordTrace tailWord_954956 prefixEnd_954956 18161164144261887554009 := by
  unfold tailWord_954956
  simp only [CollatzResearch.WordTrace]
  refine ⟨17415053364182490172686361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23220071152243320230248481 17415053364182490172686361)
  ·
    refine ⟨13061290023136867629514771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17415053364182490172686361 13061290023136867629514771)
    ·
      refine ⟨19591935034705301444272157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13061290023136867629514771 19591935034705301444272157)
      ·
        refine ⟨7346975638014488041602059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19591935034705301444272157 7346975638014488041602059)
        ·
          refine ⟨11020463457021732062403089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7346975638014488041602059 11020463457021732062403089)
          ·
            refine ⟨8265347592766299046802317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11020463457021732062403089 8265347592766299046802317)
            ·
              refine ⟨3099505347287362142550869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8265347592766299046802317 3099505347287362142550869)
              ·
                refine ⟨18161164144261887554009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3099505347287362142550869 18161164144261887554009)
                ·
                  rfl

theorem cell23_954956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 9].length) (baseStart_954956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954956 prefixEnd_954956 := by exact prefixLift 954956
  have htrace : WordTrace (prefixWord ++ tailWord_954956) baseStart_954956 baseEnd_954956 := by
    simpa [prefixWord, tailWord_954956, baseEnd_954956] using wordTrace_append hprefix tailTrace_954956
  have hstable : (prefixWord ++ tailWord_954956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954956).length < 2 ^ (prefixWord ++ tailWord_954956).sum := by decide
  have hdescent : baseEnd_954956 < baseStart_954956 := by decide
  rcases family_descends (prefixWord ++ tailWord_954956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954978 : List Nat := [3, 3, 2, 3, 1, 1, 3, 2, 1, 1, 3]
def baseStart_954978 : Nat := 118140960795 + 954978 * 2 ^ 59
def prefixEnd_954978 : Nat := 4983230072969 + 3 ^ 40 * 954978 * 2
def baseEnd_954978 : Nat := 490362728469469877883143

theorem tailTrace_954978 : CollatzResearch.WordTrace tailWord_954978 prefixEnd_954978 490362728469469877883143 := by
  unfold tailWord_954978
  simp only [CollatzResearch.WordTrace]
  refine ⟨8707727283571319525668397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23220606089523518735115725 8707727283571319525668397)
  ·
    refine ⟨3265397731339244822125649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8707727283571319525668397 3265397731339244822125649)
    ·
      refine ⟨2449048298504433616594237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3265397731339244822125649 2449048298504433616594237)
      ·
        refine ⟨918393111939162606222839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2449048298504433616594237 918393111939162606222839)
        ·
          refine ⟨1377589667908743909334259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 918393111939162606222839 1377589667908743909334259)
          ·
            refine ⟨2066384501863115864001389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1377589667908743909334259 2066384501863115864001389)
            ·
              refine ⟨774894188198668449000521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2066384501863115864001389 774894188198668449000521)
              ·
                refine ⟨581170641149001336750391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 774894188198668449000521 581170641149001336750391)
                ·
                  refine ⟨871755961723502005125587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 581170641149001336750391 871755961723502005125587)
                  ·
                    refine ⟨1307633942585253007688381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 871755961723502005125587 1307633942585253007688381)
                    ·
                      refine ⟨490362728469469877883143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1307633942585253007688381 490362728469469877883143)
                      ·
                        rfl

theorem cell23_954978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_954978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954978 prefixEnd_954978 := by exact prefixLift 954978
  have htrace : WordTrace (prefixWord ++ tailWord_954978) baseStart_954978 baseEnd_954978 := by
    simpa [prefixWord, tailWord_954978, baseEnd_954978] using wordTrace_append hprefix tailTrace_954978
  have hstable : (prefixWord ++ tailWord_954978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954978).length < 2 ^ (prefixWord ++ tailWord_954978).sum := by decide
  have hdescent : baseEnd_954978 < baseStart_954978 := by decide
  rcases family_descends (prefixWord ++ tailWord_954978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954993 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 1, 9, 2]
def baseStart_954993 : Nat := 118140960795 + 954993 * 2 ^ 59
def prefixEnd_954993 : Nat := 4983230072969 + 3 ^ 40 * 954993 * 2
def baseEnd_954993 : Nat := 490370430679287319195573

theorem tailTrace_954993 : CollatzResearch.WordTrace tailWord_954993 prefixEnd_954993 490370430679287319195573 := by
  unfold tailWord_954993
  simp only [CollatzResearch.WordTrace]
  refine ⟨34831456229230935664469633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23220970819487290442979755 34831456229230935664469633)
  ·
    refine ⟨26123592171923201748352225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34831456229230935664469633 26123592171923201748352225)
    ·
      refine ⟨19592694128942401311264169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26123592171923201748352225 19592694128942401311264169)
      ·
        refine ⟨14694520596706800983448127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19592694128942401311264169 14694520596706800983448127)
        ·
          refine ⟨22041780895060201475172191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14694520596706800983448127 22041780895060201475172191)
          ·
            refine ⟨33062671342590302212758287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22041780895060201475172191 33062671342590302212758287)
            ·
              refine ⟨49594007013885453319137431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33062671342590302212758287 49594007013885453319137431)
              ·
                refine ⟨74391010520828179978706147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49594007013885453319137431 74391010520828179978706147)
                ·
                  refine ⟨111586515781242269968059221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74391010520828179978706147 111586515781242269968059221)
                  ·
                    refine ⟨653827240905716425594097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 111586515781242269968059221 653827240905716425594097)
                    ·
                      refine ⟨490370430679287319195573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 653827240905716425594097 490370430679287319195573)
                      ·
                        rfl

theorem cell23_954993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 9, 2].length) (baseStart_954993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954993 prefixEnd_954993 := by exact prefixLift 954993
  have htrace : WordTrace (prefixWord ++ tailWord_954993) baseStart_954993 baseEnd_954993 := by
    simpa [prefixWord, tailWord_954993, baseEnd_954993] using wordTrace_append hprefix tailTrace_954993
  have hstable : (prefixWord ++ tailWord_954993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954993).length < 2 ^ (prefixWord ++ tailWord_954993).sum := by decide
  have hdescent : baseEnd_954993 < baseStart_954993 := by decide
  rcases family_descends (prefixWord ++ tailWord_954993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_954994 : List Nat := [3, 2, 1, 2, 4, 2, 2, 1, 2, 4]
def baseStart_954994 : Nat := 118140960795 + 954994 * 2 ^ 59
def prefixEnd_954994 : Nat := 4983230072969 + 3 ^ 40 * 954994 * 2
def baseEnd_954994 : Nat := 163456981386647271761023

theorem tailTrace_954994 : CollatzResearch.WordTrace tailWord_954994 prefixEnd_954994 163456981386647271761023 := by
  unfold tailWord_954994
  simp only [CollatzResearch.WordTrace]
  refine ⟨8707873175556828208814009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23220995134818208556837357 8707873175556828208814009)
  ·
    refine ⟨6530904881667621156610507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8707873175556828208814009 6530904881667621156610507)
    ·
      refine ⟨9796357322501431734915761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6530904881667621156610507 9796357322501431734915761)
      ·
        refine ⟨7347267991876073801186821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9796357322501431734915761 7347267991876073801186821)
        ·
          refine ⟨1377612748476763837722529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7347267991876073801186821 1377612748476763837722529)
          ·
            refine ⟨1033209561357572878291897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1377612748476763837722529 1033209561357572878291897)
            ·
              refine ⟨774907171018179658718923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1033209561357572878291897 774907171018179658718923)
              ·
                refine ⟨1162360756527269488078385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 774907171018179658718923 1162360756527269488078385)
                ·
                  refine ⟨871770567395452116058789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1162360756527269488078385 871770567395452116058789)
                  ·
                    refine ⟨163456981386647271761023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 871770567395452116058789 163456981386647271761023)
                    ·
                      rfl

theorem cell23_954994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 2, 4].length) (baseStart_954994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_954994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_954994 prefixEnd_954994 := by exact prefixLift 954994
  have htrace : WordTrace (prefixWord ++ tailWord_954994) baseStart_954994 baseEnd_954994 := by
    simpa [prefixWord, tailWord_954994, baseEnd_954994] using wordTrace_append hprefix tailTrace_954994
  have hstable : (prefixWord ++ tailWord_954994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_954994).length < 2 ^ (prefixWord ++ tailWord_954994).sum := by decide
  have hdescent : baseEnd_954994 < baseStart_954994 := by decide
  rcases family_descends (prefixWord ++ tailWord_954994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955000 : List Nat := [2, 1, 2, 1, 1, 1, 2, 7, 2, 1, 3]
def baseStart_955000 : Nat := 118140960795 + 955000 * 2 ^ 59
def prefixEnd_955000 : Nat := 4983230072969 + 3 ^ 40 * 955000 * 2
def baseEnd_955000 : Nat := 490374025043868791808041

theorem tailTrace_955000 : CollatzResearch.WordTrace tailWord_955000 prefixEnd_955000 490374025043868791808041 := by
  unfold tailWord_955000
  simp only [CollatzResearch.WordTrace]
  refine ⟨17415855770102787929987227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23221141026803717239982969 17415855770102787929987227)
  ·
    refine ⟨26123783655154181894980841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17415855770102787929987227 26123783655154181894980841)
    ·
      refine ⟨19592837741365636421235631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26123783655154181894980841 19592837741365636421235631)
      ·
        refine ⟨29389256612048454631853447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19592837741365636421235631 29389256612048454631853447)
        ·
          refine ⟨44083884918072681947780171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29389256612048454631853447 44083884918072681947780171)
          ·
            refine ⟨66125827377109022921670257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44083884918072681947780171 66125827377109022921670257)
            ·
              refine ⟨49594370532831767191252693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66125827377109022921670257 49594370532831767191252693)
              ·
                refine ⟨1162368059363244543544985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 49594370532831767191252693 1162368059363244543544985)
                ·
                  refine ⟨871776044522433407658739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1162368059363244543544985 871776044522433407658739)
                  ·
                    refine ⟨1307664066783650111488109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 871776044522433407658739 1307664066783650111488109)
                    ·
                      refine ⟨490374025043868791808041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1307664066783650111488109 490374025043868791808041)
                      ·
                        rfl

theorem cell23_955000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 2, 1, 3].length) (baseStart_955000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955000 prefixEnd_955000 := by exact prefixLift 955000
  have htrace : WordTrace (prefixWord ++ tailWord_955000) baseStart_955000 baseEnd_955000 := by
    simpa [prefixWord, tailWord_955000, baseEnd_955000] using wordTrace_append hprefix tailTrace_955000
  have hstable : (prefixWord ++ tailWord_955000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955000).length < 2 ^ (prefixWord ++ tailWord_955000).sum := by decide
  have hdescent : baseEnd_955000 < baseStart_955000 := by decide
  rcases family_descends (prefixWord ++ tailWord_955000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955078 : List Nat := [6, 1, 2, 1, 2, 1, 1, 3, 1, 3, 2]
def baseStart_955078 : Nat := 118140960795 + 955078 * 2 ^ 59
def prefixEnd_955078 : Nat := 4983230072969 + 3 ^ 40 * 955078 * 2
def baseEnd_955078 : Nat := 490414076534919486632683

theorem tailTrace_955078 : CollatzResearch.WordTrace tailWord_955078 prefixEnd_955078 490414076534919486632683 := by
  unfold tailWord_955078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1088579888560093599416059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 23223037622615330120875925 1088579888560093599416059)
  ·
    refine ⟨1632869832840140399124089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1088579888560093599416059 1632869832840140399124089)
    ·
      refine ⟨1224652374630105299343067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1632869832840140399124089 1224652374630105299343067)
      ·
        refine ⟨1836978561945157949014601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1224652374630105299343067 1836978561945157949014601)
        ·
          refine ⟨1377733921458868461760951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1836978561945157949014601 1377733921458868461760951)
          ·
            refine ⟨2066600882188302692641427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1377733921458868461760951 2066600882188302692641427)
            ·
              refine ⟨3099901323282454038962141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2066600882188302692641427 3099901323282454038962141)
              ·
                refine ⟨1162462996230920264610803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3099901323282454038962141 1162462996230920264610803)
                ·
                  refine ⟨1743694494346380396916205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1162462996230920264610803 1743694494346380396916205)
                  ·
                    refine ⟨653885435379892648843577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1743694494346380396916205 653885435379892648843577)
                    ·
                      refine ⟨490414076534919486632683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 653885435379892648843577 490414076534919486632683)
                      ·
                        rfl

theorem cell23_955078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_955078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955078 prefixEnd_955078 := by exact prefixLift 955078
  have htrace : WordTrace (prefixWord ++ tailWord_955078) baseStart_955078 baseEnd_955078 := by
    simpa [prefixWord, tailWord_955078, baseEnd_955078] using wordTrace_append hprefix tailTrace_955078
  have hstable : (prefixWord ++ tailWord_955078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955078).length < 2 ^ (prefixWord ++ tailWord_955078).sum := by decide
  have hdescent : baseEnd_955078 < baseStart_955078 := by decide
  rcases family_descends (prefixWord ++ tailWord_955078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955080 : List Nat := [2, 1, 3, 1, 2, 3, 1, 5, 5]
def baseStart_955080 : Nat := 118140960795 + 955080 * 2 ^ 59
def prefixEnd_955080 : Nat := 4983230072969 + 3 ^ 40 * 955080 * 2
def baseEnd_955080 : Nat := 54490567055136497645297

theorem tailTrace_955080 : CollatzResearch.WordTrace tailWord_955080 prefixEnd_955080 54490567055136497645297 := by
  unfold tailWord_955080
  simp only [CollatzResearch.WordTrace]
  refine ⟨17417314689957874761443347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23223086253277166348591129 17417314689957874761443347)
  ·
    refine ⟨26125972034936812142165021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17417314689957874761443347 26125972034936812142165021)
    ·
      refine ⟨9797239513101304553311883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26125972034936812142165021 9797239513101304553311883)
      ·
        refine ⟨14695859269651956829967825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9797239513101304553311883 14695859269651956829967825)
        ·
          refine ⟨11021894452238967622475869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14695859269651956829967825 11021894452238967622475869)
          ·
            refine ⟨4133210419589612858428451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11021894452238967622475869 4133210419589612858428451)
            ·
              refine ⟨6199815629384419287642677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4133210419589612858428451 6199815629384419287642677)
              ·
                refine ⟨581232715254789308216501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6199815629384419287642677 581232715254789308216501)
                ·
                  refine ⟨54490567055136497645297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 581232715254789308216501 54490567055136497645297)
                  ·
                    rfl

theorem cell23_955080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 5, 5].length) (baseStart_955080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955080 prefixEnd_955080 := by exact prefixLift 955080
  have htrace : WordTrace (prefixWord ++ tailWord_955080) baseStart_955080 baseEnd_955080 := by
    simpa [prefixWord, tailWord_955080, baseEnd_955080] using wordTrace_append hprefix tailTrace_955080
  have hstable : (prefixWord ++ tailWord_955080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955080).length < 2 ^ (prefixWord ++ tailWord_955080).sum := by decide
  have hdescent : baseEnd_955080 < baseStart_955080 := by decide
  rcases family_descends (prefixWord ++ tailWord_955080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955113 : List Nat := [1, 2, 1, 1, 1, 2, 5, 2, 1, 3, 4]
def baseStart_955113 : Nat := 118140960795 + 955113 * 2 ^ 59
def prefixEnd_955113 : Nat := 4983230072969 + 3 ^ 40 * 955113 * 2
def baseEnd_955113 : Nat := 490432048357826849695021

theorem tailTrace_955113 : CollatzResearch.WordTrace tailWord_955113 prefixEnd_955113 490432048357826849695021 := by
  unfold tailWord_955113
  simp only [CollatzResearch.WordTrace]
  refine ⟨34835832988796196158837993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23223888659197464105891995 34835832988796196158837993)
  ·
    refine ⟨26126874741597147119128495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34835832988796196158837993 26126874741597147119128495)
    ·
      refine ⟨39190312112395720678692743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26126874741597147119128495 39190312112395720678692743)
      ·
        refine ⟨58785468168593581018039115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39190312112395720678692743 58785468168593581018039115)
        ·
          refine ⟨88178202252890371527058673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58785468168593581018039115 88178202252890371527058673)
          ·
            refine ⟨66133651689667778645294005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88178202252890371527058673 66133651689667778645294005)
            ·
              refine ⟨6200029845906354247996313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66133651689667778645294005 6200029845906354247996313)
              ·
                refine ⟨4650022384429765685997235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6200029845906354247996313 4650022384429765685997235)
                ·
                  refine ⟨6975033576644648528995853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4650022384429765685997235 6975033576644648528995853)
                  ·
                    refine ⟨2615637591241743198373445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6975033576644648528995853 2615637591241743198373445)
                    ·
                      refine ⟨490432048357826849695021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2615637591241743198373445 490432048357826849695021)
                      ·
                        rfl

theorem cell23_955113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 3, 4].length) (baseStart_955113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955113 prefixEnd_955113 := by exact prefixLift 955113
  have htrace : WordTrace (prefixWord ++ tailWord_955113) baseStart_955113 baseEnd_955113 := by
    simpa [prefixWord, tailWord_955113, baseEnd_955113] using wordTrace_append hprefix tailTrace_955113
  have hstable : (prefixWord ++ tailWord_955113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955113).length < 2 ^ (prefixWord ++ tailWord_955113).sum := by decide
  have hdescent : baseEnd_955113 < baseStart_955113 := by decide
  rcases family_descends (prefixWord ++ tailWord_955113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955130 : List Nat := [3, 1, 1, 1, 1, 3, 2, 2, 1, 6, 2]
def baseStart_955130 : Nat := 118140960795 + 955130 * 2 ^ 59
def prefixEnd_955130 : Nat := 4983230072969 + 3 ^ 40 * 955130 * 2
def baseEnd_955130 : Nat := 490440777528953283182443

theorem tailTrace_955130 : CollatzResearch.WordTrace tailWord_955130 prefixEnd_955130 490440777528953283182443 := by
  unfold tailWord_955130
  simp only [CollatzResearch.WordTrace]
  refine ⟨8709113257433652015551711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23224302019823072041471229 8709113257433652015551711)
  ·
    refine ⟨13063669886150478023327567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8709113257433652015551711 13063669886150478023327567)
    ·
      refine ⟨19595504829225717034991351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13063669886150478023327567 19595504829225717034991351)
      ·
        refine ⟨29393257243838575552487027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19595504829225717034991351 29393257243838575552487027)
        ·
          refine ⟨44089885865757863328730541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29393257243838575552487027 44089885865757863328730541)
          ·
            refine ⟨16533707199659198748273953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44089885865757863328730541 16533707199659198748273953)
            ·
              refine ⟨12400280399744399061205465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16533707199659198748273953 12400280399744399061205465)
              ·
                refine ⟨9300210299808299295904099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12400280399744399061205465 9300210299808299295904099)
                ·
                  refine ⟨13950315449712448943856149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9300210299808299295904099 13950315449712448943856149)
                  ·
                    refine ⟨653921036705271044243257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13950315449712448943856149 653921036705271044243257)
                    ·
                      refine ⟨490440777528953283182443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 653921036705271044243257 490440777528953283182443)
                      ·
                        rfl

theorem cell23_955130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 1, 6, 2].length) (baseStart_955130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955130 prefixEnd_955130 := by exact prefixLift 955130
  have htrace : WordTrace (prefixWord ++ tailWord_955130) baseStart_955130 baseEnd_955130 := by
    simpa [prefixWord, tailWord_955130, baseEnd_955130] using wordTrace_append hprefix tailTrace_955130
  have hstable : (prefixWord ++ tailWord_955130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955130).length < 2 ^ (prefixWord ++ tailWord_955130).sum := by decide
  have hdescent : baseEnd_955130 < baseStart_955130 := by decide
  rcases family_descends (prefixWord ++ tailWord_955130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955153 : List Nat := [1, 2, 2, 1, 1, 3, 4, 1, 8]
def baseStart_955153 : Nat := 118140960795 + 955153 * 2 ^ 59
def prefixEnd_955153 : Nat := 4983230072969 + 3 ^ 40 * 955153 * 2
def baseEnd_955153 : Nat := 54494731953778521466093

theorem tailTrace_955153 : CollatzResearch.WordTrace tailWord_955153 prefixEnd_955153 54494731953778521466093 := by
  unfold tailWord_955153
  simp only [CollatzResearch.WordTrace]
  refine ⟨34837291908651282990294113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23224861272434188660196075 34837291908651282990294113)
  ·
    refine ⟨26127968931488462242720585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34837291908651282990294113 26127968931488462242720585)
    ·
      refine ⟨19595976698616346682040439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26127968931488462242720585 19595976698616346682040439)
      ·
        refine ⟨29393965047924520023060659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19595976698616346682040439 29393965047924520023060659)
        ·
          refine ⟨44090947571886780034590989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29393965047924520023060659 44090947571886780034590989)
          ·
            refine ⟨16534105339457542512971621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44090947571886780034590989 16534105339457542512971621)
            ·
              refine ⟨3100144751148289221182179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16534105339457542512971621 3100144751148289221182179)
              ·
                refine ⟨4650217126722433831773269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3100144751148289221182179 4650217126722433831773269)
                ·
                  refine ⟨54494731953778521466093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4650217126722433831773269 54494731953778521466093)
                  ·
                    rfl

theorem cell23_955153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 8].length) (baseStart_955153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955153 prefixEnd_955153 := by exact prefixLift 955153
  have htrace : WordTrace (prefixWord ++ tailWord_955153) baseStart_955153 baseEnd_955153 := by
    simpa [prefixWord, tailWord_955153, baseEnd_955153] using wordTrace_append hprefix tailTrace_955153
  have hstable : (prefixWord ++ tailWord_955153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955153).length < 2 ^ (prefixWord ++ tailWord_955153).sum := by decide
  have hdescent : baseEnd_955153 < baseStart_955153 := by decide
  rcases family_descends (prefixWord ++ tailWord_955153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955181 : List Nat := [1, 5, 3, 2, 1, 1, 2, 1, 2, 1, 4]
def baseStart_955181 : Nat := 118140960795 + 955181 * 2 ^ 59
def prefixEnd_955181 : Nat := 4983230072969 + 3 ^ 40 * 955181 * 2
def baseEnd_955181 : Nat := 490466965042332583644709

theorem tailTrace_955181 : CollatzResearch.WordTrace tailWord_955181 prefixEnd_955181 490466965042332583644709 := by
  unfold tailWord_955181
  simp only [CollatzResearch.WordTrace]
  refine ⟨34838313152549843772313397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23225542101699895848208931 34838313152549843772313397)
  ·
    refine ⟨3266091858051547853654381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34838313152549843772313397 3266091858051547853654381)
    ·
      refine ⟨1224784446769330445120393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3266091858051547853654381 1224784446769330445120393)
      ·
        refine ⟨918588335076997833840295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1224784446769330445120393 918588335076997833840295)
        ·
          refine ⟨1377882502615496750760443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 918588335076997833840295 1377882502615496750760443)
          ·
            refine ⟨2066823753923245126140665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1377882502615496750760443 2066823753923245126140665)
            ·
              refine ⟨1550117815442433844605499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2066823753923245126140665 1550117815442433844605499)
              ·
                refine ⟨2325176723163650766908249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1550117815442433844605499 2325176723163650766908249)
                ·
                  refine ⟨1743882542372738075181187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2325176723163650766908249 1743882542372738075181187)
                  ·
                    refine ⟨2615823813559107112771781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1743882542372738075181187 2615823813559107112771781)
                    ·
                      refine ⟨490466965042332583644709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2615823813559107112771781 490466965042332583644709)
                      ·
                        rfl

theorem cell23_955181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_955181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955181 prefixEnd_955181 := by exact prefixLift 955181
  have htrace : WordTrace (prefixWord ++ tailWord_955181) baseStart_955181 baseEnd_955181 := by
    simpa [prefixWord, tailWord_955181, baseEnd_955181] using wordTrace_append hprefix tailTrace_955181
  have hstable : (prefixWord ++ tailWord_955181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955181).length < 2 ^ (prefixWord ++ tailWord_955181).sum := by decide
  have hdescent : baseEnd_955181 < baseStart_955181 := by decide
  rcases family_descends (prefixWord ++ tailWord_955181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955200 : List Nat := [2, 1, 1, 2, 2, 1, 1, 7, 1, 5]
def baseStart_955200 : Nat := 118140960795 + 955200 * 2 ^ 59
def prefixEnd_955200 : Nat := 4983230072969 + 3 ^ 40 * 955200 * 2
def baseEnd_955200 : Nat := 163492240391589336435707

theorem tailTrace_955200 : CollatzResearch.WordTrace tailWord_955200 prefixEnd_955200 163492240391589336435707 := by
  unfold tailWord_955200
  simp only [CollatzResearch.WordTrace]
  refine ⟨17419503069740505008627527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23226004092987340011503369 17419503069740505008627527)
  ·
    refine ⟨26129254604610757512941291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17419503069740505008627527 26129254604610757512941291)
    ·
      refine ⟨39193881906916136269411937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26129254604610757512941291 39193881906916136269411937)
      ·
        refine ⟨29395411430187102202058953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39193881906916136269411937 29395411430187102202058953)
        ·
          refine ⟨22046558572640326651544215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29395411430187102202058953 22046558572640326651544215)
          ·
            refine ⟨33069837858960489977316323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22046558572640326651544215 33069837858960489977316323)
            ·
              refine ⟨49604756788440734965974485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33069837858960489977316323 49604756788440734965974485)
              ·
                refine ⟨1162611487229079725765027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 49604756788440734965974485 1162611487229079725765027)
                ·
                  refine ⟨1743917230843619588647541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1162611487229079725765027 1743917230843619588647541)
                  ·
                    refine ⟨163492240391589336435707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1743917230843619588647541 163492240391589336435707)
                    ·
                      rfl

theorem cell23_955200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 1, 5].length) (baseStart_955200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955200 prefixEnd_955200 := by exact prefixLift 955200
  have htrace : WordTrace (prefixWord ++ tailWord_955200) baseStart_955200 baseEnd_955200 := by
    simpa [prefixWord, tailWord_955200, baseEnd_955200] using wordTrace_append hprefix tailTrace_955200
  have hstable : (prefixWord ++ tailWord_955200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955200).length < 2 ^ (prefixWord ++ tailWord_955200).sum := by decide
  have hdescent : baseEnd_955200 < baseStart_955200 := by decide
  rcases family_descends (prefixWord ++ tailWord_955200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955243 : List Nat := [1, 1, 1, 1, 2, 2, 4, 11]
def baseStart_955243 : Nat := 118140960795 + 955243 * 2 ^ 59
def prefixEnd_955243 : Nat := 4983230072969 + 3 ^ 40 * 955243 * 2
def baseEnd_955243 : Nat := 18166622253441160780349

theorem tailTrace_955243 : CollatzResearch.WordTrace tailWord_955243 prefixEnd_955243 18166622253441160780349 := by
  unfold tailWord_955243
  simp only [CollatzResearch.WordTrace]
  refine ⟨34840574478325228361070383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23227049652216818907380255 34840574478325228361070383)
  ·
    refine ⟨52260861717487842541605575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34840574478325228361070383 52260861717487842541605575)
    ·
      refine ⟨78391292576231763812408363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52260861717487842541605575 78391292576231763812408363)
      ·
        refine ⟨117586938864347645718612545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78391292576231763812408363 117586938864347645718612545)
        ·
          refine ⟨88190204148260734288959409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117586938864347645718612545 88190204148260734288959409)
          ·
            refine ⟨66142653111195550716719557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88190204148260734288959409 66142653111195550716719557)
            ·
              refine ⟨12401747458349165759384917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66142653111195550716719557 12401747458349165759384917)
              ·
                refine ⟨18166622253441160780349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 12401747458349165759384917 18166622253441160780349)
                ·
                  rfl

theorem cell23_955243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 11].length) (baseStart_955243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955243 prefixEnd_955243 := by exact prefixLift 955243
  have htrace : WordTrace (prefixWord ++ tailWord_955243) baseStart_955243 baseEnd_955243 := by
    simpa [prefixWord, tailWord_955243, baseEnd_955243] using wordTrace_append hprefix tailTrace_955243
  have hstable : (prefixWord ++ tailWord_955243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955243).length < 2 ^ (prefixWord ++ tailWord_955243).sum := by decide
  have hdescent : baseEnd_955243 < baseStart_955243 := by decide
  rcases family_descends (prefixWord ++ tailWord_955243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955271 : List Nat := [1, 1, 4, 2, 3, 2, 2, 1, 3, 2, 2]
def baseStart_955271 : Nat := 118140960795 + 955271 * 2 ^ 59
def prefixEnd_955271 : Nat := 4983230072969 + 3 ^ 40 * 955271 * 2
def baseEnd_955271 : Nat := 490513178301237231519295

theorem tailTrace_955271 : CollatzResearch.WordTrace tailWord_955271 prefixEnd_955271 490513178301237231519295 := by
  unfold tailWord_955271
  simp only [CollatzResearch.WordTrace]
  refine ⟨34841595722223789143089667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23227730481482526095393111 34841595722223789143089667)
  ·
    refine ⟨52262393583335683714634501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34841595722223789143089667 52262393583335683714634501)
    ·
      refine ⟨9799198796875440696493969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52262393583335683714634501 9799198796875440696493969)
      ·
        refine ⟨7349399097656580522370477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9799198796875440696493969 7349399097656580522370477)
        ·
          refine ⟨2756024661621217695888929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7349399097656580522370477 2756024661621217695888929)
          ·
            refine ⟨2067018496215913271916697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2756024661621217695888929 2067018496215913271916697)
            ·
              refine ⟨1550263872161934953937523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2067018496215913271916697 1550263872161934953937523)
              ·
                refine ⟨2325395808242902430906285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1550263872161934953937523 2325395808242902430906285)
                ·
                  refine ⟨872023428091088411589857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2325395808242902430906285 872023428091088411589857)
                  ·
                    refine ⟨654017571068316308692393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 872023428091088411589857 654017571068316308692393)
                    ·
                      refine ⟨490513178301237231519295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 654017571068316308692393 490513178301237231519295)
                      ·
                        rfl

theorem cell23_955271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_955271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955271 prefixEnd_955271 := by exact prefixLift 955271
  have htrace : WordTrace (prefixWord ++ tailWord_955271) baseStart_955271 baseEnd_955271 := by
    simpa [prefixWord, tailWord_955271, baseEnd_955271] using wordTrace_append hprefix tailTrace_955271
  have hstable : (prefixWord ++ tailWord_955271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955271).length < 2 ^ (prefixWord ++ tailWord_955271).sum := by decide
  have hdescent : baseEnd_955271 < baseStart_955271 := by decide
  rcases family_descends (prefixWord ++ tailWord_955271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955300 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 1, 4, 5]
def baseStart_955300 : Nat := 118140960795 + 955300 * 2 ^ 59
def prefixEnd_955300 : Nat := 4983230072969 + 3 ^ 40 * 955300 * 2
def baseEnd_955300 : Nat := 490528069240217618056661

theorem tailTrace_955300 : CollatzResearch.WordTrace tailWord_955300 prefixEnd_955300 490528069240217618056661 := by
  unfold tailWord_955300
  simp only [CollatzResearch.WordTrace]
  refine ⟨17421326719559363547947677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23228435626079151397263569 17421326719559363547947677)
  ·
    refine ⟨6532997519834761330480379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17421326719559363547947677 6532997519834761330480379)
    ·
      refine ⟨9799496279752141995720569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6532997519834761330480379 9799496279752141995720569)
      ·
        refine ⟨7349622209814106496790427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9799496279752141995720569 7349622209814106496790427)
        ·
          refine ⟨11024433314721159745185641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7349622209814106496790427 11024433314721159745185641)
          ·
            refine ⟨8268324986040869808889231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11024433314721159745185641 8268324986040869808889231)
            ·
              refine ⟨12402487479061304713333847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8268324986040869808889231 12402487479061304713333847)
              ·
                refine ⟨18603731218591957070000771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12402487479061304713333847 18603731218591957070000771)
                ·
                  refine ⟨27905596827887935605001157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18603731218591957070000771 27905596827887935605001157)
                  ·
                    refine ⟨5232299405228987925937717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27905596827887935605001157 5232299405228987925937717)
                    ·
                      refine ⟨490528069240217618056661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5232299405228987925937717 490528069240217618056661)
                      ·
                        rfl

theorem cell23_955300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_955300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955300 prefixEnd_955300 := by exact prefixLift 955300
  have htrace : WordTrace (prefixWord ++ tailWord_955300) baseStart_955300 baseEnd_955300 := by
    simpa [prefixWord, tailWord_955300, baseEnd_955300] using wordTrace_append hprefix tailTrace_955300
  have hstable : (prefixWord ++ tailWord_955300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955300).length < 2 ^ (prefixWord ++ tailWord_955300).sum := by decide
  have hdescent : baseEnd_955300 < baseStart_955300 := by decide
  rcases family_descends (prefixWord ++ tailWord_955300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955327 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 5, 4, 2]
def baseStart_955327 : Nat := 118140960795 + 955327 * 2 ^ 59
def prefixEnd_955327 : Nat := 4983230072969 + 3 ^ 40 * 955327 * 2
def baseEnd_955327 : Nat := 490541933217889012419037

theorem tailTrace_955327 : CollatzResearch.WordTrace tailWord_955327 prefixEnd_955327 490541933217889012419037 := by
  unfold tailWord_955327
  simp only [CollatzResearch.WordTrace]
  refine ⟨34843638210020910707128235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23229092140013940471418823 34843638210020910707128235)
  ·
    refine ⟨52265457315031366060692353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34843638210020910707128235 52265457315031366060692353)
    ·
      refine ⟨39199092986273524545519265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52265457315031366060692353 39199092986273524545519265)
      ·
        refine ⟨29399319739705143409139449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39199092986273524545519265 29399319739705143409139449)
        ·
          refine ⟨22049489804778857556854587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29399319739705143409139449 22049489804778857556854587)
          ·
            refine ⟨33074234707168286335281881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22049489804778857556854587 33074234707168286335281881)
            ·
              refine ⟨24805676030376214751461411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33074234707168286335281881 24805676030376214751461411)
              ·
                refine ⟨37208514045564322127192117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24805676030376214751461411 37208514045564322127192117)
                ·
                  refine ⟨3488298191771655199424261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37208514045564322127192117 3488298191771655199424261)
                  ·
                    refine ⟨654055910957185349892049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3488298191771655199424261 654055910957185349892049)
                    ·
                      refine ⟨490541933217889012419037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 654055910957185349892049 490541933217889012419037)
                      ·
                        rfl

theorem cell23_955327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 4, 2].length) (baseStart_955327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955327 prefixEnd_955327 := by exact prefixLift 955327
  have htrace : WordTrace (prefixWord ++ tailWord_955327) baseStart_955327 baseEnd_955327 := by
    simpa [prefixWord, tailWord_955327, baseEnd_955327] using wordTrace_append hprefix tailTrace_955327
  have hstable : (prefixWord ++ tailWord_955327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955327).length < 2 ^ (prefixWord ++ tailWord_955327).sum := by decide
  have hdescent : baseEnd_955327 < baseStart_955327 := by decide
  rcases family_descends (prefixWord ++ tailWord_955327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955348 : List Nat := [2, 4, 1, 2, 1, 4, 1, 2, 1, 3, 2]
def baseStart_955348 : Nat := 118140960795 + 955348 * 2 ^ 59
def prefixEnd_955348 : Nat := 4983230072969 + 3 ^ 40 * 955348 * 2
def baseEnd_955348 : Nat := 490552716311633430256441

theorem tailTrace_955348 : CollatzResearch.WordTrace tailWord_955348 prefixEnd_955348 490552716311633430256441 := by
  unfold tailWord_955348
  simp only [CollatzResearch.WordTrace]
  refine ⟨17422202071472415646821349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23229602761963220862428465 17422202071472415646821349)
  ·
    refine ⟨3266662888401077933779003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17422202071472415646821349 3266662888401077933779003)
    ·
      refine ⟨4899994332601616900668505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3266662888401077933779003 4899994332601616900668505)
      ·
        refine ⟨3674995749451212675501379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4899994332601616900668505 3674995749451212675501379)
        ·
          refine ⟨5512493624176819013252069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3674995749451212675501379 5512493624176819013252069)
          ·
            refine ⟨1033592554533153564984763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5512493624176819013252069 1033592554533153564984763)
            ·
              refine ⟨1550388831799730347477145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1033592554533153564984763 1550388831799730347477145)
              ·
                refine ⟨1162791623849797760607859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1550388831799730347477145 1162791623849797760607859)
                ·
                  refine ⟨1744187435774696640911789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1162791623849797760607859 1744187435774696640911789)
                  ·
                    refine ⟨654070288415511240341921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1744187435774696640911789 654070288415511240341921)
                    ·
                      refine ⟨490552716311633430256441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 654070288415511240341921 490552716311633430256441)
                      ·
                        rfl

theorem cell23_955348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_955348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955348 prefixEnd_955348 := by exact prefixLift 955348
  have htrace : WordTrace (prefixWord ++ tailWord_955348) baseStart_955348 baseEnd_955348 := by
    simpa [prefixWord, tailWord_955348, baseEnd_955348] using wordTrace_append hprefix tailTrace_955348
  have hstable : (prefixWord ++ tailWord_955348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955348).length < 2 ^ (prefixWord ++ tailWord_955348).sum := by decide
  have hdescent : baseEnd_955348 < baseStart_955348 := by decide
  rcases family_descends (prefixWord ++ tailWord_955348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955365 : List Nat := [1, 3, 1, 6, 1, 1, 3, 1, 1, 3, 2]
def baseStart_955365 : Nat := 118140960795 + 955365 * 2 ^ 59
def prefixEnd_955365 : Nat := 4983230072969 + 3 ^ 40 * 955365 * 2
def baseEnd_955365 : Nat := 490561445482759863743863

theorem tailTrace_955365 : CollatzResearch.WordTrace tailWord_955365 prefixEnd_955365 490561445482759863743863 := by
  unfold tailWord_955365
  simp only [CollatzResearch.WordTrace]
  refine ⟨34845024183883243197011549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23230016122588828798007699 34845024183883243197011549)
  ·
    refine ⟨13066884068956216198879331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34845024183883243197011549 13066884068956216198879331)
    ·
      refine ⟨19600326103434324298318997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13066884068956216198879331 19600326103434324298318997)
      ·
        refine ⟨918765286098483951483703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19600326103434324298318997 918765286098483951483703)
        ·
          refine ⟨1378147929147725927225555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 918765286098483951483703 1378147929147725927225555)
          ·
            refine ⟨2067221893721588890838333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1378147929147725927225555 2067221893721588890838333)
            ·
              refine ⟨775208210145595834064375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2067221893721588890838333 775208210145595834064375)
              ·
                refine ⟨1162812315218393751096563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 775208210145595834064375 1162812315218393751096563)
                ·
                  refine ⟨1744218472827590626644845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1162812315218393751096563 1744218472827590626644845)
                  ·
                    refine ⟨654081927310346484991817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1744218472827590626644845 654081927310346484991817)
                    ·
                      refine ⟨490561445482759863743863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 654081927310346484991817 490561445482759863743863)
                      ·
                        rfl

theorem cell23_955365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_955365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955365 prefixEnd_955365 := by exact prefixLift 955365
  have htrace : WordTrace (prefixWord ++ tailWord_955365) baseStart_955365 baseEnd_955365 := by
    simpa [prefixWord, tailWord_955365, baseEnd_955365] using wordTrace_append hprefix tailTrace_955365
  have hstable : (prefixWord ++ tailWord_955365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955365).length < 2 ^ (prefixWord ++ tailWord_955365).sum := by decide
  have hdescent : baseEnd_955365 < baseStart_955365 := by decide
  rcases family_descends (prefixWord ++ tailWord_955365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955521 : List Nat := [1, 2, 4, 2, 2, 1, 3, 2, 1, 5]
def baseStart_955521 : Nat := 118140960795 + 955521 * 2 ^ 59
def prefixEnd_955521 : Nat := 4983230072969 + 3 ^ 40 * 955521 * 2
def baseEnd_955521 : Nat := 163547182821620417797715

theorem tailTrace_955521 : CollatzResearch.WordTrace tailWord_955521 prefixEnd_955521 163547182821620417797715 := by
  unfold tailWord_955521
  simp only [CollatzResearch.WordTrace]
  refine ⟨34850713971318081839690417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23233809314212054559793611 34850713971318081839690417)
  ·
    refine ⟨26138035478488561379767813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34850713971318081839690417 26138035478488561379767813)
    ·
      refine ⟨4900881652216605258706465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26138035478488561379767813 4900881652216605258706465)
      ·
        refine ⟨3675661239162453944029849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4900881652216605258706465 3675661239162453944029849)
        ·
          refine ⟨2756745929371840458022387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3675661239162453944029849 2756745929371840458022387)
          ·
            refine ⟨4135118894057760687033581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2756745929371840458022387 4135118894057760687033581)
            ·
              refine ⟨1550669585271660257637593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4135118894057760687033581 1550669585271660257637593)
              ·
                refine ⟨1163002188953745193228195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1550669585271660257637593 1163002188953745193228195)
                ·
                  refine ⟨1744503283430617789842293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1163002188953745193228195 1744503283430617789842293)
                  ·
                    refine ⟨163547182821620417797715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1744503283430617789842293 163547182821620417797715)
                    ·
                      rfl

theorem cell23_955521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_955521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955521 prefixEnd_955521 := by exact prefixLift 955521
  have htrace : WordTrace (prefixWord ++ tailWord_955521) baseStart_955521 baseEnd_955521 := by
    simpa [prefixWord, tailWord_955521, baseEnd_955521] using wordTrace_append hprefix tailTrace_955521
  have hstable : (prefixWord ++ tailWord_955521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955521).length < 2 ^ (prefixWord ++ tailWord_955521).sum := by decide
  have hdescent : baseEnd_955521 < baseStart_955521 := by decide
  rcases family_descends (prefixWord ++ tailWord_955521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955534 : List Nat := [4, 1, 1, 3, 2, 1, 1, 1, 3, 6]
def baseStart_955534 : Nat := 118140960795 + 955534 * 2 ^ 59
def prefixEnd_955534 : Nat := 4983230072969 + 3 ^ 40 * 955534 * 2
def baseEnd_955534 : Nat := 163549407904456567510195

theorem tailTrace_955534 : CollatzResearch.WordTrace tailWord_955534 prefixEnd_955534 163549407904456567510195 := by
  unfold tailWord_955534
  simp only [CollatzResearch.WordTrace]
  refine ⟨4356398515033873132489207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23234125413513990039942437 4356398515033873132489207)
  ·
    refine ⟨6534597772550809698733811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4356398515033873132489207 6534597772550809698733811)
    ·
      refine ⟨9801896658826214548100717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6534597772550809698733811 9801896658826214548100717)
      ·
        refine ⟨3675711247059830455537769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9801896658826214548100717 3675711247059830455537769)
        ·
          refine ⟨2756783435294872841653327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3675711247059830455537769 2756783435294872841653327)
          ·
            refine ⟨4135175152942309262479991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2756783435294872841653327 4135175152942309262479991)
            ·
              refine ⟨6202762729413463893719987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4135175152942309262479991 6202762729413463893719987)
              ·
                refine ⟨9304144094120195840579981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6202762729413463893719987 9304144094120195840579981)
                ·
                  refine ⟨3489054035295073440217493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9304144094120195840579981 3489054035295073440217493)
                  ·
                    refine ⟨163549407904456567510195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3489054035295073440217493 163549407904456567510195)
                    ·
                      rfl

theorem cell23_955534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_955534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955534 prefixEnd_955534 := by exact prefixLift 955534
  have htrace : WordTrace (prefixWord ++ tailWord_955534) baseStart_955534 baseEnd_955534 := by
    simpa [prefixWord, tailWord_955534, baseEnd_955534] using wordTrace_append hprefix tailTrace_955534
  have hstable : (prefixWord ++ tailWord_955534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955534).length < 2 ^ (prefixWord ++ tailWord_955534).sum := by decide
  have hdescent : baseEnd_955534 < baseStart_955534 := by decide
  rcases family_descends (prefixWord ++ tailWord_955534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955538 : List Nat := [3, 2, 3, 1, 1, 3, 3, 1, 1, 5]
def baseStart_955538 : Nat := 118140960795 + 955538 * 2 ^ 59
def prefixEnd_955538 : Nat := 4983230072969 + 3 ^ 40 * 955538 * 2
def baseEnd_955538 : Nat := 163550092545329228960189

theorem tailTrace_955538 : CollatzResearch.WordTrace tailWord_955538 prefixEnd_955538 163550092545329228960189 := by
  unfold tailWord_955538
  simp only [CollatzResearch.WordTrace]
  refine ⟨8712833503064123435764817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23234222674837662495372845 8712833503064123435764817)
  ·
    refine ⟨6534625127298092576823613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8712833503064123435764817 6534625127298092576823613)
    ·
      refine ⟨2450484422736784716308855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6534625127298092576823613 2450484422736784716308855)
      ·
        refine ⟨3675726634105177074463283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2450484422736784716308855 3675726634105177074463283)
        ·
          refine ⟨5513589951157765611694925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3675726634105177074463283 5513589951157765611694925)
          ·
            refine ⟨2067596231684162104385597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5513589951157765611694925 2067596231684162104385597)
            ·
              refine ⟨775348586881560789144599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2067596231684162104385597 775348586881560789144599)
              ·
                refine ⟨1163022880322341183716899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 775348586881560789144599 1163022880322341183716899)
                ·
                  refine ⟨1744534320483511775575349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1163022880322341183716899 1744534320483511775575349)
                  ·
                    refine ⟨163550092545329228960189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1744534320483511775575349 163550092545329228960189)
                    ·
                      rfl

theorem cell23_955538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_955538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955538 prefixEnd_955538 := by exact prefixLift 955538
  have htrace : WordTrace (prefixWord ++ tailWord_955538) baseStart_955538 baseEnd_955538 := by
    simpa [prefixWord, tailWord_955538, baseEnd_955538] using wordTrace_append hprefix tailTrace_955538
  have hstable : (prefixWord ++ tailWord_955538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955538).length < 2 ^ (prefixWord ++ tailWord_955538).sum := by decide
  have hdescent : baseEnd_955538 < baseStart_955538 := by decide
  rcases family_descends (prefixWord ++ tailWord_955538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955541 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 7, 2, 2]
def baseStart_955541 : Nat := 118140960795 + 955541 * 2 ^ 59
def prefixEnd_955541 : Nat := 4983230072969 + 3 ^ 40 * 955541 * 2
def baseEnd_955541 : Nat := 490651818077951175143053

theorem tailTrace_955541 : CollatzResearch.WordTrace tailWord_955541 prefixEnd_955541 490651818077951175143053 := by
  unfold tailWord_955541
  simp only [CollatzResearch.WordTrace]
  refine ⟨34851443431245625255418477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23234295620830416836945651 34851443431245625255418477)
  ·
    refine ⟨13069291286717109470781929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34851443431245625255418477 13069291286717109470781929)
    ·
      refine ⟨9801968465037832103086447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13069291286717109470781929 9801968465037832103086447)
      ·
        refine ⟨14702952697556748154629671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9801968465037832103086447 14702952697556748154629671)
        ·
          refine ⟨22054429046335122231944507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14702952697556748154629671 22054429046335122231944507)
          ·
            refine ⟨33081643569502683347916761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22054429046335122231944507 33081643569502683347916761)
            ·
              refine ⟨24811232677127012510937571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33081643569502683347916761 24811232677127012510937571)
              ·
                refine ⟨37216849015690518766406357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24811232677127012510937571 37216849015690518766406357)
                ·
                  refine ⟨872269898805246533587649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 37216849015690518766406357 872269898805246533587649)
                  ·
                    refine ⟨654202424103934900190737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 872269898805246533587649 654202424103934900190737)
                    ·
                      refine ⟨490651818077951175143053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 654202424103934900190737 490651818077951175143053)
                      ·
                        rfl

theorem cell23_955541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 7, 2, 2].length) (baseStart_955541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955541 prefixEnd_955541 := by exact prefixLift 955541
  have htrace : WordTrace (prefixWord ++ tailWord_955541) baseStart_955541 baseEnd_955541 := by
    simpa [prefixWord, tailWord_955541, baseEnd_955541] using wordTrace_append hprefix tailTrace_955541
  have hstable : (prefixWord ++ tailWord_955541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955541).length < 2 ^ (prefixWord ++ tailWord_955541).sum := by decide
  have hdescent : baseEnd_955541 < baseStart_955541 := by decide
  rcases family_descends (prefixWord ++ tailWord_955541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955567 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 6]
def baseStart_955567 : Nat := 118140960795 + 955567 * 2 ^ 59
def prefixEnd_955567 : Nat := 4983230072969 + 3 ^ 40 * 955567 * 2
def baseEnd_955567 : Nat := 490665168574968073417933

theorem tailTrace_955567 : CollatzResearch.WordTrace tailWord_955567 prefixEnd_955567 490665168574968073417933 := by
  unfold tailWord_955567
  simp only [CollatzResearch.WordTrace]
  refine ⟨34852391729151431695864955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23234927819434287797243303 34852391729151431695864955)
  ·
    refine ⟨52278587593727147543797433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34852391729151431695864955 52278587593727147543797433)
    ·
      refine ⟨39208940695295360657848075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52278587593727147543797433 39208940695295360657848075)
      ·
        refine ⟨58813411042943040986772113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39208940695295360657848075 58813411042943040986772113)
        ·
          refine ⟨44110058282207280740079085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58813411042943040986772113 44110058282207280740079085)
          ·
            refine ⟨16541271855827730277529657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44110058282207280740079085 16541271855827730277529657)
            ·
              refine ⟨12405953891870797708147243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16541271855827730277529657 12405953891870797708147243)
              ·
                refine ⟨18608930837806196562220865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12405953891870797708147243 18608930837806196562220865)
                ·
                  refine ⟨13956698128354647421665649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18608930837806196562220865 13956698128354647421665649)
                  ·
                    refine ⟨10467523596265985566249237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13956698128354647421665649 10467523596265985566249237)
                    ·
                      refine ⟨490665168574968073417933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10467523596265985566249237 490665168574968073417933)
                      ·
                        rfl

theorem cell23_955567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 6].length) (baseStart_955567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955567 prefixEnd_955567 := by exact prefixLift 955567
  have htrace : WordTrace (prefixWord ++ tailWord_955567) baseStart_955567 baseEnd_955567 := by
    simpa [prefixWord, tailWord_955567, baseEnd_955567] using wordTrace_append hprefix tailTrace_955567
  have hstable : (prefixWord ++ tailWord_955567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955567).length < 2 ^ (prefixWord ++ tailWord_955567).sum := by decide
  have hdescent : baseEnd_955567 < baseStart_955567 := by decide
  rcases family_descends (prefixWord ++ tailWord_955567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955608 : List Nat := [2, 1, 2, 2, 5, 1, 1, 1, 4, 1, 3]
def baseStart_955608 : Nat := 118140960795 + 955608 * 2 ^ 59
def prefixEnd_955608 : Nat := 4983230072969 + 3 ^ 40 * 955608 * 2
def baseEnd_955608 : Nat := 490686221281802413005245

theorem tailTrace_955608 : CollatzResearch.WordTrace tailWord_955608 prefixEnd_955608 490686221281802413005245 := by
  unfold tailWord_955608
  simp only [CollatzResearch.WordTrace]
  refine ⟨17426943561001447849053739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23235924748001930465404985 17426943561001447849053739)
  ·
    refine ⟨26140415341502171773580609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17426943561001447849053739 26140415341502171773580609)
    ·
      refine ⟨19605311506126628830185457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26140415341502171773580609 19605311506126628830185457)
      ·
        refine ⟨14703983629594971622639093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19605311506126628830185457 14703983629594971622639093)
        ·
          refine ⟨1378498465274528589622415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14703983629594971622639093 1378498465274528589622415)
          ·
            refine ⟨2067747697911792884433623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1378498465274528589622415 2067747697911792884433623)
            ·
              refine ⟨3101621546867689326650435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2067747697911792884433623 3101621546867689326650435)
              ·
                refine ⟨4652432320301533989975653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3101621546867689326650435 4652432320301533989975653)
                ·
                  refine ⟨872331060056537623120435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4652432320301533989975653 872331060056537623120435)
                  ·
                    refine ⟨1308496590084806434680653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 872331060056537623120435 1308496590084806434680653)
                    ·
                      refine ⟨490686221281802413005245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1308496590084806434680653 490686221281802413005245)
                      ·
                        rfl

theorem cell23_955608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 4, 1, 3].length) (baseStart_955608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955608 prefixEnd_955608 := by exact prefixLift 955608
  have htrace : WordTrace (prefixWord ++ tailWord_955608) baseStart_955608 baseEnd_955608 := by
    simpa [prefixWord, tailWord_955608, baseEnd_955608] using wordTrace_append hprefix tailTrace_955608
  have hstable : (prefixWord ++ tailWord_955608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955608).length < 2 ^ (prefixWord ++ tailWord_955608).sum := by decide
  have hdescent : baseEnd_955608 < baseStart_955608 := by decide
  rcases family_descends (prefixWord ++ tailWord_955608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955624 : List Nat := [2, 1, 4, 1, 2, 1, 1, 3, 2, 6]
def baseStart_955624 : Nat := 118140960795 + 955624 * 2 ^ 59
def prefixEnd_955624 : Nat := 4983230072969 + 3 ^ 40 * 955624 * 2
def baseEnd_955624 : Nat := 163564812324091450135057

theorem tailTrace_955624 : CollatzResearch.WordTrace tailWord_955624 prefixEnd_955624 163564812324091450135057 := by
  unfold tailWord_955624
  simp only [CollatzResearch.WordTrace]
  refine ⟨17427235344972465215344963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23236313793296620287126617 17427235344972465215344963)
  ·
    refine ⟨26140853017458697823017445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17427235344972465215344963 26140853017458697823017445)
    ·
      refine ⟨4901409940773505841815771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26140853017458697823017445 4901409940773505841815771)
      ·
        refine ⟨7352114911160258762723657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4901409940773505841815771 7352114911160258762723657)
        ·
          refine ⟨5514086183370194072042743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7352114911160258762723657 5514086183370194072042743)
          ·
            refine ⟨8271129275055291108064115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5514086183370194072042743 8271129275055291108064115)
            ·
              refine ⟨12406693912582936662096173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8271129275055291108064115 12406693912582936662096173)
              ·
                refine ⟨4652510217218601248286065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12406693912582936662096173 4652510217218601248286065)
                ·
                  refine ⟨3489382662913950936214549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4652510217218601248286065 3489382662913950936214549)
                  ·
                    refine ⟨163564812324091450135057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3489382662913950936214549 163564812324091450135057)
                    ·
                      rfl

theorem cell23_955624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_955624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955624 prefixEnd_955624 := by exact prefixLift 955624
  have htrace : WordTrace (prefixWord ++ tailWord_955624) baseStart_955624 baseEnd_955624 := by
    simpa [prefixWord, tailWord_955624, baseEnd_955624] using wordTrace_append hprefix tailTrace_955624
  have hstable : (prefixWord ++ tailWord_955624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955624).length < 2 ^ (prefixWord ++ tailWord_955624).sum := by decide
  have hdescent : baseEnd_955624 < baseStart_955624 := by decide
  rcases family_descends (prefixWord ++ tailWord_955624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955682 : List Nat := [3, 3, 1, 1, 4, 1, 1, 3, 2, 2, 2]
def baseStart_955682 : Nat := 118140960795 + 955682 * 2 ^ 59
def prefixEnd_955682 : Nat := 4983230072969 + 3 ^ 40 * 955682 * 2
def baseEnd_955682 : Nat := 490724218850235123479905

theorem tailTrace_955682 : CollatzResearch.WordTrace tailWord_955682 prefixEnd_955682 490724218850235123479905 := by
  unfold tailWord_955682
  simp only [CollatzResearch.WordTrace]
  refine ⟨8714146530933701584075325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23237724082489870890867533 8714146530933701584075325)
  ·
    refine ⟨3267804949100138094028247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8714146530933701584075325 3267804949100138094028247)
    ·
      refine ⟨4901707423650207141042371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3267804949100138094028247 4901707423650207141042371)
      ·
        refine ⟨7352561135475310711563557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4901707423650207141042371 7352561135475310711563557)
        ·
          refine ⟨1378605212901620758418167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7352561135475310711563557 1378605212901620758418167)
          ·
            refine ⟨2067907819352431137627251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1378605212901620758418167 2067907819352431137627251)
            ·
              refine ⟨3101861729028646706440877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2067907819352431137627251 3101861729028646706440877)
              ·
                refine ⟨1163198148385742514915329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3101861729028646706440877 1163198148385742514915329)
                ·
                  refine ⟨872398611289306886186497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1163198148385742514915329 872398611289306886186497)
                  ·
                    refine ⟨654298958466980164639873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 872398611289306886186497 654298958466980164639873)
                    ·
                      refine ⟨490724218850235123479905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 654298958466980164639873 490724218850235123479905)
                      ·
                        rfl

theorem cell23_955682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_955682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955682 prefixEnd_955682 := by exact prefixLift 955682
  have htrace : WordTrace (prefixWord ++ tailWord_955682) baseStart_955682 baseEnd_955682 := by
    simpa [prefixWord, tailWord_955682, baseEnd_955682] using wordTrace_append hprefix tailTrace_955682
  have hstable : (prefixWord ++ tailWord_955682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955682).length < 2 ^ (prefixWord ++ tailWord_955682).sum := by decide
  have hdescent : baseEnd_955682 < baseStart_955682 := by decide
  rcases family_descends (prefixWord ++ tailWord_955682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955701 : List Nat := [1, 3, 3, 1, 2, 2, 1, 3, 2, 5]
def baseStart_955701 : Nat := 118140960795 + 955701 * 2 ^ 59
def prefixEnd_955701 : Nat := 4983230072969 + 3 ^ 40 * 955701 * 2
def baseEnd_955701 : Nat := 163577991660890183047439

theorem tailTrace_955701 : CollatzResearch.WordTrace tailWord_955701 prefixEnd_955701 163577991660890183047439 := by
  unfold tailWord_955701
  simp only [CollatzResearch.WordTrace]
  refine ⟨34857279110665972581242957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23238186073777315054161971 34857279110665972581242957)
  ·
    refine ⟨13071479666499739717966109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34857279110665972581242957 13071479666499739717966109)
    ·
      refine ⟨4901804874937402394237291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13071479666499739717966109 4901804874937402394237291)
      ·
        refine ⟨7352707312406103591355937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4901804874937402394237291 7352707312406103591355937)
        ·
          refine ⟨5514530484304577693516953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7352707312406103591355937 5514530484304577693516953)
          ·
            refine ⟨4135897863228433270137715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5514530484304577693516953 4135897863228433270137715)
            ·
              refine ⟨6203846794842649905206573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4135897863228433270137715 6203846794842649905206573)
              ·
                refine ⟨2326442548065993714452465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6203846794842649905206573 2326442548065993714452465)
                ·
                  refine ⟨1744831911049495285839349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2326442548065993714452465 1744831911049495285839349)
                  ·
                    refine ⟨163577991660890183047439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1744831911049495285839349 163577991660890183047439)
                    ·
                      rfl

theorem cell23_955701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_955701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955701 prefixEnd_955701 := by exact prefixLift 955701
  have htrace : WordTrace (prefixWord ++ tailWord_955701) baseStart_955701 baseEnd_955701 := by
    simpa [prefixWord, tailWord_955701, baseEnd_955701] using wordTrace_append hprefix tailTrace_955701
  have hstable : (prefixWord ++ tailWord_955701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955701).length < 2 ^ (prefixWord ++ tailWord_955701).sum := by decide
  have hdescent : baseEnd_955701 < baseStart_955701 := by decide
  rcases family_descends (prefixWord ++ tailWord_955701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955721 : List Nat := [1, 2, 1, 1, 2, 3, 4, 2, 2, 1, 4]
def baseStart_955721 : Nat := 118140960795 + 955721 * 2 ^ 59
def prefixEnd_955721 : Nat := 4983230072969 + 3 ^ 40 * 955721 * 2
def baseEnd_955721 : Nat := 490744244595760470892225

theorem tailTrace_955721 : CollatzResearch.WordTrace tailWord_955721 prefixEnd_955721 490744244595760470892225 := by
  unfold tailWord_955721
  simp only [CollatzResearch.WordTrace]
  refine ⟨34858008570593515996971017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23238672380395677331314011 34858008570593515996971017)
  ·
    refine ⟨26143506427945136997728263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34858008570593515996971017 26143506427945136997728263)
    ·
      refine ⟨39215259641917705496592395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26143506427945136997728263 39215259641917705496592395)
      ·
        refine ⟨58822889462876558244888593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39215259641917705496592395 58822889462876558244888593)
        ·
          refine ⟨44117167097157418683666445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58822889462876558244888593 44117167097157418683666445)
          ·
            refine ⟨16543937661434032006374917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44117167097157418683666445 16543937661434032006374917)
            ·
              refine ⟨3101988311518881001195297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16543937661434032006374917 3101988311518881001195297)
              ·
                refine ⟨2326491233639160750896473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3101988311518881001195297 2326491233639160750896473)
                ·
                  refine ⟨1744868425229370563172355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2326491233639160750896473 1744868425229370563172355)
                  ·
                    refine ⟨2617302637844055844758533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1744868425229370563172355 2617302637844055844758533)
                    ·
                      refine ⟨490744244595760470892225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2617302637844055844758533 490744244595760470892225)
                      ·
                        rfl

theorem cell23_955721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 1, 4].length) (baseStart_955721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955721 prefixEnd_955721 := by exact prefixLift 955721
  have htrace : WordTrace (prefixWord ++ tailWord_955721) baseStart_955721 baseEnd_955721 := by
    simpa [prefixWord, tailWord_955721, baseEnd_955721] using wordTrace_append hprefix tailTrace_955721
  have hstable : (prefixWord ++ tailWord_955721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955721).length < 2 ^ (prefixWord ++ tailWord_955721).sum := by decide
  have hdescent : baseEnd_955721 < baseStart_955721 := by decide
  rcases family_descends (prefixWord ++ tailWord_955721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955731 : List Nat := [1, 1, 1, 2, 1, 1, 6, 3, 3, 4]
def baseStart_955731 : Nat := 118140960795 + 955731 * 2 ^ 59
def prefixEnd_955731 : Nat := 4983230072969 + 3 ^ 40 * 955731 * 2
def baseEnd_955731 : Nat := 163583126467435143922393

theorem tailTrace_955731 : CollatzResearch.WordTrace tailWord_955731 prefixEnd_955731 163583126467435143922393 := by
  unfold tailWord_955731
  simp only [CollatzResearch.WordTrace]
  refine ⟨34858373300557287704835047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23238915533704858469890031 34858373300557287704835047)
  ·
    refine ⟨52287559950835931557252571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34858373300557287704835047 52287559950835931557252571)
    ·
      refine ⟨78431339926253897335878857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52287559950835931557252571 78431339926253897335878857)
      ·
        refine ⟨58823504944690423001909143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78431339926253897335878857 58823504944690423001909143)
        ·
          refine ⟨88235257417035634502863715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58823504944690423001909143 88235257417035634502863715)
          ·
            refine ⟨132352886125553451754295573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88235257417035634502863715 132352886125553451754295573)
            ·
              refine ⟨6204041537135318050982605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 132352886125553451754295573 6204041537135318050982605)
              ·
                refine ⟨2326515576425744269118477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6204041537135318050982605 2326515576425744269118477)
                ·
                  refine ⟨872443341159654100919429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2326515576425744269118477 872443341159654100919429)
                  ·
                    refine ⟨163583126467435143922393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 872443341159654100919429 163583126467435143922393)
                    ·
                      rfl

theorem cell23_955731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 3, 4].length) (baseStart_955731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955731 prefixEnd_955731 := by exact prefixLift 955731
  have htrace : WordTrace (prefixWord ++ tailWord_955731) baseStart_955731 baseEnd_955731 := by
    simpa [prefixWord, tailWord_955731, baseEnd_955731] using wordTrace_append hprefix tailTrace_955731
  have hstable : (prefixWord ++ tailWord_955731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955731).length < 2 ^ (prefixWord ++ tailWord_955731).sum := by decide
  have hdescent : baseEnd_955731 < baseStart_955731 := by decide
  rcases family_descends (prefixWord ++ tailWord_955731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955748 : List Nat := [2, 3, 1, 1, 3, 3, 1, 2, 3, 4]
def baseStart_955748 : Nat := 118140960795 + 955748 * 2 ^ 59
def prefixEnd_955748 : Nat := 4983230072969 + 3 ^ 40 * 955748 * 2
def baseEnd_955748 : Nat := 163586036191143955084867

theorem tailTrace_955748 : CollatzResearch.WordTrace tailWord_955748 prefixEnd_955748 163586036191143955084867 := by
  unfold tailWord_955748
  simp only [CollatzResearch.WordTrace]
  refine ⟨17429496670747849804101949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23239328894330466405469265 17429496670747849804101949)
  ·
    refine ⟨6536061251530443676538231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17429496670747849804101949 6536061251530443676538231)
    ·
      refine ⟨9804091877295665514807347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6536061251530443676538231 9804091877295665514807347)
      ·
        refine ⟨14706137815943498272211021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9804091877295665514807347 14706137815943498272211021)
        ·
          refine ⟨5514801680978811852079133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14706137815943498272211021 5514801680978811852079133)
          ·
            refine ⟨2068050630367054444529675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5514801680978811852079133 2068050630367054444529675)
            ·
              refine ⟨3102075945550581666794513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2068050630367054444529675 3102075945550581666794513)
              ·
                refine ⟨2326556959162936250095885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3102075945550581666794513 2326556959162936250095885)
                ·
                  refine ⟨872458859686101093785957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2326556959162936250095885 872458859686101093785957)
                  ·
                    refine ⟨163586036191143955084867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 872458859686101093785957 163586036191143955084867)
                    ·
                      rfl

theorem cell23_955748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_955748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955748 prefixEnd_955748 := by exact prefixLift 955748
  have htrace : WordTrace (prefixWord ++ tailWord_955748) baseStart_955748 baseEnd_955748 := by
    simpa [prefixWord, tailWord_955748, baseEnd_955748] using wordTrace_append hprefix tailTrace_955748
  have hstable : (prefixWord ++ tailWord_955748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955748).length < 2 ^ (prefixWord ++ tailWord_955748).sum := by decide
  have hdescent : baseEnd_955748 < baseStart_955748 := by decide
  rcases family_descends (prefixWord ++ tailWord_955748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955805 : List Nat := [1, 4, 2, 1, 3, 1, 2, 2, 3, 1, 3]
def baseStart_955805 : Nat := 118140960795 + 955805 * 2 ^ 59
def prefixEnd_955805 : Nat := 4983230072969 + 3 ^ 40 * 955805 * 2
def baseEnd_955805 : Nat := 490787376970738142241839

theorem tailTrace_955805 : CollatzResearch.WordTrace tailWord_955805 prefixEnd_955805 490787376970738142241839 := by
  unfold tailWord_955805
  simp only [CollatzResearch.WordTrace]
  refine ⟨34861072302289198343028869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23240714868192798895352579 34861072302289198343028869)
  ·
    refine ⟨6536451056679224689317913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34861072302289198343028869 6536451056679224689317913)
    ·
      refine ⟨4902338292509418516988435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6536451056679224689317913 4902338292509418516988435)
      ·
        refine ⟨7353507438764127775482653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4902338292509418516988435 7353507438764127775482653)
        ·
          refine ⟨2757565289536547915805995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7353507438764127775482653 2757565289536547915805995)
          ·
            refine ⟨4136347934304821873708993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2757565289536547915805995 4136347934304821873708993)
            ·
              refine ⟨3102260950728616405281745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4136347934304821873708993 3102260950728616405281745)
              ·
                refine ⟨2326695713046462303961309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3102260950728616405281745 2326695713046462303961309)
                ·
                  refine ⟨872510892392423363985491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2326695713046462303961309 872510892392423363985491)
                  ·
                    refine ⟨1308766338588635045978237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 872510892392423363985491 1308766338588635045978237)
                    ·
                      refine ⟨490787376970738142241839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1308766338588635045978237 490787376970738142241839)
                      ·
                        rfl

theorem cell23_955805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_955805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955805 prefixEnd_955805 := by exact prefixLift 955805
  have htrace : WordTrace (prefixWord ++ tailWord_955805) baseStart_955805 baseEnd_955805 := by
    simpa [prefixWord, tailWord_955805, baseEnd_955805] using wordTrace_append hprefix tailTrace_955805
  have hstable : (prefixWord ++ tailWord_955805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955805).length < 2 ^ (prefixWord ++ tailWord_955805).sum := by decide
  have hdescent : baseEnd_955805 < baseStart_955805 := by decide
  rcases family_descends (prefixWord ++ tailWord_955805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955808 : List Nat := [2, 1, 1, 4, 1, 2, 4, 2, 1, 5]
def baseStart_955808 : Nat := 118140960795 + 955808 * 2 ^ 59
def prefixEnd_955808 : Nat := 4983230072969 + 3 ^ 40 * 955808 * 2
def baseEnd_955808 : Nat := 163596305804233876834775

theorem tailTrace_955808 : CollatzResearch.WordTrace tailWord_955808 prefixEnd_955808 163596305804233876834775 := by
  unfold tailWord_955808
  simp only [CollatzResearch.WordTrace]
  refine ⟨17430590860639164927694039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23240787814185553236925385 17430590860639164927694039)
  ·
    refine ⟨26145886290958747391541059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17430590860639164927694039 26145886290958747391541059)
    ·
      refine ⟨39218829436438121087311589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26145886290958747391541059 39218829436438121087311589)
      ·
        refine ⟨7353530519332147703870923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39218829436438121087311589 7353530519332147703870923)
        ·
          refine ⟨11030295778998221555806385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7353530519332147703870923 11030295778998221555806385)
          ·
            refine ⟨8272721834248666166854789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11030295778998221555806385 8272721834248666166854789)
            ·
              refine ⟨1551135343921624906285273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8272721834248666166854789 1551135343921624906285273)
              ·
                refine ⟨1163351507941218679713955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1551135343921624906285273 1163351507941218679713955)
                ·
                  refine ⟨1745027261911828019570933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1163351507941218679713955 1745027261911828019570933)
                  ·
                    refine ⟨163596305804233876834775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1745027261911828019570933 163596305804233876834775)
                    ·
                      rfl

theorem cell23_955808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 1, 5].length) (baseStart_955808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955808 prefixEnd_955808 := by exact prefixLift 955808
  have htrace : WordTrace (prefixWord ++ tailWord_955808) baseStart_955808 baseEnd_955808 := by
    simpa [prefixWord, tailWord_955808, baseEnd_955808] using wordTrace_append hprefix tailTrace_955808
  have hstable : (prefixWord ++ tailWord_955808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955808).length < 2 ^ (prefixWord ++ tailWord_955808).sum := by decide
  have hdescent : baseEnd_955808 < baseStart_955808 := by decide
  rcases family_descends (prefixWord ++ tailWord_955808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955815 : List Nat := [1, 1, 6, 1, 1, 1, 2, 3, 2, 3, 2]
def baseStart_955815 : Nat := 118140960795 + 955815 * 2 ^ 59
def prefixEnd_955815 : Nat := 4983230072969 + 3 ^ 40 * 955815 * 2
def baseEnd_955815 : Nat := 490792511777283103116793

theorem tailTrace_955815 : CollatzResearch.WordTrace tailWord_955815 prefixEnd_955815 490792511777283103116793 := by
  unfold tailWord_955815
  simp only [CollatzResearch.WordTrace]
  refine ⟨34861437032252970050892899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23240958021501980033928599 34861437032252970050892899)
  ·
    refine ⟨52292155548379455076339349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34861437032252970050892899 52292155548379455076339349)
    ·
      refine ⟨2451194791330286956703407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52292155548379455076339349 2451194791330286956703407)
      ·
        refine ⟨3676792186995430435055111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2451194791330286956703407 3676792186995430435055111)
        ·
          refine ⟨5515188280493145652582667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3676792186995430435055111 5515188280493145652582667)
          ·
            refine ⟨8272782420739718478874001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5515188280493145652582667 8272782420739718478874001)
            ·
              refine ⟨6204586815554788859155501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8272782420739718478874001 6204586815554788859155501)
              ·
                refine ⟨2326720055833045822183313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6204586815554788859155501 2326720055833045822183313)
                ·
                  refine ⟨1745040041874784366637485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2326720055833045822183313 1745040041874784366637485)
                  ·
                    refine ⟨654390015703044137489057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1745040041874784366637485 654390015703044137489057)
                    ·
                      refine ⟨490792511777283103116793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 654390015703044137489057 490792511777283103116793)
                      ·
                        rfl

theorem cell23_955815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_955815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955815 prefixEnd_955815 := by exact prefixLift 955815
  have htrace : WordTrace (prefixWord ++ tailWord_955815) baseStart_955815 baseEnd_955815 := by
    simpa [prefixWord, tailWord_955815, baseEnd_955815] using wordTrace_append hprefix tailTrace_955815
  have hstable : (prefixWord ++ tailWord_955815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955815).length < 2 ^ (prefixWord ++ tailWord_955815).sum := by decide
  have hdescent : baseEnd_955815 < baseStart_955815 := by decide
  rcases family_descends (prefixWord ++ tailWord_955815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955816 : List Nat := [2, 1, 6, 1, 3, 1, 1, 3, 1, 4]
def baseStart_955816 : Nat := 118140960795 + 955816 * 2 ^ 59
def prefixEnd_955816 : Nat := 4983230072969 + 3 ^ 40 * 955816 * 2
def baseEnd_955816 : Nat := 163597675085979199734763

theorem tailTrace_955816 : CollatzResearch.WordTrace tailWord_955816 prefixEnd_955816 163597675085979199734763 := by
  unfold tailWord_955816
  simp only [CollatzResearch.WordTrace]
  refine ⟨17430736752624673610839651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23240982336832898147786201 17430736752624673610839651)
  ·
    refine ⟨26146105128937010416259477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17430736752624673610839651 26146105128937010416259477)
    ·
      refine ⟨1225598677918922363262163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26146105128937010416259477 1225598677918922363262163)
      ·
        refine ⟨1838398016878383544893245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1225598677918922363262163 1838398016878383544893245)
        ·
          refine ⟨689399256329393829334967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1838398016878383544893245 689399256329393829334967)
          ·
            refine ⟨1034098884494090744002451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689399256329393829334967 1034098884494090744002451)
            ·
              refine ⟨1551148326741136116003677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1034098884494090744002451 1551148326741136116003677)
              ·
                refine ⟨581680622527926043501379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1551148326741136116003677 581680622527926043501379)
                ·
                  refine ⟨872520933791889065252069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 581680622527926043501379 872520933791889065252069)
                  ·
                    refine ⟨163597675085979199734763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 872520933791889065252069 163597675085979199734763)
                    ·
                      rfl

theorem cell23_955816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_955816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955816 prefixEnd_955816 := by exact prefixLift 955816
  have htrace : WordTrace (prefixWord ++ tailWord_955816) baseStart_955816 baseEnd_955816 := by
    simpa [prefixWord, tailWord_955816, baseEnd_955816] using wordTrace_append hprefix tailTrace_955816
  have hstable : (prefixWord ++ tailWord_955816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955816).length < 2 ^ (prefixWord ++ tailWord_955816).sum := by decide
  have hdescent : baseEnd_955816 < baseStart_955816 := by decide
  rcases family_descends (prefixWord ++ tailWord_955816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955848 : List Nat := [2, 1, 3, 1, 3, 1, 2, 2, 3, 2, 3]
def baseStart_955848 : Nat := 118140960795 + 955848 * 2 ^ 59
def prefixEnd_955848 : Nat := 4983230072969 + 3 ^ 40 * 955848 * 2
def baseEnd_955848 : Nat := 490809456638881474004141

theorem tailTrace_955848 : CollatzResearch.WordTrace tailWord_955848 prefixEnd_955848 490809456638881474004141 := by
  unfold tailWord_955848
  simp only [CollatzResearch.WordTrace]
  refine ⟨17431320320566708343422099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23241760427422277791229465 17431320320566708343422099)
  ·
    refine ⟨26146980480850062515133149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17431320320566708343422099 26146980480850062515133149)
    ·
      refine ⟨9805117680318773443174931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26146980480850062515133149 9805117680318773443174931)
      ·
        refine ⟨14707676520478160164762397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9805117680318773443174931 14707676520478160164762397)
        ·
          refine ⟨5515378695179310061785899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14707676520478160164762397 5515378695179310061785899)
          ·
            refine ⟨8273068042768965092678849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5515378695179310061785899 8273068042768965092678849)
            ·
              refine ⟨6204801032076723819509137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8273068042768965092678849 6204801032076723819509137)
              ·
                refine ⟨4653600774057542864631853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6204801032076723819509137 4653600774057542864631853)
                ·
                  refine ⟨1745100290271578574236945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4653600774057542864631853 1745100290271578574236945)
                  ·
                    refine ⟨1308825217703683930677709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1745100290271578574236945 1308825217703683930677709)
                    ·
                      refine ⟨490809456638881474004141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1308825217703683930677709 490809456638881474004141)
                      ·
                        rfl

theorem cell23_955848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_955848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955848 prefixEnd_955848 := by exact prefixLift 955848
  have htrace : WordTrace (prefixWord ++ tailWord_955848) baseStart_955848 baseEnd_955848 := by
    simpa [prefixWord, tailWord_955848, baseEnd_955848] using wordTrace_append hprefix tailTrace_955848
  have hstable : (prefixWord ++ tailWord_955848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955848).length < 2 ^ (prefixWord ++ tailWord_955848).sum := by decide
  have hdescent : baseEnd_955848 < baseStart_955848 := by decide
  rcases family_descends (prefixWord ++ tailWord_955848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955855 : List Nat := [1, 1, 2, 1, 1, 4, 6, 1, 2, 4]
def baseStart_955855 : Nat := 118140960795 + 955855 * 2 ^ 59
def prefixEnd_955855 : Nat := 4983230072969 + 3 ^ 40 * 955855 * 2
def baseEnd_955855 : Nat := 163604350334487648872203

theorem tailTrace_955855 : CollatzResearch.WordTrace tailWord_955855 prefixEnd_955855 163604350334487648872203 := by
  unfold tailWord_955855
  simp only [CollatzResearch.WordTrace]
  refine ⟨34862895952108056882349019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23241930634738704588232679 34862895952108056882349019)
  ·
    refine ⟨52294343928162085323523529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34862895952108056882349019 52294343928162085323523529)
    ·
      refine ⟨39220757946121563992642647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52294343928162085323523529 39220757946121563992642647)
      ·
        refine ⟨58831136919182345988963971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39220757946121563992642647 58831136919182345988963971)
        ·
          refine ⟨88246705378773518983445957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58831136919182345988963971 88246705378773518983445957)
          ·
            refine ⟨16546257258520034809396117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88246705378773518983445957 16546257258520034809396117)
            ·
              refine ⟨775605808993126631690443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16546257258520034809396117 775605808993126631690443)
              ·
                refine ⟨1163408713489689947535665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 775605808993126631690443 1163408713489689947535665)
                ·
                  refine ⟨872556535117267460651749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1163408713489689947535665 872556535117267460651749)
                  ·
                    refine ⟨163604350334487648872203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 872556535117267460651749 163604350334487648872203)
                    ·
                      rfl

theorem cell23_955855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 2, 4].length) (baseStart_955855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955855 prefixEnd_955855 := by exact prefixLift 955855
  have htrace : WordTrace (prefixWord ++ tailWord_955855) baseStart_955855 baseEnd_955855 := by
    simpa [prefixWord, tailWord_955855, baseEnd_955855] using wordTrace_append hprefix tailTrace_955855
  have hstable : (prefixWord ++ tailWord_955855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955855).length < 2 ^ (prefixWord ++ tailWord_955855).sum := by decide
  have hdescent : baseEnd_955855 < baseStart_955855 := by decide
  rcases family_descends (prefixWord ++ tailWord_955855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955862 : List Nat := [5, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4]
def baseStart_955862 : Nat := 118140960795 + 955862 * 2 ^ 59
def prefixEnd_955862 : Nat := 4983230072969 + 3 ^ 40 * 955862 * 2
def baseEnd_955862 : Nat := 490816645368044419229077

theorem tailTrace_955862 : CollatzResearch.WordTrace tailWord_955862 prefixEnd_955862 490816645368044419229077 := by
  unfold tailWord_955862
  simp only [CollatzResearch.WordTrace]
  refine ⟨2178946953942668567365865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23242100842055131385235893 2178946953942668567365865)
  ·
    refine ⟨1634210215457001425524399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2178946953942668567365865 1634210215457001425524399)
    ·
      refine ⟨2451315323185502138286599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1634210215457001425524399 2451315323185502138286599)
      ·
        refine ⟨3676972984778253207429899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2451315323185502138286599 3676972984778253207429899)
        ·
          refine ⟨5515459477167379811144849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3676972984778253207429899 5515459477167379811144849)
          ·
            refine ⟨4136594607875534858358637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5515459477167379811144849 4136594607875534858358637)
            ·
              refine ⟨1551222977953325571884489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4136594607875534858358637 1551222977953325571884489)
              ·
                refine ⟨1163417233464994178913367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1551222977953325571884489 1163417233464994178913367)
                ·
                  refine ⟨1745125850197491268370051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1163417233464994178913367 1745125850197491268370051)
                  ·
                    refine ⟨2617688775296236902555077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1745125850197491268370051 2617688775296236902555077)
                    ·
                      refine ⟨490816645368044419229077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2617688775296236902555077 490816645368044419229077)
                      ·
                        rfl

theorem cell23_955862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_955862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955862 prefixEnd_955862 := by exact prefixLift 955862
  have htrace : WordTrace (prefixWord ++ tailWord_955862) baseStart_955862 baseEnd_955862 := by
    simpa [prefixWord, tailWord_955862, baseEnd_955862] using wordTrace_append hprefix tailTrace_955862
  have hstable : (prefixWord ++ tailWord_955862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955862).length < 2 ^ (prefixWord ++ tailWord_955862).sum := by decide
  have hdescent : baseEnd_955862 < baseStart_955862 := by decide
  rcases family_descends (prefixWord ++ tailWord_955862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955865 : List Nat := [1, 2, 1, 2, 4, 2, 3, 2, 1, 2, 3]
def baseStart_955865 : Nat := 118140960795 + 955865 * 2 ^ 59
def prefixEnd_955865 : Nat := 4983230072969 + 3 ^ 40 * 955865 * 2
def baseEnd_955865 : Nat := 490818185810007907491563

theorem tailTrace_955865 : CollatzResearch.WordTrace tailWord_955865 prefixEnd_955865 490818185810007907491563 := by
  unfold tailWord_955865
  simp only [CollatzResearch.WordTrace]
  refine ⟨34863260682071828590213049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23242173788047885726808699 34863260682071828590213049)
  ·
    refine ⟨26147445511553871442659787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34863260682071828590213049 26147445511553871442659787)
    ·
      refine ⟨39221168267330807163989681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26147445511553871442659787 39221168267330807163989681)
      ·
        refine ⟨29415876200498105372992261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39221168267330807163989681 29415876200498105372992261)
        ·
          refine ⟨5515476787593394757436049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29415876200498105372992261 5515476787593394757436049)
          ·
            refine ⟨4136607590695046068077037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5515476787593394757436049 4136607590695046068077037)
            ·
              refine ⟨1551227846510642275528889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4136607590695046068077037 1551227846510642275528889)
              ·
                refine ⟨1163420884882981706646667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1551227846510642275528889 1163420884882981706646667)
                ·
                  refine ⟨1745131327324472559970001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1163420884882981706646667 1745131327324472559970001)
                  ·
                    refine ⟨1308848495493354419977501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1745131327324472559970001 1308848495493354419977501)
                    ·
                      refine ⟨490818185810007907491563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1308848495493354419977501 490818185810007907491563)
                      ·
                        rfl

theorem cell23_955865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 2, 3].length) (baseStart_955865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955865 prefixEnd_955865 := by exact prefixLift 955865
  have htrace : WordTrace (prefixWord ++ tailWord_955865) baseStart_955865 baseEnd_955865 := by
    simpa [prefixWord, tailWord_955865, baseEnd_955865] using wordTrace_append hprefix tailTrace_955865
  have hstable : (prefixWord ++ tailWord_955865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955865).length < 2 ^ (prefixWord ++ tailWord_955865).sum := by decide
  have hdescent : baseEnd_955865 < baseStart_955865 := by decide
  rcases family_descends (prefixWord ++ tailWord_955865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955882 : List Nat := [3, 1, 3, 1, 5, 1, 1, 1, 1, 1, 5]
def baseStart_955882 : Nat := 118140960795 + 955882 * 2 ^ 59
def prefixEnd_955882 : Nat := 4983230072969 + 3 ^ 40 * 955882 * 2
def baseEnd_955882 : Nat := 490826914981134340978985

theorem tailTrace_955882 : CollatzResearch.WordTrace tailWord_955882 prefixEnd_955882 490826914981134340978985 := by
  unfold tailWord_955882
  simp only [CollatzResearch.WordTrace]
  refine ⟨8715970180752560123395475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23242587148673493662387933 8715970180752560123395475)
  ·
    refine ⟨13073955271128840185093213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8715970180752560123395475 13073955271128840185093213)
    ·
      refine ⟨4902733226673315069409955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13073955271128840185093213 4902733226673315069409955)
      ·
        refine ⟨7354099840009972604114933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4902733226673315069409955 7354099840009972604114933)
        ·
          refine ⟨689446860000934931635775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7354099840009972604114933 689446860000934931635775)
          ·
            refine ⟨1034170290001402397453663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689446860000934931635775 1034170290001402397453663)
            ·
              refine ⟨1551255435002103596180495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1034170290001402397453663 1551255435002103596180495)
              ·
                refine ⟨2326883152503155394270743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1551255435002103596180495 2326883152503155394270743)
                ·
                  refine ⟨3490324728754733091406115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2326883152503155394270743 3490324728754733091406115)
                  ·
                    refine ⟨5235487093132099637109173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3490324728754733091406115 5235487093132099637109173)
                    ·
                      refine ⟨490826914981134340978985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5235487093132099637109173 490826914981134340978985)
                      ·
                        rfl

theorem cell23_955882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_955882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955882 prefixEnd_955882 := by exact prefixLift 955882
  have htrace : WordTrace (prefixWord ++ tailWord_955882) baseStart_955882 baseEnd_955882 := by
    simpa [prefixWord, tailWord_955882, baseEnd_955882] using wordTrace_append hprefix tailTrace_955882
  have hstable : (prefixWord ++ tailWord_955882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955882).length < 2 ^ (prefixWord ++ tailWord_955882).sum := by decide
  have hdescent : baseEnd_955882 < baseStart_955882 := by decide
  rcases family_descends (prefixWord ++ tailWord_955882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955896 : List Nat := [2, 1, 2, 1, 1, 7, 2, 2, 1, 2, 2]
def baseStart_955896 : Nat := 118140960795 + 955896 * 2 ^ 59
def prefixEnd_955896 : Nat := 4983230072969 + 3 ^ 40 * 955896 * 2
def baseEnd_955896 : Nat := 490834103710297286203921

theorem tailTrace_955896 : CollatzResearch.WordTrace tailWord_955896 prefixEnd_955896 490834103710297286203921 := by
  unfold tailWord_955896
  simp only [CollatzResearch.WordTrace]
  refine ⟨17432195672479760442295771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23242927563306347256394361 17432195672479760442295771)
  ·
    refine ⟨26148293508719640663443657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17432195672479760442295771 26148293508719640663443657)
    ·
      refine ⟨19611220131539730497582743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26148293508719640663443657 19611220131539730497582743)
      ·
        refine ⟨29416830197309595746374115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19611220131539730497582743 29416830197309595746374115)
        ·
          refine ⟨44125245295964393619561173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29416830197309595746374115 44125245295964393619561173)
          ·
            refine ⟨1034185436624165475458465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 44125245295964393619561173 1034185436624165475458465)
            ·
              refine ⟨775639077468124106593849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1034185436624165475458465 775639077468124106593849)
              ·
                refine ⟨581729308101093079945387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 775639077468124106593849 581729308101093079945387)
                ·
                  refine ⟨872593962151639619918081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 581729308101093079945387 872593962151639619918081)
                  ·
                    refine ⟨654445471613729714938561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 872593962151639619918081 654445471613729714938561)
                    ·
                      refine ⟨490834103710297286203921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 654445471613729714938561 490834103710297286203921)
                      ·
                        rfl

theorem cell23_955896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 2, 1, 2, 2].length) (baseStart_955896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955896 prefixEnd_955896 := by exact prefixLift 955896
  have htrace : WordTrace (prefixWord ++ tailWord_955896) baseStart_955896 baseEnd_955896 := by
    simpa [prefixWord, tailWord_955896, baseEnd_955896] using wordTrace_append hprefix tailTrace_955896
  have hstable : (prefixWord ++ tailWord_955896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955896).length < 2 ^ (prefixWord ++ tailWord_955896).sum := by decide
  have hdescent : baseEnd_955896 < baseStart_955896 := by decide
  rcases family_descends (prefixWord ++ tailWord_955896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955902 : List Nat := [4, 2, 2, 3, 1, 2, 1, 8]
def baseStart_955902 : Nat := 118140960795 + 955902 * 2 ^ 59
def prefixEnd_955902 : Nat := 4983230072969 + 3 ^ 40 * 955902 * 2
def baseEnd_955902 : Nat := 18179154984971268989959

theorem tailTrace_955902 : CollatzResearch.WordTrace tailWord_955902 prefixEnd_955902 18179154984971268989959 := by
  unfold tailWord_955902
  simp only [CollatzResearch.WordTrace]
  refine ⟨4358076272867222988663745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23243073455291855939539973 4358076272867222988663745)
  ·
    refine ⟨3268557204650417241497809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4358076272867222988663745 3268557204650417241497809)
    ·
      refine ⟨2451417903487812931123357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3268557204650417241497809 2451417903487812931123357)
      ·
        refine ⟨919281713807929849171259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2451417903487812931123357 919281713807929849171259)
        ·
          refine ⟨1378922570711894773756889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 919281713807929849171259 1378922570711894773756889)
          ·
            refine ⟨1034191928033921080317667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1378922570711894773756889 1034191928033921080317667)
            ·
              refine ⟨1551287892050881620476501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1034191928033921080317667 1551287892050881620476501)
              ·
                refine ⟨18179154984971268989959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1551287892050881620476501 18179154984971268989959)
                ·
                  rfl

theorem cell23_955902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 8].length) (baseStart_955902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955902 prefixEnd_955902 := by exact prefixLift 955902
  have htrace : WordTrace (prefixWord ++ tailWord_955902) baseStart_955902 baseEnd_955902 := by
    simpa [prefixWord, tailWord_955902, baseEnd_955902] using wordTrace_append hprefix tailTrace_955902
  have hstable : (prefixWord ++ tailWord_955902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955902).length < 2 ^ (prefixWord ++ tailWord_955902).sum := by decide
  have hdescent : baseEnd_955902 < baseStart_955902 := by decide
  rcases family_descends (prefixWord ++ tailWord_955902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955935 : List Nat := [1, 1, 2, 4, 1, 1, 4, 2, 1, 4, 2]
def baseStart_955935 : Nat := 118140960795 + 955935 * 2 ^ 59
def prefixEnd_955935 : Nat := 4983230072969 + 3 ^ 40 * 955935 * 2
def baseEnd_955935 : Nat := 490854129455822633616241

theorem tailTrace_955935 : CollatzResearch.WordTrace tailWord_955935 prefixEnd_955935 490854129455822633616241 := by
  unfold tailWord_955935
  simp only [CollatzResearch.WordTrace]
  refine ⟨34865813791818230545261259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23243875861212153696840839 34865813791818230545261259)
  ·
    refine ⟨52298720687727345817891889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34865813791818230545261259 52298720687727345817891889)
    ·
      refine ⟨39224040515795509363418917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52298720687727345817891889 39224040515795509363418917)
      ·
        refine ⟨7354507596711658005641047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39224040515795509363418917 7354507596711658005641047)
        ·
          refine ⟨11031761395067487008461571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7354507596711658005641047 11031761395067487008461571)
          ·
            refine ⟨16547642092601230512692357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11031761395067487008461571 16547642092601230512692357)
            ·
              refine ⟨3102682892362730721129817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16547642092601230512692357 3102682892362730721129817)
              ·
                refine ⟨2327012169272048040847363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3102682892362730721129817 2327012169272048040847363)
                ·
                  refine ⟨3490518253908072061271045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2327012169272048040847363 3490518253908072061271045)
                  ·
                    refine ⟨654472172607763511488321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3490518253908072061271045 654472172607763511488321)
                    ·
                      refine ⟨490854129455822633616241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 654472172607763511488321 490854129455822633616241)
                      ·
                        rfl

theorem cell23_955935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_955935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955935 prefixEnd_955935 := by exact prefixLift 955935
  have htrace : WordTrace (prefixWord ++ tailWord_955935) baseStart_955935 baseEnd_955935 := by
    simpa [prefixWord, tailWord_955935, baseEnd_955935] using wordTrace_append hprefix tailTrace_955935
  have hstable : (prefixWord ++ tailWord_955935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955935).length < 2 ^ (prefixWord ++ tailWord_955935).sum := by decide
  have hdescent : baseEnd_955935 < baseStart_955935 := by decide
  rcases family_descends (prefixWord ++ tailWord_955935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955938 : List Nat := [3, 3, 1, 1, 1, 1, 2, 3, 2, 1, 5]
def baseStart_955938 : Nat := 118140960795 + 955938 * 2 ^ 59
def prefixEnd_955938 : Nat := 4983230072969 + 3 ^ 40 * 955938 * 2
def baseEnd_955938 : Nat := 490855669897786121878727

theorem tailTrace_955938 : CollatzResearch.WordTrace tailWord_955938 prefixEnd_955938 490855669897786121878727 := by
  unfold tailWord_955938
  simp only [CollatzResearch.WordTrace]
  refine ⟨8716480802701840514405117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23243948807204908038413645 8716480802701840514405117)
  ·
    refine ⟨3268680301013190192901919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8716480802701840514405117 3268680301013190192901919)
    ·
      refine ⟨4903020451519785289352879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3268680301013190192901919 4903020451519785289352879)
      ·
        refine ⟨7354530677279677934029319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4903020451519785289352879 7354530677279677934029319)
        ·
          refine ⟨11031796015919516901043979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7354530677279677934029319 11031796015919516901043979)
          ·
            refine ⟨16547694023879275351565969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11031796015919516901043979 16547694023879275351565969)
            ·
              refine ⟨12410770517909456513674477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16547694023879275351565969 12410770517909456513674477)
              ·
                refine ⟨4654038944216046192627929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12410770517909456513674477 4654038944216046192627929)
                ·
                  refine ⟨3490529208162034644470947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4654038944216046192627929 3490529208162034644470947)
                  ·
                    refine ⟨5235793812243051966706421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3490529208162034644470947 5235793812243051966706421)
                    ·
                      refine ⟨490855669897786121878727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5235793812243051966706421 490855669897786121878727)
                      ·
                        rfl

theorem cell23_955938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_955938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955938 prefixEnd_955938 := by exact prefixLift 955938
  have htrace : WordTrace (prefixWord ++ tailWord_955938) baseStart_955938 baseEnd_955938 := by
    simpa [prefixWord, tailWord_955938, baseEnd_955938] using wordTrace_append hprefix tailTrace_955938
  have hstable : (prefixWord ++ tailWord_955938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955938).length < 2 ^ (prefixWord ++ tailWord_955938).sum := by decide
  have hdescent : baseEnd_955938 < baseStart_955938 := by decide
  rcases family_descends (prefixWord ++ tailWord_955938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955941 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 11]
def baseStart_955941 : Nat := 118140960795 + 955941 * 2 ^ 59
def prefixEnd_955941 : Nat := 4983230072969 + 3 ^ 40 * 955941 * 2
def baseEnd_955941 : Nat := 54539690037749956682357

theorem tailTrace_955941 : CollatzResearch.WordTrace tailWord_955941 prefixEnd_955941 54539690037749956682357 := by
  unfold tailWord_955941
  simp only [CollatzResearch.WordTrace]
  refine ⟨34866032629796493569979677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23244021753197662379986451 34866032629796493569979677)
  ·
    refine ⟨13074762236173685088742379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34866032629796493569979677 13074762236173685088742379)
    ·
      refine ⟨19612143354260527633113569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13074762236173685088742379 19612143354260527633113569)
      ·
        refine ⟨14709107515695395724835177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19612143354260527633113569 14709107515695395724835177)
        ·
          refine ⟨11031830636771546793626383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14709107515695395724835177 11031830636771546793626383)
          ·
            refine ⟨16547745955157320190439575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11031830636771546793626383 16547745955157320190439575)
            ·
              refine ⟨24821618932735980285659363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16547745955157320190439575 24821618932735980285659363)
              ·
                refine ⟨37232428399103970428489045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24821618932735980285659363 37232428399103970428489045)
                ·
                  refine ⟨54539690037749956682357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 37232428399103970428489045 54539690037749956682357)
                  ·
                    rfl

theorem cell23_955941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 11].length) (baseStart_955941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955941 prefixEnd_955941 := by exact prefixLift 955941
  have htrace : WordTrace (prefixWord ++ tailWord_955941) baseStart_955941 baseEnd_955941 := by
    simpa [prefixWord, tailWord_955941, baseEnd_955941] using wordTrace_append hprefix tailTrace_955941
  have hstable : (prefixWord ++ tailWord_955941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955941).length < 2 ^ (prefixWord ++ tailWord_955941).sum := by decide
  have hdescent : baseEnd_955941 < baseStart_955941 := by decide
  rcases family_descends (prefixWord ++ tailWord_955941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_955988 : List Nat := [2, 4, 1, 1, 1, 2, 1, 3, 1, 7]
def baseStart_955988 : Nat := 118140960795 + 955988 * 2 ^ 59
def prefixEnd_955988 : Nat := 4983230072969 + 3 ^ 40 * 955988 * 2
def baseEnd_955988 : Nat := 163627114643503642084499

theorem tailTrace_955988 : CollatzResearch.WordTrace tailWord_955988 prefixEnd_955988 163627114643503642084499 := by
  unfold tailWord_955988
  simp only [CollatzResearch.WordTrace]
  refine ⟨17433873430313110298470309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23245164573750813731293745 17433873430313110298470309)
  ·
    refine ⟨3268851268183708180963183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17433873430313110298470309 3268851268183708180963183)
    ·
      refine ⟨4903276902275562271444775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3268851268183708180963183 4903276902275562271444775)
      ·
        refine ⟨7354915353413343407167163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4903276902275562271444775 7354915353413343407167163)
        ·
          refine ⟨11032373030120015110750745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7354915353413343407167163 11032373030120015110750745)
          ·
            refine ⟨8274279772590011333063059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11032373030120015110750745 8274279772590011333063059)
            ·
              refine ⟨12411419658885016999594589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8274279772590011333063059 12411419658885016999594589)
              ·
                refine ⟨4654282372081881374847971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12411419658885016999594589 4654282372081881374847971)
                ·
                  refine ⟨6981423558122822062271957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4654282372081881374847971 6981423558122822062271957)
                  ·
                    refine ⟨163627114643503642084499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6981423558122822062271957 163627114643503642084499)
                    ·
                      rfl

theorem cell23_955988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_955988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_955988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_955988 prefixEnd_955988 := by exact prefixLift 955988
  have htrace : WordTrace (prefixWord ++ tailWord_955988) baseStart_955988 baseEnd_955988 := by
    simpa [prefixWord, tailWord_955988, baseEnd_955988] using wordTrace_append hprefix tailTrace_955988
  have hstable : (prefixWord ++ tailWord_955988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_955988).length < 2 ^ (prefixWord ++ tailWord_955988).sum := by decide
  have hdescent : baseEnd_955988 < baseStart_955988 := by decide
  rcases family_descends (prefixWord ++ tailWord_955988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956005 : List Nat := [1, 3, 1, 3, 3, 2, 1, 2, 2, 5]
def baseStart_956005 : Nat := 118140960795 + 956005 * 2 ^ 59
def prefixEnd_956005 : Nat := 4983230072969 + 3 ^ 40 * 956005 * 2
def baseEnd_956005 : Nat := 163630024367212453246973

theorem tailTrace_956005 : CollatzResearch.WordTrace tailWord_956005 prefixEnd_956005 163630024367212453246973 := by
  unfold tailWord_956005
  simp only [CollatzResearch.WordTrace]
  refine ⟨34868366901564632500309469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23245577934376421666872979 34868366901564632500309469)
  ·
    refine ⟨13075637588086737187616051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34868366901564632500309469 13075637588086737187616051)
    ·
      refine ⟨19613456382130105781424077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13075637588086737187616051 19613456382130105781424077)
      ·
        refine ⟨7355046143298789668034029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19613456382130105781424077 7355046143298789668034029)
        ·
          refine ⟨2758142303737046125512761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7355046143298789668034029 2758142303737046125512761)
          ·
            refine ⟨2068606727802784594134571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2758142303737046125512761 2068606727802784594134571)
            ·
              refine ⟨3102910091704176891201857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2068606727802784594134571 3102910091704176891201857)
              ·
                refine ⟨2327182568778132668401393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3102910091704176891201857 2327182568778132668401393)
                ·
                  refine ⟨1745386926583599501301045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2327182568778132668401393 1745386926583599501301045)
                  ·
                    refine ⟨163630024367212453246973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1745386926583599501301045 163630024367212453246973)
                    ·
                      rfl

theorem cell23_956005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 5].length) (baseStart_956005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956005 prefixEnd_956005 := by exact prefixLift 956005
  have htrace : WordTrace (prefixWord ++ tailWord_956005) baseStart_956005 baseEnd_956005 := by
    simpa [prefixWord, tailWord_956005, baseEnd_956005] using wordTrace_append hprefix tailTrace_956005
  have hstable : (prefixWord ++ tailWord_956005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956005).length < 2 ^ (prefixWord ++ tailWord_956005).sum := by decide
  have hdescent : baseEnd_956005 < baseStart_956005 := by decide
  rcases family_descends (prefixWord ++ tailWord_956005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956025 : List Nat := [1, 2, 1, 3, 3, 1, 2, 1, 1, 6, 2]
def baseStart_956025 : Nat := 118140960795 + 956025 * 2 ^ 59
def prefixEnd_956025 : Nat := 4983230072969 + 3 ^ 40 * 956025 * 2
def baseEnd_956025 : Nat := 490900342714727281490827

theorem tailTrace_956025 : CollatzResearch.WordTrace tailWord_956025 prefixEnd_956025 490900342714727281490827 := by
  unfold tailWord_956025
  simp only [CollatzResearch.WordTrace]
  refine ⟨34869096361492175916037529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23246064240994783944025019 34869096361492175916037529)
  ·
    refine ⟨26151822271119131937028147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34869096361492175916037529 26151822271119131937028147)
    ·
      refine ⟨39227733406678697905542221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26151822271119131937028147 39227733406678697905542221)
      ·
        refine ⟨14710400027504511714578333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39227733406678697905542221 14710400027504511714578333)
        ·
          refine ⟨5516400010314191892966875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14710400027504511714578333 5516400010314191892966875)
          ·
            refine ⟨8274600015471287839450313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5516400010314191892966875 8274600015471287839450313)
            ·
              refine ⟨6205950011603465879587735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8274600015471287839450313 6205950011603465879587735)
              ·
                refine ⟨9308925017405198819381603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6205950011603465879587735 9308925017405198819381603)
                ·
                  refine ⟨13963387526107798229072405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9308925017405198819381603 13963387526107798229072405)
                  ·
                    refine ⟨654533790286303041987769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13963387526107798229072405 654533790286303041987769)
                    ·
                      refine ⟨490900342714727281490827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 654533790286303041987769 490900342714727281490827)
                      ·
                        rfl

theorem cell23_956025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 6, 2].length) (baseStart_956025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956025 prefixEnd_956025 := by exact prefixLift 956025
  have htrace : WordTrace (prefixWord ++ tailWord_956025) baseStart_956025 baseEnd_956025 := by
    simpa [prefixWord, tailWord_956025, baseEnd_956025] using wordTrace_append hprefix tailTrace_956025
  have hstable : (prefixWord ++ tailWord_956025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956025).length < 2 ^ (prefixWord ++ tailWord_956025).sum := by decide
  have hdescent : baseEnd_956025 < baseStart_956025 := by decide
  rcases family_descends (prefixWord ++ tailWord_956025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956042 : List Nat := [3, 1, 2, 3, 2, 2, 2, 1, 2, 1, 4]
def baseStart_956042 : Nat := 118140960795 + 956042 * 2 ^ 59
def prefixEnd_956042 : Nat := 4983230072969 + 3 ^ 40 * 956042 * 2
def baseEnd_956042 : Nat := 490909071885853714978249

theorem tailTrace_956042 : CollatzResearch.WordTrace tailWord_956042 prefixEnd_956042 490909071885853714978249 := by
  unfold tailWord_956042
  simp only [CollatzResearch.WordTrace]
  refine ⟨8717429100607646954851595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23246477601620391879604253 8717429100607646954851595)
  ·
    refine ⟨13076143650911470432277393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8717429100607646954851595 13076143650911470432277393)
    ·
      refine ⟨9807107738183602824208045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13076143650911470432277393 9807107738183602824208045)
      ·
        refine ⟨3677665401818851059078017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9807107738183602824208045 3677665401818851059078017)
        ·
          refine ⟨2758249051364138294308513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3677665401818851059078017 2758249051364138294308513)
          ·
            refine ⟨2068686788523103720731385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2758249051364138294308513 2068686788523103720731385)
            ·
              refine ⟨1551515091392327790548539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2068686788523103720731385 1551515091392327790548539)
              ·
                refine ⟨2327272637088491685822809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1551515091392327790548539 2327272637088491685822809)
                ·
                  refine ⟨1745454477816368764367107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2327272637088491685822809 1745454477816368764367107)
                  ·
                    refine ⟨2618181716724553146550661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1745454477816368764367107 2618181716724553146550661)
                    ·
                      refine ⟨490909071885853714978249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2618181716724553146550661 490909071885853714978249)
                      ·
                        rfl

theorem cell23_956042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_956042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956042 prefixEnd_956042 := by exact prefixLift 956042
  have htrace : WordTrace (prefixWord ++ tailWord_956042) baseStart_956042 baseEnd_956042 := by
    simpa [prefixWord, tailWord_956042, baseEnd_956042] using wordTrace_append hprefix tailTrace_956042
  have hstable : (prefixWord ++ tailWord_956042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956042).length < 2 ^ (prefixWord ++ tailWord_956042).sum := by decide
  have hdescent : baseEnd_956042 < baseStart_956042 := by decide
  rcases family_descends (prefixWord ++ tailWord_956042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956065 : List Nat := [1, 2, 3, 3, 2, 1, 1, 4, 6]
def baseStart_956065 : Nat := 118140960795 + 956065 * 2 ^ 59
def prefixEnd_956065 : Nat := 4983230072969 + 3 ^ 40 * 956065 * 2
def baseEnd_956065 : Nat := 54546764660100791665627

theorem tailTrace_956065 : CollatzResearch.WordTrace tailWord_956065 prefixEnd_956065 54546764660100791665627 := by
  unfold tailWord_956065
  simp only [CollatzResearch.WordTrace]
  refine ⟨34870555281347262747493649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23247036854231508498329099 34870555281347262747493649)
  ·
    refine ⟨26152916461010447060620237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34870555281347262747493649 26152916461010447060620237)
    ·
      refine ⟨9807343672878917647732589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26152916461010447060620237 9807343672878917647732589)
      ·
        refine ⟨3677753877329594117899721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9807343672878917647732589 3677753877329594117899721)
        ·
          refine ⟨2758315407997195588424791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3677753877329594117899721 2758315407997195588424791)
          ·
            refine ⟨4137473111995793382637187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2758315407997195588424791 4137473111995793382637187)
            ·
              refine ⟨6206209667993690073955781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4137473111995793382637187 6206209667993690073955781)
              ·
                refine ⟨1163664312748816888866709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6206209667993690073955781 1163664312748816888866709)
                ·
                  refine ⟨54546764660100791665627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1163664312748816888866709 54546764660100791665627)
                  ·
                    rfl

theorem cell23_956065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 6].length) (baseStart_956065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956065 prefixEnd_956065 := by exact prefixLift 956065
  have htrace : WordTrace (prefixWord ++ tailWord_956065) baseStart_956065 baseEnd_956065 := by
    simpa [prefixWord, tailWord_956065, baseEnd_956065] using wordTrace_append hprefix tailTrace_956065
  have hstable : (prefixWord ++ tailWord_956065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956065).length < 2 ^ (prefixWord ++ tailWord_956065).sum := by decide
  have hdescent : baseEnd_956065 < baseStart_956065 := by decide
  rcases family_descends (prefixWord ++ tailWord_956065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956069 : List Nat := [1, 3, 1, 2, 1, 2, 6, 2, 1, 4]
def baseStart_956069 : Nat := 118140960795 + 956069 * 2 ^ 59
def prefixEnd_956069 : Nat := 4983230072969 + 3 ^ 40 * 956069 * 2
def baseEnd_956069 : Nat := 163640978621175036446875

theorem tailTrace_956069 : CollatzResearch.WordTrace tailWord_956069 prefixEnd_956069 163640978621175036446875 := by
  unfold tailWord_956069
  simp only [CollatzResearch.WordTrace]
  refine ⟨34870701173332771430639261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23247134115555180953759507 34870701173332771430639261)
  ·
    refine ⟨13076512939999789286489723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34870701173332771430639261 13076512939999789286489723)
    ·
      refine ⟨19614769409999683929734585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13076512939999789286489723 19614769409999683929734585)
      ·
        refine ⟨14711077057499762947300939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19614769409999683929734585 14711077057499762947300939)
        ·
          refine ⟨22066615586249644420951409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14711077057499762947300939 22066615586249644420951409)
          ·
            refine ⟨16549961689687233315713557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22066615586249644420951409 16549961689687233315713557)
            ·
              refine ⟨775779454204089061674073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16549961689687233315713557 775779454204089061674073)
              ·
                refine ⟨581834590653066796255555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 775779454204089061674073 581834590653066796255555)
                ·
                  refine ⟨872751885979600194383333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 581834590653066796255555 872751885979600194383333)
                  ·
                    refine ⟨163640978621175036446875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 872751885979600194383333 163640978621175036446875)
                    ·
                      rfl

theorem cell23_956069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 2, 1, 4].length) (baseStart_956069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956069 prefixEnd_956069 := by exact prefixLift 956069
  have htrace : WordTrace (prefixWord ++ tailWord_956069) baseStart_956069 baseEnd_956069 := by
    simpa [prefixWord, tailWord_956069, baseEnd_956069] using wordTrace_append hprefix tailTrace_956069
  have hstable : (prefixWord ++ tailWord_956069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956069).length < 2 ^ (prefixWord ++ tailWord_956069).sum := by decide
  have hdescent : baseEnd_956069 < baseStart_956069 := by decide
  rcases family_descends (prefixWord ++ tailWord_956069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956092 : List Nat := [2, 2, 2, 3, 1, 2, 1, 1, 5, 1, 3]
def baseStart_956092 : Nat := 118140960795 + 956092 * 2 ^ 59
def prefixEnd_956092 : Nat := 4983230072969 + 3 ^ 40 * 956092 * 2
def baseEnd_956092 : Nat := 490934745918578519353019

theorem tailTrace_956092 : CollatzResearch.WordTrace tailWord_956092 prefixEnd_956092 490934745918578519353019 := by
  unfold tailWord_956092
  simp only [CollatzResearch.WordTrace]
  refine ⟨17435770026124723179363265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23247693368166297572484353 17435770026124723179363265)
  ·
    refine ⟨13076827519593542384522449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17435770026124723179363265 13076827519593542384522449)
    ·
      refine ⟨9807620639695156788391837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13076827519593542384522449 9807620639695156788391837)
      ·
        refine ⟨3677857739885683795646939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9807620639695156788391837 3677857739885683795646939)
        ·
          refine ⟨5516786609828525693470409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3677857739885683795646939 5516786609828525693470409)
          ·
            refine ⟨4137589957371394270102807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5516786609828525693470409 4137589957371394270102807)
            ·
              refine ⟨6206384936057091405154211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4137589957371394270102807 6206384936057091405154211)
              ·
                refine ⟨9309577404085637107731317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6206384936057091405154211 9309577404085637107731317)
                ·
                  refine ⟨872772881633028478849811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9309577404085637107731317 872772881633028478849811)
                  ·
                    refine ⟨1309159322449542718274717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 872772881633028478849811 1309159322449542718274717)
                    ·
                      refine ⟨490934745918578519353019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1309159322449542718274717 490934745918578519353019)
                      ·
                        rfl

theorem cell23_956092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_956092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956092 prefixEnd_956092 := by exact prefixLift 956092
  have htrace : WordTrace (prefixWord ++ tailWord_956092) baseStart_956092 baseEnd_956092 := by
    simpa [prefixWord, tailWord_956092, baseEnd_956092] using wordTrace_append hprefix tailTrace_956092
  have hstable : (prefixWord ++ tailWord_956092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956092).length < 2 ^ (prefixWord ++ tailWord_956092).sum := by decide
  have hdescent : baseEnd_956092 < baseStart_956092 := by decide
  rcases family_descends (prefixWord ++ tailWord_956092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956095 : List Nat := [1, 1, 2, 2, 2, 3, 2, 4, 1, 5]
def baseStart_956095 : Nat := 118140960795 + 956095 * 2 ^ 59
def prefixEnd_956095 : Nat := 4983230072969 + 3 ^ 40 * 956095 * 2
def baseEnd_956095 : Nat := 163645428786847335871835

theorem tailTrace_956095 : CollatzResearch.WordTrace tailWord_956095 prefixEnd_956095 163645428786847335871835 := by
  unfold tailWord_956095
  simp only [CollatzResearch.WordTrace]
  refine ⟨34871649471238577871085739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23247766314159051914057159 34871649471238577871085739)
  ·
    refine ⟨52307474206857866806628609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34871649471238577871085739 52307474206857866806628609)
    ·
      refine ⟨39230605655143400104971457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52307474206857866806628609 39230605655143400104971457)
      ·
        refine ⟨29422954241357550078728593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39230605655143400104971457 29422954241357550078728593)
        ·
          refine ⟨22067215681018162559046445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29422954241357550078728593 22067215681018162559046445)
          ·
            refine ⟨8275205880381810959642417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22067215681018162559046445 8275205880381810959642417)
            ·
              refine ⟨6206404410286358219731813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8275205880381810959642417 6206404410286358219731813)
              ·
                refine ⟨1163700826928692166199715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6206404410286358219731813 1163700826928692166199715)
                ·
                  refine ⟨1745551240393038249299573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1163700826928692166199715 1745551240393038249299573)
                  ·
                    refine ⟨163645428786847335871835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1745551240393038249299573 163645428786847335871835)
                    ·
                      rfl

theorem cell23_956095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 1, 5].length) (baseStart_956095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956095 prefixEnd_956095 := by exact prefixLift 956095
  have htrace : WordTrace (prefixWord ++ tailWord_956095) baseStart_956095 baseEnd_956095 := by
    simpa [prefixWord, tailWord_956095, baseEnd_956095] using wordTrace_append hprefix tailTrace_956095
  have hstable : (prefixWord ++ tailWord_956095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956095).length < 2 ^ (prefixWord ++ tailWord_956095).sum := by decide
  have hdescent : baseEnd_956095 < baseStart_956095 := by decide
  rcases family_descends (prefixWord ++ tailWord_956095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956145 : List Nat := [1, 2, 2, 2, 2, 4, 1, 1, 1, 1, 6]
def baseStart_956145 : Nat := 118140960795 + 956145 * 2 ^ 59
def prefixEnd_956145 : Nat := 4983230072969 + 3 ^ 40 * 956145 * 2
def baseEnd_956145 : Nat := 490961960393266811990275

theorem tailTrace_956145 : CollatzResearch.WordTrace tailWord_956145 prefixEnd_956145 490961960393266811990275 := by
  unfold tailWord_956145
  simp only [CollatzResearch.WordTrace]
  refine ⟨34873473121057436410405889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23248982080704957606937259 34873473121057436410405889)
  ·
    refine ⟨26155104840793077307804417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34873473121057436410405889 26155104840793077307804417)
    ·
      refine ⟨19616328630594807980853313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26155104840793077307804417 19616328630594807980853313)
      ·
        refine ⟨14712246472946105985639985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19616328630594807980853313 14712246472946105985639985)
        ·
          refine ⟨11034184854709579489229989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14712246472946105985639985 11034184854709579489229989)
          ·
            refine ⟨2068909660258046154230623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11034184854709579489229989 2068909660258046154230623)
            ·
              refine ⟨3103364490387069231345935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2068909660258046154230623 3103364490387069231345935)
              ·
                refine ⟨4655046735580603847018903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3103364490387069231345935 4655046735580603847018903)
                ·
                  refine ⟨6982570103370905770528355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4655046735580603847018903 6982570103370905770528355)
                  ·
                    refine ⟨10473855155056358655792533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6982570103370905770528355 10473855155056358655792533)
                    ·
                      refine ⟨490961960393266811990275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10473855155056358655792533 490961960393266811990275)
                      ·
                        rfl

theorem cell23_956145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_956145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956145 prefixEnd_956145 := by exact prefixLift 956145
  have htrace : WordTrace (prefixWord ++ tailWord_956145) baseStart_956145 baseEnd_956145 := by
    simpa [prefixWord, tailWord_956145, baseEnd_956145] using wordTrace_append hprefix tailTrace_956145
  have hstable : (prefixWord ++ tailWord_956145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956145).length < 2 ^ (prefixWord ++ tailWord_956145).sum := by decide
  have hdescent : baseEnd_956145 < baseStart_956145 := by decide
  rcases family_descends (prefixWord ++ tailWord_956145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956162 : List Nat := [3, 4, 1, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_956162 : Nat := 118140960795 + 956162 * 2 ^ 59
def prefixEnd_956162 : Nat := 4983230072969 + 3 ^ 40 * 956162 * 2
def baseEnd_956162 : Nat := 490970689564393245477697

theorem tailTrace_956162 : CollatzResearch.WordTrace tailWord_956162 prefixEnd_956162 490970689564393245477697 := by
  unfold tailWord_956162
  simp only [CollatzResearch.WordTrace]
  refine ⟨8718523290498962078443685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23249395441330565542516493 8718523290498962078443685)
  ·
    refine ⟨1634723116968555389708191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8718523290498962078443685 1634723116968555389708191)
    ·
      refine ⟨2452084675452833084562287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1634723116968555389708191 2452084675452833084562287)
      ·
        refine ⟨3678127013179249626843431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2452084675452833084562287 3678127013179249626843431)
        ·
          refine ⟨5517190519768874440265147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3678127013179249626843431 5517190519768874440265147)
          ·
            refine ⟨8275785779653311660397721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5517190519768874440265147 8275785779653311660397721)
            ·
              refine ⟨6206839334739983745298291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8275785779653311660397721 6206839334739983745298291)
              ·
                refine ⟨9310259002109975617947437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6206839334739983745298291 9310259002109975617947437)
                ·
                  refine ⟨3491347125791240856730289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9310259002109975617947437 3491347125791240856730289)
                  ·
                    refine ⟨2618510344343430642547717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3491347125791240856730289 2618510344343430642547717)
                    ·
                      refine ⟨490970689564393245477697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2618510344343430642547717 490970689564393245477697)
                      ·
                        rfl

theorem cell23_956162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_956162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956162 prefixEnd_956162 := by exact prefixLift 956162
  have htrace : WordTrace (prefixWord ++ tailWord_956162) baseStart_956162 baseEnd_956162 := by
    simpa [prefixWord, tailWord_956162, baseEnd_956162] using wordTrace_append hprefix tailTrace_956162
  have hstable : (prefixWord ++ tailWord_956162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956162).length < 2 ^ (prefixWord ++ tailWord_956162).sum := by decide
  have hdescent : baseEnd_956162 < baseStart_956162 := by decide
  rcases family_descends (prefixWord ++ tailWord_956162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956209 : List Nat := [1, 2, 2, 3, 2, 3, 1, 1, 3, 3, 2]
def baseStart_956209 : Nat := 118140960795 + 956209 * 2 ^ 59
def prefixEnd_956209 : Nat := 4983230072969 + 3 ^ 40 * 956209 * 2
def baseEnd_956209 : Nat := 490994823155154561589981

theorem tailTrace_956209 : CollatzResearch.WordTrace tailWord_956209 prefixEnd_956209 490994823155154561589981 := by
  unfold tailWord_956209
  simp only [CollatzResearch.WordTrace]
  refine ⟨34875807392825575340735681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23250538261883716893823787 34875807392825575340735681)
  ·
    refine ⟨26156855544619181505551761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34875807392825575340735681 26156855544619181505551761)
    ·
      refine ⟨19617641658464386129163821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26156855544619181505551761 19617641658464386129163821)
      ·
        refine ⟨7356615621924144798436433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19617641658464386129163821 7356615621924144798436433)
        ·
          refine ⟨5517461716443108598827325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7356615621924144798436433 5517461716443108598827325)
          ·
            refine ⟨2069048143666165724560247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5517461716443108598827325 2069048143666165724560247)
            ·
              refine ⟨3103572215499248586840371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2069048143666165724560247 3103572215499248586840371)
              ·
                refine ⟨4655358323248872880260557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3103572215499248586840371 4655358323248872880260557)
                ·
                  refine ⟨1745759371218327330097709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4655358323248872880260557 1745759371218327330097709)
                  ·
                    refine ⟨654659764206872748786641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1745759371218327330097709 654659764206872748786641)
                    ·
                      refine ⟨490994823155154561589981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 654659764206872748786641 490994823155154561589981)
                      ·
                        rfl

theorem cell23_956209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_956209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956209 prefixEnd_956209 := by exact prefixLift 956209
  have htrace : WordTrace (prefixWord ++ tailWord_956209) baseStart_956209 baseEnd_956209 := by
    simpa [prefixWord, tailWord_956209, baseEnd_956209] using wordTrace_append hprefix tailTrace_956209
  have hstable : (prefixWord ++ tailWord_956209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956209).length < 2 ^ (prefixWord ++ tailWord_956209).sum := by decide
  have hdescent : baseEnd_956209 < baseStart_956209 := by decide
  rcases family_descends (prefixWord ++ tailWord_956209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956242 : List Nat := [3, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3]
def baseStart_956242 : Nat := 118140960795 + 956242 * 2 ^ 59
def prefixEnd_956242 : Nat := 4983230072969 + 3 ^ 40 * 956242 * 2
def baseEnd_956242 : Nat := 491011768016752932477329

theorem tailTrace_956242 : CollatzResearch.WordTrace tailWord_956242 prefixEnd_956242 491011768016752932477329 := by
  unfold tailWord_956242
  simp only [CollatzResearch.WordTrace]
  refine ⟨8719252750426505494171745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23251340667804014651124653 8719252750426505494171745)
  ·
    refine ⟨6539439562819879120628809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8719252750426505494171745 6539439562819879120628809)
    ·
      refine ⟨4904579672114909340471607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6539439562819879120628809 4904579672114909340471607)
      ·
        refine ⟨7356869508172364010707411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4904579672114909340471607 7356869508172364010707411)
        ·
          refine ⟨11035304262258546016061117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7356869508172364010707411 11035304262258546016061117)
          ·
            refine ⟨4138239098346954756022919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11035304262258546016061117 4138239098346954756022919)
            ·
              refine ⟨6207358647520432134034379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4138239098346954756022919 6207358647520432134034379)
              ·
                refine ⟨9311037971280648201051569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6207358647520432134034379 9311037971280648201051569)
                ·
                  refine ⟨6983278478460486150788677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9311037971280648201051569 6983278478460486150788677)
                  ·
                    refine ⟨1309364714711341153272877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6983278478460486150788677 1309364714711341153272877)
                    ·
                      refine ⟨491011768016752932477329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1309364714711341153272877 491011768016752932477329)
                      ·
                        rfl

theorem cell23_956242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_956242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956242 prefixEnd_956242 := by exact prefixLift 956242
  have htrace : WordTrace (prefixWord ++ tailWord_956242) baseStart_956242 baseEnd_956242 := by
    simpa [prefixWord, tailWord_956242, baseEnd_956242] using wordTrace_append hprefix tailTrace_956242
  have hstable : (prefixWord ++ tailWord_956242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956242).length < 2 ^ (prefixWord ++ tailWord_956242).sum := by decide
  have hdescent : baseEnd_956242 < baseStart_956242 := by decide
  rcases family_descends (prefixWord ++ tailWord_956242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956256 : List Nat := [2, 1, 1, 3, 3, 2, 2, 3, 2, 2, 2]
def baseStart_956256 : Nat := 118140960795 + 956256 * 2 ^ 59
def prefixEnd_956256 : Nat := 4983230072969 + 3 ^ 40 * 956256 * 2
def baseEnd_956256 : Nat := 491018956745915877702265

theorem tailTrace_956256 : CollatzResearch.WordTrace tailWord_956256 prefixEnd_956256 491018956745915877702265 := by
  unfold tailWord_956256
  simp only [CollatzResearch.WordTrace]
  refine ⟨17438760811827651183848311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23251681082436868245131081 17438760811827651183848311)
  ·
    refine ⟨26158141217741476775772467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17438760811827651183848311 26158141217741476775772467)
    ·
      refine ⟨39237211826612215163658701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26158141217741476775772467 39237211826612215163658701)
      ·
        refine ⟨14713954434979580686372013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39237211826612215163658701 14713954434979580686372013)
        ·
          refine ⟨5517732913117342757389505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14713954434979580686372013 5517732913117342757389505)
          ·
            refine ⟨4138299684838007068042129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5517732913117342757389505 4138299684838007068042129)
            ·
              refine ⟨3103724763628505301031597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4138299684838007068042129 3103724763628505301031597)
              ·
                refine ⟨1163896786360689487886849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3103724763628505301031597 1163896786360689487886849)
                ·
                  refine ⟨872922589770517115915137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1163896786360689487886849 872922589770517115915137)
                  ·
                    refine ⟨654691942327887836936353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 872922589770517115915137 654691942327887836936353)
                    ·
                      refine ⟨491018956745915877702265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 654691942327887836936353 491018956745915877702265)
                      ·
                        rfl

theorem cell23_956256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 2, 2, 2].length) (baseStart_956256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956256 prefixEnd_956256 := by exact prefixLift 956256
  have htrace : WordTrace (prefixWord ++ tailWord_956256) baseStart_956256 baseEnd_956256 := by
    simpa [prefixWord, tailWord_956256, baseEnd_956256] using wordTrace_append hprefix tailTrace_956256
  have hstable : (prefixWord ++ tailWord_956256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956256).length < 2 ^ (prefixWord ++ tailWord_956256).sum := by decide
  have hdescent : baseEnd_956256 < baseStart_956256 := by decide
  rcases family_descends (prefixWord ++ tailWord_956256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956292 : List Nat := [2, 3, 2, 1, 1, 1, 2, 4, 2, 5]
def baseStart_956292 : Nat := 118140960795 + 956292 * 2 ^ 59
def prefixEnd_956292 : Nat := 4983230072969 + 3 ^ 40 * 956292 * 2
def baseEnd_956292 : Nat := 163679147349825912284033

theorem tailTrace_956292 : CollatzResearch.WordTrace tailWord_956292 prefixEnd_956292 163679147349825912284033 := by
  unfold tailWord_956292
  simp only [CollatzResearch.WordTrace]
  refine ⟨17439417325762440258003565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23252556434349920344004753 17439417325762440258003565)
  ·
    refine ⟨6539781497160915096751337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17439417325762440258003565 6539781497160915096751337)
    ·
      refine ⟨4904836122870686322563503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6539781497160915096751337 4904836122870686322563503)
      ·
        refine ⟨7357254184306029483845255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4904836122870686322563503 7357254184306029483845255)
        ·
          refine ⟨11035881276459044225767883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7357254184306029483845255 11035881276459044225767883)
          ·
            refine ⟨16553821914688566338651825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11035881276459044225767883 16553821914688566338651825)
            ·
              refine ⟨12415366436016424753988869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16553821914688566338651825 12415366436016424753988869)
              ·
                refine ⟨2327881206753079641372913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12415366436016424753988869 2327881206753079641372913)
                ·
                  refine ⟨1745910905064809731029685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2327881206753079641372913 1745910905064809731029685)
                  ·
                    refine ⟨163679147349825912284033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1745910905064809731029685 163679147349825912284033)
                    ·
                      rfl

theorem cell23_956292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_956292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956292 prefixEnd_956292 := by exact prefixLift 956292
  have htrace : WordTrace (prefixWord ++ tailWord_956292) baseStart_956292 baseEnd_956292 := by
    simpa [prefixWord, tailWord_956292, baseEnd_956292] using wordTrace_append hprefix tailTrace_956292
  have hstable : (prefixWord ++ tailWord_956292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956292).length < 2 ^ (prefixWord ++ tailWord_956292).sum := by decide
  have hdescent : baseEnd_956292 < baseStart_956292 := by decide
  rcases family_descends (prefixWord ++ tailWord_956292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956335 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 10]
def baseStart_956335 : Nat := 118140960795 + 956335 * 2 ^ 59
def prefixEnd_956335 : Nat := 4983230072969 + 3 ^ 40 * 956335 * 2
def baseEnd_956335 : Nat := 54562169079735674290489

theorem tailTrace_956335 : CollatzResearch.WordTrace tailWord_956335 prefixEnd_956335 54562169079735674290489 := by
  unfold tailWord_956335
  simp only [CollatzResearch.WordTrace]
  refine ⟨34880402990369098859822459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23253601993579399239881639 34880402990369098859822459)
  ·
    refine ⟨52320604485553648289733689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34880402990369098859822459 52320604485553648289733689)
    ·
      refine ⟨39240453364165236217300267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52320604485553648289733689 39240453364165236217300267)
      ·
        refine ⟨58860680046247854325950401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39240453364165236217300267 58860680046247854325950401)
        ·
          refine ⟨44145510034685890744462801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58860680046247854325950401 44145510034685890744462801)
          ·
            refine ⟨33109132526014418058347101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44145510034685890744462801 33109132526014418058347101)
            ·
              refine ⟨12415924697255406771880163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33109132526014418058347101 12415924697255406771880163)
              ·
                refine ⟨18623887045883110157820245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12415924697255406771880163 18623887045883110157820245)
                ·
                  refine ⟨54562169079735674290489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 18623887045883110157820245 54562169079735674290489)
                  ·
                    rfl

theorem cell23_956335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 10].length) (baseStart_956335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956335 prefixEnd_956335 := by exact prefixLift 956335
  have htrace : WordTrace (prefixWord ++ tailWord_956335) baseStart_956335 baseEnd_956335 := by
    simpa [prefixWord, tailWord_956335, baseEnd_956335] using wordTrace_append hprefix tailTrace_956335
  have hstable : (prefixWord ++ tailWord_956335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956335).length < 2 ^ (prefixWord ++ tailWord_956335).sum := by decide
  have hdescent : baseEnd_956335 < baseStart_956335 := by decide
  rcases family_descends (prefixWord ++ tailWord_956335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956349 : List Nat := [1, 4, 1, 2, 3, 1, 1, 1, 4, 2, 3]
def baseStart_956349 : Nat := 118140960795 + 956349 * 2 ^ 59
def prefixEnd_956349 : Nat := 4983230072969 + 3 ^ 40 * 956349 * 2
def baseEnd_956349 : Nat := 491066710446784013839337

theorem tailTrace_956349 : CollatzResearch.WordTrace tailWord_956349 prefixEnd_956349 491066710446784013839337 := by
  unfold tailWord_956349
  simp only [CollatzResearch.WordTrace]
  refine ⟨34880913612318379250832101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23253942408212252833888067 34880913612318379250832101)
  ·
    refine ⟨6540171302309696109531019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34880913612318379250832101 6540171302309696109531019)
    ·
      refine ⟨9810256953464544164296529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6540171302309696109531019 9810256953464544164296529)
      ·
        refine ⟨7357692715098408123222397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9810256953464544164296529 7357692715098408123222397)
        ·
          refine ⟨2759134768161903046208399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7357692715098408123222397 2759134768161903046208399)
          ·
            refine ⟨4138702152242854569312599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2759134768161903046208399 4138702152242854569312599)
            ·
              refine ⟨6208053228364281853968899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4138702152242854569312599 6208053228364281853968899)
              ·
                refine ⟨9312079842546422780953349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6208053228364281853968899 9312079842546422780953349)
                ·
                  refine ⟨1746014970477454271428753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9312079842546422780953349 1746014970477454271428753)
                  ·
                    refine ⟨1309511227858090703571565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1746014970477454271428753 1309511227858090703571565)
                    ·
                      refine ⟨491066710446784013839337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1309511227858090703571565 491066710446784013839337)
                      ·
                        rfl

theorem cell23_956349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_956349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956349 prefixEnd_956349 := by exact prefixLift 956349
  have htrace : WordTrace (prefixWord ++ tailWord_956349) baseStart_956349 baseEnd_956349 := by
    simpa [prefixWord, tailWord_956349, baseEnd_956349] using wordTrace_append hprefix tailTrace_956349
  have hstable : (prefixWord ++ tailWord_956349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956349).length < 2 ^ (prefixWord ++ tailWord_956349).sum := by decide
  have hdescent : baseEnd_956349 < baseStart_956349 := by decide
  rcases family_descends (prefixWord ++ tailWord_956349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956352 : List Nat := [2, 1, 1, 2, 3, 2, 2, 4, 6]
def baseStart_956352 : Nat := 118140960795 + 956352 * 2 ^ 59
def prefixEnd_956352 : Nat := 4983230072969 + 3 ^ 40 * 956352 * 2
def baseEnd_956352 : Nat := 54563138987638611344647

theorem tailTrace_956352 : CollatzResearch.WordTrace tailWord_956352 prefixEnd_956352 54563138987638611344647 := by
  unfold tailWord_956352
  simp only [CollatzResearch.WordTrace]
  refine ⟨17440511515653755381595655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23254015354205007175460873 17440511515653755381595655)
  ·
    refine ⟨26160767273480633072393483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17440511515653755381595655 26160767273480633072393483)
    ·
      refine ⟨39241150910220949608590225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26160767273480633072393483 39241150910220949608590225)
      ·
        refine ⟨29430863182665712206442669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39241150910220949608590225 29430863182665712206442669)
        ·
          refine ⟨11036573693499642077416001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29430863182665712206442669 11036573693499642077416001)
          ·
            refine ⟨8277430270124731558062001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11036573693499642077416001 8277430270124731558062001)
            ·
              refine ⟨6208072702593548668546501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8277430270124731558062001 6208072702593548668546501)
              ·
                refine ⟨1164013631736290375352469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6208072702593548668546501 1164013631736290375352469)
                ·
                  refine ⟨54563138987638611344647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1164013631736290375352469 54563138987638611344647)
                  ·
                    rfl

theorem cell23_956352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 6].length) (baseStart_956352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956352 prefixEnd_956352 := by exact prefixLift 956352
  have htrace : WordTrace (prefixWord ++ tailWord_956352) baseStart_956352 baseEnd_956352 := by
    simpa [prefixWord, tailWord_956352, baseEnd_956352] using wordTrace_append hprefix tailTrace_956352
  have hstable : (prefixWord ++ tailWord_956352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956352).length < 2 ^ (prefixWord ++ tailWord_956352).sum := by decide
  have hdescent : baseEnd_956352 < baseStart_956352 := by decide
  rcases family_descends (prefixWord ++ tailWord_956352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956380 : List Nat := [2, 2, 6, 1, 1, 1, 2, 1, 2, 1, 4]
def baseStart_956380 : Nat := 118140960795 + 956380 * 2 ^ 59
def prefixEnd_956380 : Nat := 4983230072969 + 3 ^ 40 * 956380 * 2
def baseEnd_956380 : Nat := 491082628347073392551695

theorem tailTrace_956380 : CollatzResearch.WordTrace tailWord_956380 prefixEnd_956380 491082628347073392551695 := by
  unfold tailWord_956380
  simp only [CollatzResearch.WordTrace]
  refine ⟨17441022137603035772605297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23254696183470714363473729 17441022137603035772605297)
  ·
    refine ⟨13080766603202276829453973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17441022137603035772605297 13080766603202276829453973)
    ·
      refine ⟨613160934525106726380655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13080766603202276829453973 613160934525106726380655)
      ·
        refine ⟨919741401787660089570983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613160934525106726380655 919741401787660089570983)
        ·
          refine ⟨1379612102681490134356475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 919741401787660089570983 1379612102681490134356475)
          ·
            refine ⟨2069418154022235201534713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1379612102681490134356475 2069418154022235201534713)
            ·
              refine ⟨1552063615516676401151035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2069418154022235201534713 1552063615516676401151035)
              ·
                refine ⟨2328095423275014601726553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1552063615516676401151035 2328095423275014601726553)
                ·
                  refine ⟨1746071567456260951294915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2328095423275014601726553 1746071567456260951294915)
                  ·
                    refine ⟨2619107351184391426942373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1746071567456260951294915 2619107351184391426942373)
                    ·
                      refine ⟨491082628347073392551695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2619107351184391426942373 491082628347073392551695)
                      ·
                        rfl

theorem cell23_956380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_956380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956380 prefixEnd_956380 := by exact prefixLift 956380
  have htrace : WordTrace (prefixWord ++ tailWord_956380) baseStart_956380 baseEnd_956380 := by
    simpa [prefixWord, tailWord_956380, baseEnd_956380] using wordTrace_append hprefix tailTrace_956380
  have hstable : (prefixWord ++ tailWord_956380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956380).length < 2 ^ (prefixWord ++ tailWord_956380).sum := by decide
  have hdescent : baseEnd_956380 < baseStart_956380 := by decide
  rcases family_descends (prefixWord ++ tailWord_956380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956412 : List Nat := [2, 2, 2, 1, 2, 2, 1, 2, 3, 6]
def baseStart_956412 : Nat := 118140960795 + 956412 * 2 ^ 59
def prefixEnd_956412 : Nat := 4983230072969 + 3 ^ 40 * 956412 * 2
def baseEnd_956412 : Nat := 163699686576005755783849

theorem tailTrace_956412 : CollatzResearch.WordTrace tailWord_956412 prefixEnd_956412 163699686576005755783849 := by
  unfold tailWord_956412
  simp only [CollatzResearch.WordTrace]
  refine ⟨17441605705545070505187745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23255474274060094006916993 17441605705545070505187745)
  ·
    refine ⟨13081204279158802878890809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17441605705545070505187745 13081204279158802878890809)
    ·
      refine ⟨9810903209369102159168107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13081204279158802878890809 9810903209369102159168107)
      ·
        refine ⟨14716354814053653238752161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9810903209369102159168107 14716354814053653238752161)
        ·
          refine ⟨11037266110540239929064121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14716354814053653238752161 11037266110540239929064121)
          ·
            refine ⟨8277949582905179946798091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11037266110540239929064121 8277949582905179946798091)
            ·
              refine ⟨12416924374357769920197137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8277949582905179946798091 12416924374357769920197137)
              ·
                refine ⟨9312693280768327440147853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12416924374357769920197137 9312693280768327440147853)
                ·
                  refine ⟨3492259980288122790055445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9312693280768327440147853 3492259980288122790055445)
                  ·
                    refine ⟨163699686576005755783849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3492259980288122790055445 163699686576005755783849)
                    ·
                      rfl

theorem cell23_956412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_956412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956412 prefixEnd_956412 := by exact prefixLift 956412
  have htrace : WordTrace (prefixWord ++ tailWord_956412) baseStart_956412 baseEnd_956412 := by
    simpa [prefixWord, tailWord_956412, baseEnd_956412] using wordTrace_append hprefix tailTrace_956412
  have hstable : (prefixWord ++ tailWord_956412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956412).length < 2 ^ (prefixWord ++ tailWord_956412).sum := by decide
  have hdescent : baseEnd_956412 < baseStart_956412 := by decide
  rcases family_descends (prefixWord ++ tailWord_956412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956432 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 4]
def baseStart_956432 : Nat := 118140960795 + 956432 * 2 ^ 59
def prefixEnd_956432 : Nat := 4983230072969 + 3 ^ 40 * 956432 * 2
def baseEnd_956432 : Nat := 491109329341107189101455

theorem tailTrace_956432 : CollatzResearch.WordTrace tailWord_956432 prefixEnd_956432 491109329341107189101455 := by
  unfold tailWord_956432
  simp only [CollatzResearch.WordTrace]
  refine ⟨17441970435508842213051775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23255960580678456284069033 17441970435508842213051775)
  ·
    refine ⟨26162955653263263319577663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17441970435508842213051775 26162955653263263319577663)
    ·
      refine ⟨39244433479894894979366495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26162955653263263319577663 39244433479894894979366495)
      ·
        refine ⟨58866650219842342469049743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39244433479894894979366495 58866650219842342469049743)
        ·
          refine ⟨88299975329763513703574615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58866650219842342469049743 88299975329763513703574615)
          ·
            refine ⟨132449962994645270555361923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88299975329763513703574615 132449962994645270555361923)
            ·
              refine ⟨198674944491967905833042885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132449962994645270555361923 198674944491967905833042885)
              ·
                refine ⟨37251552092243982343695541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198674944491967905833042885 37251552092243982343695541)
                ·
                  refine ⟨3492333008647873344721457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37251552092243982343695541 3492333008647873344721457)
                  ·
                    refine ⟨2619249756485905008541093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3492333008647873344721457 2619249756485905008541093)
                    ·
                      refine ⟨491109329341107189101455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2619249756485905008541093 491109329341107189101455)
                      ·
                        rfl

theorem cell23_956432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 4].length) (baseStart_956432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956432 prefixEnd_956432 := by exact prefixLift 956432
  have htrace : WordTrace (prefixWord ++ tailWord_956432) baseStart_956432 baseEnd_956432 := by
    simpa [prefixWord, tailWord_956432, baseEnd_956432] using wordTrace_append hprefix tailTrace_956432
  have hstable : (prefixWord ++ tailWord_956432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956432).length < 2 ^ (prefixWord ++ tailWord_956432).sum := by decide
  have hdescent : baseEnd_956432 < baseStart_956432 := by decide
  rcases family_descends (prefixWord ++ tailWord_956432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956453 : List Nat := [1, 3, 1, 2, 2, 5, 2, 1, 1, 1, 4]
def baseStart_956453 : Nat := 118140960795 + 956453 * 2 ^ 59
def prefixEnd_956453 : Nat := 4983230072969 + 3 ^ 40 * 956453 * 2
def baseEnd_956453 : Nat := 491120112434851606938859

theorem tailTrace_956453 : CollatzResearch.WordTrace tailWord_956453 prefixEnd_956453 491120112434851606938859 := by
  unfold tailWord_956453
  simp only [CollatzResearch.WordTrace]
  refine ⟨34884706803941605012618013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23256471202627736675078675 34884706803941605012618013)
  ·
    refine ⟨13081765051478101879731755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34884706803941605012618013 13081765051478101879731755)
    ·
      refine ⟨19622647577217152819597633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13081765051478101879731755 19622647577217152819597633)
      ·
        refine ⟨14716985682912864614698225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19622647577217152819597633 14716985682912864614698225)
        ·
          refine ⟨11037739262184648461023669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14716985682912864614698225 11037739262184648461023669)
          ·
            refine ⟨1034788055829810793220969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11037739262184648461023669 1034788055829810793220969)
            ·
              refine ⟨776091041872358094915727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1034788055829810793220969 776091041872358094915727)
              ·
                refine ⟨1164136562808537142373591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 776091041872358094915727 1164136562808537142373591)
                ·
                  refine ⟨1746204844212805713560387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1164136562808537142373591 1746204844212805713560387)
                  ·
                    refine ⟨2619307266319208570340581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1746204844212805713560387 2619307266319208570340581)
                    ·
                      refine ⟨491120112434851606938859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2619307266319208570340581 491120112434851606938859)
                      ·
                        rfl

theorem cell23_956453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 1, 1, 4].length) (baseStart_956453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956453 prefixEnd_956453 := by exact prefixLift 956453
  have htrace : WordTrace (prefixWord ++ tailWord_956453) baseStart_956453 baseEnd_956453 := by
    simpa [prefixWord, tailWord_956453, baseEnd_956453] using wordTrace_append hprefix tailTrace_956453
  have hstable : (prefixWord ++ tailWord_956453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956453).length < 2 ^ (prefixWord ++ tailWord_956453).sum := by decide
  have hdescent : baseEnd_956453 < baseStart_956453 := by decide
  rcases family_descends (prefixWord ++ tailWord_956453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956469 : List Nat := [1, 3, 3, 1, 1, 1, 2, 2, 3, 3, 3]
def baseStart_956469 : Nat := 118140960795 + 956469 * 2 ^ 59
def prefixEnd_956469 : Nat := 4983230072969 + 3 ^ 40 * 956469 * 2
def baseEnd_956469 : Nat := 491128328125323544338785

theorem tailTrace_956469 : CollatzResearch.WordTrace tailWord_956469 prefixEnd_956469 491128328125323544338785 := by
  unfold tailWord_956469
  simp only [CollatzResearch.WordTrace]
  refine ⟨34885290371883639745200461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23256860247922426496800307 34885290371883639745200461)
  ·
    refine ⟨13081983889456364904450173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34885290371883639745200461 13081983889456364904450173)
    ·
      refine ⟨4905743958546136839168815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13081983889456364904450173 4905743958546136839168815)
      ·
        refine ⟨7358615937819205258753223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4905743958546136839168815 7358615937819205258753223)
        ·
          refine ⟨11037923906728807888129835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7358615937819205258753223 11037923906728807888129835)
          ·
            refine ⟨16556885860093211832194753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11037923906728807888129835 16556885860093211832194753)
            ·
              refine ⟨12417664395069908874146065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16556885860093211832194753 12417664395069908874146065)
              ·
                refine ⟨9313248296302431655609549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12417664395069908874146065 9313248296302431655609549)
                ·
                  refine ⟨3492468111113411870853581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9313248296302431655609549 3492468111113411870853581)
                  ·
                    refine ⟨1309675541667529451570093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3492468111113411870853581 1309675541667529451570093)
                    ·
                      refine ⟨491128328125323544338785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1309675541667529451570093 491128328125323544338785)
                      ·
                        rfl

theorem cell23_956469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_956469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956469 prefixEnd_956469 := by exact prefixLift 956469
  have htrace : WordTrace (prefixWord ++ tailWord_956469) baseStart_956469 baseEnd_956469 := by
    simpa [prefixWord, tailWord_956469, baseEnd_956469] using wordTrace_append hprefix tailTrace_956469
  have hstable : (prefixWord ++ tailWord_956469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956469).length < 2 ^ (prefixWord ++ tailWord_956469).sum := by decide
  have hdescent : baseEnd_956469 < baseStart_956469 := by decide
  rcases family_descends (prefixWord ++ tailWord_956469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956470 : List Nat := [5, 1, 2, 1, 1, 1, 4, 1, 3, 2, 2]
def baseStart_956470 : Nat := 118140960795 + 956470 * 2 ^ 59
def prefixEnd_956470 : Nat := 4983230072969 + 3 ^ 40 * 956470 * 2
def baseEnd_956470 : Nat := 491128841605978040426281

theorem tailTrace_956470 : CollatzResearch.WordTrace tailWord_956470 prefixEnd_956470 491128841605978040426281 := by
  unfold tailWord_956470
  simp only [CollatzResearch.WordTrace]
  refine ⟨2180332927805001057249179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23256884563253344610657909 2180332927805001057249179)
  ·
    refine ⟨3270499391707501585873769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2180332927805001057249179 3270499391707501585873769)
    ·
      refine ⟨2452874543780626189405327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3270499391707501585873769 2452874543780626189405327)
      ·
        refine ⟨3679311815670939284107991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2452874543780626189405327 3679311815670939284107991)
        ·
          refine ⟨5518967723506408926161987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3679311815670939284107991 5518967723506408926161987)
          ·
            refine ⟨8278451585259613389242981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5518967723506408926161987 8278451585259613389242981)
            ·
              refine ⟨1552209672236177510483059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8278451585259613389242981 1552209672236177510483059)
              ·
                refine ⟨2328314508354266265724589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1552209672236177510483059 2328314508354266265724589)
                ·
                  refine ⟨873117940632849849646721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2328314508354266265724589 873117940632849849646721)
                  ·
                    refine ⟨654838455474637387235041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 873117940632849849646721 654838455474637387235041)
                    ·
                      refine ⟨491128841605978040426281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 654838455474637387235041 491128841605978040426281)
                      ·
                        rfl

theorem cell23_956470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_956470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956470 prefixEnd_956470 := by exact prefixLift 956470
  have htrace : WordTrace (prefixWord ++ tailWord_956470) baseStart_956470 baseEnd_956470 := by
    simpa [prefixWord, tailWord_956470, baseEnd_956470] using wordTrace_append hprefix tailTrace_956470
  have hstable : (prefixWord ++ tailWord_956470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956470).length < 2 ^ (prefixWord ++ tailWord_956470).sum := by decide
  have hdescent : baseEnd_956470 < baseStart_956470 := by decide
  rcases family_descends (prefixWord ++ tailWord_956470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956510 : List Nat := [4, 4, 1, 1, 3, 1, 9]
def baseStart_956510 : Nat := 118140960795 + 956510 * 2 ^ 59
def prefixEnd_956510 : Nat := 4983230072969 + 3 ^ 40 * 956510 * 2
def baseEnd_956510 : Nat := 6063572602866146715137

theorem tailTrace_956510 : CollatzResearch.WordTrace tailWord_956510 prefixEnd_956510 6063572602866146715137 := by
  unfold tailWord_956510
  simp only [CollatzResearch.WordTrace]
  refine ⟨4360848220591887968430373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23257857176490069164961989 4360848220591887968430373)
  ·
    refine ⟨817659041360978994080695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4360848220591887968430373 817659041360978994080695)
    ·
      refine ⟨1226488562041468491121043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 817659041360978994080695 1226488562041468491121043)
      ·
        refine ⟨1839732843062202736681565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1226488562041468491121043 1839732843062202736681565)
        ·
          refine ⟨689899816148326026255587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1839732843062202736681565 689899816148326026255587)
          ·
            refine ⟨1034849724222489039383381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689899816148326026255587 1034849724222489039383381)
            ·
              refine ⟨6063572602866146715137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1034849724222489039383381 6063572602866146715137)
              ·
                rfl

theorem cell23_956510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 9].length) (baseStart_956510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956510 prefixEnd_956510 := by exact prefixLift 956510
  have htrace : WordTrace (prefixWord ++ tailWord_956510) baseStart_956510 baseEnd_956510 := by
    simpa [prefixWord, tailWord_956510, baseEnd_956510] using wordTrace_append hprefix tailTrace_956510
  have hstable : (prefixWord ++ tailWord_956510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956510).length < 2 ^ (prefixWord ++ tailWord_956510).sum := by decide
  have hdescent : baseEnd_956510 < baseStart_956510 := by decide
  rcases family_descends (prefixWord ++ tailWord_956510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956529 : List Nat := [1, 2, 2, 2, 1, 1, 4, 1, 2, 4, 3]
def baseStart_956529 : Nat := 118140960795 + 956529 * 2 ^ 59
def prefixEnd_956529 : Nat := 4983230072969 + 3 ^ 40 * 956529 * 2
def baseEnd_956529 : Nat := 491159136964593309588509

theorem tailTrace_956529 : CollatzResearch.WordTrace tailWord_956529 prefixEnd_956529 491159136964593309588509 := by
  unfold tailWord_956529
  simp only [CollatzResearch.WordTrace]
  refine ⟨34887478751666269992384641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23258319167777513328256427 34887478751666269992384641)
  ·
    refine ⟨26165609063749702494288481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34887478751666269992384641 26165609063749702494288481)
    ·
      refine ⟨19624206797812276870716361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26165609063749702494288481 19624206797812276870716361)
      ·
        refine ⟨14718155098359207653037271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19624206797812276870716361 14718155098359207653037271)
        ·
          refine ⟨22077232647538811479555907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14718155098359207653037271 22077232647538811479555907)
          ·
            refine ⟨33115848971308217219333861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22077232647538811479555907 33115848971308217219333861)
            ·
              refine ⟨6209221682120290728625099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33115848971308217219333861 6209221682120290728625099)
              ·
                refine ⟨9313832523180436092937649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6209221682120290728625099 9313832523180436092937649)
                ·
                  refine ⟨6985374392385327069703237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9313832523180436092937649 6985374392385327069703237)
                  ·
                    refine ⟨1309757698572248825569357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6985374392385327069703237 1309757698572248825569357)
                    ·
                      refine ⟨491159136964593309588509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1309757698572248825569357 491159136964593309588509)
                      ·
                        rfl

theorem cell23_956529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_956529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956529 prefixEnd_956529 := by exact prefixLift 956529
  have htrace : WordTrace (prefixWord ++ tailWord_956529) baseStart_956529 baseEnd_956529 := by
    simpa [prefixWord, tailWord_956529, baseEnd_956529] using wordTrace_append hprefix tailTrace_956529
  have hstable : (prefixWord ++ tailWord_956529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956529).length < 2 ^ (prefixWord ++ tailWord_956529).sum := by decide
  have hdescent : baseEnd_956529 < baseStart_956529 := by decide
  rcases family_descends (prefixWord ++ tailWord_956529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956564 : List Nat := [2, 4, 2, 3, 1, 1, 3, 1, 1, 3, 2]
def baseStart_956564 : Nat := 118140960795 + 956564 * 2 ^ 59
def prefixEnd_956564 : Nat := 4983230072969 + 3 ^ 40 * 956564 * 2
def baseEnd_956564 : Nat := 491177108787500672650849

theorem tailTrace_956564 : CollatzResearch.WordTrace tailWord_956564 prefixEnd_956564 491177108787500672650849 := by
  unfold tailWord_956564
  simp only [CollatzResearch.WordTrace]
  refine ⟨17444377653269735484954373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23259170204359647313272497 17444377653269735484954373)
  ·
    refine ⟨3270820809988075403428945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17444377653269735484954373 3270820809988075403428945)
    ·
      refine ⟨2453115607491056552571709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3270820809988075403428945 2453115607491056552571709)
      ·
        refine ⟨919918352809146207214391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2453115607491056552571709 919918352809146207214391)
        ·
          refine ⟨1379877529213719310821587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 919918352809146207214391 1379877529213719310821587)
          ·
            refine ⟨2069816293820578966232381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1379877529213719310821587 2069816293820578966232381)
            ·
              refine ⟨776181110182717112337143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2069816293820578966232381 776181110182717112337143)
              ·
                refine ⟨1164271665274075668505715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 776181110182717112337143 1164271665274075668505715)
                ·
                  refine ⟨1746407497911113502758573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1164271665274075668505715 1746407497911113502758573)
                  ·
                    refine ⟨654902811716667563534465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1746407497911113502758573 654902811716667563534465)
                    ·
                      refine ⟨491177108787500672650849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 654902811716667563534465 491177108787500672650849)
                      ·
                        rfl

theorem cell23_956564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_956564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956564 prefixEnd_956564 := by exact prefixLift 956564
  have htrace : WordTrace (prefixWord ++ tailWord_956564) baseStart_956564 baseEnd_956564 := by
    simpa [prefixWord, tailWord_956564, baseEnd_956564] using wordTrace_append hprefix tailTrace_956564
  have hstable : (prefixWord ++ tailWord_956564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956564).length < 2 ^ (prefixWord ++ tailWord_956564).sum := by decide
  have hdescent : baseEnd_956564 < baseStart_956564 := by decide
  rcases family_descends (prefixWord ++ tailWord_956564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956590 : List Nat := [4, 1, 4, 2, 1, 1, 1, 1, 2, 2, 4]
def baseStart_956590 : Nat := 118140960795 + 956590 * 2 ^ 59
def prefixEnd_956590 : Nat := 4983230072969 + 3 ^ 40 * 956590 * 2
def baseEnd_956590 : Nat := 491190459284517570925729

theorem tailTrace_956590 : CollatzResearch.WordTrace tailWord_956590 prefixEnd_956590 491190459284517570925729 := by
  unfold tailWord_956590
  simp only [CollatzResearch.WordTrace]
  refine ⟨4361212950555659676294403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23259802402963518273570149 4361212950555659676294403)
  ·
    refine ⟨6541819425833489514441605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4361212950555659676294403 6541819425833489514441605)
    ·
      refine ⟨1226591142343779283957801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6541819425833489514441605 1226591142343779283957801)
      ·
        refine ⟨919943356757834462968351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1226591142343779283957801 919943356757834462968351)
        ·
          refine ⟨1379915035136751694452527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 919943356757834462968351 1379915035136751694452527)
          ·
            refine ⟨2069872552705127541678791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1379915035136751694452527 2069872552705127541678791)
            ·
              refine ⟨3104808829057691312518187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2069872552705127541678791 3104808829057691312518187)
              ·
                refine ⟨4657213243586536968777281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3104808829057691312518187 4657213243586536968777281)
                ·
                  refine ⟨3492909932689902726582961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4657213243586536968777281 3492909932689902726582961)
                  ·
                    refine ⟨2619682449517427044937221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3492909932689902726582961 2619682449517427044937221)
                    ·
                      refine ⟨491190459284517570925729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2619682449517427044937221 491190459284517570925729)
                      ·
                        rfl

theorem cell23_956590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_956590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956590 prefixEnd_956590 := by exact prefixLift 956590
  have htrace : WordTrace (prefixWord ++ tailWord_956590) baseStart_956590 baseEnd_956590 := by
    simpa [prefixWord, tailWord_956590, baseEnd_956590] using wordTrace_append hprefix tailTrace_956590
  have hstable : (prefixWord ++ tailWord_956590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956590).length < 2 ^ (prefixWord ++ tailWord_956590).sum := by decide
  have hdescent : baseEnd_956590 < baseStart_956590 := by decide
  rcases family_descends (prefixWord ++ tailWord_956590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956593 : List Nat := [1, 2, 2, 5, 2, 1, 1, 1, 2, 3, 3]
def baseStart_956593 : Nat := 118140960795 + 956593 * 2 ^ 59
def prefixEnd_956593 : Nat := 4983230072969 + 3 ^ 40 * 956593 * 2
def baseEnd_956593 : Nat := 491191999726481059188215

theorem tailTrace_956593 : CollatzResearch.WordTrace tailWord_956593 prefixEnd_956593 491191999726481059188215 := by
  unfold tailWord_956593
  simp only [CollatzResearch.WordTrace]
  refine ⟨34889813023434408922714433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23259875348956272615142955 34889813023434408922714433)
  ·
    refine ⟨26167359767575806692035825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34889813023434408922714433 26167359767575806692035825)
    ·
      refine ⟨19625519825681855019026869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26167359767575806692035825 19625519825681855019026869)
      ·
        refine ⟨1839892483657673908033769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19625519825681855019026869 1839892483657673908033769)
        ·
          refine ⟨1379919362743255431025327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1839892483657673908033769 1379919362743255431025327)
          ·
            refine ⟨2069879044114883146537991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1379919362743255431025327 2069879044114883146537991)
            ·
              refine ⟨3104818566172324719806987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2069879044114883146537991 3104818566172324719806987)
              ·
                refine ⟨4657227849258487079710481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3104818566172324719806987 4657227849258487079710481)
                ·
                  refine ⟨3492920886943865309782861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4657227849258487079710481 3492920886943865309782861)
                  ·
                    refine ⟨1309845332603949491168573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3492920886943865309782861 1309845332603949491168573)
                    ·
                      refine ⟨491191999726481059188215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1309845332603949491168573 491191999726481059188215)
                      ·
                        rfl

theorem cell23_956593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_956593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956593 prefixEnd_956593 := by exact prefixLift 956593
  have htrace : WordTrace (prefixWord ++ tailWord_956593) baseStart_956593 baseEnd_956593 := by
    simpa [prefixWord, tailWord_956593, baseEnd_956593] using wordTrace_append hprefix tailTrace_956593
  have hstable : (prefixWord ++ tailWord_956593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956593).length < 2 ^ (prefixWord ++ tailWord_956593).sum := by decide
  have hdescent : baseEnd_956593 < baseStart_956593 := by decide
  rcases family_descends (prefixWord ++ tailWord_956593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956616 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 3, 6, 2]
def baseStart_956616 : Nat := 118140960795 + 956616 * 2 ^ 59
def prefixEnd_956616 : Nat := 4983230072969 + 3 ^ 40 * 956616 * 2
def baseEnd_956616 : Nat := 491203809781534469200609

theorem tailTrace_956616 : CollatzResearch.WordTrace tailWord_956616 prefixEnd_956616 491203809781534469200609 := by
  unfold tailWord_956616
  simp only [CollatzResearch.WordTrace]
  refine ⟨17445325951175541925400851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23260434601567389233867801 17445325951175541925400851)
  ·
    refine ⟨26167988926763312888101277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17445325951175541925400851 26167988926763312888101277)
    ·
      refine ⟨9812995847536242333037979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26167988926763312888101277 9812995847536242333037979)
      ·
        refine ⟨14719493771304363499556969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9812995847536242333037979 14719493771304363499556969)
        ·
          refine ⟨11039620328478272624667727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14719493771304363499556969 11039620328478272624667727)
          ·
            refine ⟨16559430492717408937001591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11039620328478272624667727 16559430492717408937001591)
            ·
              refine ⟨24839145739076113405502387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16559430492717408937001591 24839145739076113405502387)
              ·
                refine ⟨37258718608614170108253581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24839145739076113405502387 37258718608614170108253581)
                ·
                  refine ⟨13972019478230313790595093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37258718608614170108253581 13972019478230313790595093)
                  ·
                    refine ⟨654938413042045958934145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13972019478230313790595093 654938413042045958934145)
                    ·
                      refine ⟨491203809781534469200609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 654938413042045958934145 491203809781534469200609)
                      ·
                        rfl

theorem cell23_956616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 3, 6, 2].length) (baseStart_956616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956616 prefixEnd_956616 := by exact prefixLift 956616
  have htrace : WordTrace (prefixWord ++ tailWord_956616) baseStart_956616 baseEnd_956616 := by
    simpa [prefixWord, tailWord_956616, baseEnd_956616] using wordTrace_append hprefix tailTrace_956616
  have hstable : (prefixWord ++ tailWord_956616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956616).length < 2 ^ (prefixWord ++ tailWord_956616).sum := by decide
  have hdescent : baseEnd_956616 < baseStart_956616 := by decide
  rcases family_descends (prefixWord ++ tailWord_956616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956659 : List Nat := [1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 6]
def baseStart_956659 : Nat := 118140960795 + 956659 * 2 ^ 59
def prefixEnd_956659 : Nat := 4983230072969 + 3 ^ 40 * 956659 * 2
def baseEnd_956659 : Nat := 491225889449677800962911

theorem tailTrace_956659 : CollatzResearch.WordTrace tailWord_956659 prefixEnd_956659 491225889449677800962911 := by
  unfold tailWord_956659
  simp only [CollatzResearch.WordTrace]
  refine ⟨34892220241195302194617031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23261480160796868129744687 34892220241195302194617031)
  ·
    refine ⟨52338330361792953291925547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34892220241195302194617031 52338330361792953291925547)
    ·
      refine ⟨78507495542689429937888321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52338330361792953291925547 78507495542689429937888321)
      ·
        refine ⟨58880621657017072453416241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78507495542689429937888321 58880621657017072453416241)
        ·
          refine ⟨44160466242762804340062181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58880621657017072453416241 44160466242762804340062181)
          ·
            refine ⟨8280087420518025813761659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44160466242762804340062181 8280087420518025813761659)
            ·
              refine ⟨12420131130777038720642489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8280087420518025813761659 12420131130777038720642489)
              ·
                refine ⟨9315098348082779040481867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12420131130777038720642489 9315098348082779040481867)
                ·
                  refine ⟨13972647522124168560722801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9315098348082779040481867 13972647522124168560722801)
                  ·
                    refine ⟨10479485641593126420542101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13972647522124168560722801 10479485641593126420542101)
                    ·
                      refine ⟨491225889449677800962911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10479485641593126420542101 491225889449677800962911)
                      ·
                        rfl

theorem cell23_956659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 6].length) (baseStart_956659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956659 prefixEnd_956659 := by exact prefixLift 956659
  have htrace : WordTrace (prefixWord ++ tailWord_956659) baseStart_956659 baseEnd_956659 := by
    simpa [prefixWord, tailWord_956659, baseEnd_956659] using wordTrace_append hprefix tailTrace_956659
  have hstable : (prefixWord ++ tailWord_956659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956659).length < 2 ^ (prefixWord ++ tailWord_956659).sum := by decide
  have hdescent : baseEnd_956659 < baseStart_956659 := by decide
  rcases family_descends (prefixWord ++ tailWord_956659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956669 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 2, 9]
def baseStart_956669 : Nat := 118140960795 + 956669 * 2 ^ 59
def prefixEnd_956669 : Nat := 4983230072969 + 3 ^ 40 * 956669 * 2
def baseEnd_956669 : Nat := 163743674752074253945955

theorem tailTrace_956669 : CollatzResearch.WordTrace tailWord_956669 prefixEnd_956669 163743674752074253945955 := by
  unfold tailWord_956669
  simp only [CollatzResearch.WordTrace]
  refine ⟨34892584971159073902481061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23261723314106049268320707 34892584971159073902481061)
  ·
    refine ⟨6542359682092326356715199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34892584971159073902481061 6542359682092326356715199)
    ·
      refine ⟨9813539523138489535072799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6542359682092326356715199 9813539523138489535072799)
      ·
        refine ⟨14720309284707734302609199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9813539523138489535072799 14720309284707734302609199)
        ·
          refine ⟨22080463927061601453913799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14720309284707734302609199 22080463927061601453913799)
          ·
            refine ⟨33120695890592402180870699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22080463927061601453913799 33120695890592402180870699)
            ·
              refine ⟨49681043835888603271306049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33120695890592402180870699 49681043835888603271306049)
              ·
                refine ⟨37260782876916452453479537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49681043835888603271306049 37260782876916452453479537)
                ·
                  refine ⟨27945587157687339340109653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37260782876916452453479537 27945587157687339340109653)
                  ·
                    refine ⟨163743674752074253945955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 27945587157687339340109653 163743674752074253945955)
                    ·
                      rfl

theorem cell23_956669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_956669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956669 prefixEnd_956669 := by exact prefixLift 956669
  have htrace : WordTrace (prefixWord ++ tailWord_956669) baseStart_956669 baseEnd_956669 := by
    simpa [prefixWord, tailWord_956669, baseEnd_956669] using wordTrace_append hprefix tailTrace_956669
  have hstable : (prefixWord ++ tailWord_956669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956669).length < 2 ^ (prefixWord ++ tailWord_956669).sum := by decide
  have hdescent : baseEnd_956669 < baseStart_956669 := by decide
  rcases family_descends (prefixWord ++ tailWord_956669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956693 : List Nat := [1, 3, 2, 1, 2, 1, 3, 1, 4, 3, 2]
def baseStart_956693 : Nat := 118140960795 + 956693 * 2 ^ 59
def prefixEnd_956693 : Nat := 4983230072969 + 3 ^ 40 * 956693 * 2
def baseEnd_956693 : Nat := 491243347791930667937755

theorem tailTrace_956693 : CollatzResearch.WordTrace tailWord_956693 prefixEnd_956693 491243347791930667937755 := by
  unfold tailWord_956693
  simp only [CollatzResearch.WordTrace]
  refine ⟨34893460323072126001354733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23262306882048084000903155 34893460323072126001354733)
  ·
    refine ⟨13085047621152047250508025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34893460323072126001354733 13085047621152047250508025)
    ·
      refine ⟨9813785715864035437881019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13085047621152047250508025 9813785715864035437881019)
      ·
        refine ⟨14720678573796053156821529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9813785715864035437881019 14720678573796053156821529)
        ·
          refine ⟨11040508930347039867616147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14720678573796053156821529 11040508930347039867616147)
          ·
            refine ⟨16560763395520559801424221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11040508930347039867616147 16560763395520559801424221)
            ·
              refine ⟨6210286273320209925534083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16560763395520559801424221 6210286273320209925534083)
              ·
                refine ⟨9315429409980314888301125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6210286273320209925534083 9315429409980314888301125)
                ·
                  refine ⟨1746643014371309041556461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9315429409980314888301125 1746643014371309041556461)
                  ·
                    refine ⟨654991130389240890583673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1746643014371309041556461 654991130389240890583673)
                    ·
                      refine ⟨491243347791930667937755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 654991130389240890583673 491243347791930667937755)
                      ·
                        rfl

theorem cell23_956693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 3, 2].length) (baseStart_956693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956693 prefixEnd_956693 := by exact prefixLift 956693
  have htrace : WordTrace (prefixWord ++ tailWord_956693) baseStart_956693 baseEnd_956693 := by
    simpa [prefixWord, tailWord_956693, baseEnd_956693] using wordTrace_append hprefix tailTrace_956693
  have hstable : (prefixWord ++ tailWord_956693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956693).length < 2 ^ (prefixWord ++ tailWord_956693).sum := by decide
  have hdescent : baseEnd_956693 < baseStart_956693 := by decide
  rcases family_descends (prefixWord ++ tailWord_956693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956737 : List Nat := [1, 2, 5, 2, 2, 1, 3, 1, 1, 5]
def baseStart_956737 : Nat := 118140960795 + 956737 * 2 ^ 59
def prefixEnd_956737 : Nat := 4983230072969 + 3 ^ 40 * 956737 * 2
def baseEnd_956737 : Nat := 163755313646909498595851

theorem tailTrace_956737 : CollatzResearch.WordTrace tailWord_956737 prefixEnd_956737 163755313646909498595851 := by
  unfold tailWord_956737
  simp only [CollatzResearch.WordTrace]
  refine ⟨34895065134912721515956465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23263376756608481010637643 34895065134912721515956465)
  ·
    refine ⟨26171298851184541136967349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34895065134912721515956465 26171298851184541136967349)
    ·
      refine ⟨2453559267298550731590689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26171298851184541136967349 2453559267298550731590689)
      ·
        refine ⟨1840169450473913048693017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2453559267298550731590689 1840169450473913048693017)
        ·
          refine ⟨1380127087855434786519763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1840169450473913048693017 1380127087855434786519763)
          ·
            refine ⟨2070190631783152179779645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1380127087855434786519763 2070190631783152179779645)
            ·
              refine ⟨776321486918682067417367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2070190631783152179779645 776321486918682067417367)
              ·
                refine ⟨1164482230378023101126051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 776321486918682067417367 1164482230378023101126051)
                ·
                  refine ⟨1746723345567034651689077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1164482230378023101126051 1746723345567034651689077)
                  ·
                    refine ⟨163755313646909498595851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1746723345567034651689077 163755313646909498595851)
                    ·
                      rfl

theorem cell23_956737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_956737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956737 prefixEnd_956737 := by exact prefixLift 956737
  have htrace : WordTrace (prefixWord ++ tailWord_956737) baseStart_956737 baseEnd_956737 := by
    simpa [prefixWord, tailWord_956737, baseEnd_956737] using wordTrace_append hprefix tailTrace_956737
  have hstable : (prefixWord ++ tailWord_956737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956737).length < 2 ^ (prefixWord ++ tailWord_956737).sum := by decide
  have hdescent : baseEnd_956737 < baseStart_956737 := by decide
  rcases family_descends (prefixWord ++ tailWord_956737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956770 : List Nat := [3, 3, 2, 1, 1, 3, 2, 1, 1, 2, 4]
def baseStart_956770 : Nat := 118140960795 + 956770 * 2 ^ 59
def prefixEnd_956770 : Nat := 4983230072969 + 3 ^ 40 * 956770 * 2
def baseEnd_956770 : Nat := 491282885802326866674901

theorem tailTrace_956770 : CollatzResearch.WordTrace tailWord_956770 prefixEnd_956770 491282885802326866674901 := by
  unfold tailWord_956770
  simp only [CollatzResearch.WordTrace]
  refine ⟨8724067185948292037976941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23264179162528778767938509 8724067185948292037976941)
  ·
    refine ⟨3271525194730609514241353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8724067185948292037976941 3271525194730609514241353)
    ·
      refine ⟨2453643896047957135681015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3271525194730609514241353 2453643896047957135681015)
      ·
        refine ⟨3680465844071935703521523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2453643896047957135681015 3680465844071935703521523)
        ·
          refine ⟨5520698766107903555282285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3680465844071935703521523 5520698766107903555282285)
          ·
            refine ⟨2070262037290463833230857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5520698766107903555282285 2070262037290463833230857)
            ·
              refine ⟨1552696527967847874923143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2070262037290463833230857 1552696527967847874923143)
              ·
                refine ⟨2329044791951771812384715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1552696527967847874923143 2329044791951771812384715)
                ·
                  refine ⟨3493567187927657718577073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2329044791951771812384715 3493567187927657718577073)
                  ·
                    refine ⟨2620175390945743288932805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3493567187927657718577073 2620175390945743288932805)
                    ·
                      refine ⟨491282885802326866674901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2620175390945743288932805 491282885802326866674901)
                      ·
                        rfl

theorem cell23_956770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_956770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956770 prefixEnd_956770 := by exact prefixLift 956770
  have htrace : WordTrace (prefixWord ++ tailWord_956770) baseStart_956770 baseEnd_956770 := by
    simpa [prefixWord, tailWord_956770, baseEnd_956770] using wordTrace_append hprefix tailTrace_956770
  have hstable : (prefixWord ++ tailWord_956770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956770).length < 2 ^ (prefixWord ++ tailWord_956770).sum := by decide
  have hdescent : baseEnd_956770 < baseStart_956770 := by decide
  rcases family_descends (prefixWord ++ tailWord_956770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956773 : List Nat := [1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 3]
def baseStart_956773 : Nat := 118140960795 + 956773 * 2 ^ 59
def prefixEnd_956773 : Nat := 4983230072969 + 3 ^ 40 * 956773 * 2
def baseEnd_956773 : Nat := 491284426244290354937387

theorem tailTrace_956773 : CollatzResearch.WordTrace tailWord_956773 prefixEnd_956773 491284426244290354937387 := by
  unfold tailWord_956773
  simp only [CollatzResearch.WordTrace]
  refine ⟨34896378162782299664266973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23264252108521533109511315 34896378162782299664266973)
  ·
    refine ⟨13086141811043362374100115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34896378162782299664266973 13086141811043362374100115)
    ·
      refine ⟨19629212716565043561150173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13086141811043362374100115 19629212716565043561150173)
      ·
        refine ⟨7360954768711891335431315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19629212716565043561150173 7360954768711891335431315)
        ·
          refine ⟨11041432153067837003146973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7360954768711891335431315 11041432153067837003146973)
          ·
            refine ⟨4140537057400438876180115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11041432153067837003146973 4140537057400438876180115)
            ·
              refine ⟨6210805586100658314270173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4140537057400438876180115 6210805586100658314270173)
              ·
                refine ⟨2329052094787746867851315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6210805586100658314270173 2329052094787746867851315)
                ·
                  refine ⟨3493578142181620301776973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2329052094787746867851315 3493578142181620301776973)
                  ·
                    refine ⟨1310091803318107613166365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3493578142181620301776973 1310091803318107613166365)
                    ·
                      refine ⟨491284426244290354937387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1310091803318107613166365 491284426244290354937387)
                      ·
                        rfl

theorem cell23_956773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_956773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956773 prefixEnd_956773 := by exact prefixLift 956773
  have htrace : WordTrace (prefixWord ++ tailWord_956773) baseStart_956773 baseEnd_956773 := by
    simpa [prefixWord, tailWord_956773, baseEnd_956773] using wordTrace_append hprefix tailTrace_956773
  have hstable : (prefixWord ++ tailWord_956773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956773).length < 2 ^ (prefixWord ++ tailWord_956773).sum := by decide
  have hdescent : baseEnd_956773 < baseStart_956773 := by decide
  rcases family_descends (prefixWord ++ tailWord_956773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956796 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 1, 5, 4]
def baseStart_956796 : Nat := 118140960795 + 956796 * 2 ^ 59
def prefixEnd_956796 : Nat := 4983230072969 + 3 ^ 40 * 956796 * 2
def baseEnd_956796 : Nat := 491296236299343764949781

theorem tailTrace_956796 : CollatzResearch.WordTrace tailWord_956796 prefixEnd_956796 491296236299343764949781 := by
  unfold tailWord_956796
  simp only [CollatzResearch.WordTrace]
  refine ⟨17448608520849487296177121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23264811361132649728236161 17448608520849487296177121)
  ·
    refine ⟨13086456390637115472132841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17448608520849487296177121 13086456390637115472132841)
    ·
      refine ⟨9814842292977836604099631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13086456390637115472132841 9814842292977836604099631)
      ·
        refine ⟨14722263439466754906149447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9814842292977836604099631 14722263439466754906149447)
        ·
          refine ⟨22083395159200132359224171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14722263439466754906149447 22083395159200132359224171)
          ·
            refine ⟨33125092738800198538836257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22083395159200132359224171 33125092738800198538836257)
            ·
              refine ⟨24843819554100148904127193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33125092738800198538836257 24843819554100148904127193)
              ·
                refine ⟨18632864665575111678095395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24843819554100148904127193 18632864665575111678095395)
                ·
                  refine ⟨27949296998362667517143093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18632864665575111678095395 27949296998362667517143093)
                  ·
                    refine ⟨2620246593596500079732165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27949296998362667517143093 2620246593596500079732165)
                    ·
                      refine ⟨491296236299343764949781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2620246593596500079732165 491296236299343764949781)
                      ·
                        rfl

theorem cell23_956796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_956796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956796 prefixEnd_956796 := by exact prefixLift 956796
  have htrace : WordTrace (prefixWord ++ tailWord_956796) baseStart_956796 baseEnd_956796 := by
    simpa [prefixWord, tailWord_956796, baseEnd_956796] using wordTrace_append hprefix tailTrace_956796
  have hstable : (prefixWord ++ tailWord_956796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956796).length < 2 ^ (prefixWord ++ tailWord_956796).sum := by decide
  have hdescent : baseEnd_956796 < baseStart_956796 := by decide
  rcases family_descends (prefixWord ++ tailWord_956796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956824 : List Nat := [2, 1, 2, 5, 1, 2, 3, 1, 2, 1, 3]
def baseStart_956824 : Nat := 118140960795 + 956824 * 2 ^ 59
def prefixEnd_956824 : Nat := 4983230072969 + 3 ^ 40 * 956824 * 2
def baseEnd_956824 : Nat := 491310613757669655399653

theorem tailTrace_956824 : CollatzResearch.WordTrace tailWord_956824 prefixEnd_956824 491310613757669655399653 := by
  unfold tailWord_956824
  simp only [CollatzResearch.WordTrace]
  refine ⟨17449119142798767687186763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23265492190398356916249017 17449119142798767687186763)
  ·
    refine ⟨26173678714198151530780145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17449119142798767687186763 26173678714198151530780145)
    ·
      refine ⟨19630259035648613648085109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26173678714198151530780145 19630259035648613648085109)
      ·
        refine ⟨1840336784592057529507979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19630259035648613648085109 1840336784592057529507979)
        ·
          refine ⟨2760505176888086294261969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1840336784592057529507979 2760505176888086294261969)
          ·
            refine ⟨2070378882666064720696477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2760505176888086294261969 2070378882666064720696477)
            ·
              refine ⟨776392080999774270261179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2070378882666064720696477 776392080999774270261179)
              ·
                refine ⟨1164588121499661405391769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 776392080999774270261179 1164588121499661405391769)
                ·
                  refine ⟨873441091124746054043827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1164588121499661405391769 873441091124746054043827)
                  ·
                    refine ⟨1310161636687119081065741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 873441091124746054043827 1310161636687119081065741)
                    ·
                      refine ⟨491310613757669655399653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1310161636687119081065741 491310613757669655399653)
                      ·
                        rfl

theorem cell23_956824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_956824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956824 prefixEnd_956824 := by exact prefixLift 956824
  have htrace : WordTrace (prefixWord ++ tailWord_956824) baseStart_956824 baseEnd_956824 := by
    simpa [prefixWord, tailWord_956824, baseEnd_956824] using wordTrace_append hprefix tailTrace_956824
  have hstable : (prefixWord ++ tailWord_956824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956824).length < 2 ^ (prefixWord ++ tailWord_956824).sum := by decide
  have hdescent : baseEnd_956824 < baseStart_956824 := by decide
  rcases family_descends (prefixWord ++ tailWord_956824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956842 : List Nat := [3, 1, 6, 1, 2, 1, 1, 3, 1, 2, 2]
def baseStart_956842 : Nat := 118140960795 + 956842 * 2 ^ 59
def prefixEnd_956842 : Nat := 4983230072969 + 3 ^ 40 * 956842 * 2
def baseEnd_956842 : Nat := 491319856409450584974571

theorem tailTrace_956842 : CollatzResearch.WordTrace tailWord_956842 prefixEnd_956842 491319856409450584974571 := by
  unfold tailWord_956842
  simp only [CollatzResearch.WordTrace]
  refine ⟨8724723699883081112132195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23265929866354882965685853 8724723699883081112132195)
  ·
    refine ⟨13087085549824621668198293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8724723699883081112132195 13087085549824621668198293)
    ·
      refine ⟨613457135148029140696795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13087085549824621668198293 613457135148029140696795)
      ·
        refine ⟨920185702722043711045193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613457135148029140696795 920185702722043711045193)
        ·
          refine ⟨690139277041532783283895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 920185702722043711045193 690139277041532783283895)
          ·
            refine ⟨1035208915562299174925843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690139277041532783283895 1035208915562299174925843)
            ·
              refine ⟨1552813373343448762388765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035208915562299174925843 1552813373343448762388765)
              ·
                refine ⟨582305015003793285895787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1552813373343448762388765 582305015003793285895787)
                ·
                  refine ⟨873457522505689928843681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 582305015003793285895787 873457522505689928843681)
                  ·
                    refine ⟨655093141879267446632761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 873457522505689928843681 655093141879267446632761)
                    ·
                      refine ⟨491319856409450584974571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 655093141879267446632761 491319856409450584974571)
                      ·
                        rfl

theorem cell23_956842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_956842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956842 prefixEnd_956842 := by exact prefixLift 956842
  have htrace : WordTrace (prefixWord ++ tailWord_956842) baseStart_956842 baseEnd_956842 := by
    simpa [prefixWord, tailWord_956842, baseEnd_956842] using wordTrace_append hprefix tailTrace_956842
  have hstable : (prefixWord ++ tailWord_956842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956842).length < 2 ^ (prefixWord ++ tailWord_956842).sum := by decide
  have hdescent : baseEnd_956842 < baseStart_956842 := by decide
  rcases family_descends (prefixWord ++ tailWord_956842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956893 : List Nat := [1, 4, 3, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_956893 : Nat := 118140960795 + 956893 * 2 ^ 59
def prefixEnd_956893 : Nat := 4983230072969 + 3 ^ 40 * 956893 * 2
def baseEnd_956893 : Nat := 491346043922829885436835

theorem tailTrace_956893 : CollatzResearch.WordTrace tailWord_956893 prefixEnd_956893 491346043922829885436835 := by
  unfold tailWord_956893
  simp only [CollatzResearch.WordTrace]
  refine ⟨34900754922347560158635333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23267169948231706772423555 34900754922347560158635333)
  ·
    refine ⟨6543891547940167529744125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34900754922347560158635333 6543891547940167529744125)
    ·
      refine ⟨2453959330477562823654047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6543891547940167529744125 2453959330477562823654047)
      ·
        refine ⟨3680938995716344235481071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2453959330477562823654047 3680938995716344235481071)
        ·
          refine ⟨5521408493574516353221607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3680938995716344235481071 5521408493574516353221607)
          ·
            refine ⟨8282112740361774529832411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5521408493574516353221607 8282112740361774529832411)
            ·
              refine ⟨12423169110542661794748617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8282112740361774529832411 12423169110542661794748617)
              ·
                refine ⟨9317376832906996346061463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12423169110542661794748617 9317376832906996346061463)
                ·
                  refine ⟨13976065249360494519092195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9317376832906996346061463 13976065249360494519092195)
                  ·
                    refine ⟨20964097874040741778638293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13976065249360494519092195 20964097874040741778638293)
                    ·
                      refine ⟨491346043922829885436835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 20964097874040741778638293 491346043922829885436835)
                      ·
                        rfl

theorem cell23_956893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_956893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956893 prefixEnd_956893 := by exact prefixLift 956893
  have htrace : WordTrace (prefixWord ++ tailWord_956893) baseStart_956893 baseEnd_956893 := by
    simpa [prefixWord, tailWord_956893, baseEnd_956893] using wordTrace_append hprefix tailTrace_956893
  have hstable : (prefixWord ++ tailWord_956893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956893).length < 2 ^ (prefixWord ++ tailWord_956893).sum := by decide
  have hdescent : baseEnd_956893 < baseStart_956893 := by decide
  rcases family_descends (prefixWord ++ tailWord_956893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956920 : List Nat := [2, 1, 2, 1, 1, 4, 2, 2, 2, 4, 2]
def baseStart_956920 : Nat := 118140960795 + 956920 * 2 ^ 59
def prefixEnd_956920 : Nat := 4983230072969 + 3 ^ 40 * 956920 * 2
def baseEnd_956920 : Nat := 491359907900501279799211

theorem tailTrace_956920 : CollatzResearch.WordTrace tailWord_956920 prefixEnd_956920 491359907900501279799211 := by
  unfold tailWord_956920
  simp only [CollatzResearch.WordTrace]
  refine ⟨17450869846624871884934107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23267826462166495846578809 17450869846624871884934107)
  ·
    refine ⟨26176304769937307827401161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17450869846624871884934107 26176304769937307827401161)
    ·
      refine ⟨19632228577452980870550871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26176304769937307827401161 19632228577452980870550871)
      ·
        refine ⟨29448342866179471305826307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19632228577452980870550871 29448342866179471305826307)
        ·
          refine ⟨44172514299269206958739461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29448342866179471305826307 44172514299269206958739461)
          ·
            refine ⟨8282346431112976304763649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44172514299269206958739461 8282346431112976304763649)
            ·
              refine ⟨6211759823334732228572737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8282346431112976304763649 6211759823334732228572737)
              ·
                refine ⟨4658819867501049171429553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6211759823334732228572737 4658819867501049171429553)
                ·
                  refine ⟨3494114900625786878572165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4658819867501049171429553 3494114900625786878572165)
                  ·
                    refine ⟨655146543867335039732281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3494114900625786878572165 655146543867335039732281)
                    ·
                      refine ⟨491359907900501279799211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 655146543867335039732281 491359907900501279799211)
                      ·
                        rfl

theorem cell23_956920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 2, 4, 2].length) (baseStart_956920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956920 prefixEnd_956920 := by exact prefixLift 956920
  have htrace : WordTrace (prefixWord ++ tailWord_956920) baseStart_956920 baseEnd_956920 := by
    simpa [prefixWord, tailWord_956920, baseEnd_956920] using wordTrace_append hprefix tailTrace_956920
  have hstable : (prefixWord ++ tailWord_956920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956920).length < 2 ^ (prefixWord ++ tailWord_956920).sum := by decide
  have hdescent : baseEnd_956920 < baseStart_956920 := by decide
  rcases family_descends (prefixWord ++ tailWord_956920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956953 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 2, 5, 3]
def baseStart_956953 : Nat := 118140960795 + 956953 * 2 ^ 59
def prefixEnd_956953 : Nat := 4983230072969 + 3 ^ 40 * 956953 * 2
def baseEnd_956953 : Nat := 491376852762099650686559

theorem tailTrace_956953 : CollatzResearch.WordTrace tailWord_956953 prefixEnd_956953 491376852762099650686559 := by
  unfold tailWord_956953
  simp only [CollatzResearch.WordTrace]
  refine ⟨34902943302130190405819513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23268628868086793603879675 34902943302130190405819513)
  ·
    refine ⟨26177207476597642804364635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34902943302130190405819513 26177207476597642804364635)
    ·
      refine ⟨39265811214896464206546953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26177207476597642804364635 39265811214896464206546953)
      ·
        refine ⟨29449358411172348154910215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39265811214896464206546953 29449358411172348154910215)
        ·
          refine ⟨44174037616758522232365323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29449358411172348154910215 44174037616758522232365323)
          ·
            refine ⟨66261056425137783348547985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44174037616758522232365323 66261056425137783348547985)
            ·
              refine ⟨49695792318853337511410989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66261056425137783348547985 49695792318853337511410989)
              ·
                refine ⟨18635922119570001566779121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49695792318853337511410989 18635922119570001566779121)
                ·
                  refine ⟨13976941589677501175084341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18635922119570001566779121 13976941589677501175084341)
                  ·
                    refine ⟨1310338274032265735164157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13976941589677501175084341 1310338274032265735164157)
                    ·
                      refine ⟨491376852762099650686559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1310338274032265735164157 491376852762099650686559)
                      ·
                        rfl

theorem cell23_956953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 5, 3].length) (baseStart_956953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956953 prefixEnd_956953 := by exact prefixLift 956953
  have htrace : WordTrace (prefixWord ++ tailWord_956953) baseStart_956953 baseEnd_956953 := by
    simpa [prefixWord, tailWord_956953, baseEnd_956953] using wordTrace_append hprefix tailTrace_956953
  have hstable : (prefixWord ++ tailWord_956953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956953).length < 2 ^ (prefixWord ++ tailWord_956953).sum := by decide
  have hdescent : baseEnd_956953 < baseStart_956953 := by decide
  rcases family_descends (prefixWord ++ tailWord_956953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_956957 : List Nat := [1, 4, 2, 2, 1, 2, 3, 1, 2, 2, 3]
def baseStart_956957 : Nat := 118140960795 + 956957 * 2 ^ 59
def prefixEnd_956957 : Nat := 4983230072969 + 3 ^ 40 * 956957 * 2
def baseEnd_956957 : Nat := 491378906684717635036541

theorem tailTrace_956957 : CollatzResearch.WordTrace tailWord_956957 prefixEnd_956957 491378906684717635036541 := by
  unfold tailWord_956957
  simp only [CollatzResearch.WordTrace]
  refine ⟨34903089194115699088965125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23268726129410466059310083 34903089194115699088965125)
  ·
    refine ⟨6544329223896693579180961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34903089194115699088965125 6544329223896693579180961)
    ·
      refine ⟨4908246917922520184385721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6544329223896693579180961 4908246917922520184385721)
      ·
        refine ⟨3681185188441890138289291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4908246917922520184385721 3681185188441890138289291)
        ·
          refine ⟨5521777782662835207433937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3681185188441890138289291 5521777782662835207433937)
          ·
            refine ⟨4141333336997126405575453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5521777782662835207433937 4141333336997126405575453)
            ·
              refine ⟨1553000001373922402090795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4141333336997126405575453 1553000001373922402090795)
              ·
                refine ⟨2329500002060883603136193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1553000001373922402090795 2329500002060883603136193)
                ·
                  refine ⟨1747125001545662702352145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2329500002060883603136193 1747125001545662702352145)
                  ·
                    refine ⟨1310343751159247026764109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1747125001545662702352145 1310343751159247026764109)
                    ·
                      refine ⟨491378906684717635036541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1310343751159247026764109 491378906684717635036541)
                      ·
                        rfl

theorem cell23_956957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_956957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_956957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_956957 prefixEnd_956957 := by exact prefixLift 956957
  have htrace : WordTrace (prefixWord ++ tailWord_956957) baseStart_956957 baseEnd_956957 := by
    simpa [prefixWord, tailWord_956957, baseEnd_956957] using wordTrace_append hprefix tailTrace_956957
  have hstable : (prefixWord ++ tailWord_956957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_956957).length < 2 ^ (prefixWord ++ tailWord_956957).sum := by decide
  have hdescent : baseEnd_956957 < baseStart_956957 := by decide
  rcases family_descends (prefixWord ++ tailWord_956957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957037 : List Nat := [1, 5, 1, 1, 3, 1, 2, 1, 4, 4]
def baseStart_957037 : Nat := 118140960795 + 957037 * 2 ^ 59
def prefixEnd_957037 : Nat := 4983230072969 + 3 ^ 40 * 957037 * 2
def baseEnd_957037 : Nat := 163806661712359107345391

theorem tailTrace_957037 : CollatzResearch.WordTrace tailWord_957037 prefixEnd_957037 163806661712359107345391 := by
  unfold tailWord_957037
  simp only [CollatzResearch.WordTrace]
  refine ⟨34906007033825872751877365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23270671355883915167918243 34906007033825872751877365)
  ·
    refine ⟨3272438159421175570488503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34906007033825872751877365 3272438159421175570488503)
    ·
      refine ⟨4908657239131763355732755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3272438159421175570488503 4908657239131763355732755)
      ·
        refine ⟨7362985858697645033599133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4908657239131763355732755 7362985858697645033599133)
        ·
          refine ⟨2761119697011616887599675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7362985858697645033599133 2761119697011616887599675)
          ·
            refine ⟨4141679545517425331399513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2761119697011616887599675 4141679545517425331399513)
            ·
              refine ⟨3106259659138068998549635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4141679545517425331399513 3106259659138068998549635)
              ·
                refine ⟨4659389488707103497824453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3106259659138068998549635 4659389488707103497824453)
                ·
                  refine ⟨873635529132581905842085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4659389488707103497824453 873635529132581905842085)
                  ·
                    refine ⟨163806661712359107345391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 873635529132581905842085 163806661712359107345391)
                    ·
                      rfl

theorem cell23_957037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_957037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957037 prefixEnd_957037 := by exact prefixLift 957037
  have htrace : WordTrace (prefixWord ++ tailWord_957037) baseStart_957037 baseEnd_957037 := by
    simpa [prefixWord, tailWord_957037, baseEnd_957037] using wordTrace_append hprefix tailTrace_957037
  have hstable : (prefixWord ++ tailWord_957037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957037).length < 2 ^ (prefixWord ++ tailWord_957037).sum := by decide
  have hdescent : baseEnd_957037 < baseStart_957037 := by decide
  rcases family_descends (prefixWord ++ tailWord_957037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957038 : List Nat := [4, 1, 2, 2, 2, 2, 3, 2, 1, 1, 3]
def baseStart_957038 : Nat := 118140960795 + 957038 * 2 ^ 59
def prefixEnd_957038 : Nat := 4983230072969 + 3 ^ 40 * 957038 * 2
def baseEnd_957038 : Nat := 491420498617731818123669

theorem tailTrace_957038 : CollatzResearch.WordTrace tailWord_957038 prefixEnd_957038 491420498617731818123669 := by
  unfold tailWord_957038
  simp only [CollatzResearch.WordTrace]
  refine ⟨4363255438352781240332971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23270695671214833281775845 4363255438352781240332971)
  ·
    refine ⟨6544883157529171860499457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4363255438352781240332971 6544883157529171860499457)
    ·
      refine ⟨4908662368146878895374593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6544883157529171860499457 4908662368146878895374593)
      ·
        refine ⟨3681496776110159171530945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4908662368146878895374593 3681496776110159171530945)
        ·
          refine ⟨2761122582082619378648209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3681496776110159171530945 2761122582082619378648209)
          ·
            refine ⟨2070841936561964533986157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2761122582082619378648209 2070841936561964533986157)
            ·
              refine ⟨776565726210736700244809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2070841936561964533986157 776565726210736700244809)
              ·
                refine ⟨582424294658052525183607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 776565726210736700244809 582424294658052525183607)
                ·
                  refine ⟨873636441987078787775411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 582424294658052525183607 873636441987078787775411)
                  ·
                    refine ⟨1310454662980618181663117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 873636441987078787775411 1310454662980618181663117)
                    ·
                      refine ⟨491420498617731818123669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1310454662980618181663117 491420498617731818123669)
                      ·
                        rfl

theorem cell23_957038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_957038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957038 prefixEnd_957038 := by exact prefixLift 957038
  have htrace : WordTrace (prefixWord ++ tailWord_957038) baseStart_957038 baseEnd_957038 := by
    simpa [prefixWord, tailWord_957038, baseEnd_957038] using wordTrace_append hprefix tailTrace_957038
  have hstable : (prefixWord ++ tailWord_957038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957038).length < 2 ^ (prefixWord ++ tailWord_957038).sum := by decide
  have hdescent : baseEnd_957038 < baseStart_957038 := by decide
  rcases family_descends (prefixWord ++ tailWord_957038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957073 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 7]
def baseStart_957073 : Nat := 118140960795 + 957073 * 2 ^ 59
def prefixEnd_957073 : Nat := 4983230072969 + 3 ^ 40 * 957073 * 2
def baseEnd_957073 : Nat := 491438470440639181186007

theorem tailTrace_957073 : CollatzResearch.WordTrace tailWord_957073 prefixEnd_957073 491438470440639181186007 := by
  unfold tailWord_957073
  simp only [CollatzResearch.WordTrace]
  refine ⟨34907320061695450900187873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23271546707796967266791915 34907320061695450900187873)
  ·
    refine ⟨26180490046271588175140905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34907320061695450900187873 26180490046271588175140905)
    ·
      refine ⟨19635367534703691131355679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26180490046271588175140905 19635367534703691131355679)
      ·
        refine ⟨29453051302055536697033519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19635367534703691131355679 29453051302055536697033519)
        ·
          refine ⟨44179576953083305045550279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29453051302055536697033519 44179576953083305045550279)
          ·
            refine ⟨66269365429624957568325419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44179576953083305045550279 66269365429624957568325419)
            ·
              refine ⟨99404048144437436352488129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66269365429624957568325419 99404048144437436352488129)
              ·
                refine ⟨74553036108328077264366097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99404048144437436352488129 74553036108328077264366097)
                ·
                  refine ⟨55914777081246057948274573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74553036108328077264366097 55914777081246057948274573)
                  ·
                    refine ⟨20968041405467271730602965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55914777081246057948274573 20968041405467271730602965)
                    ·
                      refine ⟨491438470440639181186007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 20968041405467271730602965 491438470440639181186007)
                      ·
                        rfl

theorem cell23_957073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_957073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957073 prefixEnd_957073 := by exact prefixLift 957073
  have htrace : WordTrace (prefixWord ++ tailWord_957073) baseStart_957073 baseEnd_957073 := by
    simpa [prefixWord, tailWord_957073, baseEnd_957073] using wordTrace_append hprefix tailTrace_957073
  have hstable : (prefixWord ++ tailWord_957073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957073).length < 2 ^ (prefixWord ++ tailWord_957073).sum := by decide
  have hdescent : baseEnd_957073 < baseStart_957073 := by decide
  rcases family_descends (prefixWord ++ tailWord_957073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957095 : List Nat := [1, 1, 6, 3, 1, 1, 1, 4, 1, 2, 2]
def baseStart_957095 : Nat := 118140960795 + 957095 * 2 ^ 59
def prefixEnd_957095 : Nat := 4983230072969 + 3 ^ 40 * 957095 * 2
def baseEnd_957095 : Nat := 491449767015038095110907

theorem tailTrace_957095 : CollatzResearch.WordTrace tailWord_957095 prefixEnd_957095 491449767015038095110907 := by
  unfold tailWord_957095
  simp only [CollatzResearch.WordTrace]
  refine ⟨34908122467615748657488739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23272081645077165771659159 34908122467615748657488739)
  ·
    refine ⟨52362183701423622986233109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34908122467615748657488739 52362183701423622986233109)
    ·
      refine ⟨2454477361004232327479677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52362183701423622986233109 2454477361004232327479677)
      ·
        refine ⟨920429010376587122804879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2454477361004232327479677 920429010376587122804879)
        ·
          refine ⟨1380643515564880684207319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 920429010376587122804879 1380643515564880684207319)
          ·
            refine ⟨2070965273347321026310979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1380643515564880684207319 2070965273347321026310979)
            ·
              refine ⟨3106447910020981539466469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2070965273347321026310979 3106447910020981539466469)
              ·
                refine ⟨582458983128934038649963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3106447910020981539466469 582458983128934038649963)
                ·
                  refine ⟨873688474693401057974945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 582458983128934038649963 873688474693401057974945)
                  ·
                    refine ⟨655266356020050793481209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 873688474693401057974945 655266356020050793481209)
                    ·
                      refine ⟨491449767015038095110907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 655266356020050793481209 491449767015038095110907)
                      ·
                        rfl

theorem cell23_957095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_957095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957095 prefixEnd_957095 := by exact prefixLift 957095
  have htrace : WordTrace (prefixWord ++ tailWord_957095) baseStart_957095 baseEnd_957095 := by
    simpa [prefixWord, tailWord_957095, baseEnd_957095] using wordTrace_append hprefix tailTrace_957095
  have hstable : (prefixWord ++ tailWord_957095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957095).length < 2 ^ (prefixWord ++ tailWord_957095).sum := by decide
  have hdescent : baseEnd_957095 < baseStart_957095 := by decide
  rcases family_descends (prefixWord ++ tailWord_957095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957134 : List Nat := [4, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2]
def baseStart_957134 : Nat := 118140960795 + 957134 * 2 ^ 59
def prefixEnd_957134 : Nat := 4983230072969 + 3 ^ 40 * 957134 * 2
def baseEnd_957134 : Nat := 491469792760563442523227

theorem tailTrace_957134 : CollatzResearch.WordTrace tailWord_957134 prefixEnd_957134 491469792760563442523227 := by
  unfold tailWord_957134
  simp only [CollatzResearch.WordTrace]
  refine ⟨4363693114309307289769807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23273029942982972212105637 4363693114309307289769807)
  ·
    refine ⟨6545539671463960934654711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4363693114309307289769807 6545539671463960934654711)
    ·
      refine ⟨9818309507195941401982067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6545539671463960934654711 9818309507195941401982067)
      ·
        refine ⟨14727464260793912102973101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9818309507195941401982067 14727464260793912102973101)
        ·
          refine ⟨5522799097797717038614913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14727464260793912102973101 5522799097797717038614913)
          ·
            refine ⟨4142099323348287778961185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5522799097797717038614913 4142099323348287778961185)
            ·
              refine ⟨3106574492511215834220889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4142099323348287778961185 3106574492511215834220889)
              ·
                refine ⟨2329930869383411875665667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3106574492511215834220889 2329930869383411875665667)
                ·
                  refine ⟨3494896304075117813498501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2329930869383411875665667 3494896304075117813498501)
                  ·
                    refine ⟨655293057014084590030969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3494896304075117813498501 655293057014084590030969)
                    ·
                      refine ⟨491469792760563442523227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 655293057014084590030969 491469792760563442523227)
                      ·
                        rfl

theorem cell23_957134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2].length) (baseStart_957134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957134 prefixEnd_957134 := by exact prefixLift 957134
  have htrace : WordTrace (prefixWord ++ tailWord_957134) baseStart_957134 baseEnd_957134 := by
    simpa [prefixWord, tailWord_957134, baseEnd_957134] using wordTrace_append hprefix tailTrace_957134
  have hstable : (prefixWord ++ tailWord_957134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957134).length < 2 ^ (prefixWord ++ tailWord_957134).sum := by decide
  have hdescent : baseEnd_957134 < baseStart_957134 := by decide
  rcases family_descends (prefixWord ++ tailWord_957134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957151 : List Nat := [1, 1, 2, 3, 2, 3, 3, 2, 2, 2, 2]
def baseStart_957151 : Nat := 118140960795 + 957151 * 2 ^ 59
def prefixEnd_957151 : Nat := 4983230072969 + 3 ^ 40 * 957151 * 2
def baseEnd_957151 : Nat := 491478521931689876010649

theorem tailTrace_957151 : CollatzResearch.WordTrace tailWord_957151 prefixEnd_957151 491478521931689876010649 := by
  unfold tailWord_957151
  simp only [CollatzResearch.WordTrace]
  refine ⟨34910164955412870221527307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23273443303608580147684871 34910164955412870221527307)
  ·
    refine ⟨52365247433119305332290961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34910164955412870221527307 52365247433119305332290961)
    ·
      refine ⟨39273935574839478999218221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52365247433119305332290961 39273935574839478999218221)
      ·
        refine ⟨14727725840564804624706833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39273935574839478999218221 14727725840564804624706833)
        ·
          refine ⟨11045794380423603468530125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14727725840564804624706833 11045794380423603468530125)
          ·
            refine ⟨4142172892658851300698797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11045794380423603468530125 4142172892658851300698797)
            ·
              refine ⟨1553314834747069237762049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4142172892658851300698797 1553314834747069237762049)
              ·
                refine ⟨1164986126060301928321537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1553314834747069237762049 1164986126060301928321537)
                ·
                  refine ⟨873739594545226446241153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1164986126060301928321537 873739594545226446241153)
                  ·
                    refine ⟨655304695908919834680865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 873739594545226446241153 655304695908919834680865)
                    ·
                      refine ⟨491478521931689876010649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 655304695908919834680865 491478521931689876010649)
                      ·
                        rfl

theorem cell23_957151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 2, 2, 2].length) (baseStart_957151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957151 prefixEnd_957151 := by exact prefixLift 957151
  have htrace : WordTrace (prefixWord ++ tailWord_957151) baseStart_957151 baseEnd_957151 := by
    simpa [prefixWord, tailWord_957151, baseEnd_957151] using wordTrace_append hprefix tailTrace_957151
  have hstable : (prefixWord ++ tailWord_957151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957151).length < 2 ^ (prefixWord ++ tailWord_957151).sum := by decide
  have hdescent : baseEnd_957151 < baseStart_957151 := by decide
  rcases family_descends (prefixWord ++ tailWord_957151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957157 : List Nat := [1, 3, 1, 4, 1, 3, 2, 1, 7]
def baseStart_957157 : Nat := 118140960795 + 957157 * 2 ^ 59
def prefixEnd_957157 : Nat := 4983230072969 + 3 ^ 40 * 957157 * 2
def baseEnd_957157 : Nat := 54609066979512983615069

theorem tailTrace_957157 : CollatzResearch.WordTrace tailWord_957157 prefixEnd_957157 54609066979512983615069 := by
  unfold tailWord_957157
  simp only [CollatzResearch.WordTrace]
  refine ⟨34910383793391133246245725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23273589195594088830830483 34910383793391133246245725)
  ·
    refine ⟨13091393922521674967342147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34910383793391133246245725 13091393922521674967342147)
    ·
      refine ⟨19637090883782512451013221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13091393922521674967342147 19637090883782512451013221)
      ·
        refine ⟨3681954540709221084564979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19637090883782512451013221 3681954540709221084564979)
        ·
          refine ⟨5522931811063831626847469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3681954540709221084564979 5522931811063831626847469)
          ·
            refine ⟨2071099429148936860067801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5522931811063831626847469 2071099429148936860067801)
            ·
              refine ⟨1553324571861702645050851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2071099429148936860067801 1553324571861702645050851)
              ·
                refine ⟨2329986857792553967576277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1553324571861702645050851 2329986857792553967576277)
                ·
                  refine ⟨54609066979512983615069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2329986857792553967576277 54609066979512983615069)
                  ·
                    rfl

theorem cell23_957157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 7].length) (baseStart_957157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957157 prefixEnd_957157 := by exact prefixLift 957157
  have htrace : WordTrace (prefixWord ++ tailWord_957157) baseStart_957157 baseEnd_957157 := by
    simpa [prefixWord, tailWord_957157, baseEnd_957157] using wordTrace_append hprefix tailTrace_957157
  have hstable : (prefixWord ++ tailWord_957157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957157).length < 2 ^ (prefixWord ++ tailWord_957157).sum := by decide
  have hdescent : baseEnd_957157 < baseStart_957157 := by decide
  rcases family_descends (prefixWord ++ tailWord_957157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957167 : List Nat := [1, 1, 2, 1, 5, 2, 2, 1, 2, 3, 3]
def baseStart_957167 : Nat := 118140960795 + 957167 * 2 ^ 59
def prefixEnd_957167 : Nat := 4983230072969 + 3 ^ 40 * 957167 * 2
def baseEnd_957167 : Nat := 491486737622161813410575

theorem tailTrace_957167 : CollatzResearch.WordTrace tailWord_957167 prefixEnd_957167 491486737622161813410575 := by
  unfold tailWord_957167
  simp only [CollatzResearch.WordTrace]
  refine ⟨34910748523354904954109755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23273832348903269969406503 34910748523354904954109755)
  ·
    refine ⟨52366122785032357431164633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34910748523354904954109755 52366122785032357431164633)
    ·
      refine ⟨39274592088774268073373475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52366122785032357431164633 39274592088774268073373475)
      ·
        refine ⟨58911888133161402110060213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39274592088774268073373475 58911888133161402110060213)
        ·
          refine ⟨5522989512483881447818145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58911888133161402110060213 5522989512483881447818145)
          ·
            refine ⟨4142242134362911085863609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5522989512483881447818145 4142242134362911085863609)
            ·
              refine ⟨3106681600772183314397707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4142242134362911085863609 3106681600772183314397707)
              ·
                refine ⟨4660022401158274971596561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3106681600772183314397707 4660022401158274971596561)
                ·
                  refine ⟨3495016800868706228697421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4660022401158274971596561 3495016800868706228697421)
                  ·
                    refine ⟨1310631300325764835761533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3495016800868706228697421 1310631300325764835761533)
                    ·
                      refine ⟨491486737622161813410575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1310631300325764835761533 491486737622161813410575)
                      ·
                        rfl

theorem cell23_957167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 3, 3].length) (baseStart_957167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957167 prefixEnd_957167 := by exact prefixLift 957167
  have htrace : WordTrace (prefixWord ++ tailWord_957167) baseStart_957167 baseEnd_957167 := by
    simpa [prefixWord, tailWord_957167, baseEnd_957167] using wordTrace_append hprefix tailTrace_957167
  have hstable : (prefixWord ++ tailWord_957167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957167).length < 2 ^ (prefixWord ++ tailWord_957167).sum := by decide
  have hdescent : baseEnd_957167 < baseStart_957167 := by decide
  rcases family_descends (prefixWord ++ tailWord_957167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957177 : List Nat := [1, 2, 1, 3, 1, 1, 1, 4, 2, 5, 2]
def baseStart_957177 : Nat := 118140960795 + 957177 * 2 ^ 59
def prefixEnd_957177 : Nat := 4983230072969 + 3 ^ 40 * 957177 * 2
def baseEnd_957177 : Nat := 491491872428706774285529

theorem tailTrace_957177 : CollatzResearch.WordTrace tailWord_957177 prefixEnd_957177 491491872428706774285529 := by
  unfold tailWord_957177
  simp only [CollatzResearch.WordTrace]
  refine ⟨34911113253318676661973785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23274075502212451107982523 34911113253318676661973785)
  ·
    refine ⟨26183334939989007496480339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34911113253318676661973785 26183334939989007496480339)
    ·
      refine ⟨39275002409983511244720509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26183334939989007496480339 39275002409983511244720509)
      ·
        refine ⟨14728125903743816716770191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39275002409983511244720509 14728125903743816716770191)
        ·
          refine ⟨22092188855615725075155287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14728125903743816716770191 22092188855615725075155287)
          ·
            refine ⟨33138283283423587612732931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22092188855615725075155287 33138283283423587612732931)
            ·
              refine ⟨49707424925135381419099397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33138283283423587612732931 49707424925135381419099397)
              ·
                refine ⟨9320142173462884016081137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49707424925135381419099397 9320142173462884016081137)
                ·
                  refine ⟨6990106630097163012060853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9320142173462884016081137 6990106630097163012060853)
                  ·
                    refine ⟨655322496571609032380705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6990106630097163012060853 655322496571609032380705)
                    ·
                      refine ⟨491491872428706774285529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 655322496571609032380705 491491872428706774285529)
                      ·
                        rfl

theorem cell23_957177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 5, 2].length) (baseStart_957177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957177 prefixEnd_957177 := by exact prefixLift 957177
  have htrace : WordTrace (prefixWord ++ tailWord_957177) baseStart_957177 baseEnd_957177 := by
    simpa [prefixWord, tailWord_957177, baseEnd_957177] using wordTrace_append hprefix tailTrace_957177
  have hstable : (prefixWord ++ tailWord_957177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957177).length < 2 ^ (prefixWord ++ tailWord_957177).sum := by decide
  have hdescent : baseEnd_957177 < baseStart_957177 := by decide
  rcases family_descends (prefixWord ++ tailWord_957177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957191 : List Nat := [1, 1, 4, 4, 1, 3, 1, 3, 5]
def baseStart_957191 : Nat := 118140960795 + 957191 * 2 ^ 59
def prefixEnd_957191 : Nat := 4983230072969 + 3 ^ 40 * 957191 * 2
def baseEnd_957191 : Nat := 54611006795318857723385

theorem tailTrace_957191 : CollatzResearch.WordTrace tailWord_957191 prefixEnd_957191 54611006795318857723385 := by
  unfold tailWord_957191
  simp only [CollatzResearch.WordTrace]
  refine ⟨34911623875267957052983427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23274415916845304701988951 34911623875267957052983427)
  ·
    refine ⟨52367435812901935579475141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34911623875267957052983427 52367435812901935579475141)
    ·
      refine ⟨9818894214919112921151589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52367435812901935579475141 9818894214919112921151589)
      ·
        refine ⟨1841042665297333672715923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9818894214919112921151589 1841042665297333672715923)
        ·
          refine ⟨2761563997946000509073885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1841042665297333672715923 2761563997946000509073885)
          ·
            refine ⟨1035586499229750190902707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2761563997946000509073885 1035586499229750190902707)
            ·
              refine ⟨1553379748844625286354061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035586499229750190902707 1553379748844625286354061)
              ·
                refine ⟨582517405816734482382773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1553379748844625286354061 582517405816734482382773)
                ·
                  refine ⟨54611006795318857723385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 582517405816734482382773 54611006795318857723385)
                  ·
                    rfl

theorem cell23_957191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 3, 5].length) (baseStart_957191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957191 prefixEnd_957191 := by exact prefixLift 957191
  have htrace : WordTrace (prefixWord ++ tailWord_957191) baseStart_957191 baseEnd_957191 := by
    simpa [prefixWord, tailWord_957191, baseEnd_957191] using wordTrace_append hprefix tailTrace_957191
  have hstable : (prefixWord ++ tailWord_957191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957191).length < 2 ^ (prefixWord ++ tailWord_957191).sum := by decide
  have hdescent : baseEnd_957191 < baseStart_957191 := by decide
  rcases family_descends (prefixWord ++ tailWord_957191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957224 : List Nat := [2, 1, 5, 1, 1, 1, 2, 1, 1, 6, 2]
def baseStart_957224 : Nat := 118140960795 + 957224 * 2 ^ 59
def prefixEnd_957224 : Nat := 4983230072969 + 3 ^ 40 * 957224 * 2
def baseEnd_957224 : Nat := 491516006019468090397813

theorem tailTrace_957224 : CollatzResearch.WordTrace tailWord_957224 prefixEnd_957224 491516006019468090397813 := by
  unfold tailWord_957224
  simp only [CollatzResearch.WordTrace]
  refine ⟨17456413742074201844467363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23275218322765602459289817 17456413742074201844467363)
  ·
    refine ⟨26184620613111302766701045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17456413742074201844467363 26184620613111302766701045)
    ·
      refine ⟨2454808182479184634378223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26184620613111302766701045 2454808182479184634378223)
      ·
        refine ⟨3682212273718776951567335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2454808182479184634378223 3682212273718776951567335)
        ·
          refine ⟨5523318410578165427351003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3682212273718776951567335 5523318410578165427351003)
          ·
            refine ⟨8284977615867248141026505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5523318410578165427351003 8284977615867248141026505)
            ·
              refine ⟨6213733211900436105769879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8284977615867248141026505 6213733211900436105769879)
              ·
                refine ⟨9320599817850654158654819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6213733211900436105769879 9320599817850654158654819)
                ·
                  refine ⟨13980899726775981237982229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9320599817850654158654819 13980899726775981237982229)
                  ·
                    refine ⟨655354674692624120530417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13980899726775981237982229 655354674692624120530417)
                    ·
                      refine ⟨491516006019468090397813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 655354674692624120530417 491516006019468090397813)
                      ·
                        rfl

theorem cell23_957224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_957224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957224 prefixEnd_957224 := by exact prefixLift 957224
  have htrace : WordTrace (prefixWord ++ tailWord_957224) baseStart_957224 baseEnd_957224 := by
    simpa [prefixWord, tailWord_957224, baseEnd_957224] using wordTrace_append hprefix tailTrace_957224
  have hstable : (prefixWord ++ tailWord_957224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957224).length < 2 ^ (prefixWord ++ tailWord_957224).sum := by decide
  have hdescent : baseEnd_957224 < baseStart_957224 := by decide
  rcases family_descends (prefixWord ++ tailWord_957224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957268 : List Nat := [2, 4, 1, 1, 4, 1, 1, 4, 1, 4]
def baseStart_957268 : Nat := 118140960795 + 957268 * 2 ^ 59
def prefixEnd_957268 : Nat := 4983230072969 + 3 ^ 40 * 957268 * 2
def baseEnd_957268 : Nat := 163846199722755306082537

theorem tailTrace_957268 : CollatzResearch.WordTrace tailWord_957268 prefixEnd_957268 163846199722755306082537 := by
  unfold tailWord_957268
  simp only [CollatzResearch.WordTrace]
  refine ⟨17457216147994499601768229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23276288197325999469024305 17457216147994499601768229)
  ·
    refine ⟨3273228027748968675331543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17457216147994499601768229 3273228027748968675331543)
    ·
      refine ⟨4909842041623453012997315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3273228027748968675331543 4909842041623453012997315)
      ·
        refine ⟨7364763062435179519495973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4909842041623453012997315 7364763062435179519495973)
        ·
          refine ⟨1380893074206596159905495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7364763062435179519495973 1380893074206596159905495)
          ·
            refine ⟨2071339611309894239858243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1380893074206596159905495 2071339611309894239858243)
            ·
              refine ⟨3107009416964841359787365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2071339611309894239858243 3107009416964841359787365)
              ·
                refine ⟨582564265680907754960131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3107009416964841359787365 582564265680907754960131)
                ·
                  refine ⟨873846398521361632440197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 582564265680907754960131 873846398521361632440197)
                  ·
                    refine ⟨163846199722755306082537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 873846398521361632440197 163846199722755306082537)
                    ·
                      rfl

theorem cell23_957268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_957268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957268 prefixEnd_957268 := by exact prefixLift 957268
  have htrace : WordTrace (prefixWord ++ tailWord_957268) baseStart_957268 baseEnd_957268 := by
    simpa [prefixWord, tailWord_957268, baseEnd_957268] using wordTrace_append hprefix tailTrace_957268
  have hstable : (prefixWord ++ tailWord_957268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957268).length < 2 ^ (prefixWord ++ tailWord_957268).sum := by decide
  have hdescent : baseEnd_957268 < baseStart_957268 := by decide
  rcases family_descends (prefixWord ++ tailWord_957268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957301 : List Nat := [1, 3, 4, 1, 1, 3, 1, 1, 1, 5, 2]
def baseStart_957301 : Nat := 118140960795 + 957301 * 2 ^ 59
def prefixEnd_957301 : Nat := 4983230072969 + 3 ^ 40 * 957301 * 2
def baseEnd_957301 : Nat := 491555544029864289134959

theorem tailTrace_957301 : CollatzResearch.WordTrace tailWord_957301 prefixEnd_957301 491555544029864289134959 := by
  unfold tailWord_957301
  simp only [CollatzResearch.WordTrace]
  refine ⟨34915635904869445839487757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23277090603246297226325171 34915635904869445839487757)
  ·
    refine ⟨13093363464326042189807909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34915635904869445839487757 13093363464326042189807909)
    ·
      refine ⟨2455005649561132910588983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13093363464326042189807909 2455005649561132910588983)
      ·
        refine ⟨3682508474341699365883475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2455005649561132910588983 3682508474341699365883475)
        ·
          refine ⟨5523762711512549048825213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3682508474341699365883475 5523762711512549048825213)
          ·
            refine ⟨2071411016817205893309455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5523762711512549048825213 2071411016817205893309455)
            ·
              refine ⟨3107116525225808839964183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2071411016817205893309455 3107116525225808839964183)
              ·
                refine ⟨4660674787838713259946275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3107116525225808839964183 4660674787838713259946275)
                ·
                  refine ⟨6991012181758069889919413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4660674787838713259946275 6991012181758069889919413)
                  ·
                    refine ⟨655407392039819052179945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6991012181758069889919413 655407392039819052179945)
                    ·
                      refine ⟨491555544029864289134959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 655407392039819052179945 491555544029864289134959)
                      ·
                        rfl

theorem cell23_957301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_957301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957301 prefixEnd_957301 := by exact prefixLift 957301
  have htrace : WordTrace (prefixWord ++ tailWord_957301) baseStart_957301 baseEnd_957301 := by
    simpa [prefixWord, tailWord_957301, baseEnd_957301] using wordTrace_append hprefix tailTrace_957301
  have hstable : (prefixWord ++ tailWord_957301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957301).length < 2 ^ (prefixWord ++ tailWord_957301).sum := by decide
  have hdescent : baseEnd_957301 < baseStart_957301 := by decide
  rcases family_descends (prefixWord ++ tailWord_957301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957307 : List Nat := [1, 1, 1, 1, 1, 5, 4, 2, 1, 6]
def baseStart_957307 : Nat := 118140960795 + 957307 * 2 ^ 59
def prefixEnd_957307 : Nat := 4983230072969 + 3 ^ 40 * 957307 * 2
def baseEnd_957307 : Nat := 163852874971263755219977

theorem tailTrace_957307 : CollatzResearch.WordTrace tailWord_957307 prefixEnd_957307 163852874971263755219977 := by
  unfold tailWord_957307
  simp only [CollatzResearch.WordTrace]
  refine ⟨34915854742847708864206175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23277236495231805909470783 34915854742847708864206175)
  ·
    refine ⟨52373782114271563296309263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34915854742847708864206175 52373782114271563296309263)
    ·
      refine ⟨78560673171407344944463895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52373782114271563296309263 78560673171407344944463895)
      ·
        refine ⟨117841009757111017416695843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78560673171407344944463895 117841009757111017416695843)
        ·
          refine ⟨176761514635666526125043765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117841009757111017416695843 176761514635666526125043765)
          ·
            refine ⟨16571391997093736824222853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 176761514635666526125043765 16571391997093736824222853)
            ·
              refine ⟨3107135999455075654541785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16571391997093736824222853 3107135999455075654541785)
              ·
                refine ⟨2330351999591306740906339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3107135999455075654541785 2330351999591306740906339)
                ·
                  refine ⟨3495527999386960111359509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2330351999591306740906339 3495527999386960111359509)
                  ·
                    refine ⟨163852874971263755219977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3495527999386960111359509 163852874971263755219977)
                    ·
                      rfl

theorem cell23_957307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 6].length) (baseStart_957307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957307 prefixEnd_957307 := by exact prefixLift 957307
  have htrace : WordTrace (prefixWord ++ tailWord_957307) baseStart_957307 baseEnd_957307 := by
    simpa [prefixWord, tailWord_957307, baseEnd_957307] using wordTrace_append hprefix tailTrace_957307
  have hstable : (prefixWord ++ tailWord_957307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957307).length < 2 ^ (prefixWord ++ tailWord_957307).sum := by decide
  have hdescent : baseEnd_957307 < baseStart_957307 := by decide
  rcases family_descends (prefixWord ++ tailWord_957307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957344 : List Nat := [2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 4]
def baseStart_957344 : Nat := 118140960795 + 957344 * 2 ^ 59
def prefixEnd_957344 : Nat := 4983230072969 + 3 ^ 40 * 957344 * 2
def baseEnd_957344 : Nat := 491577623698007620897261

theorem tailTrace_957344 : CollatzResearch.WordTrace tailWord_957344 prefixEnd_957344 491577623698007620897261 := by
  unfold tailWord_957344
  simp only [CollatzResearch.WordTrace]
  refine ⟨17458602121856832091651543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23278136162475776122202057 17458602121856832091651543)
  ·
    refine ⟨26187903182785248137477315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17458602121856832091651543 26187903182785248137477315)
    ·
      refine ⟨39281854774177872206215973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26187903182785248137477315 39281854774177872206215973)
      ·
        refine ⟨7365347770158351038665495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39281854774177872206215973 7365347770158351038665495)
        ·
          refine ⟨11048021655237526557998243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7365347770158351038665495 11048021655237526557998243)
          ·
            refine ⟨16572032482856289836997365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11048021655237526557998243 16572032482856289836997365)
            ·
              refine ⟨1553628045267777172218503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16572032482856289836997365 1553628045267777172218503)
              ·
                refine ⟨2330442067901665758327755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1553628045267777172218503 2330442067901665758327755)
                ·
                  refine ⟨3495663101852498637491633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2330442067901665758327755 3495663101852498637491633)
                  ·
                    refine ⟨2621747326389373978118725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3495663101852498637491633 2621747326389373978118725)
                    ·
                      refine ⟨491577623698007620897261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2621747326389373978118725 491577623698007620897261)
                      ·
                        rfl

theorem cell23_957344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_957344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957344 prefixEnd_957344 := by exact prefixLift 957344
  have htrace : WordTrace (prefixWord ++ tailWord_957344) baseStart_957344 baseEnd_957344 := by
    simpa [prefixWord, tailWord_957344, baseEnd_957344] using wordTrace_append hprefix tailTrace_957344
  have hstable : (prefixWord ++ tailWord_957344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957344).length < 2 ^ (prefixWord ++ tailWord_957344).sum := by decide
  have hdescent : baseEnd_957344 < baseStart_957344 := by decide
  rcases family_descends (prefixWord ++ tailWord_957344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957425 : List Nat := [1, 2, 2, 2, 4, 2, 3, 1, 1, 3, 2]
def baseStart_957425 : Nat := 118140960795 + 957425 * 2 ^ 59
def prefixEnd_957425 : Nat := 4983230072969 + 3 ^ 40 * 957425 * 2
def baseEnd_957425 : Nat := 491619215631021803984389

theorem tailTrace_957425 : CollatzResearch.WordTrace tailWord_957425 prefixEnd_957425 491619215631021803984389 := by
  unfold tailWord_957425
  simp only [CollatzResearch.WordTrace]
  refine ⟨34920158556420215017001729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23280105704280143344667819 34920158556420215017001729)
  ·
    refine ⟨26190118917315161262751297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34920158556420215017001729 26190118917315161262751297)
    ·
      refine ⟨19642589187986370947063473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26190118917315161262751297 19642589187986370947063473)
      ·
        refine ⟨14731941890989778210297605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19642589187986370947063473 14731941890989778210297605)
        ·
          refine ⟨2762239104560583414430801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14731941890989778210297605 2762239104560583414430801)
          ·
            refine ⟨2071679328420437560823101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2762239104560583414430801 2071679328420437560823101)
            ·
              refine ⟨776879748157664085308663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2071679328420437560823101 776879748157664085308663)
              ·
                refine ⟨1165319622236496127962995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 776879748157664085308663 1165319622236496127962995)
                ·
                  refine ⟨1747979433354744191944493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1165319622236496127962995 1747979433354744191944493)
                  ·
                    refine ⟨655492287508029071979185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1747979433354744191944493 655492287508029071979185)
                    ·
                      refine ⟨491619215631021803984389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 655492287508029071979185 491619215631021803984389)
                      ·
                        rfl

theorem cell23_957425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 1, 3, 2].length) (baseStart_957425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957425 prefixEnd_957425 := by exact prefixLift 957425
  have htrace : WordTrace (prefixWord ++ tailWord_957425) baseStart_957425 baseEnd_957425 := by
    simpa [prefixWord, tailWord_957425, baseEnd_957425] using wordTrace_append hprefix tailTrace_957425
  have hstable : (prefixWord ++ tailWord_957425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957425).length < 2 ^ (prefixWord ++ tailWord_957425).sum := by decide
  have hdescent : baseEnd_957425 < baseStart_957425 := by decide
  rcases family_descends (prefixWord ++ tailWord_957425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957521 : List Nat := [1, 2, 2, 1, 3, 1, 4, 2, 3, 4]
def baseStart_957521 : Nat := 118140960795 + 957521 * 2 ^ 59
def prefixEnd_957521 : Nat := 4983230072969 + 3 ^ 40 * 957521 * 2
def baseEnd_957521 : Nat := 163889503257951142794649

theorem tailTrace_957521 : CollatzResearch.WordTrace tailWord_957521 prefixEnd_957521 163889503257951142794649 := by
  unfold tailWord_957521
  simp only [CollatzResearch.WordTrace]
  refine ⟨34923659964072423412496417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23282439976048282274997611 34923659964072423412496417)
  ·
    refine ⟨26192744973054317559372313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34923659964072423412496417 26192744973054317559372313)
    ·
      refine ⟨19644558729790738169529235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26192744973054317559372313 19644558729790738169529235)
      ·
        refine ⟨29466838094686107254293853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19644558729790738169529235 29466838094686107254293853)
        ·
          refine ⟨11050064285507290220360195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29466838094686107254293853 11050064285507290220360195)
          ·
            refine ⟨16575096428260935330540293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11050064285507290220360195 16575096428260935330540293)
            ·
              refine ⟨3107830580298925374476305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16575096428260935330540293 3107830580298925374476305)
              ·
                refine ⟨2330872935224194030857229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3107830580298925374476305 2330872935224194030857229)
                ·
                  refine ⟨874077350709072761571461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2330872935224194030857229 874077350709072761571461)
                  ·
                    refine ⟨163889503257951142794649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 874077350709072761571461 163889503257951142794649)
                    ·
                      rfl

theorem cell23_957521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 3, 4].length) (baseStart_957521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957521 prefixEnd_957521 := by exact prefixLift 957521
  have htrace : WordTrace (prefixWord ++ tailWord_957521) baseStart_957521 baseEnd_957521 := by
    simpa [prefixWord, tailWord_957521, baseEnd_957521] using wordTrace_append hprefix tailTrace_957521
  have hstable : (prefixWord ++ tailWord_957521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957521).length < 2 ^ (prefixWord ++ tailWord_957521).sum := by decide
  have hdescent : baseEnd_957521 < baseStart_957521 := by decide
  rcases family_descends (prefixWord ++ tailWord_957521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957578 : List Nat := [3, 1, 2, 3, 1, 1, 2, 1, 5, 1, 3]
def baseStart_957578 : Nat := 118140960795 + 957578 * 2 ^ 59
def prefixEnd_957578 : Nat := 4983230072969 + 3 ^ 40 * 957578 * 2
def baseEnd_957578 : Nat := 491697778171159705371185

theorem tailTrace_957578 : CollatzResearch.WordTrace tailWord_957578 prefixEnd_957578 491697778171159705371185 := by
  unfold tailWord_957578
  simp only [CollatzResearch.WordTrace]
  refine ⟨8731434731216480536830347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23283825949910614764880925 8731434731216480536830347)
  ·
    refine ⟨13097152096824720805245521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8731434731216480536830347 13097152096824720805245521)
    ·
      refine ⟨9822864072618540603934141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13097152096824720805245521 9822864072618540603934141)
      ·
        refine ⟨3683574027231952726475303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9822864072618540603934141 3683574027231952726475303)
        ·
          refine ⟨5525361040847929089712955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3683574027231952726475303 5525361040847929089712955)
          ·
            refine ⟨8288041561271893634569433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5525361040847929089712955 8288041561271893634569433)
            ·
              refine ⟨6216031170953920225927075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8288041561271893634569433 6216031170953920225927075)
              ·
                refine ⟨9324046756430880338890613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6216031170953920225927075 9324046756430880338890613)
                ·
                  refine ⟨874129383415395031770995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9324046756430880338890613 874129383415395031770995)
                  ·
                    refine ⟨1311194075123092547656493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 874129383415395031770995 1311194075123092547656493)
                    ·
                      refine ⟨491697778171159705371185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1311194075123092547656493 491697778171159705371185)
                      ·
                        rfl

theorem cell23_957578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_957578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957578 prefixEnd_957578 := by exact prefixLift 957578
  have htrace : WordTrace (prefixWord ++ tailWord_957578) baseStart_957578 baseEnd_957578 := by
    simpa [prefixWord, tailWord_957578, baseEnd_957578] using wordTrace_append hprefix tailTrace_957578
  have hstable : (prefixWord ++ tailWord_957578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957578).length < 2 ^ (prefixWord ++ tailWord_957578).sum := by decide
  have hdescent : baseEnd_957578 < baseStart_957578 := by decide
  rcases family_descends (prefixWord ++ tailWord_957578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957624 : List Nat := [2, 1, 2, 1, 2, 1, 2, 12]
def baseStart_957624 : Nat := 118140960795 + 957624 * 2 ^ 59
def prefixEnd_957624 : Nat := 4983230072969 + 3 ^ 40 * 957624 * 2
def baseEnd_957624 : Nat := 18211903640046908347999

theorem tailTrace_957624 : CollatzResearch.WordTrace tailWord_957624 prefixEnd_957624 18211903640046908347999 := by
  unfold tailWord_957624
  simp only [CollatzResearch.WordTrace]
  refine ⟨17463708341349636001747963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23284944455132848002330617 17463708341349636001747963)
  ·
    refine ⟨26195562512024454002621945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17463708341349636001747963 26195562512024454002621945)
    ·
      refine ⟨19646671884018340501966459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26195562512024454002621945 19646671884018340501966459)
      ·
        refine ⟨29470007826027510752949689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19646671884018340501966459 29470007826027510752949689)
        ·
          refine ⟨22102505869520633064712267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29470007826027510752949689 22102505869520633064712267)
          ·
            refine ⟨33153758804280949597068401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22102505869520633064712267 33153758804280949597068401)
            ·
              refine ⟨24865319103210712197801301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33153758804280949597068401 24865319103210712197801301)
              ·
                refine ⟨18211903640046908347999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 24865319103210712197801301 18211903640046908347999)
                ·
                  rfl

theorem cell23_957624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 12].length) (baseStart_957624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957624 prefixEnd_957624 := by exact prefixLift 957624
  have htrace : WordTrace (prefixWord ++ tailWord_957624) baseStart_957624 baseEnd_957624 := by
    simpa [prefixWord, tailWord_957624, baseEnd_957624] using wordTrace_append hprefix tailTrace_957624
  have hstable : (prefixWord ++ tailWord_957624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957624).length < 2 ^ (prefixWord ++ tailWord_957624).sum := by decide
  have hdescent : baseEnd_957624 < baseStart_957624 := by decide
  rcases family_descends (prefixWord ++ tailWord_957624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957628 : List Nat := [2, 2, 2, 3, 2, 2, 2, 1, 1, 6]
def baseStart_957628 : Nat := 118140960795 + 957628 * 2 ^ 59
def prefixEnd_957628 : Nat := 4983230072969 + 3 ^ 40 * 957628 * 2
def baseEnd_957628 : Nat := 163907817401294836581985

theorem tailTrace_957628 : CollatzResearch.WordTrace tailWord_957628 prefixEnd_957628 163907817401294836581985 := by
  unfold tailWord_957628
  simp only [CollatzResearch.WordTrace]
  refine ⟨17463781287342390343320769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23285041716456520457761025 17463781287342390343320769)
  ·
    refine ⟨13097835965506792757490577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17463781287342390343320769 13097835965506792757490577)
    ·
      refine ⟨9823376974130094568117933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13097835965506792757490577 9823376974130094568117933)
      ·
        refine ⟨3683766365298785463044225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9823376974130094568117933 3683766365298785463044225)
        ·
          refine ⟨2762824773974089097283169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3683766365298785463044225 2762824773974089097283169)
          ·
            refine ⟨2072118580480566822962377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2762824773974089097283169 2072118580480566822962377)
            ·
              refine ⟨1554088935360425117221783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2072118580480566822962377 1554088935360425117221783)
              ·
                refine ⟨2331133403040637675832675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1554088935360425117221783 2331133403040637675832675)
                ·
                  refine ⟨3496700104560956513749013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2331133403040637675832675 3496700104560956513749013)
                  ·
                    refine ⟨163907817401294836581985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3496700104560956513749013 163907817401294836581985)
                    ·
                      rfl

theorem cell23_957628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_957628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957628 prefixEnd_957628 := by exact prefixLift 957628
  have htrace : WordTrace (prefixWord ++ tailWord_957628) baseStart_957628 baseEnd_957628 := by
    simpa [prefixWord, tailWord_957628, baseEnd_957628] using wordTrace_append hprefix tailTrace_957628
  have hstable : (prefixWord ++ tailWord_957628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957628).length < 2 ^ (prefixWord ++ tailWord_957628).sum := by decide
  have hdescent : baseEnd_957628 < baseStart_957628 := by decide
  rcases family_descends (prefixWord ++ tailWord_957628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957631 : List Nat := [1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 4]
def baseStart_957631 : Nat := 118140960795 + 957631 * 2 ^ 59
def prefixEnd_957631 : Nat := 4983230072969 + 3 ^ 40 * 957631 * 2
def baseEnd_957631 : Nat := 491724992645847998008441

theorem tailTrace_957631 : CollatzResearch.WordTrace tailWord_957631 prefixEnd_957631 491724992645847998008441 := by
  unfold tailWord_957631
  simp only [CollatzResearch.WordTrace]
  refine ⟨34927671993673912199000747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23285114662449274799333831 34927671993673912199000747)
  ·
    refine ⟨52391507990510868298501121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34927671993673912199000747 52391507990510868298501121)
    ·
      refine ⟨39293630992883151223875841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52391507990510868298501121 39293630992883151223875841)
      ·
        refine ⟨29470223244662363417906881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39293630992883151223875841 29470223244662363417906881)
        ·
          refine ⟨22102667433496772563430161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29470223244662363417906881 22102667433496772563430161)
          ·
            refine ⟨16577000575122579422572621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22102667433496772563430161 16577000575122579422572621)
            ·
              refine ⟨6216375215670967283464733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16577000575122579422572621 6216375215670967283464733)
              ·
                refine ⟨2331140705876612731299275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6216375215670967283464733 2331140705876612731299275)
                ·
                  refine ⟨3496711058814919096948913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2331140705876612731299275 3496711058814919096948913)
                  ·
                    refine ⟨2622533294111189322711685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3496711058814919096948913 2622533294111189322711685)
                    ·
                      refine ⟨491724992645847998008441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2622533294111189322711685 491724992645847998008441)
                      ·
                        rfl

theorem cell23_957631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 4].length) (baseStart_957631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957631 prefixEnd_957631 := by exact prefixLift 957631
  have htrace : WordTrace (prefixWord ++ tailWord_957631) baseStart_957631 baseEnd_957631 := by
    simpa [prefixWord, tailWord_957631, baseEnd_957631] using wordTrace_append hprefix tailTrace_957631
  have hstable : (prefixWord ++ tailWord_957631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957631).length < 2 ^ (prefixWord ++ tailWord_957631).sum := by decide
  have hdescent : baseEnd_957631 < baseStart_957631 := by decide
  rcases family_descends (prefixWord ++ tailWord_957631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957652 : List Nat := [2, 4, 1, 4, 1, 1, 1, 3, 1, 1, 4]
def baseStart_957652 : Nat := 118140960795 + 957652 * 2 ^ 59
def prefixEnd_957652 : Nat := 4983230072969 + 3 ^ 40 * 957652 * 2
def baseEnd_957652 : Nat := 491735775739592415845845

theorem tailTrace_957652 : CollatzResearch.WordTrace tailWord_957652 prefixEnd_957652 491735775739592415845845 := by
  unfold tailWord_957652
  simp only [CollatzResearch.WordTrace]
  refine ⟨17464218963298916392757605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23285625284398555190343473 17464218963298916392757605)
  ·
    refine ⟨3274541055618546823642051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17464218963298916392757605 3274541055618546823642051)
    ·
      refine ⟨4911811583427820235463077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3274541055618546823642051 4911811583427820235463077)
      ·
        refine ⟨920964671892716294149327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4911811583427820235463077 920964671892716294149327)
        ·
          refine ⟨1381447007839074441223991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 920964671892716294149327 1381447007839074441223991)
          ·
            refine ⟨2072170511758611661835987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1381447007839074441223991 2072170511758611661835987)
            ·
              refine ⟨3108255767637917492753981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2072170511758611661835987 3108255767637917492753981)
              ·
                refine ⟨1165595912864219059782743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3108255767637917492753981 1165595912864219059782743)
                ·
                  refine ⟨1748393869296328589674115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1165595912864219059782743 1748393869296328589674115)
                  ·
                    refine ⟨2622590803944492884511173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1748393869296328589674115 2622590803944492884511173)
                    ·
                      refine ⟨491735775739592415845845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2622590803944492884511173 491735775739592415845845)
                      ·
                        rfl

theorem cell23_957652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_957652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957652 prefixEnd_957652 := by exact prefixLift 957652
  have htrace : WordTrace (prefixWord ++ tailWord_957652) baseStart_957652 baseEnd_957652 := by
    simpa [prefixWord, tailWord_957652, baseEnd_957652] using wordTrace_append hprefix tailTrace_957652
  have hstable : (prefixWord ++ tailWord_957652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957652).length < 2 ^ (prefixWord ++ tailWord_957652).sum := by decide
  have hdescent : baseEnd_957652 < baseStart_957652 := by decide
  rcases family_descends (prefixWord ++ tailWord_957652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957655 : List Nat := [1, 1, 3, 2, 1, 2, 6, 1, 1, 2, 3]
def baseStart_957655 : Nat := 118140960795 + 957655 * 2 ^ 59
def prefixEnd_957655 : Nat := 4983230072969 + 3 ^ 40 * 957655 * 2
def baseEnd_957655 : Nat := 491737316181555904108331

theorem tailTrace_957655 : CollatzResearch.WordTrace tailWord_957655 prefixEnd_957655 491737316181555904108331 := by
  unfold tailWord_957655
  simp only [CollatzResearch.WordTrace]
  refine ⟨34928547345586964297874419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23285698230391309531916279 34928547345586964297874419)
  ·
    refine ⟨52392821018380446446811629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34928547345586964297874419 52392821018380446446811629)
    ·
      refine ⟨19647307881892667417554361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52392821018380446446811629 19647307881892667417554361)
      ·
        refine ⟨14735480911419500563165771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19647307881892667417554361 14735480911419500563165771)
        ·
          refine ⟨22103221367129250844748657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14735480911419500563165771 22103221367129250844748657)
          ·
            refine ⟨16577416025346938133561493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22103221367129250844748657 16577416025346938133561493)
            ·
              refine ⟨777066376188137725010695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16577416025346938133561493 777066376188137725010695)
              ·
                refine ⟨1165599564282206587516043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 777066376188137725010695 1165599564282206587516043)
                ·
                  refine ⟨1748399346423309881274065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1165599564282206587516043 1748399346423309881274065)
                  ·
                    refine ⟨1311299509817482410955549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1748399346423309881274065 1311299509817482410955549)
                    ·
                      refine ⟨491737316181555904108331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1311299509817482410955549 491737316181555904108331)
                      ·
                        rfl

theorem cell23_957655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 1, 2, 3].length) (baseStart_957655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957655 prefixEnd_957655 := by exact prefixLift 957655
  have htrace : WordTrace (prefixWord ++ tailWord_957655) baseStart_957655 baseEnd_957655 := by
    simpa [prefixWord, tailWord_957655, baseEnd_957655] using wordTrace_append hprefix tailTrace_957655
  have hstable : (prefixWord ++ tailWord_957655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957655).length < 2 ^ (prefixWord ++ tailWord_957655).sum := by decide
  have hdescent : baseEnd_957655 < baseStart_957655 := by decide
  rcases family_descends (prefixWord ++ tailWord_957655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957682 : List Nat := [3, 2, 1, 3, 4, 1, 1, 1, 1, 2, 4]
def baseStart_957682 : Nat := 118140960795 + 957682 * 2 ^ 59
def prefixEnd_957682 : Nat := 4983230072969 + 3 ^ 40 * 957682 * 2
def baseEnd_957682 : Nat := 491751180159227298470707

theorem tailTrace_957682 : CollatzResearch.WordTrace tailWord_957682 prefixEnd_957682 491751180159227298470707 := by
  unfold tailWord_957682
  simp only [CollatzResearch.WordTrace]
  refine ⟨8732383029122286977276825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23286354744326098606071533 8732383029122286977276825)
  ·
    refine ⟨6549287271841715232957619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8732383029122286977276825 6549287271841715232957619)
    ·
      refine ⟨9823930907762572849436429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6549287271841715232957619 9823930907762572849436429)
      ·
        refine ⟨3683974090410964818538661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9823930907762572849436429 3683974090410964818538661)
        ·
          refine ⟨690745141952055903475999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3683974090410964818538661 690745141952055903475999)
          ·
            refine ⟨1036117712928083855213999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690745141952055903475999 1036117712928083855213999)
            ·
              refine ⟨1554176569392125782820999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1036117712928083855213999 1554176569392125782820999)
              ·
                refine ⟨2331264854088188674231499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1554176569392125782820999 2331264854088188674231499)
                ·
                  refine ⟨3496897281132283011347249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2331264854088188674231499 3496897281132283011347249)
                  ·
                    refine ⟨2622672960849212258510437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3496897281132283011347249 2622672960849212258510437)
                    ·
                      refine ⟨491751180159227298470707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2622672960849212258510437 491751180159227298470707)
                      ·
                        rfl

theorem cell23_957682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_957682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957682 prefixEnd_957682 := by exact prefixLift 957682
  have htrace : WordTrace (prefixWord ++ tailWord_957682) baseStart_957682 baseEnd_957682 := by
    simpa [prefixWord, tailWord_957682, baseEnd_957682] using wordTrace_append hprefix tailTrace_957682
  have hstable : (prefixWord ++ tailWord_957682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957682).length < 2 ^ (prefixWord ++ tailWord_957682).sum := by decide
  have hdescent : baseEnd_957682 < baseStart_957682 := by decide
  rcases family_descends (prefixWord ++ tailWord_957682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957695 : List Nat := [1, 1, 2, 2, 1, 5, 1, 4, 1, 3, 2]
def baseStart_957695 : Nat := 118140960795 + 957695 * 2 ^ 59
def prefixEnd_957695 : Nat := 4983230072969 + 3 ^ 40 * 957695 * 2
def baseEnd_957695 : Nat := 491757855407735747608147

theorem tailTrace_957695 : CollatzResearch.WordTrace tailWord_957695 prefixEnd_957695 491757855407735747608147 := by
  unfold tailWord_957695
  simp only [CollatzResearch.WordTrace]
  refine ⟨34930006265442051129330539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23286670843628034086220359 34930006265442051129330539)
  ·
    refine ⟨52395009398163076693995809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34930006265442051129330539 52395009398163076693995809)
    ·
      refine ⟨39296257048622307520496857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52395009398163076693995809 39296257048622307520496857)
      ·
        refine ⟨29472192786466730640372643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39296257048622307520496857 29472192786466730640372643)
        ·
          refine ⟨44208289179700095960558965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29472192786466730640372643 44208289179700095960558965)
          ·
            refine ⟨4144527110596883996302403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44208289179700095960558965 4144527110596883996302403)
            ·
              refine ⟨6216790665895325994453605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4144527110596883996302403 6216790665895325994453605)
              ·
                refine ⟨1165648249855373623960051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6216790665895325994453605 1165648249855373623960051)
                ·
                  refine ⟨1748472374783060435940077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1165648249855373623960051 1748472374783060435940077)
                  ·
                    refine ⟨655677140543647663477529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1748472374783060435940077 655677140543647663477529)
                    ·
                      refine ⟨491757855407735747608147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 655677140543647663477529 491757855407735747608147)
                      ·
                        rfl

theorem cell23_957695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 3, 2].length) (baseStart_957695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957695 prefixEnd_957695 := by exact prefixLift 957695
  have htrace : WordTrace (prefixWord ++ tailWord_957695) baseStart_957695 baseEnd_957695 := by
    simpa [prefixWord, tailWord_957695, baseEnd_957695] using wordTrace_append hprefix tailTrace_957695
  have hstable : (prefixWord ++ tailWord_957695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957695).length < 2 ^ (prefixWord ++ tailWord_957695).sum := by decide
  have hdescent : baseEnd_957695 < baseStart_957695 := by decide
  rcases family_descends (prefixWord ++ tailWord_957695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957711 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 3, 6, 3]
def baseStart_957711 : Nat := 118140960795 + 957711 * 2 ^ 59
def prefixEnd_957711 : Nat := 4983230072969 + 3 ^ 40 * 957711 * 2
def baseEnd_957711 : Nat := 491766071098207685008073

theorem tailTrace_957711 : CollatzResearch.WordTrace tailWord_957711 prefixEnd_957711 491766071098207685008073 := by
  unfold tailWord_957711
  simp only [CollatzResearch.WordTrace]
  refine ⟨34930589833384085861912987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23287059888922723907941991 34930589833384085861912987)
  ·
    refine ⟨52395884750076128792869481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34930589833384085861912987 52395884750076128792869481)
    ·
      refine ⟨39296913562557096594652111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52395884750076128792869481 39296913562557096594652111)
      ·
        refine ⟨58945370343835644891978167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39296913562557096594652111 58945370343835644891978167)
        ·
          refine ⟨88418055515753467337967251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58945370343835644891978167 88418055515753467337967251)
          ·
            refine ⟨132627083273630201006950877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88418055515753467337967251 132627083273630201006950877)
            ·
              refine ⟨49735156227611325377606579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132627083273630201006950877 49735156227611325377606579)
              ·
                refine ⟨74602734341416988066409869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49735156227611325377606579 74602734341416988066409869)
                ·
                  refine ⟨27976025378031370524903701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74602734341416988066409869 27976025378031370524903701)
                  ·
                    refine ⟨1311376189595220493354861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27976025378031370524903701 1311376189595220493354861)
                    ·
                      refine ⟨491766071098207685008073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1311376189595220493354861 491766071098207685008073)
                      ·
                        rfl

theorem cell23_957711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 6, 3].length) (baseStart_957711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957711 prefixEnd_957711 := by exact prefixLift 957711
  have htrace : WordTrace (prefixWord ++ tailWord_957711) baseStart_957711 baseEnd_957711 := by
    simpa [prefixWord, tailWord_957711, baseEnd_957711] using wordTrace_append hprefix tailTrace_957711
  have hstable : (prefixWord ++ tailWord_957711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957711).length < 2 ^ (prefixWord ++ tailWord_957711).sum := by decide
  have hdescent : baseEnd_957711 < baseStart_957711 := by decide
  rcases family_descends (prefixWord ++ tailWord_957711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957748 : List Nat := [2, 5, 1, 1, 1, 1, 2, 1, 9]
def baseStart_957748 : Nat := 118140960795 + 957748 * 2 ^ 59
def prefixEnd_957748 : Nat := 4983230072969 + 3 ^ 40 * 957748 * 2
def baseEnd_957748 : Nat := 54642785542491560027267

theorem tailTrace_957748 : CollatzResearch.WordTrace tailWord_957748 prefixEnd_957748 54642785542491560027267 := by
  unfold tailWord_957748
  simp only [CollatzResearch.WordTrace]
  refine ⟨17465969667125020590504949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23287959556166694120673265 17465969667125020590504949)
  ·
    refine ⟨1637434656292970680359839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17465969667125020590504949 1637434656292970680359839)
    ·
      refine ⟨2456151984439456020539759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1637434656292970680359839 2456151984439456020539759)
      ·
        refine ⟨3684227976659184030809639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2456151984439456020539759 3684227976659184030809639)
        ·
          refine ⟨5526341964988776046214459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3684227976659184030809639 5526341964988776046214459)
          ·
            refine ⟨8289512947483164069321689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5526341964988776046214459 8289512947483164069321689)
            ·
              refine ⟨6217134710612373051991267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8289512947483164069321689 6217134710612373051991267)
              ·
                refine ⟨9325702065918559577986901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6217134710612373051991267 9325702065918559577986901)
                ·
                  refine ⟨54642785542491560027267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9325702065918559577986901 54642785542491560027267)
                  ·
                    rfl

theorem cell23_957748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_957748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957748 prefixEnd_957748 := by exact prefixLift 957748
  have htrace : WordTrace (prefixWord ++ tailWord_957748) baseStart_957748 baseEnd_957748 := by
    simpa [prefixWord, tailWord_957748, baseEnd_957748] using wordTrace_append hprefix tailTrace_957748
  have hstable : (prefixWord ++ tailWord_957748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957748).length < 2 ^ (prefixWord ++ tailWord_957748).sum := by decide
  have hdescent : baseEnd_957748 < baseStart_957748 := by decide
  rcases family_descends (prefixWord ++ tailWord_957748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957789 : List Nat := [1, 4, 5, 1, 1, 1, 1, 1, 2, 2, 4]
def baseStart_957789 : Nat := 118140960795 + 957789 * 2 ^ 59
def prefixEnd_957789 : Nat := 4983230072969 + 3 ^ 40 * 957789 * 2
def baseEnd_957789 : Nat := 491806122589258379832715

theorem tailTrace_957789 : CollatzResearch.WordTrace tailWord_957789 prefixEnd_957789 491806122589258379832715 := by
  unfold tailWord_957789
  simp only [CollatzResearch.WordTrace]
  refine ⟨34933434727101505183252421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23288956484734336788834947 34933434727101505183252421)
  ·
    refine ⟨6550019011331532221859829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34933434727101505183252421 6550019011331532221859829)
    ·
      refine ⟨614064282312331145799359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6550019011331532221859829 614064282312331145799359)
      ·
        refine ⟨921096423468496718699039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614064282312331145799359 921096423468496718699039)
        ·
          refine ⟨1381644635202745078048559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 921096423468496718699039 1381644635202745078048559)
          ·
            refine ⟨2072466952804117617072839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1381644635202745078048559 2072466952804117617072839)
            ·
              refine ⟨3108700429206176425609259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2072466952804117617072839 3108700429206176425609259)
              ·
                refine ⟨4663050643809264638413889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3108700429206176425609259 4663050643809264638413889)
                ·
                  refine ⟨3497287982856948478810417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4663050643809264638413889 3497287982856948478810417)
                  ·
                    refine ⟨2622965987142711359107813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3497287982856948478810417 2622965987142711359107813)
                    ·
                      refine ⟨491806122589258379832715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2622965987142711359107813 491806122589258379832715)
                      ·
                        rfl

theorem cell23_957789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_957789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957789 prefixEnd_957789 := by exact prefixLift 957789
  have htrace : WordTrace (prefixWord ++ tailWord_957789) baseStart_957789 baseEnd_957789 := by
    simpa [prefixWord, tailWord_957789, baseEnd_957789] using wordTrace_append hprefix tailTrace_957789
  have hstable : (prefixWord ++ tailWord_957789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957789).length < 2 ^ (prefixWord ++ tailWord_957789).sum := by decide
  have hdescent : baseEnd_957789 < baseStart_957789 := by decide
  rcases family_descends (prefixWord ++ tailWord_957789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957791 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 2, 8]
def baseStart_957791 : Nat := 118140960795 + 957791 * 2 ^ 59
def prefixEnd_957791 : Nat := 4983230072969 + 3 ^ 40 * 957791 * 2
def baseEnd_957791 : Nat := 163935716516855790669235

theorem tailTrace_957791 : CollatzResearch.WordTrace tailWord_957791 prefixEnd_957791 163935716516855790669235 := by
  unfold tailWord_957791
  simp only [CollatzResearch.WordTrace]
  refine ⟨34933507673094259524825227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23289005115396173016550151 34933507673094259524825227)
  ·
    refine ⟨52400261509641389287237841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34933507673094259524825227 52400261509641389287237841)
    ·
      refine ⟨39300196132231041965428381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52400261509641389287237841 39300196132231041965428381)
      ·
        refine ⟨14737573549586640737035643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39300196132231041965428381 14737573549586640737035643)
        ·
          refine ⟨22106360324379961105553465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14737573549586640737035643 22106360324379961105553465)
          ·
            refine ⟨16579770243284970829165099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22106360324379961105553465 16579770243284970829165099)
            ·
              refine ⟨24869655364927456243747649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16579770243284970829165099 24869655364927456243747649)
              ·
                refine ⟨18652241523695592182810737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24869655364927456243747649 18652241523695592182810737)
                ·
                  refine ⟨13989181142771694137108053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18652241523695592182810737 13989181142771694137108053)
                  ·
                    refine ⟨163935716516855790669235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13989181142771694137108053 163935716516855790669235)
                    ·
                      rfl

theorem cell23_957791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 8].length) (baseStart_957791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957791 prefixEnd_957791 := by exact prefixLift 957791
  have htrace : WordTrace (prefixWord ++ tailWord_957791) baseStart_957791 baseEnd_957791 := by
    simpa [prefixWord, tailWord_957791, baseEnd_957791] using wordTrace_append hprefix tailTrace_957791
  have hstable : (prefixWord ++ tailWord_957791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957791).length < 2 ^ (prefixWord ++ tailWord_957791).sum := by decide
  have hdescent : baseEnd_957791 < baseStart_957791 := by decide
  rcases family_descends (prefixWord ++ tailWord_957791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957811 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 6]
def baseStart_957811 : Nat := 118140960795 + 957811 * 2 ^ 59
def prefixEnd_957811 : Nat := 4983230072969 + 3 ^ 40 * 957811 * 2
def baseEnd_957811 : Nat := 491817419163657293757613

theorem tailTrace_957811 : CollatzResearch.WordTrace tailWord_957811 prefixEnd_957811 491817419163657293757613 := by
  unfold tailWord_957811
  simp only [CollatzResearch.WordTrace]
  refine ⟨34934237133021802940553287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23289491422014535293702191 34934237133021802940553287)
  ·
    refine ⟨52401355699532704410829931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34934237133021802940553287 52401355699532704410829931)
    ·
      refine ⟨78602033549299056616244897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52401355699532704410829931 78602033549299056616244897)
      ·
        refine ⟨58951525161974292462183673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78602033549299056616244897 58951525161974292462183673)
        ·
          refine ⟨44213643871480719346637755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58951525161974292462183673 44213643871480719346637755)
          ·
            refine ⟨66320465807221079019956633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44213643871480719346637755 66320465807221079019956633)
            ·
              refine ⟨49740349355415809264967475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66320465807221079019956633 49740349355415809264967475)
              ·
                refine ⟨74610524033123713897451213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49740349355415809264967475 74610524033123713897451213)
                ·
                  refine ⟨27978946512421392711544205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74610524033123713897451213 27978946512421392711544205)
                  ·
                    refine ⟨10492104942158022266829077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27978946512421392711544205 10492104942158022266829077)
                    ·
                      refine ⟨491817419163657293757613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10492104942158022266829077 491817419163657293757613)
                      ·
                        rfl

theorem cell23_957811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 6].length) (baseStart_957811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957811 prefixEnd_957811 := by exact prefixLift 957811
  have htrace : WordTrace (prefixWord ++ tailWord_957811) baseStart_957811 baseEnd_957811 := by
    simpa [prefixWord, tailWord_957811, baseEnd_957811] using wordTrace_append hprefix tailTrace_957811
  have hstable : (prefixWord ++ tailWord_957811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957811).length < 2 ^ (prefixWord ++ tailWord_957811).sum := by decide
  have hdescent : baseEnd_957811 < baseStart_957811 := by decide
  rcases family_descends (prefixWord ++ tailWord_957811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957818 : List Nat := [3, 1, 1, 1, 1, 1, 2, 5, 1, 4, 3]
def baseStart_957818 : Nat := 118140960795 + 957818 * 2 ^ 59
def prefixEnd_957818 : Nat := 4983230072969 + 3 ^ 40 * 957818 * 2
def baseEnd_957818 : Nat := 491821013528238766370081

theorem tailTrace_957818 : CollatzResearch.WordTrace tailWord_957818 prefixEnd_957818 491821013528238766370081 := by
  unfold tailWord_957818
  simp only [CollatzResearch.WordTrace]
  refine ⟨8733623110999110784014527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23289661629330962090705405 8733623110999110784014527)
  ·
    refine ⟨13100434666498666176021791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8733623110999110784014527 13100434666498666176021791)
    ·
      refine ⟨19650651999747999264032687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13100434666498666176021791 19650651999747999264032687)
      ·
        refine ⟨29475977999621998896049031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19650651999747999264032687 29475977999621998896049031)
        ·
          refine ⟨44213966999432998344073547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29475977999621998896049031 44213966999432998344073547)
          ·
            refine ⟨66320950499149497516110321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44213966999432998344073547 66320950499149497516110321)
            ·
              refine ⟨49740712874362123137082741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66320950499149497516110321 49740712874362123137082741)
              ·
                refine ⟨4663191831971449044101507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49740712874362123137082741 4663191831971449044101507)
                ·
                  refine ⟨6994787747957173566152261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4663191831971449044101507 6994787747957173566152261)
                  ·
                    refine ⟨1311522702741970043653549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6994787747957173566152261 1311522702741970043653549)
                    ·
                      refine ⟨491821013528238766370081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1311522702741970043653549 491821013528238766370081)
                      ·
                        rfl

theorem cell23_957818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 1, 4, 3].length) (baseStart_957818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957818 prefixEnd_957818 := by exact prefixLift 957818
  have htrace : WordTrace (prefixWord ++ tailWord_957818) baseStart_957818 baseEnd_957818 := by
    simpa [prefixWord, tailWord_957818, baseEnd_957818] using wordTrace_append hprefix tailTrace_957818
  have hstable : (prefixWord ++ tailWord_957818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957818).length < 2 ^ (prefixWord ++ tailWord_957818).sum := by decide
  have hdescent : baseEnd_957818 < baseStart_957818 := by decide
  rcases family_descends (prefixWord ++ tailWord_957818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957828 : List Nat := [2, 3, 2, 1, 1, 3, 1, 1, 2, 1, 6]
def baseStart_957828 : Nat := 118140960795 + 957828 * 2 ^ 59
def prefixEnd_957828 : Nat := 4983230072969 + 3 ^ 40 * 957828 * 2
def baseEnd_957828 : Nat := 491826148334783727245035

theorem tailTrace_957828 : CollatzResearch.WordTrace tailWord_957828 prefixEnd_957828 491826148334783727245035 := by
  unfold tailWord_957828
  simp only [CollatzResearch.WordTrace]
  refine ⟨17467428586980107421961069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23289904782640143229281425 17467428586980107421961069)
  ·
    refine ⟨6550285720117540283235401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17467428586980107421961069 6550285720117540283235401)
    ·
      refine ⟨4912714290088155212426551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6550285720117540283235401 4912714290088155212426551)
      ·
        refine ⟨7369071435132232818639827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4912714290088155212426551 7369071435132232818639827)
        ·
          refine ⟨11053607152698349227959741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7369071435132232818639827 11053607152698349227959741)
          ·
            refine ⟨4145102682261880960484903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11053607152698349227959741 4145102682261880960484903)
            ·
              refine ⟨6217654023392821440727355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4145102682261880960484903 6217654023392821440727355)
              ·
                refine ⟨9326481035089232161091033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6217654023392821440727355 9326481035089232161091033)
                ·
                  refine ⟨6994860776316924120818275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9326481035089232161091033 6994860776316924120818275)
                  ·
                    refine ⟨10492291164475386181227413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6994860776316924120818275 10492291164475386181227413)
                    ·
                      refine ⟨491826148334783727245035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10492291164475386181227413 491826148334783727245035)
                      ·
                        rfl

theorem cell23_957828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_957828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957828 prefixEnd_957828 := by exact prefixLift 957828
  have htrace : WordTrace (prefixWord ++ tailWord_957828) baseStart_957828 baseEnd_957828 := by
    simpa [prefixWord, tailWord_957828, baseEnd_957828] using wordTrace_append hprefix tailTrace_957828
  have hstable : (prefixWord ++ tailWord_957828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957828).length < 2 ^ (prefixWord ++ tailWord_957828).sum := by decide
  have hdescent : baseEnd_957828 < baseStart_957828 := by decide
  rcases family_descends (prefixWord ++ tailWord_957828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957868 : List Nat := [2, 2, 1, 1, 1, 1, 4, 3, 3, 5]
def baseStart_957868 : Nat := 118140960795 + 957868 * 2 ^ 59
def prefixEnd_957868 : Nat := 4983230072969 + 3 ^ 40 * 957868 * 2
def baseEnd_957868 : Nat := 163948895853654523581617

theorem tailTrace_957868 : CollatzResearch.WordTrace tailWord_957868 prefixEnd_957868 163948895853654523581617 := by
  unfold tailWord_957868
  simp only [CollatzResearch.WordTrace]
  refine ⟨17468158046907650837689129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23290877395876867783585505 17468158046907650837689129)
  ·
    refine ⟨13101118535180738128266847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17468158046907650837689129 13101118535180738128266847)
    ·
      refine ⟨19651677802771107192400271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13101118535180738128266847 19651677802771107192400271)
      ·
        refine ⟨29477516704156660788600407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19651677802771107192400271 29477516704156660788600407)
        ·
          refine ⟨44216275056234991182900611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29477516704156660788600407 44216275056234991182900611)
          ·
            refine ⟨66324412584352486774350917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44216275056234991182900611 66324412584352486774350917)
            ·
              refine ⟨12435827359566091270190797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66324412584352486774350917 12435827359566091270190797)
              ·
                refine ⟨4663435259837284226321549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12435827359566091270190797 4663435259837284226321549)
                ·
                  refine ⟨1748788222438981584870581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4663435259837284226321549 1748788222438981584870581)
                  ·
                    refine ⟨163948895853654523581617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1748788222438981584870581 163948895853654523581617)
                    ·
                      rfl

theorem cell23_957868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 5].length) (baseStart_957868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957868 prefixEnd_957868 := by exact prefixLift 957868
  have htrace : WordTrace (prefixWord ++ tailWord_957868) baseStart_957868 baseEnd_957868 := by
    simpa [prefixWord, tailWord_957868, baseEnd_957868] using wordTrace_append hprefix tailTrace_957868
  have hstable : (prefixWord ++ tailWord_957868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957868).length < 2 ^ (prefixWord ++ tailWord_957868).sum := by decide
  have hdescent : baseEnd_957868 < baseStart_957868 := by decide
  rcases family_descends (prefixWord ++ tailWord_957868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957875 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 6, 3, 2]
def baseStart_957875 : Nat := 118140960795 + 957875 * 2 ^ 59
def prefixEnd_957875 : Nat := 4983230072969 + 3 ^ 40 * 957875 * 2
def baseEnd_957875 : Nat := 491850281925545043357319

theorem tailTrace_957875 : CollatzResearch.WordTrace tailWord_957875 prefixEnd_957875 491850281925545043357319 := by
  unfold tailWord_957875
  simp only [CollatzResearch.WordTrace]
  refine ⟨34936571404789941870883079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23291047603193294580588719 34936571404789941870883079)
  ·
    refine ⟨52404857107184912806324619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34936571404789941870883079 52404857107184912806324619)
    ·
      refine ⟨78607285660777369209486929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52404857107184912806324619 78607285660777369209486929)
      ·
        refine ⟨58955464245583026907115197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78607285660777369209486929 58955464245583026907115197)
        ·
          refine ⟨22108299092093635090168199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58955464245583026907115197 22108299092093635090168199)
          ·
            refine ⟨33162448638140452635252299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22108299092093635090168199 33162448638140452635252299)
            ·
              refine ⟨49743672957210678952878449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33162448638140452635252299 49743672957210678952878449)
              ·
                refine ⟨37307754717908009214658837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49743672957210678952878449 37307754717908009214658837)
                ·
                  refine ⟨1748801002401937931937133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37307754717908009214658837 1748801002401937931937133)
                  ·
                    refine ⟨655800375900726724476425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1748801002401937931937133 655800375900726724476425)
                    ·
                      refine ⟨491850281925545043357319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 655800375900726724476425 491850281925545043357319)
                      ·
                        rfl

theorem cell23_957875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 3, 2].length) (baseStart_957875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957875 prefixEnd_957875 := by exact prefixLift 957875
  have htrace : WordTrace (prefixWord ++ tailWord_957875) baseStart_957875 baseEnd_957875 := by
    simpa [prefixWord, tailWord_957875, baseEnd_957875] using wordTrace_append hprefix tailTrace_957875
  have hstable : (prefixWord ++ tailWord_957875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957875).length < 2 ^ (prefixWord ++ tailWord_957875).sum := by decide
  have hdescent : baseEnd_957875 < baseStart_957875 := by decide
  rcases family_descends (prefixWord ++ tailWord_957875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957885 : List Nat := [1, 4, 1, 2, 2, 1, 1, 5, 1, 5]
def baseStart_957885 : Nat := 118140960795 + 957885 * 2 ^ 59
def prefixEnd_957885 : Nat := 4983230072969 + 3 ^ 40 * 957885 * 2
def baseEnd_957885 : Nat := 163951805577363334744091

theorem tailTrace_957885 : CollatzResearch.WordTrace tailWord_957885 prefixEnd_957885 163951805577363334744091 := by
  unfold tailWord_957885
  simp only [CollatzResearch.WordTrace]
  refine ⟨34936936134753713578747109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23291290756502475719164739 34936936134753713578747109)
  ·
    refine ⟨6550675525266321296015083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34936936134753713578747109 6550675525266321296015083)
    ·
      refine ⟨9826013287899481944022625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6550675525266321296015083 9826013287899481944022625)
      ·
        refine ⟨7369509965924611458016969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9826013287899481944022625 7369509965924611458016969)
        ·
          refine ⟨5527132474443458593512727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7369509965924611458016969 5527132474443458593512727)
          ·
            refine ⟨8290698711665187890269091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5527132474443458593512727 8290698711665187890269091)
            ·
              refine ⟨12436048067497781835403637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8290698711665187890269091 12436048067497781835403637)
              ·
                refine ⟨1165879506327917047069091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12436048067497781835403637 1165879506327917047069091)
                ·
                  refine ⟨1748819259491875570603637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1165879506327917047069091 1748819259491875570603637)
                  ·
                    refine ⟨163951805577363334744091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1748819259491875570603637 163951805577363334744091)
                    ·
                      rfl

theorem cell23_957885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_957885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957885 prefixEnd_957885 := by exact prefixLift 957885
  have htrace : WordTrace (prefixWord ++ tailWord_957885) baseStart_957885 baseEnd_957885 := by
    simpa [prefixWord, tailWord_957885, baseEnd_957885] using wordTrace_append hprefix tailTrace_957885
  have hstable : (prefixWord ++ tailWord_957885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957885).length < 2 ^ (prefixWord ++ tailWord_957885).sum := by decide
  have hdescent : baseEnd_957885 < baseStart_957885 := by decide
  rcases family_descends (prefixWord ++ tailWord_957885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957928 : List Nat := [2, 1, 4, 1, 1, 2, 1, 11]
def baseStart_957928 : Nat := 118140960795 + 957928 * 2 ^ 59
def prefixEnd_957928 : Nat := 4983230072969 + 3 ^ 40 * 957928 * 2
def baseEnd_957928 : Nat := 18217685051860493925725

theorem tailTrace_957928 : CollatzResearch.WordTrace tailWord_957928 prefixEnd_957928 18217685051860493925725 := by
  unfold tailWord_957928
  simp only [CollatzResearch.WordTrace]
  refine ⟨17469252236798965961281219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23292336315731954615041625 17469252236798965961281219)
  ·
    refine ⟨26203878355198448941921829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17469252236798965961281219 26203878355198448941921829)
    ·
      refine ⟨4913227191599709176610343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26203878355198448941921829 4913227191599709176610343)
      ·
        refine ⟨7369840787399563764915515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4913227191599709176610343 7369840787399563764915515)
        ·
          refine ⟨11054761181099345647373273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7369840787399563764915515 11054761181099345647373273)
          ·
            refine ⟨8291070885824509235529955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11054761181099345647373273 8291070885824509235529955)
            ·
              refine ⟨12436606328736763853294933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8291070885824509235529955 12436606328736763853294933)
              ·
                refine ⟨18217685051860493925725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 12436606328736763853294933 18217685051860493925725)
                ·
                  rfl

theorem cell23_957928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 11].length) (baseStart_957928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957928 prefixEnd_957928 := by exact prefixLift 957928
  have htrace : WordTrace (prefixWord ++ tailWord_957928) baseStart_957928 baseEnd_957928 := by
    simpa [prefixWord, tailWord_957928, baseEnd_957928] using wordTrace_append hprefix tailTrace_957928
  have hstable : (prefixWord ++ tailWord_957928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957928).length < 2 ^ (prefixWord ++ tailWord_957928).sum := by decide
  have hdescent : baseEnd_957928 < baseStart_957928 := by decide
  rcases family_descends (prefixWord ++ tailWord_957928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_957942 : List Nat := [5, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5]
def baseStart_957942 : Nat := 118140960795 + 957942 * 2 ^ 59
def prefixEnd_957942 : Nat := 4983230072969 + 3 ^ 40 * 957942 * 2
def baseEnd_957942 : Nat := 491884685129396281219511

theorem tailTrace_957942 : CollatzResearch.WordTrace tailWord_957942 prefixEnd_957942 491884685129396281219511 := by
  unfold tailWord_957942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2183688443471700769598255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23292676730364808209048053 2183688443471700769598255)
  ·
    refine ⟨3275532665207551154397383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2183688443471700769598255 3275532665207551154397383)
    ·
      refine ⟨4913298997811326731596075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3275532665207551154397383 4913298997811326731596075)
      ·
        refine ⟨7369948496716990097394113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4913298997811326731596075 7369948496716990097394113)
        ·
          refine ⟨5527461372537742573045585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7369948496716990097394113 5527461372537742573045585)
          ·
            refine ⟨4145596029403306929784189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5527461372537742573045585 4145596029403306929784189)
            ·
              refine ⟨1554598511026240098669071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4145596029403306929784189 1554598511026240098669071)
              ·
                refine ⟨2331897766539360148003607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1554598511026240098669071 2331897766539360148003607)
                ·
                  refine ⟨3497846649809040222005411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2331897766539360148003607 3497846649809040222005411)
                  ·
                    refine ⟨5246769974713560333008117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3497846649809040222005411 5246769974713560333008117)
                    ·
                      refine ⟨491884685129396281219511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5246769974713560333008117 491884685129396281219511)
                      ·
                        rfl

theorem cell23_957942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_957942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_957942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_957942 prefixEnd_957942 := by exact prefixLift 957942
  have htrace : WordTrace (prefixWord ++ tailWord_957942) baseStart_957942 baseEnd_957942 := by
    simpa [prefixWord, tailWord_957942, baseEnd_957942] using wordTrace_append hprefix tailTrace_957942
  have hstable : (prefixWord ++ tailWord_957942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_957942).length < 2 ^ (prefixWord ++ tailWord_957942).sum := by decide
  have hdescent : baseEnd_957942 < baseStart_957942 := by decide
  rcases family_descends (prefixWord ++ tailWord_957942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958005 : List Nat := [1, 3, 3, 1, 1, 3, 1, 2, 2, 6]
def baseStart_958005 : Nat := 118140960795 + 958005 * 2 ^ 59
def prefixEnd_958005 : Nat := 4983230072969 + 3 ^ 40 * 958005 * 2
def baseEnd_958005 : Nat := 163972344803543178243907

theorem tailTrace_958005 : CollatzResearch.WordTrace tailWord_958005 prefixEnd_958005 163972344803543178243907 := by
  unfold tailWord_958005
  simp only [CollatzResearch.WordTrace]
  refine ⟨34941312894318974073115469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23294208596212649382076979 34941312894318974073115469)
  ·
    refine ⟨13102992335369615277418301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34941312894318974073115469 13102992335369615277418301)
    ·
      refine ⟨4913622125763605729031863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13102992335369615277418301 4913622125763605729031863)
      ·
        refine ⟨7370433188645408593547795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4913622125763605729031863 7370433188645408593547795)
        ·
          refine ⟨11055649782968112890321693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7370433188645408593547795 11055649782968112890321693)
          ·
            refine ⟨4145868668613042333870635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11055649782968112890321693 4145868668613042333870635)
            ·
              refine ⟨6218803002919563500805953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4145868668613042333870635 6218803002919563500805953)
              ·
                refine ⟨4664102252189672625604465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6218803002919563500805953 4664102252189672625604465)
                ·
                  refine ⟨3498076689142254469203349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4664102252189672625604465 3498076689142254469203349)
                  ·
                    refine ⟨163972344803543178243907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3498076689142254469203349 163972344803543178243907)
                    ·
                      rfl

theorem cell23_958005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_958005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958005 prefixEnd_958005 := by exact prefixLift 958005
  have htrace : WordTrace (prefixWord ++ tailWord_958005) baseStart_958005 baseEnd_958005 := by
    simpa [prefixWord, tailWord_958005, baseEnd_958005] using wordTrace_append hprefix tailTrace_958005
  have hstable : (prefixWord ++ tailWord_958005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958005).length < 2 ^ (prefixWord ++ tailWord_958005).sum := by decide
  have hdescent : baseEnd_958005 < baseStart_958005 := by decide
  rcases family_descends (prefixWord ++ tailWord_958005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958006 : List Nat := [5, 1, 2, 1, 3, 1, 1, 1, 4, 1, 3]
def baseStart_958006 : Nat := 118140960795 + 958006 * 2 ^ 59
def prefixEnd_958006 : Nat := 4983230072969 + 3 ^ 40 * 958006 * 2
def baseEnd_958006 : Nat := 491917547891284030819217

theorem tailTrace_958006 : CollatzResearch.WordTrace tailWord_958006 prefixEnd_958006 491917547891284030819217 := by
  unfold tailWord_958006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2183834335457209452743867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23294232911543567495934581 2183834335457209452743867)
  ·
    refine ⟨3275751503185814179115801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2183834335457209452743867 3275751503185814179115801)
    ·
      refine ⟨2456813627389360634336851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3275751503185814179115801 2456813627389360634336851)
      ·
        refine ⟨3685220441084040951505277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2456813627389360634336851 3685220441084040951505277)
        ·
          refine ⟨1381957665406515356814479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3685220441084040951505277 1381957665406515356814479)
          ·
            refine ⟨2072936498109773035221719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1381957665406515356814479 2072936498109773035221719)
            ·
              refine ⟨3109404747164659552832579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2072936498109773035221719 3109404747164659552832579)
              ·
                refine ⟨4664107120746989329248869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3109404747164659552832579 4664107120746989329248869)
                ·
                  refine ⟨874520085140060499234163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4664107120746989329248869 874520085140060499234163)
                  ·
                    refine ⟨1311780127710090748851245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 874520085140060499234163 1311780127710090748851245)
                    ·
                      refine ⟨491917547891284030819217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1311780127710090748851245 491917547891284030819217)
                      ·
                        rfl

theorem cell23_958006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_958006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958006 prefixEnd_958006 := by exact prefixLift 958006
  have htrace : WordTrace (prefixWord ++ tailWord_958006) baseStart_958006 baseEnd_958006 := by
    simpa [prefixWord, tailWord_958006, baseEnd_958006] using wordTrace_append hprefix tailTrace_958006
  have hstable : (prefixWord ++ tailWord_958006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958006).length < 2 ^ (prefixWord ++ tailWord_958006).sum := by decide
  have hdescent : baseEnd_958006 < baseStart_958006 := by decide
  rcases family_descends (prefixWord ++ tailWord_958006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958069 : List Nat := [1, 3, 4, 2, 1, 3, 1, 1, 7]
def baseStart_958069 : Nat := 118140960795 + 958069 * 2 ^ 59
def prefixEnd_958069 : Nat := 4983230072969 + 3 ^ 40 * 958069 * 2
def baseEnd_958069 : Nat := 54661099685835253814603

theorem tailTrace_958069 : CollatzResearch.WordTrace tailWord_958069 prefixEnd_958069 54661099685835253814603 := by
  unfold tailWord_958069
  simp only [CollatzResearch.WordTrace]
  refine ⟨34943647166087113003445261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23295764777391408668963507 34943647166087113003445261)
  ·
    refine ⟨13103867687282667376291973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34943647166087113003445261 13103867687282667376291973)
    ·
      refine ⟨2456975191365500133054745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13103867687282667376291973 2456975191365500133054745)
      ·
        refine ⟨1842731393524125099791059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2456975191365500133054745 1842731393524125099791059)
        ·
          refine ⟨2764097090286187649686589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1842731393524125099791059 2764097090286187649686589)
          ·
            refine ⟨1036536408857320368632471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2764097090286187649686589 1036536408857320368632471)
            ·
              refine ⟨1554804613285980552948707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1036536408857320368632471 1554804613285980552948707)
              ·
                refine ⟨2332206919928970829423061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1554804613285980552948707 2332206919928970829423061)
                ·
                  refine ⟨54661099685835253814603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2332206919928970829423061 54661099685835253814603)
                  ·
                    rfl

theorem cell23_958069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 7].length) (baseStart_958069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958069 prefixEnd_958069 := by exact prefixLift 958069
  have htrace : WordTrace (prefixWord ++ tailWord_958069) baseStart_958069 baseEnd_958069 := by
    simpa [prefixWord, tailWord_958069, baseEnd_958069] using wordTrace_append hprefix tailTrace_958069
  have hstable : (prefixWord ++ tailWord_958069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958069).length < 2 ^ (prefixWord ++ tailWord_958069).sum := by decide
  have hdescent : baseEnd_958069 < baseStart_958069 := by decide
  rcases family_descends (prefixWord ++ tailWord_958069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958075 : List Nat := [1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 5]
def baseStart_958075 : Nat := 118140960795 + 958075 * 2 ^ 59
def prefixEnd_958075 : Nat := 4983230072969 + 3 ^ 40 * 958075 * 2
def baseEnd_958075 : Nat := 491952978056444260856399

theorem tailTrace_958075 : CollatzResearch.WordTrace tailWord_958075 prefixEnd_958075 491952978056444260856399 := by
  unfold tailWord_958075
  simp only [CollatzResearch.WordTrace]
  refine ⟨34943866004065376028163679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23295910669376917352109119 34943866004065376028163679)
  ·
    refine ⟨52415799006098064042245519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34943866004065376028163679 52415799006098064042245519)
    ·
      refine ⟨78623698509147096063368279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52415799006098064042245519 78623698509147096063368279)
      ·
        refine ⟨117935547763720644095052419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78623698509147096063368279 117935547763720644095052419)
        ·
          refine ⟨176903321645580966142578629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117935547763720644095052419 176903321645580966142578629)
          ·
            refine ⟨33169372808546431151733493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176903321645580966142578629 33169372808546431151733493)
            ·
              refine ⟨3109628700801227920475015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33169372808546431151733493 3109628700801227920475015)
              ·
                refine ⟨4664443051201841880712523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3109628700801227920475015 4664443051201841880712523)
                ·
                  refine ⟨6996664576802762821068785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4664443051201841880712523 6996664576802762821068785)
                  ·
                    refine ⟨5247498432602072115801589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6996664576802762821068785 5247498432602072115801589)
                    ·
                      refine ⟨491952978056444260856399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5247498432602072115801589 491952978056444260856399)
                      ·
                        rfl

theorem cell23_958075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 5].length) (baseStart_958075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958075 prefixEnd_958075 := by exact prefixLift 958075
  have htrace : WordTrace (prefixWord ++ tailWord_958075) baseStart_958075 baseEnd_958075 := by
    simpa [prefixWord, tailWord_958075, baseEnd_958075] using wordTrace_append hprefix tailTrace_958075
  have hstable : (prefixWord ++ tailWord_958075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958075).length < 2 ^ (prefixWord ++ tailWord_958075).sum := by decide
  have hdescent : baseEnd_958075 < baseStart_958075 := by decide
  rcases family_descends (prefixWord ++ tailWord_958075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958115 : List Nat := [1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 6]
def baseStart_958115 : Nat := 118140960795 + 958115 * 2 ^ 59
def prefixEnd_958115 : Nat := 4983230072969 + 3 ^ 40 * 958115 * 2
def baseEnd_958115 : Nat := 491973517282624104356215

theorem tailTrace_958115 : CollatzResearch.WordTrace tailWord_958115 prefixEnd_958115 491973517282624104356215 := by
  unfold tailWord_958115
  simp only [CollatzResearch.WordTrace]
  refine ⟨34945324923920462859619799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23296883282613641906413199 34945324923920462859619799)
  ·
    refine ⟨52417987385880694289429699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34945324923920462859619799 52417987385880694289429699)
    ·
      refine ⟨78626981078821041434144549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52417987385880694289429699 78626981078821041434144549)
      ·
        refine ⟨14742558952278945268902103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78626981078821041434144549 14742558952278945268902103)
        ·
          refine ⟨22113838428418417903353155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14742558952278945268902103 22113838428418417903353155)
          ·
            refine ⟨33170757642627626855029733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22113838428418417903353155 33170757642627626855029733)
            ·
              refine ⟨6219517057992680035318075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33170757642627626855029733 6219517057992680035318075)
              ·
                refine ⟨9329275586989020052977113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6219517057992680035318075 9329275586989020052977113)
                ·
                  refine ⟨6996956690241765039732835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9329275586989020052977113 6996956690241765039732835)
                  ·
                    refine ⟨10495435035362647559599253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6996956690241765039732835 10495435035362647559599253)
                    ·
                      refine ⟨491973517282624104356215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10495435035362647559599253 491973517282624104356215)
                      ·
                        rfl

theorem cell23_958115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_958115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958115 prefixEnd_958115 := by exact prefixLift 958115
  have htrace : WordTrace (prefixWord ++ tailWord_958115) baseStart_958115 baseEnd_958115 := by
    simpa [prefixWord, tailWord_958115, baseEnd_958115] using wordTrace_append hprefix tailTrace_958115
  have hstable : (prefixWord ++ tailWord_958115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958115).length < 2 ^ (prefixWord ++ tailWord_958115).sum := by decide
  have hdescent : baseEnd_958115 < baseStart_958115 := by decide
  rcases family_descends (prefixWord ++ tailWord_958115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958192 : List Nat := [2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 4]
def baseStart_958192 : Nat := 118140960795 + 958192 * 2 ^ 59
def prefixEnd_958192 : Nat := 4983230072969 + 3 ^ 40 * 958192 * 2
def baseEnd_958192 : Nat := 492013055293020303093361

theorem tailTrace_958192 : CollatzResearch.WordTrace tailWord_958192 prefixEnd_958192 492013055293020303093361 := by
  unfold tailWord_958192
  simp only [CollatzResearch.WordTrace]
  refine ⟨17474066672320752505086415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23298755563094336673448553 17474066672320752505086415)
  ·
    refine ⟨26211100008481128757629623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17474066672320752505086415 26211100008481128757629623)
    ·
      refine ⟨39316650012721693136444435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26211100008481128757629623 39316650012721693136444435)
      ·
        refine ⟨58974975019082539704666653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39316650012721693136444435 58974975019082539704666653)
        ·
          refine ⟨22115615632155952389249995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58974975019082539704666653 22115615632155952389249995)
          ·
            refine ⟨33173423448233928583874993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22115615632155952389249995 33173423448233928583874993)
            ·
              refine ⟨24880067586175446437906245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33173423448233928583874993 24880067586175446437906245)
              ·
                refine ⟨4665012672407896207107421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24880067586175446437906245 4665012672407896207107421)
                ·
                  refine ⟨1749379752152961077665283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4665012672407896207107421 1749379752152961077665283)
                  ·
                    refine ⟨2624069628229441616497925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1749379752152961077665283 2624069628229441616497925)
                    ·
                      refine ⟨492013055293020303093361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2624069628229441616497925 492013055293020303093361)
                      ·
                        rfl

theorem cell23_958192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 4].length) (baseStart_958192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958192 prefixEnd_958192 := by exact prefixLift 958192
  have htrace : WordTrace (prefixWord ++ tailWord_958192) baseStart_958192 baseEnd_958192 := by
    simpa [prefixWord, tailWord_958192, baseEnd_958192] using wordTrace_append hprefix tailTrace_958192
  have hstable : (prefixWord ++ tailWord_958192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958192).length < 2 ^ (prefixWord ++ tailWord_958192).sum := by decide
  have hdescent : baseEnd_958192 < baseStart_958192 := by decide
  rcases family_descends (prefixWord ++ tailWord_958192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958209 : List Nat := [1, 2, 4, 1, 1, 1, 3, 4, 1, 1, 4]
def baseStart_958209 : Nat := 118140960795 + 958209 * 2 ^ 59
def prefixEnd_958209 : Nat := 4983230072969 + 3 ^ 40 * 958209 * 2
def baseEnd_958209 : Nat := 492021784464146736580783

theorem tailTrace_958209 : CollatzResearch.WordTrace tailWord_958209 prefixEnd_958209 492021784464146736580783 := by
  unfold tailWord_958209
  simp only [CollatzResearch.WordTrace]
  refine ⟨34948753385579916913541681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23299168923719944609027787 34948753385579916913541681)
  ·
    refine ⟨26211565039184937685156261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34948753385579916913541681 26211565039184937685156261)
    ·
      refine ⟨4914668444847175815966799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26211565039184937685156261 4914668444847175815966799)
      ·
        refine ⟨7372002667270763723950199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4914668444847175815966799 7372002667270763723950199)
        ·
          refine ⟨11058004000906145585925299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7372002667270763723950199 11058004000906145585925299)
          ·
            refine ⟨16587006001359218378887949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11058004000906145585925299 16587006001359218378887949)
            ·
              refine ⟨6220127250509706892082981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16587006001359218378887949 6220127250509706892082981)
              ·
                refine ⟨1166273859470570042265559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6220127250509706892082981 1166273859470570042265559)
                ·
                  refine ⟨1749410789205855063398339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1166273859470570042265559 1749410789205855063398339)
                  ·
                    refine ⟨2624116183808782595097509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1749410789205855063398339 2624116183808782595097509)
                    ·
                      refine ⟨492021784464146736580783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2624116183808782595097509 492021784464146736580783)
                      ·
                        rfl

theorem cell23_958209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_958209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958209 prefixEnd_958209 := by exact prefixLift 958209
  have htrace : WordTrace (prefixWord ++ tailWord_958209) baseStart_958209 baseEnd_958209 := by
    simpa [prefixWord, tailWord_958209, baseEnd_958209] using wordTrace_append hprefix tailTrace_958209
  have hstable : (prefixWord ++ tailWord_958209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958209).length < 2 ^ (prefixWord ++ tailWord_958209).sum := by decide
  have hdescent : baseEnd_958209 < baseStart_958209 := by decide
  rcases family_descends (prefixWord ++ tailWord_958209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958229 : List Nat := [1, 3, 2, 1, 2, 4, 2, 1, 1, 1, 5]
def baseStart_958229 : Nat := 118140960795 + 958229 * 2 ^ 59
def prefixEnd_958229 : Nat := 4983230072969 + 3 ^ 40 * 958229 * 2
def baseEnd_958229 : Nat := 492032054077236658330691

theorem tailTrace_958229 : CollatzResearch.WordTrace tailWord_958229 prefixEnd_958229 492032054077236658330691 := by
  unfold tailWord_958229
  simp only [CollatzResearch.WordTrace]
  refine ⟨34949482845507460329269741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23299655230338306886179827 34949482845507460329269741)
  ·
    refine ⟨13106056067065297623476153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34949482845507460329269741 13106056067065297623476153)
    ·
      refine ⟨9829542050298973217607115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13106056067065297623476153 9829542050298973217607115)
      ·
        refine ⟨14744313075448459826410673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9829542050298973217607115 14744313075448459826410673)
        ·
          refine ⟨11058234806586344869808005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14744313075448459826410673 11058234806586344869808005)
          ·
            refine ⟨2073419026234939663089001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11058234806586344869808005 2073419026234939663089001)
            ·
              refine ⟨1555064269676204747316751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2073419026234939663089001 1555064269676204747316751)
              ·
                refine ⟨2332596404514307120975127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1555064269676204747316751 2332596404514307120975127)
                ·
                  refine ⟨3498894606771460681462691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2332596404514307120975127 3498894606771460681462691)
                  ·
                    refine ⟨5248341910157191022194037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3498894606771460681462691 5248341910157191022194037)
                    ·
                      refine ⟨492032054077236658330691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5248341910157191022194037 492032054077236658330691)
                      ·
                        rfl

theorem cell23_958229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_958229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958229 prefixEnd_958229 := by exact prefixLift 958229
  have htrace : WordTrace (prefixWord ++ tailWord_958229) baseStart_958229 baseEnd_958229 := by
    simpa [prefixWord, tailWord_958229, baseEnd_958229] using wordTrace_append hprefix tailTrace_958229
  have hstable : (prefixWord ++ tailWord_958229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958229).length < 2 ^ (prefixWord ++ tailWord_958229).sum := by decide
  have hdescent : baseEnd_958229 < baseStart_958229 := by decide
  rcases family_descends (prefixWord ++ tailWord_958229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958243 : List Nat := [1, 1, 1, 4, 2, 1, 2, 6, 1, 2, 2]
def baseStart_958243 : Nat := 118140960795 + 958243 * 2 ^ 59
def prefixEnd_958243 : Nat := 4983230072969 + 3 ^ 40 * 958243 * 2
def baseEnd_958243 : Nat := 492039242806399603555627

theorem tailTrace_958243 : CollatzResearch.WordTrace tailWord_958243 prefixEnd_958243 492039242806399603555627 := by
  unfold tailWord_958243
  simp only [CollatzResearch.WordTrace]
  refine ⟨34949993467456740720279383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23299995644971160480186255 34949993467456740720279383)
  ·
    refine ⟨52424990201185111080419075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34949993467456740720279383 52424990201185111080419075)
    ·
      refine ⟨78637485301777666620628613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52424990201185111080419075 78637485301777666620628613)
      ·
        refine ⟨14744528494083312491367865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78637485301777666620628613 14744528494083312491367865)
        ·
          refine ⟨11058396370562484368525899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14744528494083312491367865 11058396370562484368525899)
          ·
            refine ⟨16587594555843726552788849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11058396370562484368525899 16587594555843726552788849)
            ·
              refine ⟨12440695916882794914591637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16587594555843726552788849 12440695916882794914591637)
              ·
                refine ⟨583157621103881011621483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12440695916882794914591637 583157621103881011621483)
                ·
                  refine ⟨874736431655821517432225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 583157621103881011621483 874736431655821517432225)
                  ·
                    refine ⟨656052323741866138074169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 874736431655821517432225 656052323741866138074169)
                    ·
                      refine ⟨492039242806399603555627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 656052323741866138074169 492039242806399603555627)
                      ·
                        rfl

theorem cell23_958243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 6, 1, 2, 2].length) (baseStart_958243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958243 prefixEnd_958243 := by exact prefixLift 958243
  have htrace : WordTrace (prefixWord ++ tailWord_958243) baseStart_958243 baseEnd_958243 := by
    simpa [prefixWord, tailWord_958243, baseEnd_958243] using wordTrace_append hprefix tailTrace_958243
  have hstable : (prefixWord ++ tailWord_958243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958243).length < 2 ^ (prefixWord ++ tailWord_958243).sum := by decide
  have hdescent : baseEnd_958243 < baseStart_958243 := by decide
  rcases family_descends (prefixWord ++ tailWord_958243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958293 : List Nat := [1, 3, 2, 2, 2, 3, 2, 2, 2, 1, 3]
def baseStart_958293 : Nat := 118140960795 + 958293 * 2 ^ 59
def prefixEnd_958293 : Nat := 4983230072969 + 3 ^ 40 * 958293 * 2
def baseEnd_958293 : Nat := 492064916839124407930397

theorem tailTrace_958293 : CollatzResearch.WordTrace tailWord_958293 prefixEnd_958293 492064916839124407930397 := by
  unfold tailWord_958293
  simp only [CollatzResearch.WordTrace]
  refine ⟨34951817117275599259599533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23301211411517066173066355 34951817117275599259599533)
  ·
    refine ⟨13106931418978349722349825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34951817117275599259599533 13106931418978349722349825)
    ·
      refine ⟨9830198564233762291762369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13106931418978349722349825 9830198564233762291762369)
      ·
        refine ⟨7372648923175321718821777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9830198564233762291762369 7372648923175321718821777)
        ·
          refine ⟨5529486692381491289116333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7372648923175321718821777 5529486692381491289116333)
          ·
            refine ⟨2073557509643059233418625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5529486692381491289116333 2073557509643059233418625)
            ·
              refine ⟨1555168132232294425063969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2073557509643059233418625 1555168132232294425063969)
              ·
                refine ⟨1166376099174220818797977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1555168132232294425063969 1166376099174220818797977)
                ·
                  refine ⟨874782074380665614098483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1166376099174220818797977 874782074380665614098483)
                  ·
                    refine ⟨1312173111570998421147725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 874782074380665614098483 1312173111570998421147725)
                    ·
                      refine ⟨492064916839124407930397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1312173111570998421147725 492064916839124407930397)
                      ·
                        rfl

theorem cell23_958293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_958293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958293 prefixEnd_958293 := by exact prefixLift 958293
  have htrace : WordTrace (prefixWord ++ tailWord_958293) baseStart_958293 baseEnd_958293 := by
    simpa [prefixWord, tailWord_958293, baseEnd_958293] using wordTrace_append hprefix tailTrace_958293
  have hstable : (prefixWord ++ tailWord_958293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958293).length < 2 ^ (prefixWord ++ tailWord_958293).sum := by decide
  have hdescent : baseEnd_958293 < baseStart_958293 := by decide
  rcases family_descends (prefixWord ++ tailWord_958293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958316 : List Nat := [2, 2, 1, 1, 4, 2, 1, 3, 1, 4, 2]
def baseStart_958316 : Nat := 118140960795 + 958316 * 2 ^ 59
def prefixEnd_958316 : Nat := 4983230072969 + 3 ^ 40 * 958316 * 2
def baseEnd_958316 : Nat := 492076726894177817942791

theorem tailTrace_958316 : CollatzResearch.WordTrace tailWord_958316 prefixEnd_958316 492076726894177817942791 := by
  unfold tailWord_958316
  simp only [CollatzResearch.WordTrace]
  refine ⟨17476327998096137093843401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23301770664128182791791201 17476327998096137093843401)
  ·
    refine ⟨13107245998572102820382551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17476327998096137093843401 13107245998572102820382551)
    ·
      refine ⟨19660868997858154230573827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13107245998572102820382551 19660868997858154230573827)
      ·
        refine ⟨29491303496787231345860741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19660868997858154230573827 29491303496787231345860741)
        ·
          refine ⟨5529619405647605877348889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29491303496787231345860741 5529619405647605877348889)
          ·
            refine ⟨4147214554235704408011667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5529619405647605877348889 4147214554235704408011667)
            ·
              refine ⟨6220821831353556612017501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4147214554235704408011667 6220821831353556612017501)
              ·
                refine ⟨2332808186757583729506563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6220821831353556612017501 2332808186757583729506563)
                ·
                  refine ⟨3499212280136375594259845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2332808186757583729506563 3499212280136375594259845)
                  ·
                    refine ⟨656102302525570423923721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3499212280136375594259845 656102302525570423923721)
                    ·
                      refine ⟨492076726894177817942791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 656102302525570423923721 492076726894177817942791)
                      ·
                        rfl

theorem cell23_958316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 4, 2].length) (baseStart_958316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958316 prefixEnd_958316 := by exact prefixLift 958316
  have htrace : WordTrace (prefixWord ++ tailWord_958316) baseStart_958316 baseEnd_958316 := by
    simpa [prefixWord, tailWord_958316, baseEnd_958316] using wordTrace_append hprefix tailTrace_958316
  have hstable : (prefixWord ++ tailWord_958316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958316).length < 2 ^ (prefixWord ++ tailWord_958316).sum := by decide
  have hdescent : baseEnd_958316 < baseStart_958316 := by decide
  rcases family_descends (prefixWord ++ tailWord_958316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958332 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 3, 2, 7]
def baseStart_958332 : Nat := 118140960795 + 958332 * 2 ^ 59
def prefixEnd_958332 : Nat := 4983230072969 + 3 ^ 40 * 958332 * 2
def baseEnd_958332 : Nat := 492084942584649755342717

theorem tailTrace_958332 : CollatzResearch.WordTrace tailWord_958332 prefixEnd_958332 492084942584649755342717 := by
  unfold tailWord_958332
  simp only [CollatzResearch.WordTrace]
  refine ⟨17476619782067154460134625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23302159709422872613512833 17476619782067154460134625)
  ·
    refine ⟨13107464836550365845100969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17476619782067154460134625 13107464836550365845100969)
    ·
      refine ⟨9830598627412774383825727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13107464836550365845100969 9830598627412774383825727)
      ·
        refine ⟨14745897941119161575738591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9830598627412774383825727 14745897941119161575738591)
        ·
          refine ⟨22118846911678742363607887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14745897941119161575738591 22118846911678742363607887)
          ·
            refine ⟨33178270367518113545411831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22118846911678742363607887 33178270367518113545411831)
            ·
              refine ⟨49767405551277170318117747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33178270367518113545411831 49767405551277170318117747)
              ·
                refine ⟨74651108326915755477176621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49767405551277170318117747 74651108326915755477176621)
                ·
                  refine ⟨27994165622593408303941233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74651108326915755477176621 27994165622593408303941233)
                  ·
                    refine ⟨20995624216945056227955925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27994165622593408303941233 20995624216945056227955925)
                    ·
                      refine ⟨492084942584649755342717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 20995624216945056227955925 492084942584649755342717)
                      ·
                        rfl

theorem cell23_958332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_958332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958332 prefixEnd_958332 := by exact prefixLift 958332
  have htrace : WordTrace (prefixWord ++ tailWord_958332) baseStart_958332 baseEnd_958332 := by
    simpa [prefixWord, tailWord_958332, baseEnd_958332] using wordTrace_append hprefix tailTrace_958332
  have hstable : (prefixWord ++ tailWord_958332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958332).length < 2 ^ (prefixWord ++ tailWord_958332).sum := by decide
  have hdescent : baseEnd_958332 < baseStart_958332 := by decide
  rcases family_descends (prefixWord ++ tailWord_958332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_958352 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 3, 7]
def baseStart_958352 : Nat := 118140960795 + 958352 * 2 ^ 59
def prefixEnd_958352 : Nat := 4983230072969 + 3 ^ 40 * 958352 * 2
def baseEnd_958352 : Nat := 164031737399246559030875

theorem tailTrace_958352 : CollatzResearch.WordTrace tailWord_958352 prefixEnd_958352 164031737399246559030875 := by
  unfold tailWord_958352
  simp only [CollatzResearch.WordTrace]
  refine ⟨17476984512030926167998655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23302646016041234890664873 17476984512030926167998655)
  ·
    refine ⟨26215476768046389251997983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17476984512030926167998655 26215476768046389251997983)
    ·
      refine ⟨39323215152069583877996975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26215476768046389251997983 39323215152069583877996975)
      ·
        refine ⟨58984822728104375816995463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39323215152069583877996975 58984822728104375816995463)
        ·
          refine ⟨88477234092156563725493195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58984822728104375816995463 88477234092156563725493195)
          ·
            refine ⟨132715851138234845588239793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88477234092156563725493195 132715851138234845588239793)
            ·
              refine ⟨99536888353676134191179845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132715851138234845588239793 99536888353676134191179845)
              ·
                refine ⟨18663166566314275160846221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99536888353676134191179845 18663166566314275160846221)
                ·
                  refine ⟨6998687462367853185317333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18663166566314275160846221 6998687462367853185317333)
                  ·
                    refine ⟨164031737399246559030875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6998687462367853185317333 164031737399246559030875)
                    ·
                      rfl

theorem cell23_958352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 3, 7].length) (baseStart_958352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_958352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_958352 prefixEnd_958352 := by exact prefixLift 958352
  have htrace : WordTrace (prefixWord ++ tailWord_958352) baseStart_958352 baseEnd_958352 := by
    simpa [prefixWord, tailWord_958352, baseEnd_958352] using wordTrace_append hprefix tailTrace_958352
  have hstable : (prefixWord ++ tailWord_958352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_958352).length < 2 ^ (prefixWord ++ tailWord_958352).sum := by decide
  have hdescent : baseEnd_958352 < baseStart_958352 := by decide
  rcases family_descends (prefixWord ++ tailWord_958352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
