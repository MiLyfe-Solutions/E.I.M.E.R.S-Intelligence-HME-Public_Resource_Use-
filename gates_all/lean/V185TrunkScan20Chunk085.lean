import V185TrunkScan20Chunk084

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_517041 : List Nat := [1, 2, 2, 4, 3, 2, 1, 2, 3]
def baseStart_517041 : Nat := 118140960795 + 517041 * 2 ^ 59
def prefixEnd_517041 : Nat := 4983230072969 + 3 ^ 40 * 517041 * 2
def baseEnd_517041 : Nat := 235991600961259385253047

theorem tailTrace_517041 : CollatzResearch.WordTrace tailWord_517041 prefixEnd_517041 235991600961259385253047 := by
  unfold tailWord_517041
  simp only [CollatzResearch.WordTrace]
  refine ⟨18858034519856235417702977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12572023013237490278468651 18858034519856235417702977)
  ·
    refine ⟨14143525889892176563277233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18858034519856235417702977 14143525889892176563277233)
    ·
      refine ⟨10607644417419132422457925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14143525889892176563277233 10607644417419132422457925)
      ·
        refine ⟨1988933328266087329210861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10607644417419132422457925 1988933328266087329210861)
        ·
          refine ⟨745849998099782748454073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1988933328266087329210861 745849998099782748454073)
          ·
            refine ⟨559387498574837061340555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 745849998099782748454073 559387498574837061340555)
            ·
              refine ⟨839081247862255592010833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 559387498574837061340555 839081247862255592010833)
              ·
                refine ⟨629310935896691694008125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 839081247862255592010833 629310935896691694008125)
                ·
                  refine ⟨235991600961259385253047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 629310935896691694008125 235991600961259385253047)
                  ·
                    rfl

theorem cell20_517041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 3].length) (baseStart_517041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517041 prefixEnd_517041 := by exact prefixLift 517041
  have htrace : WordTrace (prefixWord ++ tailWord_517041) baseStart_517041 baseEnd_517041 := by
    simpa [prefixWord, tailWord_517041, baseEnd_517041] using wordTrace_append hprefix tailTrace_517041
  have hstable : (prefixWord ++ tailWord_517041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517041).length < 2 ^ (prefixWord ++ tailWord_517041).sum := by decide
  have hdescent : baseEnd_517041 < baseStart_517041 := by decide
  rcases family_descends (prefixWord ++ tailWord_517041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517045 : List Nat := [1, 3, 3, 2, 1, 1, 3, 1, 5]
def baseStart_517045 : Nat := 118140960795 + 517045 * 2 ^ 59
def prefixEnd_517045 : Nat := 4983230072969 + 3 ^ 40 * 517045 * 2
def baseEnd_517045 : Nat := 235993426670253149119697

theorem tailTrace_517045 : CollatzResearch.WordTrace tailWord_517045 prefixEnd_517045 235993426670253149119697 := by
  unfold tailWord_517045
  simp only [CollatzResearch.WordTrace]
  refine ⟨18858180411841744100848589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12572120274561162733899059 18858180411841744100848589)
  ·
    refine ⟨7071817654440654037818221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18858180411841744100848589 7071817654440654037818221)
    ·
      refine ⟨2651931620415245264181833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7071817654440654037818221 2651931620415245264181833)
      ·
        refine ⟨1988948715311433948136375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2651931620415245264181833 1988948715311433948136375)
        ·
          refine ⟨2983423072967150922204563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1988948715311433948136375 2983423072967150922204563)
          ·
            refine ⟨4475134609450726383306845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2983423072967150922204563 4475134609450726383306845)
            ·
              refine ⟨1678175478544022393740067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4475134609450726383306845 1678175478544022393740067)
              ·
                refine ⟨2517263217816033590610101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1678175478544022393740067 2517263217816033590610101)
                ·
                  refine ⟨235993426670253149119697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2517263217816033590610101 235993426670253149119697)
                  ·
                    rfl

theorem cell20_517045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_517045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517045 prefixEnd_517045 := by exact prefixLift 517045
  have htrace : WordTrace (prefixWord ++ tailWord_517045) baseStart_517045 baseEnd_517045 := by
    simpa [prefixWord, tailWord_517045, baseEnd_517045] using wordTrace_append hprefix tailTrace_517045
  have hstable : (prefixWord ++ tailWord_517045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517045).length < 2 ^ (prefixWord ++ tailWord_517045).sum := by decide
  have hdescent : baseEnd_517045 < baseStart_517045 := by decide
  rcases family_descends (prefixWord ++ tailWord_517045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517076 : List Nat := [2, 4, 1, 2, 1, 3, 1, 6]
def baseStart_517076 : Nat := 118140960795 + 517076 * 2 ^ 59
def prefixEnd_517076 : Nat := 4983230072969 + 3 ^ 40 * 517076 * 2
def baseEnd_517076 : Nat := 78669191971651606362079

theorem tailTrace_517076 : CollatzResearch.WordTrace tailWord_517076 prefixEnd_517076 78669191971651606362079 := by
  unfold tailWord_517076
  simp only [CollatzResearch.WordTrace]
  refine ⟨9429655537364718197613541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12572874049819624263484721 9429655537364718197613541)
  ·
    refine ⟨1768060413255884662052539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9429655537364718197613541 1768060413255884662052539)
    ·
      refine ⟨2652090619883826993078809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1768060413255884662052539 2652090619883826993078809)
      ·
        refine ⟨1989067964912870244809107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2652090619883826993078809 1989067964912870244809107)
        ·
          refine ⟨2983601947369305367213661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1989067964912870244809107 2983601947369305367213661)
          ·
            refine ⟨1118850730263489512705123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2983601947369305367213661 1118850730263489512705123)
            ·
              refine ⟨1678276095395234269057685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1118850730263489512705123 1678276095395234269057685)
              ·
                refine ⟨78669191971651606362079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1678276095395234269057685 78669191971651606362079)
                ·
                  rfl

theorem cell20_517076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 6].length) (baseStart_517076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517076 prefixEnd_517076 := by exact prefixLift 517076
  have htrace : WordTrace (prefixWord ++ tailWord_517076) baseStart_517076 baseEnd_517076 := by
    simpa [prefixWord, tailWord_517076, baseEnd_517076] using wordTrace_append hprefix tailTrace_517076
  have hstable : (prefixWord ++ tailWord_517076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517076).length < 2 ^ (prefixWord ++ tailWord_517076).sum := by decide
  have hdescent : baseEnd_517076 < baseStart_517076 := by decide
  rcases family_descends (prefixWord ++ tailWord_517076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517093 : List Nat := [1, 3, 1, 6, 1, 2, 6]
def baseStart_517093 : Nat := 118140960795 + 517093 * 2 ^ 59
def prefixEnd_517093 : Nat := 4983230072969 + 3 ^ 40 * 517093 * 2
def baseEnd_517093 : Nat := 26223926130908701724389

theorem tailTrace_517093 : CollatzResearch.WordTrace tailWord_517093 prefixEnd_517093 26223926130908701724389 := by
  unfold tailWord_517093
  simp only [CollatzResearch.WordTrace]
  refine ⟨18859931115667848298595933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12573287410445232199063955 18859931115667848298595933)
  ·
    refine ⟨7072474168375443111973475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18859931115667848298595933 7072474168375443111973475)
    ·
      refine ⟨10608711252563164667960213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7072474168375443111973475 10608711252563164667960213)
      ·
        refine ⟨497283339963898343810635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10608711252563164667960213 497283339963898343810635)
        ·
          refine ⟨745925009945847515715953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497283339963898343810635 745925009945847515715953)
          ·
            refine ⟨559443757459385636786965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 745925009945847515715953 559443757459385636786965)
            ·
              refine ⟨26223926130908701724389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 559443757459385636786965 26223926130908701724389)
              ·
                rfl

theorem cell20_517093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 6].length) (baseStart_517093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517093 prefixEnd_517093 := by exact prefixLift 517093
  have htrace : WordTrace (prefixWord ++ tailWord_517093) baseStart_517093 baseEnd_517093 := by
    simpa [prefixWord, tailWord_517093, baseEnd_517093] using wordTrace_append hprefix tailTrace_517093
  have hstable : (prefixWord ++ tailWord_517093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517093).length < 2 ^ (prefixWord ++ tailWord_517093).sum := by decide
  have hdescent : baseEnd_517093 < baseStart_517093 := by decide
  rcases family_descends (prefixWord ++ tailWord_517093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517152 : List Nat := [2, 1, 1, 7, 1, 8]
def baseStart_517152 : Nat := 118140960795 + 517152 * 2 ^ 59
def prefixEnd_517152 : Nat := 4983230072969 + 3 ^ 40 * 517152 * 2
def baseEnd_517152 : Nat := 8742306088364308613059

theorem tailTrace_517152 : CollatzResearch.WordTrace tailWord_517152 prefixEnd_517152 8742306088364308613059 := by
  unfold tailWord_517152
  simp only [CollatzResearch.WordTrace]
  refine ⟨9431041511227050687496855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12574722014969400916662473 9431041511227050687496855)
  ·
    refine ⟨14146562266840576031245283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9431041511227050687496855 14146562266840576031245283)
    ·
      refine ⟨21219843400260864046867925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14146562266840576031245283 21219843400260864046867925)
      ·
        refine ⟨497340079693614001098467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 21219843400260864046867925 497340079693614001098467)
        ·
          refine ⟨746010119540421001647701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497340079693614001098467 746010119540421001647701)
          ·
            refine ⟨8742306088364308613059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 746010119540421001647701 8742306088364308613059)
            ·
              rfl

theorem cell20_517152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 8].length) (baseStart_517152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517152 prefixEnd_517152 := by exact prefixLift 517152
  have htrace : WordTrace (prefixWord ++ tailWord_517152) baseStart_517152 baseEnd_517152 := by
    simpa [prefixWord, tailWord_517152, baseEnd_517152] using wordTrace_append hprefix tailTrace_517152
  have hstable : (prefixWord ++ tailWord_517152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517152).length < 2 ^ (prefixWord ++ tailWord_517152).sum := by decide
  have hdescent : baseEnd_517152 < baseStart_517152 := by decide
  rcases family_descends (prefixWord ++ tailWord_517152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517221 : List Nat := [1, 3, 1, 3, 2, 1, 1, 6, 2]
def baseStart_517221 : Nat := 118140960795 + 517221 * 2 ^ 59
def prefixEnd_517221 : Nat := 4983230072969 + 3 ^ 40 * 517221 * 2
def baseEnd_517221 : Nat := 236073757865978759252311

theorem tailTrace_517221 : CollatzResearch.WordTrace tailWord_517221 prefixEnd_517221 236073757865978759252311 := by
  unfold tailWord_517221
  simp only [CollatzResearch.WordTrace]
  refine ⟨18864599659204126159255517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12576399772802750772837011 18864599659204126159255517)
  ·
    refine ⟨7074224872201547309720819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18864599659204126159255517 7074224872201547309720819)
    ·
      refine ⟨10611337308302320964581229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7074224872201547309720819 10611337308302320964581229)
      ·
        refine ⟨3979251490613370361717961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10611337308302320964581229 3979251490613370361717961)
        ·
          refine ⟨2984438617960027771288471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3979251490613370361717961 2984438617960027771288471)
          ·
            refine ⟨4476657926940041656932707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2984438617960027771288471 4476657926940041656932707)
            ·
              refine ⟨6714986890410062485399061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4476657926940041656932707 6714986890410062485399061)
              ·
                refine ⟨314765010487971679003081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6714986890410062485399061 314765010487971679003081)
                ·
                  refine ⟨236073757865978759252311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 314765010487971679003081 236073757865978759252311)
                  ·
                    rfl

theorem cell20_517221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 6, 2].length) (baseStart_517221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517221 prefixEnd_517221 := by exact prefixLift 517221
  have htrace : WordTrace (prefixWord ++ tailWord_517221) baseStart_517221 baseEnd_517221 := by
    simpa [prefixWord, tailWord_517221, baseEnd_517221] using wordTrace_append hprefix tailTrace_517221
  have hstable : (prefixWord ++ tailWord_517221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517221).length < 2 ^ (prefixWord ++ tailWord_517221).sum := by decide
  have hdescent : baseEnd_517221 < baseStart_517221 := by decide
  rcases family_descends (prefixWord ++ tailWord_517221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517266 : List Nat := [3, 2, 3, 1, 1, 4, 6]
def baseStart_517266 : Nat := 118140960795 + 517266 * 2 ^ 59
def prefixEnd_517266 : Nat := 4983230072969 + 3 ^ 40 * 517266 * 2
def baseEnd_517266 : Nat := 26232699676906511416903

theorem tailTrace_517266 : CollatzResearch.WordTrace tailWord_517266 prefixEnd_517266 26232699676906511416903 := by
  unfold tailWord_517266
  simp only [CollatzResearch.WordTrace]
  refine ⟨4716560236010274711160913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12577493962694065896429101 4716560236010274711160913)
  ·
    refine ⟨3537420177007706033370685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4716560236010274711160913 3537420177007706033370685)
    ·
      refine ⟨1326532566377889762514007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3537420177007706033370685 1326532566377889762514007)
      ·
        refine ⟨1989798849566834643771011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1326532566377889762514007 1989798849566834643771011)
        ·
          refine ⟨2984698274350251965656517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1989798849566834643771011 2984698274350251965656517)
          ·
            refine ⟨559630926440672243560597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2984698274350251965656517 559630926440672243560597)
            ·
              refine ⟨26232699676906511416903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 559630926440672243560597 26232699676906511416903)
              ·
                rfl

theorem cell20_517266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 6].length) (baseStart_517266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517266 prefixEnd_517266 := by exact prefixLift 517266
  have htrace : WordTrace (prefixWord ++ tailWord_517266) baseStart_517266 baseEnd_517266 := by
    simpa [prefixWord, tailWord_517266, baseEnd_517266] using wordTrace_append hprefix tailTrace_517266
  have hstable : (prefixWord ++ tailWord_517266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517266).length < 2 ^ (prefixWord ++ tailWord_517266).sum := by decide
  have hdescent : baseEnd_517266 < baseStart_517266 := by decide
  rcases family_descends (prefixWord ++ tailWord_517266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517356 : List Nat := [2, 2, 1, 1, 2, 5, 1, 2, 4]
def baseStart_517356 : Nat := 118140960795 + 517356 * 2 ^ 59
def prefixEnd_517356 : Nat := 4983230072969 + 3 ^ 40 * 517356 * 2
def baseEnd_517356 : Nat := 236135375544518289751759

theorem tailTrace_517356 : CollatzResearch.WordTrace tailWord_517356 prefixEnd_517356 236135375544518289751759 := by
  unfold tailWord_517356
  simp only [CollatzResearch.WordTrace]
  refine ⟨9434761756857522107709961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12579682342476696143613281 9434761756857522107709961)
  ·
    refine ⟨7076071317643141580782471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9434761756857522107709961 7076071317643141580782471)
    ·
      refine ⟨10614106976464712371173707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7076071317643141580782471 10614106976464712371173707)
      ·
        refine ⟨15921160464697068556760561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10614106976464712371173707 15921160464697068556760561)
        ·
          refine ⟨11940870348522801417570421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15921160464697068556760561 11940870348522801417570421)
          ·
            refine ⟨1119456595174012632897227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11940870348522801417570421 1119456595174012632897227)
            ·
              refine ⟨1679184892761018949345841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1119456595174012632897227 1679184892761018949345841)
              ·
                refine ⟨1259388669570764212009381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1679184892761018949345841 1259388669570764212009381)
                ·
                  refine ⟨236135375544518289751759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1259388669570764212009381 236135375544518289751759)
                  ·
                    rfl

theorem cell20_517356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_517356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517356 prefixEnd_517356 := by exact prefixLift 517356
  have htrace : WordTrace (prefixWord ++ tailWord_517356) baseStart_517356 baseEnd_517356 := by
    simpa [prefixWord, tailWord_517356, baseEnd_517356] using wordTrace_append hprefix tailTrace_517356
  have hstable : (prefixWord ++ tailWord_517356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517356).length < 2 ^ (prefixWord ++ tailWord_517356).sum := by decide
  have hdescent : baseEnd_517356 < baseStart_517356 := by decide
  rcases family_descends (prefixWord ++ tailWord_517356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517370 : List Nat := [3, 1, 1, 1, 1, 4, 2, 2, 5]
def baseStart_517370 : Nat := 118140960795 + 517370 * 2 ^ 59
def prefixEnd_517370 : Nat := 4983230072969 + 3 ^ 40 * 517370 * 2
def baseEnd_517370 : Nat := 236141765525996463285035

theorem tailTrace_517370 : CollatzResearch.WordTrace tailWord_517370 prefixEnd_517370 236141765525996463285035 := by
  unfold tailWord_517370
  simp only [CollatzResearch.WordTrace]
  refine ⟨4717508533916081151607391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12580022757109549737619709 4717508533916081151607391)
  ·
    refine ⟨7076262800874121727411087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4717508533916081151607391 7076262800874121727411087)
    ·
      refine ⟨10614394201311182591116631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7076262800874121727411087 10614394201311182591116631)
      ·
        refine ⟨15921591301966773886674947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10614394201311182591116631 15921591301966773886674947)
        ·
          refine ⟨23882386952950160830012421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15921591301966773886674947 23882386952950160830012421)
          ·
            refine ⟨4477947553678155155627329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23882386952950160830012421 4477947553678155155627329)
            ·
              refine ⟨3358460665258616366720497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4477947553678155155627329 3358460665258616366720497)
              ·
                refine ⟨2518845498943962275040373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3358460665258616366720497 2518845498943962275040373)
                ·
                  refine ⟨236141765525996463285035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2518845498943962275040373 236141765525996463285035)
                  ·
                    rfl

theorem cell20_517370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_517370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517370 prefixEnd_517370 := by exact prefixLift 517370
  have htrace : WordTrace (prefixWord ++ tailWord_517370) baseStart_517370 baseEnd_517370 := by
    simpa [prefixWord, tailWord_517370, baseEnd_517370] using wordTrace_append hprefix tailTrace_517370
  have hstable : (prefixWord ++ tailWord_517370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517370).length < 2 ^ (prefixWord ++ tailWord_517370).sum := by decide
  have hdescent : baseEnd_517370 < baseStart_517370 := by decide
  rcases family_descends (prefixWord ++ tailWord_517370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517387 : List Nat := [1, 1, 1, 1, 5, 3, 3, 2, 3]
def baseStart_517387 : Nat := 118140960795 + 517387 * 2 ^ 59
def prefixEnd_517387 : Nat := 4983230072969 + 3 ^ 40 * 517387 * 2
def baseEnd_517387 : Nat := 236149524789219959718299

theorem tailTrace_517387 : CollatzResearch.WordTrace tailWord_517387 prefixEnd_517387 236149524789219959718299 := by
  unfold tailWord_517387
  simp only [CollatzResearch.WordTrace]
  refine ⟨18870654176602736509798415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12580436117735157673198943 18870654176602736509798415)
  ·
    refine ⟨28305981264904104764697623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18870654176602736509798415 28305981264904104764697623)
    ·
      refine ⟨42458971897356157147046435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28305981264904104764697623 42458971897356157147046435)
      ·
        refine ⟨63688457846034235720569653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42458971897356157147046435 63688457846034235720569653)
        ·
          refine ⟨5970792923065709598803405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63688457846034235720569653 5970792923065709598803405)
          ·
            refine ⟨2239047346149641099551277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5970792923065709598803405 2239047346149641099551277)
            ·
              refine ⟨839642754806115412331729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2239047346149641099551277 839642754806115412331729)
              ·
                refine ⟨629732066104586559248797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 839642754806115412331729 629732066104586559248797)
                ·
                  refine ⟨236149524789219959718299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 629732066104586559248797 236149524789219959718299)
                  ·
                    rfl

theorem cell20_517387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 3].length) (baseStart_517387 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517387 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517387 prefixEnd_517387 := by exact prefixLift 517387
  have htrace : WordTrace (prefixWord ++ tailWord_517387) baseStart_517387 baseEnd_517387 := by
    simpa [prefixWord, tailWord_517387, baseEnd_517387] using wordTrace_append hprefix tailTrace_517387
  have hstable : (prefixWord ++ tailWord_517387).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517387).length < 2 ^ (prefixWord ++ tailWord_517387).sum := by decide
  have hdescent : baseEnd_517387 < baseStart_517387 := by decide
  rcases family_descends (prefixWord ++ tailWord_517387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517418 : List Nat := [3, 1, 4, 2, 1, 2, 1, 6]
def baseStart_517418 : Nat := 118140960795 + 517418 * 2 ^ 59
def prefixEnd_517418 : Nat := 4983230072969 + 3 ^ 40 * 517418 * 2
def baseEnd_517418 : Nat := 78721224677973876561613

theorem tailTrace_517418 : CollatzResearch.WordTrace tailWord_517418 prefixEnd_517418 78721224677973876561613 := by
  unfold tailWord_517418
  simp only [CollatzResearch.WordTrace]
  refine ⟨4717946209872607201044227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12581189892993619202784605 4717946209872607201044227)
  ·
    refine ⟨7076919314808910801566341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4717946209872607201044227 7076919314808910801566341)
    ·
      refine ⟨1326922371526670775293689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7076919314808910801566341 1326922371526670775293689)
      ·
        refine ⟨995191778645003081470267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1326922371526670775293689 995191778645003081470267)
        ·
          refine ⟨1492787667967504622205401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 995191778645003081470267 1492787667967504622205401)
          ·
            refine ⟨1119590750975628466654051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1492787667967504622205401 1119590750975628466654051)
            ·
              refine ⟨1679386126463442699981077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1119590750975628466654051 1679386126463442699981077)
              ·
                refine ⟨78721224677973876561613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1679386126463442699981077 78721224677973876561613)
                ·
                  rfl

theorem cell20_517418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_517418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517418 prefixEnd_517418 := by exact prefixLift 517418
  have htrace : WordTrace (prefixWord ++ tailWord_517418) baseStart_517418 baseEnd_517418 := by
    simpa [prefixWord, tailWord_517418, baseEnd_517418] using wordTrace_append hprefix tailTrace_517418
  have hstable : (prefixWord ++ tailWord_517418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517418).length < 2 ^ (prefixWord ++ tailWord_517418).sum := by decide
  have hdescent : baseEnd_517418 < baseStart_517418 := by decide
  rcases family_descends (prefixWord ++ tailWord_517418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517439 : List Nat := [1, 1, 2, 2, 4, 4, 6]
def baseStart_517439 : Nat := 118140960795 + 517439 * 2 ^ 59
def prefixEnd_517439 : Nat := 4983230072969 + 3 ^ 40 * 517439 * 2
def baseEnd_517439 : Nat := 26241473222904321109417

theorem tailTrace_517439 : CollatzResearch.WordTrace tailWord_517439 prefixEnd_517439 26241473222904321109417 := by
  unfold tailWord_517439
  simp only [CollatzResearch.WordTrace]
  refine ⟨18872550772414349390691371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12581700514942899593794247 18872550772414349390691371)
  ·
    refine ⟨28308826158621524086037057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18872550772414349390691371 28308826158621524086037057)
    ·
      refine ⟨21231619618966143064527793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28308826158621524086037057 21231619618966143064527793)
      ·
        refine ⟨15923714714224607298395845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21231619618966143064527793 15923714714224607298395845)
        ·
          refine ⟨2985696508917113868449221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15923714714224607298395845 2985696508917113868449221)
          ·
            refine ⟨559818095421958850334229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2985696508917113868449221 559818095421958850334229)
            ·
              refine ⟨26241473222904321109417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 559818095421958850334229 26241473222904321109417)
              ·
                rfl

theorem cell20_517439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 6].length) (baseStart_517439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517439 prefixEnd_517439 := by exact prefixLift 517439
  have htrace : WordTrace (prefixWord ++ tailWord_517439) baseStart_517439 baseEnd_517439 := by
    simpa [prefixWord, tailWord_517439, baseEnd_517439] using wordTrace_append hprefix tailTrace_517439
  have hstable : (prefixWord ++ tailWord_517439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517439).length < 2 ^ (prefixWord ++ tailWord_517439).sum := by decide
  have hdescent : baseEnd_517439 < baseStart_517439 := by decide
  rcases family_descends (prefixWord ++ tailWord_517439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517463 : List Nat := [1, 1, 3, 2, 3, 3, 1, 3, 3]
def baseStart_517463 : Nat := 118140960795 + 517463 * 2 ^ 59
def prefixEnd_517463 : Nat := 4983230072969 + 3 ^ 40 * 517463 * 2
def baseEnd_517463 : Nat := 236184213260101473184655

theorem tailTrace_517463 : CollatzResearch.WordTrace tailWord_517463 prefixEnd_517463 236184213260101473184655 := by
  unfold tailWord_517463
  simp only [CollatzResearch.WordTrace]
  refine ⟨18873426124327401489565043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12582284082884934326376695 18873426124327401489565043)
  ·
    refine ⟨28310139186491102234347565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18873426124327401489565043 28310139186491102234347565)
    ·
      refine ⟨10616302194934163337880337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28310139186491102234347565 10616302194934163337880337)
      ·
        refine ⟨7962226646200622503410253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10616302194934163337880337 7962226646200622503410253)
        ·
          refine ⟨2985834992325233438778845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7962226646200622503410253 2985834992325233438778845)
          ·
            refine ⟨1119688122121962539542067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2985834992325233438778845 1119688122121962539542067)
            ·
              refine ⟨1679532183182943809313101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1119688122121962539542067 1679532183182943809313101)
              ·
                refine ⟨629824568693603928492413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1679532183182943809313101 629824568693603928492413)
                ·
                  refine ⟨236184213260101473184655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 629824568693603928492413 236184213260101473184655)
                  ·
                    rfl

theorem cell20_517463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 3].length) (baseStart_517463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517463 prefixEnd_517463 := by exact prefixLift 517463
  have htrace : WordTrace (prefixWord ++ tailWord_517463) baseStart_517463 baseEnd_517463 := by
    simpa [prefixWord, tailWord_517463, baseEnd_517463] using wordTrace_append hprefix tailTrace_517463
  have hstable : (prefixWord ++ tailWord_517463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517463).length < 2 ^ (prefixWord ++ tailWord_517463).sum := by decide
  have hdescent : baseEnd_517463 < baseStart_517463 := by decide
  rcases family_descends (prefixWord ++ tailWord_517463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517501 : List Nat := [1, 4, 1, 1, 2, 2, 4, 2, 3]
def baseStart_517501 : Nat := 118140960795 + 517501 * 2 ^ 59
def prefixEnd_517501 : Nat := 4983230072969 + 3 ^ 40 * 517501 * 2
def baseEnd_517501 : Nat := 236201557495542229917833

theorem tailTrace_517501 : CollatzResearch.WordTrace tailWord_517501 prefixEnd_517501 236201557495542229917833 := by
  unfold tailWord_517501
  simp only [CollatzResearch.WordTrace]
  refine ⟨18874812098189733979448357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12583208065459822652965571 18874812098189733979448357)
  ·
    refine ⟨3539027268410575121146567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18874812098189733979448357 3539027268410575121146567)
    ·
      refine ⟨5308540902615862681719851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3539027268410575121146567 5308540902615862681719851)
      ·
        refine ⟨7962811353923794022579777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5308540902615862681719851 7962811353923794022579777)
        ·
          refine ⟨5972108515442845516934833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7962811353923794022579777 5972108515442845516934833)
          ·
            refine ⟨4479081386582134137701125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5972108515442845516934833 4479081386582134137701125)
            ·
              refine ⟨839827759984150150818961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4479081386582134137701125 839827759984150150818961)
              ·
                refine ⟨629870819988112613114221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 839827759984150150818961 629870819988112613114221)
                ·
                  refine ⟨236201557495542229917833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 629870819988112613114221 236201557495542229917833)
                  ·
                    rfl

theorem cell20_517501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_517501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517501 prefixEnd_517501 := by exact prefixLift 517501
  have htrace : WordTrace (prefixWord ++ tailWord_517501) baseStart_517501 baseEnd_517501 := by
    simpa [prefixWord, tailWord_517501, baseEnd_517501] using wordTrace_append hprefix tailTrace_517501
  have hstable : (prefixWord ++ tailWord_517501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517501).length < 2 ^ (prefixWord ++ tailWord_517501).sum := by decide
  have hdescent : baseEnd_517501 < baseStart_517501 := by decide
  rcases family_descends (prefixWord ++ tailWord_517501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517529 : List Nat := [1, 2, 1, 2, 1, 5, 1, 1, 6]
def baseStart_517529 : Nat := 118140960795 + 517529 * 2 ^ 59
def prefixEnd_517529 : Nat := 4983230072969 + 3 ^ 40 * 517529 * 2
def baseEnd_517529 : Nat := 236214337458498576984385

theorem tailTrace_517529 : CollatzResearch.WordTrace tailWord_517529 prefixEnd_517529 236214337458498576984385 := by
  unfold tailWord_517529
  simp only [CollatzResearch.WordTrace]
  refine ⟨18875833342088294761467641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12583888894725529840978427 18875833342088294761467641)
  ·
    refine ⟨14156875006566221071100731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18875833342088294761467641 14156875006566221071100731)
    ·
      refine ⟨21235312509849331606651097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14156875006566221071100731 21235312509849331606651097)
      ·
        refine ⟨15926484382386998704988323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21235312509849331606651097 15926484382386998704988323)
        ·
          refine ⟨23889726573580498057482485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15926484382386998704988323 23889726573580498057482485)
          ·
            refine ⟨2239661866273171692888983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23889726573580498057482485 2239661866273171692888983)
            ·
              refine ⟨3359492799409757539333475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2239661866273171692888983 3359492799409757539333475)
              ·
                refine ⟨5039239199114636309000213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3359492799409757539333475 5039239199114636309000213)
                ·
                  refine ⟨236214337458498576984385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5039239199114636309000213 236214337458498576984385)
                  ·
                    rfl

theorem cell20_517529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_517529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517529 prefixEnd_517529 := by exact prefixLift 517529
  have htrace : WordTrace (prefixWord ++ tailWord_517529) baseStart_517529 baseEnd_517529 := by
    simpa [prefixWord, tailWord_517529, baseEnd_517529] using wordTrace_append hprefix tailTrace_517529
  have hstable : (prefixWord ++ tailWord_517529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517529).length < 2 ^ (prefixWord ++ tailWord_517529).sum := by decide
  have hdescent : baseEnd_517529 < baseStart_517529 := by decide
  rcases family_descends (prefixWord ++ tailWord_517529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517601 : List Nat := [1, 2, 3, 1, 2, 3, 3, 3, 2]
def baseStart_517601 : Nat := 118140960795 + 517601 * 2 ^ 59
def prefixEnd_517601 : Nat := 4983230072969 + 3 ^ 40 * 517601 * 2
def baseEnd_517601 : Nat := 236247200220386326584091

theorem tailTrace_517601 : CollatzResearch.WordTrace tailWord_517601 prefixEnd_517601 236247200220386326584091 := by
  unfold tailWord_517601
  simp only [CollatzResearch.WordTrace]
  refine ⟨18878459397827451058088657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12585639598551634038725771 18878459397827451058088657)
  ·
    refine ⟨14158844548370588293566493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18878459397827451058088657 14158844548370588293566493)
    ·
      refine ⟨5309566705638970610087435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14158844548370588293566493 5309566705638970610087435)
      ·
        refine ⟨7964350058458455915131153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5309566705638970610087435 7964350058458455915131153)
        ·
          refine ⟨5973262543843841936348365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7964350058458455915131153 5973262543843841936348365)
          ·
            refine ⟨2239973453941440726130637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5973262543843841936348365 2239973453941440726130637)
            ·
              refine ⟨839990045228040272298989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2239973453941440726130637 839990045228040272298989)
              ·
                refine ⟨314996266960515102112121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 839990045228040272298989 314996266960515102112121)
                ·
                  refine ⟨236247200220386326584091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 314996266960515102112121 236247200220386326584091)
                  ·
                    rfl

theorem cell20_517601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 3, 2].length) (baseStart_517601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517601 prefixEnd_517601 := by exact prefixLift 517601
  have htrace : WordTrace (prefixWord ++ tailWord_517601) baseStart_517601 baseEnd_517601 := by
    simpa [prefixWord, tailWord_517601, baseEnd_517601] using wordTrace_append hprefix tailTrace_517601
  have hstable : (prefixWord ++ tailWord_517601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517601).length < 2 ^ (prefixWord ++ tailWord_517601).sum := by decide
  have hdescent : baseEnd_517601 < baseStart_517601 := by decide
  rcases family_descends (prefixWord ++ tailWord_517601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517629 : List Nat := [1, 4, 1, 1, 1, 5, 2, 5]
def baseStart_517629 : Nat := 118140960795 + 517629 * 2 ^ 59
def prefixEnd_517629 : Nat := 4983230072969 + 3 ^ 40 * 517629 * 2
def baseEnd_517629 : Nat := 78753326727780891216881

theorem tailTrace_517629 : CollatzResearch.WordTrace tailWord_517629 prefixEnd_517629 78753326727780891216881 := by
  unfold tailWord_517629
  simp only [CollatzResearch.WordTrace]
  refine ⟨18879480641726011840107941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12586320427817341226738627 18879480641726011840107941)
  ·
    refine ⟨3539902620323627220020239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18879480641726011840107941 3539902620323627220020239)
    ·
      refine ⟨5309853930485440830030359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3539902620323627220020239 5309853930485440830030359)
      ·
        refine ⟨7964780895728161245045539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5309853930485440830030359 7964780895728161245045539)
        ·
          refine ⟨11947171343592241867568309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7964780895728161245045539 11947171343592241867568309)
          ·
            refine ⟨1120047313461772675084529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11947171343592241867568309 1120047313461772675084529)
            ·
              refine ⟨840035485096329506313397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1120047313461772675084529 840035485096329506313397)
              ·
                refine ⟨78753326727780891216881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 840035485096329506313397 78753326727780891216881)
                ·
                  rfl

theorem cell20_517629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 5].length) (baseStart_517629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517629 prefixEnd_517629 := by exact prefixLift 517629
  have htrace : WordTrace (prefixWord ++ tailWord_517629) baseStart_517629 baseEnd_517629 := by
    simpa [prefixWord, tailWord_517629, baseEnd_517629] using wordTrace_append hprefix tailTrace_517629
  have hstable : (prefixWord ++ tailWord_517629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517629).length < 2 ^ (prefixWord ++ tailWord_517629).sum := by decide
  have hdescent : baseEnd_517629 < baseStart_517629 := by decide
  rcases family_descends (prefixWord ++ tailWord_517629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517667 : List Nat := [1, 1, 1, 4, 6, 7]
def baseStart_517667 : Nat := 118140960795 + 517667 * 2 ^ 59
def prefixEnd_517667 : Nat := 4983230072969 + 3 ^ 40 * 517667 * 2
def baseEnd_517667 : Nat := 8751012015510497421623

theorem tailTrace_517667 : CollatzResearch.WordTrace tailWord_517667 prefixEnd_517667 8751012015510497421623 := by
  unfold tailWord_517667
  simp only [CollatzResearch.WordTrace]
  refine ⟨18880866615588344329991255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12587244410392229553327503 18880866615588344329991255)
  ·
    refine ⟨28321299923382516494986883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18880866615588344329991255 28321299923382516494986883)
    ·
      refine ⟨42481949885073774742480325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28321299923382516494986883 42481949885073774742480325)
      ·
        refine ⟨7965365603451332764215061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42481949885073774742480325 7965365603451332764215061)
        ·
          refine ⟨373376512661781223322581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7965365603451332764215061 373376512661781223322581)
          ·
            refine ⟨8751012015510497421623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 373376512661781223322581 8751012015510497421623)
            ·
              rfl

theorem cell20_517667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 7].length) (baseStart_517667 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517667 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517667 prefixEnd_517667 := by exact prefixLift 517667
  have htrace : WordTrace (prefixWord ++ tailWord_517667) baseStart_517667 baseEnd_517667 := by
    simpa [prefixWord, tailWord_517667, baseEnd_517667] using wordTrace_append hprefix tailTrace_517667
  have hstable : (prefixWord ++ tailWord_517667).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517667).length < 2 ^ (prefixWord ++ tailWord_517667).sum := by decide
  have hdescent : baseEnd_517667 < baseStart_517667 := by decide
  rcases family_descends (prefixWord ++ tailWord_517667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517681 : List Nat := [1, 2, 2, 3, 1, 1, 1, 5, 4]
def baseStart_517681 : Nat := 118140960795 + 517681 * 2 ^ 59
def prefixEnd_517681 : Nat := 4983230072969 + 3 ^ 40 * 517681 * 2
def baseEnd_517681 : Nat := 236283714400261603917097

theorem tailTrace_517681 : CollatzResearch.WordTrace tailWord_517681 prefixEnd_517681 236283714400261603917097 := by
  unfold tailWord_517681
  simp only [CollatzResearch.WordTrace]
  refine ⟨18881377237537624721000897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12587584825025083147333931 18881377237537624721000897)
  ·
    refine ⟨14161032928153218540750673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18881377237537624721000897 14161032928153218540750673)
    ·
      refine ⟨10620774696114913905563005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14161032928153218540750673 10620774696114913905563005)
      ·
        refine ⟨3982790511043092714586127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10620774696114913905563005 3982790511043092714586127)
        ·
          refine ⟨5974185766564639071879191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3982790511043092714586127 5974185766564639071879191)
          ·
            refine ⟨8961278649846958607818787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5974185766564639071879191 8961278649846958607818787)
            ·
              refine ⟨13441917974770437911728181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8961278649846958607818787 13441917974770437911728181)
              ·
                refine ⟨1260179810134728554224517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13441917974770437911728181 1260179810134728554224517)
                ·
                  refine ⟨236283714400261603917097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1260179810134728554224517 236283714400261603917097)
                  ·
                    rfl

theorem cell20_517681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_517681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517681 prefixEnd_517681 := by exact prefixLift 517681
  have htrace : WordTrace (prefixWord ++ tailWord_517681) baseStart_517681 baseEnd_517681 := by
    simpa [prefixWord, tailWord_517681, baseEnd_517681] using wordTrace_append hprefix tailTrace_517681
  have hstable : (prefixWord ++ tailWord_517681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517681).length < 2 ^ (prefixWord ++ tailWord_517681).sum := by decide
  have hdescent : baseEnd_517681 < baseStart_517681 := by decide
  rcases family_descends (prefixWord ++ tailWord_517681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517736 : List Nat := [2, 1, 4, 3, 1, 1, 1, 3, 4]
def baseStart_517736 : Nat := 118140960795 + 517736 * 2 ^ 59
def prefixEnd_517736 : Nat := 4983230072969 + 3 ^ 40 * 517736 * 2
def baseEnd_517736 : Nat := 236308817898925857083539

theorem tailTrace_517736 : CollatzResearch.WordTrace tailWord_517736 prefixEnd_517736 236308817898925857083539 := by
  unfold tailWord_517736
  simp only [CollatzResearch.WordTrace]
  refine ⟨9441691626169184557126531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12588922168225579409502041 9441691626169184557126531)
  ·
    refine ⟨14162537439253776835689797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9441691626169184557126531 14162537439253776835689797)
    ·
      refine ⟨2655475769860083156691837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14162537439253776835689797 2655475769860083156691837)
      ·
        refine ⟨995803413697531183759439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2655475769860083156691837 995803413697531183759439)
        ·
          refine ⟨1493705120546296775639159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 995803413697531183759439 1493705120546296775639159)
          ·
            refine ⟨2240557680819445163458739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1493705120546296775639159 2240557680819445163458739)
            ·
              refine ⟨3360836521229167745188109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2240557680819445163458739 3360836521229167745188109)
              ·
                refine ⟨1260313695460937904445541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3360836521229167745188109 1260313695460937904445541)
                ·
                  refine ⟨236308817898925857083539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1260313695460937904445541 236308817898925857083539)
                  ·
                    rfl

theorem cell20_517736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 4].length) (baseStart_517736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517736 prefixEnd_517736 := by exact prefixLift 517736
  have htrace : WordTrace (prefixWord ++ tailWord_517736) baseStart_517736 baseEnd_517736 := by
    simpa [prefixWord, tailWord_517736, baseEnd_517736] using wordTrace_append hprefix tailTrace_517736
  have hstable : (prefixWord ++ tailWord_517736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517736).length < 2 ^ (prefixWord ++ tailWord_517736).sum := by decide
  have hdescent : baseEnd_517736 < baseStart_517736 := by decide
  rcases family_descends (prefixWord ++ tailWord_517736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517746 : List Nat := [3, 2, 1, 2, 3, 2, 3, 1, 3]
def baseStart_517746 : Nat := 118140960795 + 517746 * 2 ^ 59
def prefixEnd_517746 : Nat := 4983230072969 + 3 ^ 40 * 517746 * 2
def baseEnd_517746 : Nat := 236313382171410266750165

theorem tailTrace_517746 : CollatzResearch.WordTrace tailWord_517746 prefixEnd_517746 236313382171410266750165 := by
  unfold tailWord_517746
  simp only [CollatzResearch.WordTrace]
  refine ⟨4720936995575535205529273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12589165321534760548078061 4720936995575535205529273)
  ·
    refine ⟨3540702746681651404146955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4720936995575535205529273 3540702746681651404146955)
    ·
      refine ⟨5311054120022477106220433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3540702746681651404146955 5311054120022477106220433)
      ·
        refine ⟨3983290590016857829665325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5311054120022477106220433 3983290590016857829665325)
        ·
          refine ⟨1493733971256321686124497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3983290590016857829665325 1493733971256321686124497)
          ·
            refine ⟨1120300478442241264593373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1493733971256321686124497 1120300478442241264593373)
            ·
              refine ⟨420112679415840474222515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1120300478442241264593373 420112679415840474222515)
              ·
                refine ⟨630169019123760711333773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420112679415840474222515 630169019123760711333773)
                ·
                  refine ⟨236313382171410266750165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 630169019123760711333773 236313382171410266750165)
                  ·
                    rfl

theorem cell20_517746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_517746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517746 prefixEnd_517746 := by exact prefixLift 517746
  have htrace : WordTrace (prefixWord ++ tailWord_517746) baseStart_517746 baseEnd_517746 := by
    simpa [prefixWord, tailWord_517746, baseEnd_517746] using wordTrace_append hprefix tailTrace_517746
  have hstable : (prefixWord ++ tailWord_517746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517746).length < 2 ^ (prefixWord ++ tailWord_517746).sum := by decide
  have hdescent : baseEnd_517746 < baseStart_517746 := by decide
  rcases family_descends (prefixWord ++ tailWord_517746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517770 : List Nat := [3, 1, 2, 3, 2, 3, 1, 3, 2]
def baseStart_517770 : Nat := 118140960795 + 517770 * 2 ^ 59
def prefixEnd_517770 : Nat := 4983230072969 + 3 ^ 40 * 517770 * 2
def baseEnd_517770 : Nat := 236324336425372849950067

theorem tailTrace_517770 : CollatzResearch.WordTrace tailWord_517770 prefixEnd_517770 236324336425372849950067 := by
  unfold tailWord_517770
  simp only [CollatzResearch.WordTrace]
  refine ⟨4721155833553798230247691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12589748889476795280660509 4721155833553798230247691)
  ·
    refine ⟨7081733750330697345371537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4721155833553798230247691 7081733750330697345371537)
    ·
      refine ⟨5311300312748023009028653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7081733750330697345371537 5311300312748023009028653)
      ·
        refine ⟨1991737617280508628385745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5311300312748023009028653 1991737617280508628385745)
        ·
          refine ⟨1493803212960381471289309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1991737617280508628385745 1493803212960381471289309)
          ·
            refine ⟨560176204860143051733491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1493803212960381471289309 560176204860143051733491)
            ·
              refine ⟨840264307290214577600237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560176204860143051733491 840264307290214577600237)
              ·
                refine ⟨315099115233830466600089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 840264307290214577600237 315099115233830466600089)
                ·
                  refine ⟨236324336425372849950067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 315099115233830466600089 236324336425372849950067)
                  ·
                    rfl

theorem cell20_517770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 3, 2].length) (baseStart_517770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517770 prefixEnd_517770 := by exact prefixLift 517770
  have htrace : WordTrace (prefixWord ++ tailWord_517770) baseStart_517770 baseEnd_517770 := by
    simpa [prefixWord, tailWord_517770, baseEnd_517770] using wordTrace_append hprefix tailTrace_517770
  have hstable : (prefixWord ++ tailWord_517770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517770).length < 2 ^ (prefixWord ++ tailWord_517770).sum := by decide
  have hdescent : baseEnd_517770 < baseStart_517770 := by decide
  rcases family_descends (prefixWord ++ tailWord_517770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517771 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 7]
def baseStart_517771 : Nat := 118140960795 + 517771 * 2 ^ 59
def prefixEnd_517771 : Nat := 4983230072969 + 3 ^ 40 * 517771 * 2
def baseEnd_517771 : Nat := 236324792852621290916729

theorem tailTrace_517771 : CollatzResearch.WordTrace tailWord_517771 prefixEnd_517771 236324792852621290916729 := by
  unfold tailWord_517771
  simp only [CollatzResearch.WordTrace]
  refine ⟨18884659807211570091777167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12589773204807713394518111 18884659807211570091777167)
  ·
    refine ⟨28326989710817355137665751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18884659807211570091777167 28326989710817355137665751)
    ·
      refine ⟨42490484566226032706498627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28326989710817355137665751 42490484566226032706498627)
      ·
        refine ⟨63735726849339049059747941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42490484566226032706498627 63735726849339049059747941)
        ·
          refine ⟨11950448784251071698702739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63735726849339049059747941 11950448784251071698702739)
          ·
            refine ⟨17925673176376607548054109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11950448784251071698702739 17925673176376607548054109)
            ·
              refine ⟨6722127441141227830520291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17925673176376607548054109 6722127441141227830520291)
              ·
                refine ⟨10083191161711841745780437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6722127441141227830520291 10083191161711841745780437)
                ·
                  refine ⟨236324792852621290916729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10083191161711841745780437 236324792852621290916729)
                  ·
                    rfl

theorem cell20_517771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 7].length) (baseStart_517771 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517771 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517771 prefixEnd_517771 := by exact prefixLift 517771
  have htrace : WordTrace (prefixWord ++ tailWord_517771) baseStart_517771 baseEnd_517771 := by
    simpa [prefixWord, tailWord_517771, baseEnd_517771] using wordTrace_append hprefix tailTrace_517771
  have hstable : (prefixWord ++ tailWord_517771).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517771).length < 2 ^ (prefixWord ++ tailWord_517771).sum := by decide
  have hdescent : baseEnd_517771 < baseStart_517771 := by decide
  rcases family_descends (prefixWord ++ tailWord_517771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517805 : List Nat := [1, 5, 2, 1, 1, 1, 3, 3, 3]
def baseStart_517805 : Nat := 118140960795 + 517805 * 2 ^ 59
def prefixEnd_517805 : Nat := 4983230072969 + 3 ^ 40 * 517805 * 2
def baseEnd_517805 : Nat := 236340311379068283783257

theorem tailTrace_517805 : CollatzResearch.WordTrace tailWord_517805 prefixEnd_517805 236340311379068283783257 := by
  unfold tailWord_517805
  simp only [CollatzResearch.WordTrace]
  refine ⟨18885899889088393898514869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12590599926058929265676579 18885899889088393898514869)
  ·
    refine ⟨1770553114602036927985769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18885899889088393898514869 1770553114602036927985769)
    ·
      refine ⟨1327914835951527695989327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1770553114602036927985769 1327914835951527695989327)
      ·
        refine ⟨1991872253927291543983991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1327914835951527695989327 1991872253927291543983991)
        ·
          refine ⟨2987808380890937315975987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1991872253927291543983991 2987808380890937315975987)
          ·
            refine ⟨4481712571336405973963981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2987808380890937315975987 4481712571336405973963981)
            ·
              refine ⟨1680642214251152240236493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4481712571336405973963981 1680642214251152240236493)
              ·
                refine ⟨630240830344182090088685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1680642214251152240236493 630240830344182090088685)
                ·
                  refine ⟨236340311379068283783257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 630240830344182090088685 236340311379068283783257)
                  ·
                    rfl

theorem cell20_517805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_517805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517805 prefixEnd_517805 := by exact prefixLift 517805
  have htrace : WordTrace (prefixWord ++ tailWord_517805) baseStart_517805 baseEnd_517805 := by
    simpa [prefixWord, tailWord_517805, baseEnd_517805] using wordTrace_append hprefix tailTrace_517805
  have hstable : (prefixWord ++ tailWord_517805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517805).length < 2 ^ (prefixWord ++ tailWord_517805).sum := by decide
  have hdescent : baseEnd_517805 < baseStart_517805 := by decide
  rcases family_descends (prefixWord ++ tailWord_517805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517853 : List Nat := [1, 4, 3, 3, 1, 2, 1, 5]
def baseStart_517853 : Nat := 118140960795 + 517853 * 2 ^ 59
def prefixEnd_517853 : Nat := 4983230072969 + 3 ^ 40 * 517853 * 2
def baseEnd_517853 : Nat := 78787406628997816727687

theorem tailTrace_517853 : CollatzResearch.WordTrace tailWord_517853 prefixEnd_517853 78787406628997816727687 := by
  unfold tailWord_517853
  simp only [CollatzResearch.WordTrace]
  refine ⟨18887650592914498096262213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12591767061942998730841475 18887650592914498096262213)
  ·
    refine ⟨3541434486171468393049165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18887650592914498096262213 3541434486171468393049165)
    ·
      refine ⟨1328037932314300647393437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3541434486171468393049165 1328037932314300647393437)
      ·
        refine ⟨498014224617862742772539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1328037932314300647393437 498014224617862742772539)
        ·
          refine ⟨747021336926794114158809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498014224617862742772539 747021336926794114158809)
          ·
            refine ⟨560266002695095585619107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 747021336926794114158809 560266002695095585619107)
            ·
              refine ⟨840399004042643378428661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560266002695095585619107 840399004042643378428661)
              ·
                refine ⟨78787406628997816727687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 840399004042643378428661 78787406628997816727687)
                ·
                  rfl

theorem cell20_517853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 5].length) (baseStart_517853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517853 prefixEnd_517853 := by exact prefixLift 517853
  have htrace : WordTrace (prefixWord ++ tailWord_517853) baseStart_517853 baseEnd_517853 := by
    simpa [prefixWord, tailWord_517853, baseEnd_517853] using wordTrace_append hprefix tailTrace_517853
  have hstable : (prefixWord ++ tailWord_517853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517853).length < 2 ^ (prefixWord ++ tailWord_517853).sum := by decide
  have hdescent : baseEnd_517853 < baseStart_517853 := by decide
  rcases family_descends (prefixWord ++ tailWord_517853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517871 : List Nat := [1, 1, 2, 1, 5, 1, 3, 2, 4]
def baseStart_517871 : Nat := 118140960795 + 517871 * 2 ^ 59
def prefixEnd_517871 : Nat := 4983230072969 + 3 ^ 40 * 517871 * 2
def baseEnd_517871 : Nat := 236370435577465387582987

theorem tailTrace_517871 : CollatzResearch.WordTrace tailWord_517871 prefixEnd_517871 236370435577465387582987 := by
  unfold tailWord_517871
  simp only [CollatzResearch.WordTrace]
  refine ⟨18888307106849287170417467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12592204737899524780278311 18888307106849287170417467)
  ·
    refine ⟨28332460660273930755626201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18888307106849287170417467 28332460660273930755626201)
    ·
      refine ⟨21249345495205448066719651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28332460660273930755626201 21249345495205448066719651)
      ·
        refine ⟨31874018242808172100079477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21249345495205448066719651 31874018242808172100079477)
        ·
          refine ⟨2988189210263266134382451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31874018242808172100079477 2988189210263266134382451)
          ·
            refine ⟨4482283815394899201573677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2988189210263266134382451 4482283815394899201573677)
            ·
              refine ⟨1680856430773087200590129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4482283815394899201573677 1680856430773087200590129)
              ·
                refine ⟨1260642323079815400442597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1680856430773087200590129 1260642323079815400442597)
                ·
                  refine ⟨236370435577465387582987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1260642323079815400442597 236370435577465387582987)
                  ·
                    rfl

theorem cell20_517871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 4].length) (baseStart_517871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517871 prefixEnd_517871 := by exact prefixLift 517871
  have htrace : WordTrace (prefixWord ++ tailWord_517871) baseStart_517871 baseEnd_517871 := by
    simpa [prefixWord, tailWord_517871, baseEnd_517871] using wordTrace_append hprefix tailTrace_517871
  have hstable : (prefixWord ++ tailWord_517871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517871).length < 2 ^ (prefixWord ++ tailWord_517871).sum := by decide
  have hdescent : baseEnd_517871 < baseStart_517871 := by decide
  rcases family_descends (prefixWord ++ tailWord_517871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517895 : List Nat := [1, 1, 4, 4, 2, 1, 7]
def baseStart_517895 : Nat := 118140960795 + 517895 * 2 ^ 59
def prefixEnd_517895 : Nat := 4983230072969 + 3 ^ 40 * 517895 * 2
def baseEnd_517895 : Nat := 26264598870158663420321

theorem tailTrace_517895 : CollatzResearch.WordTrace tailWord_517895 prefixEnd_517895 26264598870158663420321 := by
  unfold tailWord_517895
  simp only [CollatzResearch.WordTrace]
  refine ⟨18889182458762339269291139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12592788305841559512860759 18889182458762339269291139)
  ·
    refine ⟨28333773688143508903936709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18889182458762339269291139 28333773688143508903936709)
    ·
      refine ⟨5312582566526907919488133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28333773688143508903936709 5312582566526907919488133)
      ·
        refine ⟨996109231223795234904025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5312582566526907919488133 996109231223795234904025)
        ·
          refine ⟨747081923417846426178019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 996109231223795234904025 747081923417846426178019)
          ·
            refine ⟨1120622885126769639267029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747081923417846426178019 1120622885126769639267029)
            ·
              refine ⟨26264598870158663420321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1120622885126769639267029 26264598870158663420321)
              ·
                rfl

theorem cell20_517895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 7].length) (baseStart_517895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517895 prefixEnd_517895 := by exact prefixLift 517895
  have htrace : WordTrace (prefixWord ++ tailWord_517895) baseStart_517895 baseEnd_517895 := by
    simpa [prefixWord, tailWord_517895, baseEnd_517895] using wordTrace_append hprefix tailTrace_517895
  have hstable : (prefixWord ++ tailWord_517895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517895).length < 2 ^ (prefixWord ++ tailWord_517895).sum := by decide
  have hdescent : baseEnd_517895 < baseStart_517895 := by decide
  rcases family_descends (prefixWord ++ tailWord_517895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517909 : List Nat := [1, 3, 2, 1, 2, 3, 1, 3, 4]
def baseStart_517909 : Nat := 118140960795 + 517909 * 2 ^ 59
def prefixEnd_517909 : Nat := 4983230072969 + 3 ^ 40 * 517909 * 2
def baseEnd_517909 : Nat := 236387779812906144316165

theorem tailTrace_517909 : CollatzResearch.WordTrace tailWord_517909 prefixEnd_517909 236387779812906144316165 := by
  unfold tailWord_517909
  simp only [CollatzResearch.WordTrace]
  refine ⟨18889693080711619660300781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12593128720474413106867187 18889693080711619660300781)
  ·
    refine ⟨7083634905266857372612793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18889693080711619660300781 7083634905266857372612793)
    ·
      refine ⟨5312726178950143029459595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7083634905266857372612793 5312726178950143029459595)
      ·
        refine ⟨7969089268425214544189393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5312726178950143029459595 7969089268425214544189393)
        ·
          refine ⟨5976816951318910908142045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7969089268425214544189393 5976816951318910908142045)
          ·
            refine ⟨2241306356744591590553267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5976816951318910908142045 2241306356744591590553267)
            ·
              refine ⟨3361959535116887385829901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2241306356744591590553267 3361959535116887385829901)
              ·
                refine ⟨1260734825668832769686213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3361959535116887385829901 1260734825668832769686213)
                ·
                  refine ⟨236387779812906144316165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1260734825668832769686213 236387779812906144316165)
                  ·
                    rfl

theorem cell20_517909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_517909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517909 prefixEnd_517909 := by exact prefixLift 517909
  have htrace : WordTrace (prefixWord ++ tailWord_517909) baseStart_517909 baseEnd_517909 := by
    simpa [prefixWord, tailWord_517909, baseEnd_517909] using wordTrace_append hprefix tailTrace_517909
  have hstable : (prefixWord ++ tailWord_517909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517909).length < 2 ^ (prefixWord ++ tailWord_517909).sum := by decide
  have hdescent : baseEnd_517909 < baseStart_517909 := by decide
  rcases family_descends (prefixWord ++ tailWord_517909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517916 : List Nat := [2, 2, 3, 1, 1, 2, 2, 7]
def baseStart_517916 : Nat := 118140960795 + 517916 * 2 ^ 59
def prefixEnd_517916 : Nat := 4983230072969 + 3 ^ 40 * 517916 * 2
def baseEnd_517916 : Nat := 78796991601215077027601

theorem tailTrace_517916 : CollatzResearch.WordTrace tailWord_517916 prefixEnd_517916 78796991601215077027601 := by
  unfold tailWord_517916
  simp only [CollatzResearch.WordTrace]
  refine ⟨9444974195843129927902801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12593298927790839903870401 9444974195843129927902801)
  ·
    refine ⟨7083730646882347445927101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9444974195843129927902801 7083730646882347445927101)
    ·
      refine ⟨2656398992580880292222663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7083730646882347445927101 2656398992580880292222663)
      ·
        refine ⟨3984598488871320438333995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2656398992580880292222663 3984598488871320438333995)
        ·
          refine ⟨5976897733306980657500993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3984598488871320438333995 5976897733306980657500993)
          ·
            refine ⟨4482673299980235493125745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5976897733306980657500993 4482673299980235493125745)
            ·
              refine ⟨3362004974985176619844309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4482673299980235493125745 3362004974985176619844309)
              ·
                refine ⟨78796991601215077027601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3362004974985176619844309 78796991601215077027601)
                ·
                  rfl

theorem cell20_517916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 7].length) (baseStart_517916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517916 prefixEnd_517916 := by exact prefixLift 517916
  have htrace : WordTrace (prefixWord ++ tailWord_517916) baseStart_517916 baseEnd_517916 := by
    simpa [prefixWord, tailWord_517916, baseEnd_517916] using wordTrace_append hprefix tailTrace_517916
  have hstable : (prefixWord ++ tailWord_517916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517916).length < 2 ^ (prefixWord ++ tailWord_517916).sum := by decide
  have hdescent : baseEnd_517916 < baseStart_517916 := by decide
  rcases family_descends (prefixWord ++ tailWord_517916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517919 : List Nat := [1, 1, 2, 4, 2, 1, 5, 1, 3]
def baseStart_517919 : Nat := 118140960795 + 517919 * 2 ^ 59
def prefixEnd_517919 : Nat := 4983230072969 + 3 ^ 40 * 517919 * 2
def baseEnd_517919 : Nat := 236392344085390553982791

theorem tailTrace_517919 : CollatzResearch.WordTrace tailWord_517919 prefixEnd_517919 236392344085390553982791 := by
  unfold tailWord_517919
  simp only [CollatzResearch.WordTrace]
  refine ⟨18890057810675391368164811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12593371873783594245443207 18890057810675391368164811)
  ·
    refine ⟨28335086716013087052247217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18890057810675391368164811 28335086716013087052247217)
    ·
      refine ⟨21251315037009815289185413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28335086716013087052247217 21251315037009815289185413)
      ·
        refine ⟨3984621569439340366722265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21251315037009815289185413 3984621569439340366722265)
        ·
          refine ⟨2988466177079505275041699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3984621569439340366722265 2988466177079505275041699)
          ·
            refine ⟨4482699265619257912562549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2988466177079505275041699 4482699265619257912562549)
            ·
              refine ⟨420253056151805429302739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4482699265619257912562549 420253056151805429302739)
              ·
                refine ⟨630379584227708143954109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420253056151805429302739 630379584227708143954109)
                ·
                  refine ⟨236392344085390553982791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 630379584227708143954109 236392344085390553982791)
                  ·
                    rfl

theorem cell20_517919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 3].length) (baseStart_517919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517919 prefixEnd_517919 := by exact prefixLift 517919
  have htrace : WordTrace (prefixWord ++ tailWord_517919) baseStart_517919 baseEnd_517919 := by
    simpa [prefixWord, tailWord_517919, baseEnd_517919] using wordTrace_append hprefix tailTrace_517919
  have hstable : (prefixWord ++ tailWord_517919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517919).length < 2 ^ (prefixWord ++ tailWord_517919).sum := by decide
  have hdescent : baseEnd_517919 < baseStart_517919 := by decide
  rcases family_descends (prefixWord ++ tailWord_517919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517961 : List Nat := [1, 2, 1, 1, 2, 4, 1, 3, 5]
def baseStart_517961 : Nat := 118140960795 + 517961 * 2 ^ 59
def prefixEnd_517961 : Nat := 4983230072969 + 3 ^ 40 * 517961 * 2
def baseEnd_517961 : Nat := 236411514029825074582619

theorem tailTrace_517961 : CollatzResearch.WordTrace tailWord_517961 prefixEnd_517961 236411514029825074582619 := by
  unfold tailWord_517961
  simp only [CollatzResearch.WordTrace]
  refine ⟨18891589676523232541193737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12594393117682155027462491 18891589676523232541193737)
  ·
    refine ⟨14168692257392424405895303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18891589676523232541193737 14168692257392424405895303)
    ·
      refine ⟨21253038386088636608842955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14168692257392424405895303 21253038386088636608842955)
      ·
        refine ⟨31879557579132954913264433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21253038386088636608842955 31879557579132954913264433)
        ·
          refine ⟨23909668184349716184948325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31879557579132954913264433 23909668184349716184948325)
          ·
            refine ⟨4483062784565571784677811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23909668184349716184948325 4483062784565571784677811)
            ·
              refine ⟨6724594176848357677016717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4483062784565571784677811 6724594176848357677016717)
              ·
                refine ⟨2521722816318134128881269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6724594176848357677016717 2521722816318134128881269)
                ·
                  refine ⟨236411514029825074582619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2521722816318134128881269 236411514029825074582619)
                  ·
                    rfl

theorem cell20_517961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_517961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517961 prefixEnd_517961 := by exact prefixLift 517961
  have htrace : WordTrace (prefixWord ++ tailWord_517961) baseStart_517961 baseEnd_517961 := by
    simpa [prefixWord, tailWord_517961, baseEnd_517961] using wordTrace_append hprefix tailTrace_517961
  have hstable : (prefixWord ++ tailWord_517961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517961).length < 2 ^ (prefixWord ++ tailWord_517961).sum := by decide
  have hdescent : baseEnd_517961 < baseStart_517961 := by decide
  rcases family_descends (prefixWord ++ tailWord_517961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517978 : List Nat := [3, 1, 1, 2, 1, 3, 3, 3, 3]
def baseStart_517978 : Nat := 118140960795 + 517978 * 2 ^ 59
def prefixEnd_517978 : Nat := 4983230072969 + 3 ^ 40 * 517978 * 2
def baseEnd_517978 : Nat := 236419273293048571015883

theorem tailTrace_517978 : CollatzResearch.WordTrace tailWord_517978 prefixEnd_517978 236419273293048571015883 := by
  unfold tailWord_517978
  simp only [CollatzResearch.WordTrace]
  refine ⟨4723052429365411111140647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12594806478307762963041725 4723052429365411111140647)
  ·
    refine ⟨7084578644048116666710971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4723052429365411111140647 7084578644048116666710971)
    ·
      refine ⟨10626867966072175000066457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7084578644048116666710971 10626867966072175000066457)
      ·
        refine ⟨7970150974554131250049843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10626867966072175000066457 7970150974554131250049843)
        ·
          refine ⟨11955226461831196875074765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7970150974554131250049843 11955226461831196875074765)
          ·
            refine ⟨4483209923186698828153037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11955226461831196875074765 4483209923186698828153037)
            ·
              refine ⟨1681203721195012060557389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4483209923186698828153037 1681203721195012060557389)
              ·
                refine ⟨630451395448129522709021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1681203721195012060557389 630451395448129522709021)
                ·
                  refine ⟨236419273293048571015883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 630451395448129522709021 236419273293048571015883)
                  ·
                    rfl

theorem cell20_517978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_517978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517978 prefixEnd_517978 := by exact prefixLift 517978
  have htrace : WordTrace (prefixWord ++ tailWord_517978) baseStart_517978 baseEnd_517978 := by
    simpa [prefixWord, tailWord_517978, baseEnd_517978] using wordTrace_append hprefix tailTrace_517978
  have hstable : (prefixWord ++ tailWord_517978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517978).length < 2 ^ (prefixWord ++ tailWord_517978).sum := by decide
  have hdescent : baseEnd_517978 < baseStart_517978 := by decide
  rcases family_descends (prefixWord ++ tailWord_517978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_517992 : List Nat := [2, 1, 4, 2, 1, 1, 1, 8]
def baseStart_517992 : Nat := 118140960795 + 517992 * 2 ^ 59
def prefixEnd_517992 : Nat := 4983230072969 + 3 ^ 40 * 517992 * 2
def baseEnd_517992 : Nat := 78808554424842248183053

theorem tailTrace_517992 : CollatzResearch.WordTrace tailWord_517992 prefixEnd_517992 78808554424842248183053 := by
  unfold tailWord_517992
  simp only [CollatzResearch.WordTrace]
  refine ⟨9446360169705462417786115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12595146892940616557048153 9446360169705462417786115)
  ·
    refine ⟨14169540254558193626679173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9446360169705462417786115 14169540254558193626679173)
    ·
      refine ⟨2656788797729661305002345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14169540254558193626679173 2656788797729661305002345)
      ·
        refine ⟨1992591598297245978751759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2656788797729661305002345 1992591598297245978751759)
        ·
          refine ⟨2988887397445868968127639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1992591598297245978751759 2988887397445868968127639)
          ·
            refine ⟨4483331096168803452191459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2988887397445868968127639 4483331096168803452191459)
            ·
              refine ⟨6724996644253205178287189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4483331096168803452191459 6724996644253205178287189)
              ·
                refine ⟨78808554424842248183053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6724996644253205178287189 78808554424842248183053)
                ·
                  rfl

theorem cell20_517992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 8].length) (baseStart_517992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_517992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_517992 prefixEnd_517992 := by exact prefixLift 517992
  have htrace : WordTrace (prefixWord ++ tailWord_517992) baseStart_517992 baseEnd_517992 := by
    simpa [prefixWord, tailWord_517992, baseEnd_517992] using wordTrace_append hprefix tailTrace_517992
  have hstable : (prefixWord ++ tailWord_517992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_517992).length < 2 ^ (prefixWord ++ tailWord_517992).sum := by decide
  have hdescent : baseEnd_517992 < baseStart_517992 := by decide
  rcases family_descends (prefixWord ++ tailWord_517992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518002 : List Nat := [3, 2, 1, 2, 1, 1, 1, 7, 2]
def baseStart_518002 : Nat := 118140960795 + 518002 * 2 ^ 59
def prefixEnd_518002 : Nat := 4983230072969 + 3 ^ 40 * 518002 * 2
def baseEnd_518002 : Nat := 236430227547011154215785

theorem tailTrace_518002 : CollatzResearch.WordTrace tailWord_518002 prefixEnd_518002 236430227547011154215785 := by
  unfold tailWord_518002
  simp only [CollatzResearch.WordTrace]
  refine ⟨4723271267343674135859065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12595390046249797695624173 4723271267343674135859065)
  ·
    refine ⟨3542453450507755601894299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4723271267343674135859065 3542453450507755601894299)
    ·
      refine ⟨5313680175761633402841449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3542453450507755601894299 5313680175761633402841449)
      ·
        refine ⟨3985260131821225052131087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5313680175761633402841449 3985260131821225052131087)
        ·
          refine ⟨5977890197731837578196631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3985260131821225052131087 5977890197731837578196631)
          ·
            refine ⟨8966835296597756367294947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5977890197731837578196631 8966835296597756367294947)
            ·
              refine ⟨13450252944896634550942421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8966835296597756367294947 13450252944896634550942421)
              ·
                refine ⟨315240303396014872287713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 13450252944896634550942421 315240303396014872287713)
                ·
                  refine ⟨236430227547011154215785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 315240303396014872287713 236430227547011154215785)
                  ·
                    rfl

theorem cell20_518002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_518002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518002 prefixEnd_518002 := by exact prefixLift 518002
  have htrace : WordTrace (prefixWord ++ tailWord_518002) baseStart_518002 baseEnd_518002 := by
    simpa [prefixWord, tailWord_518002, baseEnd_518002] using wordTrace_append hprefix tailTrace_518002
  have hstable : (prefixWord ++ tailWord_518002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518002).length < 2 ^ (prefixWord ++ tailWord_518002).sum := by decide
  have hdescent : baseEnd_518002 < baseStart_518002 := by decide
  rcases family_descends (prefixWord ++ tailWord_518002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518016 : List Nat := [2, 1, 1, 2, 1, 2, 6, 2, 3]
def baseStart_518016 : Nat := 118140960795 + 518016 * 2 ^ 59
def prefixEnd_518016 : Nat := 4983230072969 + 3 ^ 40 * 518016 * 2
def baseEnd_518016 : Nat := 236436617528489327749061

theorem tailTrace_518016 : CollatzResearch.WordTrace tailWord_518016 prefixEnd_518016 236436617528489327749061 := by
  unfold tailWord_518016
  simp only [CollatzResearch.WordTrace]
  refine ⟨9446797845661988467222951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12595730460882651289630601 9446797845661988467222951)
  ·
    refine ⟨14170196768492982700834427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9446797845661988467222951 14170196768492982700834427)
    ·
      refine ⟨21255295152739474051251641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14170196768492982700834427 21255295152739474051251641)
      ·
        refine ⟨15941471364554605538438731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21255295152739474051251641 15941471364554605538438731)
        ·
          refine ⟨23912207046831908307658097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15941471364554605538438731 23912207046831908307658097)
          ·
            refine ⟨17934155285123931230743573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23912207046831908307658097 17934155285123931230743573)
            ·
              refine ⟨840663528990184276441105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17934155285123931230743573 840663528990184276441105)
              ·
                refine ⟨630497646742638207330829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 840663528990184276441105 630497646742638207330829)
                ·
                  refine ⟨236436617528489327749061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 630497646742638207330829 236436617528489327749061)
                  ·
                    rfl

theorem cell20_518016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 3].length) (baseStart_518016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518016 prefixEnd_518016 := by exact prefixLift 518016
  have htrace : WordTrace (prefixWord ++ tailWord_518016) baseStart_518016 baseEnd_518016 := by
    simpa [prefixWord, tailWord_518016, baseEnd_518016] using wordTrace_append hprefix tailTrace_518016
  have hstable : (prefixWord ++ tailWord_518016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518016).length < 2 ^ (prefixWord ++ tailWord_518016).sum := by decide
  have hdescent : baseEnd_518016 < baseStart_518016 := by decide
  rcases family_descends (prefixWord ++ tailWord_518016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518019 : List Nat := [1, 1, 1, 3, 4, 2, 4, 2, 2]
def baseStart_518019 : Nat := 118140960795 + 518019 * 2 ^ 59
def prefixEnd_518019 : Nat := 4983230072969 + 3 ^ 40 * 518019 * 2
def baseEnd_518019 : Nat := 236437986810234650649049

theorem tailTrace_518019 : CollatzResearch.WordTrace tailWord_518019 prefixEnd_518019 236437986810234650649049 := by
  unfold tailWord_518019
  simp only [CollatzResearch.WordTrace]
  refine ⟨18893705110313108446805111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12595803406875405631203407 18893705110313108446805111)
  ·
    refine ⟨28340557665469662670207667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18893705110313108446805111 28340557665469662670207667)
    ·
      refine ⟨42510836498204494005311501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28340557665469662670207667 42510836498204494005311501)
      ·
        refine ⟨15941563686826685251991813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42510836498204494005311501 15941563686826685251991813)
        ·
          refine ⟨2989043191280003484748465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15941563686826685251991813 2989043191280003484748465)
          ·
            refine ⟨2241782393460002613561349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2989043191280003484748465 2241782393460002613561349)
            ·
              refine ⟨420334198773750490042753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2241782393460002613561349 420334198773750490042753)
              ·
                refine ⟨315250649080312867532065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 420334198773750490042753 315250649080312867532065)
                ·
                  refine ⟨236437986810234650649049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 315250649080312867532065 236437986810234650649049)
                  ·
                    rfl

theorem cell20_518019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 2, 2].length) (baseStart_518019 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518019 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518019 prefixEnd_518019 := by exact prefixLift 518019
  have htrace : WordTrace (prefixWord ++ tailWord_518019) baseStart_518019 baseEnd_518019 := by
    simpa [prefixWord, tailWord_518019, baseEnd_518019] using wordTrace_append hprefix tailTrace_518019
  have hstable : (prefixWord ++ tailWord_518019).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518019).length < 2 ^ (prefixWord ++ tailWord_518019).sum := by decide
  have hdescent : baseEnd_518019 < baseStart_518019 := by decide
  rcases family_descends (prefixWord ++ tailWord_518019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518026 : List Nat := [3, 1, 2, 4, 2, 2, 1, 5]
def baseStart_518026 : Nat := 118140960795 + 518026 * 2 ^ 59
def prefixEnd_518026 : Nat := 4983230072969 + 3 ^ 40 * 518026 * 2
def baseEnd_518026 : Nat := 78813727266991245805229

theorem tailTrace_518026 : CollatzResearch.WordTrace tailWord_518026 prefixEnd_518026 78813727266991245805229 := by
  unfold tailWord_518026
  simp only [CollatzResearch.WordTrace]
  refine ⟨4723490105321937160577483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12595973614191832428206621 4723490105321937160577483)
  ·
    refine ⟨7085235157982905740866225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4723490105321937160577483 7085235157982905740866225)
    ·
      refine ⟨5313926368487179305649669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7085235157982905740866225 5313926368487179305649669)
      ·
        refine ⟨996361194091346119809313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5313926368487179305649669 996361194091346119809313)
        ·
          refine ⟨747270895568509589856985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 996361194091346119809313 747270895568509589856985)
          ·
            refine ⟨560453171676382192392739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 747270895568509589856985 560453171676382192392739)
            ·
              refine ⟨840679757514573288589109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560453171676382192392739 840679757514573288589109)
              ·
                refine ⟨78813727266991245805229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 840679757514573288589109 78813727266991245805229)
                ·
                  rfl

theorem cell20_518026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_518026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518026 prefixEnd_518026 := by exact prefixLift 518026
  have htrace : WordTrace (prefixWord ++ tailWord_518026) baseStart_518026 baseEnd_518026 := by
    simpa [prefixWord, tailWord_518026, baseEnd_518026] using wordTrace_append hprefix tailTrace_518026
  have hstable : (prefixWord ++ tailWord_518026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518026).length < 2 ^ (prefixWord ++ tailWord_518026).sum := by decide
  have hdescent : baseEnd_518026 < baseStart_518026 := by decide
  rcases family_descends (prefixWord ++ tailWord_518026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518078 : List Nat := [4, 2, 1, 1, 1, 4, 2, 1, 4]
def baseStart_518078 : Nat := 118140960795 + 518078 * 2 ^ 59
def prefixEnd_518078 : Nat := 4983230072969 + 3 ^ 40 * 518078 * 2
def baseEnd_518078 : Nat := 236464916017892667682141

theorem tailTrace_518078 : CollatzResearch.WordTrace tailWord_518078 prefixEnd_518078 236464916017892667682141 := by
  unfold tailWord_518078
  simp only [CollatzResearch.WordTrace]
  refine ⟨2361982127137420190400361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12597238011399574348801925 2361982127137420190400361)
  ·
    refine ⟨1771486595353065142800271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2361982127137420190400361 1771486595353065142800271)
    ·
      refine ⟨2657229893029597714200407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1771486595353065142800271 2657229893029597714200407)
      ·
        refine ⟨3985844839544396571300611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2657229893029597714200407 3985844839544396571300611)
        ·
          refine ⟨5978767259316594856950917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3985844839544396571300611 5978767259316594856950917)
          ·
            refine ⟨1121018861121861535678297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5978767259316594856950917 1121018861121861535678297)
            ·
              refine ⟨840764145841396151758723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1121018861121861535678297 840764145841396151758723)
              ·
                refine ⟨1261146218762094227638085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 840764145841396151758723 1261146218762094227638085)
                ·
                  refine ⟨236464916017892667682141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1261146218762094227638085 236464916017892667682141)
                  ·
                    rfl

theorem cell20_518078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_518078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518078 prefixEnd_518078 := by exact prefixLift 518078
  have htrace : WordTrace (prefixWord ++ tailWord_518078) baseStart_518078 baseEnd_518078 := by
    simpa [prefixWord, tailWord_518078, baseEnd_518078] using wordTrace_append hprefix tailTrace_518078
  have hstable : (prefixWord ++ tailWord_518078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518078).length < 2 ^ (prefixWord ++ tailWord_518078).sum := by decide
  have hdescent : baseEnd_518078 < baseStart_518078 := by decide
  rcases family_descends (prefixWord ++ tailWord_518078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518102 : List Nat := [5, 2, 1, 1, 3, 1, 1, 6]
def baseStart_518102 : Nat := 118140960795 + 518102 * 2 ^ 59
def prefixEnd_518102 : Nat := 4983230072969 + 3 ^ 40 * 518102 * 2
def baseEnd_518102 : Nat := 78825290090618416960681

theorem tailTrace_518102 : CollatzResearch.WordTrace tailWord_518102 prefixEnd_518102 78825290090618416960681 := by
  unfold tailWord_518102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1181045773063275851379785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12597821579341609081384373 1181045773063275851379785)
  ·
    refine ⟨885784329797456888534839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1181045773063275851379785 885784329797456888534839)
    ·
      refine ⟨1328676494696185332802259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 885784329797456888534839 1328676494696185332802259)
      ·
        refine ⟨1993014742044277999203389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1328676494696185332802259 1993014742044277999203389)
        ·
          refine ⟨747380528266604249701271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1993014742044277999203389 747380528266604249701271)
          ·
            refine ⟨1121070792399906374551907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747380528266604249701271 1121070792399906374551907)
            ·
              refine ⟨1681606188599859561827861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1121070792399906374551907 1681606188599859561827861)
              ·
                refine ⟨78825290090618416960681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1681606188599859561827861 78825290090618416960681)
                ·
                  rfl

theorem cell20_518102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_518102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518102 prefixEnd_518102 := by exact prefixLift 518102
  have htrace : WordTrace (prefixWord ++ tailWord_518102) baseStart_518102 baseEnd_518102 := by
    simpa [prefixWord, tailWord_518102, baseEnd_518102] using wordTrace_append hprefix tailTrace_518102
  have hstable : (prefixWord ++ tailWord_518102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518102).length < 2 ^ (prefixWord ++ tailWord_518102).sum := by decide
  have hdescent : baseEnd_518102 < baseStart_518102 := by decide
  rcases family_descends (prefixWord ++ tailWord_518102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518108 : List Nat := [2, 2, 6, 1, 1, 2, 1, 3, 2]
def baseStart_518108 : Nat := 118140960795 + 518108 * 2 ^ 59
def prefixEnd_518108 : Nat := 4983230072969 + 3 ^ 40 * 518108 * 2
def baseEnd_518108 : Nat := 236478608835345896682019

theorem tailTrace_518108 : CollatzResearch.WordTrace tailWord_518108 prefixEnd_518108 236478608835345896682019 := by
  unfold tailWord_518108
  simp only [CollatzResearch.WordTrace]
  refine ⟨9448475603495338323397489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12597967471327117764529985 9448475603495338323397489)
  ·
    refine ⟨7086356702621503742548117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9448475603495338323397489 7086356702621503742548117)
    ·
      refine ⟨332172970435382987931943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7086356702621503742548117 332172970435382987931943)
      ·
        refine ⟨498259455653074481897915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332172970435382987931943 498259455653074481897915)
        ·
          refine ⟨747389183479611722846873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498259455653074481897915 747389183479611722846873)
          ·
            refine ⟨560541887609708792135155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 747389183479611722846873 560541887609708792135155)
            ·
              refine ⟨840812831414563188202733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560541887609708792135155 840812831414563188202733)
              ·
                refine ⟨315304811780461195576025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 840812831414563188202733 315304811780461195576025)
                ·
                  refine ⟨236478608835345896682019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 315304811780461195576025 236478608835345896682019)
                  ·
                    rfl

theorem cell20_518108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 3, 2].length) (baseStart_518108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518108 prefixEnd_518108 := by exact prefixLift 518108
  have htrace : WordTrace (prefixWord ++ tailWord_518108) baseStart_518108 baseEnd_518108 := by
    simpa [prefixWord, tailWord_518108, baseEnd_518108] using wordTrace_append hprefix tailTrace_518108
  have hstable : (prefixWord ++ tailWord_518108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518108).length < 2 ^ (prefixWord ++ tailWord_518108).sum := by decide
  have hdescent : baseEnd_518108 < baseStart_518108 := by decide
  rcases family_descends (prefixWord ++ tailWord_518108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518113 : List Nat := [1, 2, 3, 1, 2, 1, 3, 2, 5]
def baseStart_518113 : Nat := 118140960795 + 518113 * 2 ^ 59
def prefixEnd_518113 : Nat := 4983230072969 + 3 ^ 40 * 518113 * 2
def baseEnd_518113 : Nat := 236480890971588101515331

theorem tailTrace_518113 : CollatzResearch.WordTrace tailWord_518113 prefixEnd_518113 236480890971588101515331 := by
  unfold tailWord_518113
  simp only [CollatzResearch.WordTrace]
  refine ⟨18897133571972562500726993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12598089047981708333817995 18897133571972562500726993)
  ·
    refine ⟨14172850178979421875545245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18897133571972562500726993 14172850178979421875545245)
    ·
      refine ⟨5314818817117283203329467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14172850178979421875545245 5314818817117283203329467)
      ·
        refine ⟨7972228225675924804994201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5314818817117283203329467 7972228225675924804994201)
        ·
          refine ⟨5979171169256943603745651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7972228225675924804994201 5979171169256943603745651)
          ·
            refine ⟨8968756753885415405618477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5979171169256943603745651 8968756753885415405618477)
            ·
              refine ⟨3363283782707030777106929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8968756753885415405618477 3363283782707030777106929)
              ·
                refine ⟨2522462837030273082830197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3363283782707030777106929 2522462837030273082830197)
                ·
                  refine ⟨236480890971588101515331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2522462837030273082830197 236480890971588101515331)
                  ·
                    rfl

theorem cell20_518113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_518113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518113 prefixEnd_518113 := by exact prefixLift 518113
  have htrace : WordTrace (prefixWord ++ tailWord_518113) baseStart_518113 baseEnd_518113 := by
    simpa [prefixWord, tailWord_518113, baseEnd_518113] using wordTrace_append hprefix tailTrace_518113
  have hstable : (prefixWord ++ tailWord_518113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518113).length < 2 ^ (prefixWord ++ tailWord_518113).sum := by decide
  have hdescent : baseEnd_518113 < baseStart_518113 := by decide
  rcases family_descends (prefixWord ++ tailWord_518113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518137 : List Nat := [1, 2, 1, 3, 1, 4, 3, 1, 4]
def baseStart_518137 : Nat := 118140960795 + 518137 * 2 ^ 59
def prefixEnd_518137 : Nat := 4983230072969 + 3 ^ 40 * 518137 * 2
def baseEnd_518137 : Nat := 236491845225550684715233

theorem tailTrace_518137 : CollatzResearch.WordTrace tailWord_518137 prefixEnd_518137 236491845225550684715233 := by
  unfold tailWord_518137
  simp only [CollatzResearch.WordTrace]
  refine ⟨18898008923885614599600665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12598672615923743066400443 18898008923885614599600665)
  ·
    refine ⟨14173506692914210949700499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18898008923885614599600665 14173506692914210949700499)
    ·
      refine ⟨21260260039371316424550749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14173506692914210949700499 21260260039371316424550749)
      ·
        refine ⟨7972597514764243659206531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21260260039371316424550749 7972597514764243659206531)
        ·
          refine ⟨11958896272146365488809797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7972597514764243659206531 11958896272146365488809797)
          ·
            refine ⟨2242293051027443529151837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11958896272146365488809797 2242293051027443529151837)
            ·
              refine ⟨840859894135291323431939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2242293051027443529151837 840859894135291323431939)
              ·
                refine ⟨1261289841202936985147909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 840859894135291323431939 1261289841202936985147909)
                ·
                  refine ⟨236491845225550684715233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1261289841202936985147909 236491845225550684715233)
                  ·
                    rfl

theorem cell20_518137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 4].length) (baseStart_518137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518137 prefixEnd_518137 := by exact prefixLift 518137
  have htrace : WordTrace (prefixWord ++ tailWord_518137) baseStart_518137 baseEnd_518137 := by
    simpa [prefixWord, tailWord_518137, baseEnd_518137] using wordTrace_append hprefix tailTrace_518137
  have hstable : (prefixWord ++ tailWord_518137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518137).length < 2 ^ (prefixWord ++ tailWord_518137).sum := by decide
  have hdescent : baseEnd_518137 < baseStart_518137 := by decide
  rcases family_descends (prefixWord ++ tailWord_518137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518184 : List Nat := [2, 1, 5, 3, 2, 1, 2, 2, 2]
def baseStart_518184 : Nat := 118140960795 + 518184 * 2 ^ 59
def prefixEnd_518184 : Nat := 4983230072969 + 3 ^ 40 * 518184 * 2
def baseEnd_518184 : Nat := 236513297306227410148375

theorem tailTrace_518184 : CollatzResearch.WordTrace tailWord_518184 prefixEnd_518184 236513297306227410148375 := by
  unfold tailWord_518184
  simp only [CollatzResearch.WordTrace]
  refine ⟨9449861577357670813280803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12599815436476894417707737 9449861577357670813280803)
  ·
    refine ⟨14174792366036506219921205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9449861577357670813280803 14174792366036506219921205)
    ·
      refine ⟨1328886784315922458117613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14174792366036506219921205 1328886784315922458117613)
      ·
        refine ⟨498332544118470921794105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1328886784315922458117613 498332544118470921794105)
        ·
          refine ⟨373749408088853191345579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 498332544118470921794105 373749408088853191345579)
          ·
            refine ⟨560624112133279787018369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373749408088853191345579 560624112133279787018369)
            ·
              refine ⟨420468084099959840263777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 560624112133279787018369 420468084099959840263777)
              ·
                refine ⟨315351063074969880197833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 420468084099959840263777 315351063074969880197833)
                ·
                  refine ⟨236513297306227410148375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 315351063074969880197833 236513297306227410148375)
                  ·
                    rfl

theorem cell20_518184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 2, 2].length) (baseStart_518184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518184 prefixEnd_518184 := by exact prefixLift 518184
  have htrace : WordTrace (prefixWord ++ tailWord_518184) baseStart_518184 baseEnd_518184 := by
    simpa [prefixWord, tailWord_518184, baseEnd_518184] using wordTrace_append hprefix tailTrace_518184
  have hstable : (prefixWord ++ tailWord_518184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518184).length < 2 ^ (prefixWord ++ tailWord_518184).sum := by decide
  have hdescent : baseEnd_518184 < baseStart_518184 := by decide
  rcases family_descends (prefixWord ++ tailWord_518184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518192 : List Nat := [2, 1, 1, 1, 2, 6, 1, 4, 2]
def baseStart_518192 : Nat := 118140960795 + 518192 * 2 ^ 59
def prefixEnd_518192 : Nat := 4983230072969 + 3 ^ 40 * 518192 * 2
def baseEnd_518192 : Nat := 236516948724214937881675

theorem tailTrace_518192 : CollatzResearch.WordTrace tailWord_518192 prefixEnd_518192 236516948724214937881675 := by
  unfold tailWord_518192
  simp only [CollatzResearch.WordTrace]
  refine ⟨9450007469343179496426415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12600009959124239328568553 9450007469343179496426415)
  ·
    refine ⟨14175011204014769244639623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9450007469343179496426415 14175011204014769244639623)
    ·
      refine ⟨21262516806022153866959435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14175011204014769244639623 21262516806022153866959435)
      ·
        refine ⟨31893775209033230800439153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21262516806022153866959435 31893775209033230800439153)
        ·
          refine ⟨23920331406774923100329365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31893775209033230800439153 23920331406774923100329365)
          ·
            refine ⟨1121265534692574520327939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23920331406774923100329365 1121265534692574520327939)
            ·
              refine ⟨1681898302038861780491909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1121265534692574520327939 1681898302038861780491909)
              ·
                refine ⟨315355931632286583842233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1681898302038861780491909 315355931632286583842233)
                ·
                  refine ⟨236516948724214937881675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 315355931632286583842233 236516948724214937881675)
                  ·
                    rfl

theorem cell20_518192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 4, 2].length) (baseStart_518192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518192 prefixEnd_518192 := by exact prefixLift 518192
  have htrace : WordTrace (prefixWord ++ tailWord_518192) baseStart_518192 baseEnd_518192 := by
    simpa [prefixWord, tailWord_518192, baseEnd_518192] using wordTrace_append hprefix tailTrace_518192
  have hstable : (prefixWord ++ tailWord_518192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518192).length < 2 ^ (prefixWord ++ tailWord_518192).sum := by decide
  have hdescent : baseEnd_518192 < baseStart_518192 := by decide
  rcases family_descends (prefixWord ++ tailWord_518192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518234 : List Nat := [3, 1, 1, 2, 1, 1, 3, 2, 6]
def baseStart_518234 : Nat := 118140960795 + 518234 * 2 ^ 59
def prefixEnd_518234 : Nat := 4983230072969 + 3 ^ 40 * 518234 * 2
def baseEnd_518234 : Nat := 236536118668649458481503

theorem tailTrace_518234 : CollatzResearch.WordTrace tailWord_518234 prefixEnd_518234 236536118668649458481503 := by
  unfold tailWord_518234
  simp only [CollatzResearch.WordTrace]
  refine ⟨4725386701133550041470439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12601031203022800110587837 4725386701133550041470439)
  ·
    refine ⟨7088080051700325062205659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4725386701133550041470439 7088080051700325062205659)
    ·
      refine ⟨10632120077550487593308489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7088080051700325062205659 10632120077550487593308489)
      ·
        refine ⟨7974090058162865694981367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10632120077550487593308489 7974090058162865694981367)
        ·
          refine ⟨11961135087244298542472051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7974090058162865694981367 11961135087244298542472051)
          ·
            refine ⟨17941702630866447813708077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11961135087244298542472051 17941702630866447813708077)
            ·
              refine ⟨6728138486574917930140529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17941702630866447813708077 6728138486574917930140529)
              ·
                refine ⟨5046103864931188447605397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6728138486574917930140529 5046103864931188447605397)
                ·
                  refine ⟨236536118668649458481503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5046103864931188447605397 236536118668649458481503)
                  ·
                    rfl

theorem cell20_518234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_518234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518234 prefixEnd_518234 := by exact prefixLift 518234
  have htrace : WordTrace (prefixWord ++ tailWord_518234) baseStart_518234 baseEnd_518234 := by
    simpa [prefixWord, tailWord_518234, baseEnd_518234] using wordTrace_append hprefix tailTrace_518234
  have hstable : (prefixWord ++ tailWord_518234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518234).length < 2 ^ (prefixWord ++ tailWord_518234).sum := by decide
  have hdescent : baseEnd_518234 < baseStart_518234 := by decide
  rcases family_descends (prefixWord ++ tailWord_518234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518237 : List Nat := [1, 4, 4, 1, 1, 2, 7]
def baseStart_518237 : Nat := 118140960795 + 518237 * 2 ^ 59
def prefixEnd_518237 : Nat := 4983230072969 + 3 ^ 40 * 518237 * 2
def baseEnd_518237 : Nat := 26281943105599420153499

theorem tailTrace_518237 : CollatzResearch.WordTrace tailWord_518237 prefixEnd_518237 26281943105599420153499 := by
  unfold tailWord_518237
  simp only [CollatzResearch.WordTrace]
  refine ⟨18901656223523331678240965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12601104149015554452160643 18901656223523331678240965)
  ·
    refine ⟨3544060541910624689670181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18901656223523331678240965 3544060541910624689670181)
    ·
      refine ⟨664511351608242129313159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3544060541910624689670181 664511351608242129313159)
      ·
        refine ⟨996767027412363193969739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664511351608242129313159 996767027412363193969739)
        ·
          refine ⟨1495150541118544790954609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 996767027412363193969739 1495150541118544790954609)
          ·
            refine ⟨1121362905838908593215957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1495150541118544790954609 1121362905838908593215957)
            ·
              refine ⟨26281943105599420153499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1121362905838908593215957 26281943105599420153499)
              ·
                rfl

theorem cell20_518237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 7].length) (baseStart_518237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518237 prefixEnd_518237 := by exact prefixLift 518237
  have htrace : WordTrace (prefixWord ++ tailWord_518237) baseStart_518237 baseEnd_518237 := by
    simpa [prefixWord, tailWord_518237, baseEnd_518237] using wordTrace_append hprefix tailTrace_518237
  have hstable : (prefixWord ++ tailWord_518237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518237).length < 2 ^ (prefixWord ++ tailWord_518237).sum := by decide
  have hdescent : baseEnd_518237 < baseStart_518237 := by decide
  rcases family_descends (prefixWord ++ tailWord_518237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518244 : List Nat := [2, 3, 1, 1, 2, 1, 5, 2, 3]
def baseStart_518244 : Nat := 118140960795 + 518244 * 2 ^ 59
def prefixEnd_518244 : Nat := 4983230072969 + 3 ^ 40 * 518244 * 2
def baseEnd_518244 : Nat := 236540682941133868148129

theorem tailTrace_518244 : CollatzResearch.WordTrace tailWord_518244 prefixEnd_518244 236540682941133868148129 := by
  unfold tailWord_518244
  simp only [CollatzResearch.WordTrace]
  refine ⟨9450955767248985936872893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12601274356331981249163857 9450955767248985936872893)
  ·
    refine ⟨3544108412718369726327335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9450955767248985936872893 3544108412718369726327335)
    ·
      refine ⟨5316162619077554589491003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3544108412718369726327335 5316162619077554589491003)
      ·
        refine ⟨7974243928616331884236505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5316162619077554589491003 7974243928616331884236505)
        ·
          refine ⟨5980682946462248913177379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7974243928616331884236505 5980682946462248913177379)
          ·
            refine ⟨8971024419693373369766069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5980682946462248913177379 8971024419693373369766069)
            ·
              refine ⟨841033539346253753415569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8971024419693373369766069 841033539346253753415569)
              ·
                refine ⟨630775154509690315061677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 841033539346253753415569 630775154509690315061677)
                ·
                  refine ⟨236540682941133868148129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 630775154509690315061677 236540682941133868148129)
                  ·
                    rfl

theorem cell20_518244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_518244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518244 prefixEnd_518244 := by exact prefixLift 518244
  have htrace : WordTrace (prefixWord ++ tailWord_518244) baseStart_518244 baseEnd_518244 := by
    simpa [prefixWord, tailWord_518244, baseEnd_518244] using wordTrace_append hprefix tailTrace_518244
  have hstable : (prefixWord ++ tailWord_518244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518244).length < 2 ^ (prefixWord ++ tailWord_518244).sum := by decide
  have hdescent : baseEnd_518244 < baseStart_518244 := by decide
  rcases family_descends (prefixWord ++ tailWord_518244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518275 : List Nat := [1, 1, 1, 3, 3, 5, 2, 4]
def baseStart_518275 : Nat := 118140960795 + 518275 * 2 ^ 59
def prefixEnd_518275 : Nat := 4983230072969 + 3 ^ 40 * 518275 * 2
def baseEnd_518275 : Nat := 78851610728611846038223

theorem tailTrace_518275 : CollatzResearch.WordTrace tailWord_518275 prefixEnd_518275 78851610728611846038223 := by
  unfold tailWord_518275
  simp only [CollatzResearch.WordTrace]
  refine ⟨18903042197385664168124279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12602028131590442778749519 18903042197385664168124279)
  ·
    refine ⟨28354563296078496252186419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18903042197385664168124279 28354563296078496252186419)
    ·
      refine ⟨42531844944117744378279629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28354563296078496252186419 42531844944117744378279629)
      ·
        refine ⟨15949441854044154141854861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42531844944117744378279629 15949441854044154141854861)
        ·
          refine ⟨5981040695266557803195573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15949441854044154141854861 5981040695266557803195573)
          ·
            refine ⟨560722565181239794049585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5981040695266557803195573 560722565181239794049585)
            ·
              refine ⟨420541923885929845537189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 560722565181239794049585 420541923885929845537189)
              ·
                refine ⟨78851610728611846038223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 420541923885929845537189 78851610728611846038223)
                ·
                  rfl

theorem cell20_518275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 4].length) (baseStart_518275 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518275 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518275 prefixEnd_518275 := by exact prefixLift 518275
  have htrace : WordTrace (prefixWord ++ tailWord_518275) baseStart_518275 baseEnd_518275 := by
    simpa [prefixWord, tailWord_518275, baseEnd_518275] using wordTrace_append hprefix tailTrace_518275
  have hstable : (prefixWord ++ tailWord_518275).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518275).length < 2 ^ (prefixWord ++ tailWord_518275).sum := by decide
  have hdescent : baseEnd_518275 < baseStart_518275 := by decide
  rcases family_descends (prefixWord ++ tailWord_518275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518292 : List Nat := [2, 4, 2, 3, 1, 2, 6]
def baseStart_518292 : Nat := 118140960795 + 518292 * 2 ^ 59
def prefixEnd_518292 : Nat := 4983230072969 + 3 ^ 40 * 518292 * 2
def baseEnd_518292 : Nat := 26284732383228781616437

theorem tailTrace_518292 : CollatzResearch.WordTrace tailWord_518292 prefixEnd_518292 26284732383228781616437 := by
  unfold tailWord_518292
  simp only [CollatzResearch.WordTrace]
  refine ⟨9451831119162038035746565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12602441492216050714328753 9451831119162038035746565)
  ·
    refine ⟨1772218334842882131702481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9451831119162038035746565 1772218334842882131702481)
    ·
      refine ⟨1329163751132161598776861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1772218334842882131702481 1329163751132161598776861)
      ·
        refine ⟨498436406674560599541323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1329163751132161598776861 498436406674560599541323)
        ·
          refine ⟨747654610011840899311985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498436406674560599541323 747654610011840899311985)
          ·
            refine ⟨560740957508880674483989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 747654610011840899311985 560740957508880674483989)
            ·
              refine ⟨26284732383228781616437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 560740957508880674483989 26284732383228781616437)
              ·
                rfl

theorem cell20_518292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 6].length) (baseStart_518292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518292 prefixEnd_518292 := by exact prefixLift 518292
  have htrace : WordTrace (prefixWord ++ tailWord_518292) baseStart_518292 baseEnd_518292 := by
    simpa [prefixWord, tailWord_518292, baseEnd_518292] using wordTrace_append hprefix tailTrace_518292
  have hstable : (prefixWord ++ tailWord_518292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518292).length < 2 ^ (prefixWord ++ tailWord_518292).sum := by decide
  have hdescent : baseEnd_518292 < baseStart_518292 := by decide
  rcases family_descends (prefixWord ++ tailWord_518292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518302 : List Nat := [4, 3, 1, 1, 4, 1, 1, 1, 4]
def baseStart_518302 : Nat := 118140960795 + 518302 * 2 ^ 59
def prefixEnd_518302 : Nat := 4983230072969 + 3 ^ 40 * 518302 * 2
def baseEnd_518302 : Nat := 236567155721543444214559

theorem tailTrace_518302 : CollatzResearch.WordTrace tailWord_518302 prefixEnd_518302 236567155721543444214559 := by
  unfold tailWord_518302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2363003371035980972419645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12602684645525231852904773 2363003371035980972419645)
  ·
    refine ⟨886126264138492864657367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2363003371035980972419645 886126264138492864657367)
    ·
      refine ⟨1329189396207739296986051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 886126264138492864657367 1329189396207739296986051)
      ·
        refine ⟨1993784094311608945479077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1329189396207739296986051 1993784094311608945479077)
        ·
          refine ⟨373834517683426677277327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1993784094311608945479077 373834517683426677277327)
          ·
            refine ⟨560751776525140015915991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373834517683426677277327 560751776525140015915991)
            ·
              refine ⟨841127664787710023873987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560751776525140015915991 841127664787710023873987)
              ·
                refine ⟨1261691497181565035810981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 841127664787710023873987 1261691497181565035810981)
                ·
                  refine ⟨236567155721543444214559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1261691497181565035810981 236567155721543444214559)
                  ·
                    rfl

theorem cell20_518302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_518302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518302 prefixEnd_518302 := by exact prefixLift 518302
  have htrace : WordTrace (prefixWord ++ tailWord_518302) baseStart_518302 baseEnd_518302 := by
    simpa [prefixWord, tailWord_518302, baseEnd_518302] using wordTrace_append hprefix tailTrace_518302
  have hstable : (prefixWord ++ tailWord_518302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518302).length < 2 ^ (prefixWord ++ tailWord_518302).sum := by decide
  have hdescent : baseEnd_518302 < baseStart_518302 := by decide
  rcases family_descends (prefixWord ++ tailWord_518302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518306 : List Nat := [3, 3, 1, 3, 1, 1, 3, 1, 4]
def baseStart_518306 : Nat := 118140960795 + 518306 * 2 ^ 59
def prefixEnd_518306 : Nat := 4983230072969 + 3 ^ 40 * 518306 * 2
def baseEnd_518306 : Nat := 236568981430537208081209

theorem tailTrace_518306 : CollatzResearch.WordTrace tailWord_518306 prefixEnd_518306 236568981430537208081209 := by
  unfold tailWord_518306
  simp only [CollatzResearch.WordTrace]
  refine ⟨4726043215068339115625693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12602781906848904308335181 4726043215068339115625693)
  ·
    refine ⟨1772266205650627168359635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4726043215068339115625693 1772266205650627168359635)
    ·
      refine ⟨2658399308475940752539453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1772266205650627168359635 2658399308475940752539453)
      ·
        refine ⟨996899740678477782202295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2658399308475940752539453 996899740678477782202295)
        ·
          refine ⟨1495349611017716673303443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 996899740678477782202295 1495349611017716673303443)
          ·
            refine ⟨2243024416526575009955165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1495349611017716673303443 2243024416526575009955165)
            ·
              refine ⟨841134156197465628733187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2243024416526575009955165 841134156197465628733187)
              ·
                refine ⟨1261701234296198443099781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 841134156197465628733187 1261701234296198443099781)
                ·
                  refine ⟨236568981430537208081209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1261701234296198443099781 236568981430537208081209)
                  ·
                    rfl

theorem cell20_518306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_518306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518306 prefixEnd_518306 := by exact prefixLift 518306
  have htrace : WordTrace (prefixWord ++ tailWord_518306) baseStart_518306 baseEnd_518306 := by
    simpa [prefixWord, tailWord_518306, baseEnd_518306] using wordTrace_append hprefix tailTrace_518306
  have hstable : (prefixWord ++ tailWord_518306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518306).length < 2 ^ (prefixWord ++ tailWord_518306).sum := by decide
  have hdescent : baseEnd_518306 < baseStart_518306 := by decide
  rcases family_descends (prefixWord ++ tailWord_518306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518357 : List Nat := [1, 3, 2, 4, 3, 1, 2, 2, 2]
def baseStart_518357 : Nat := 118140960795 + 518357 * 2 ^ 59
def prefixEnd_518357 : Nat := 4983230072969 + 3 ^ 40 * 518357 * 2
def baseEnd_518357 : Nat := 236592259220207697381001

theorem tailTrace_518357 : CollatzResearch.WordTrace tailWord_518357 prefixEnd_518357 236592259220207697381001 := by
  unfold tailWord_518357
  simp only [CollatzResearch.WordTrace]
  refine ⟨18906032983088592172609325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12604021988725728115072883 18906032983088592172609325)
  ·
    refine ⟨7089762368658222064728497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18906032983088592172609325 7089762368658222064728497)
    ·
      refine ⟨5317321776493666548546373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7089762368658222064728497 5317321776493666548546373)
      ·
        refine ⟨996997833092562477852445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5317321776493666548546373 996997833092562477852445)
        ·
          refine ⟨373874187409710929194667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 996997833092562477852445 373874187409710929194667)
          ·
            refine ⟨560811281114566393792001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373874187409710929194667 560811281114566393792001)
            ·
              refine ⟨420608460835924795344001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 560811281114566393792001 420608460835924795344001)
              ·
                refine ⟨315456345626943596508001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 420608460835924795344001 315456345626943596508001)
                ·
                  refine ⟨236592259220207697381001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 315456345626943596508001 236592259220207697381001)
                  ·
                    rfl

theorem cell20_518357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 2, 2].length) (baseStart_518357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518357 prefixEnd_518357 := by exact prefixLift 518357
  have htrace : WordTrace (prefixWord ++ tailWord_518357) baseStart_518357 baseEnd_518357 := by
    simpa [prefixWord, tailWord_518357, baseEnd_518357] using wordTrace_append hprefix tailTrace_518357
  have hstable : (prefixWord ++ tailWord_518357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518357).length < 2 ^ (prefixWord ++ tailWord_518357).sum := by decide
  have hdescent : baseEnd_518357 < baseStart_518357 := by decide
  rcases family_descends (prefixWord ++ tailWord_518357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518379 : List Nat := [1, 1, 1, 1, 2, 5, 1, 5, 3]
def baseStart_518379 : Nat := 118140960795 + 518379 * 2 ^ 59
def prefixEnd_518379 : Nat := 4983230072969 + 3 ^ 40 * 518379 * 2
def baseEnd_518379 : Nat := 236602300619673398647577

theorem tailTrace_518379 : CollatzResearch.WordTrace tailWord_518379 prefixEnd_518379 236602300619673398647577 := by
  unfold tailWord_518379
  simp only [CollatzResearch.WordTrace]
  refine ⟨18906835389008889929910191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12604556926005926619940127 18906835389008889929910191)
  ·
    refine ⟨28360253083513334894865287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18906835389008889929910191 28360253083513334894865287)
    ·
      refine ⟨42540379625270002342297931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28360253083513334894865287 42540379625270002342297931)
      ·
        refine ⟨63810569437905003513446897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42540379625270002342297931 63810569437905003513446897)
        ·
          refine ⟨47857927078428752635085173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63810569437905003513446897 47857927078428752635085173)
          ·
            refine ⟨4486680663602695559539235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47857927078428752635085173 4486680663602695559539235)
            ·
              refine ⟨6730020995404043339308853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4486680663602695559539235 6730020995404043339308853)
              ·
                refine ⟨630939468319129063060205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6730020995404043339308853 630939468319129063060205)
                ·
                  refine ⟨236602300619673398647577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 630939468319129063060205 236602300619673398647577)
                  ·
                    rfl

theorem cell20_518379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 3].length) (baseStart_518379 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518379 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518379 prefixEnd_518379 := by exact prefixLift 518379
  have htrace : WordTrace (prefixWord ++ tailWord_518379) baseStart_518379 baseEnd_518379 := by
    simpa [prefixWord, tailWord_518379, baseEnd_518379] using wordTrace_append hprefix tailTrace_518379
  have hstable : (prefixWord ++ tailWord_518379).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518379).length < 2 ^ (prefixWord ++ tailWord_518379).sum := by decide
  have hdescent : baseEnd_518379 < baseStart_518379 := by decide
  rcases family_descends (prefixWord ++ tailWord_518379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518417 : List Nat := [1, 2, 2, 1, 1, 6, 1, 1, 5]
def baseStart_518417 : Nat := 118140960795 + 518417 * 2 ^ 59
def prefixEnd_518417 : Nat := 4983230072969 + 3 ^ 40 * 518417 * 2
def baseEnd_518417 : Nat := 236619644855114155380755

theorem tailTrace_518417 : CollatzResearch.WordTrace tailWord_518417 prefixEnd_518417 236619644855114155380755 := by
  unfold tailWord_518417
  simp only [CollatzResearch.WordTrace]
  refine ⟨18908221362871222419793505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12605480908580814946529003 18908221362871222419793505)
  ·
    refine ⟨14181166022153416814845129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18908221362871222419793505 14181166022153416814845129)
    ·
      refine ⟨10635874516615062611133847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14181166022153416814845129 10635874516615062611133847)
      ·
        refine ⟨15953811774922593916700771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10635874516615062611133847 15953811774922593916700771)
        ·
          refine ⟨23930717662383890875051157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15953811774922593916700771 23930717662383890875051157)
          ·
            refine ⟨1121752390424244884768023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23930717662383890875051157 1121752390424244884768023)
            ·
              refine ⟨1682628585636367327152035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1121752390424244884768023 1682628585636367327152035)
              ·
                refine ⟨2523942878454550990728053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1682628585636367327152035 2523942878454550990728053)
                ·
                  refine ⟨236619644855114155380755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2523942878454550990728053 236619644855114155380755)
                  ·
                    rfl

theorem cell20_518417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 5].length) (baseStart_518417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518417 prefixEnd_518417 := by exact prefixLift 518417
  have htrace : WordTrace (prefixWord ++ tailWord_518417) baseStart_518417 baseEnd_518417 := by
    simpa [prefixWord, tailWord_518417, baseEnd_518417] using wordTrace_append hprefix tailTrace_518417
  have hstable : (prefixWord ++ tailWord_518417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518417).length < 2 ^ (prefixWord ++ tailWord_518417).sum := by decide
  have hdescent : baseEnd_518417 < baseStart_518417 := by decide
  rcases family_descends (prefixWord ++ tailWord_518417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518458 : List Nat := [3, 1, 1, 1, 4, 2, 3, 3, 2]
def baseStart_518458 : Nat := 118140960795 + 518458 * 2 ^ 59
def prefixEnd_518458 : Nat := 4983230072969 + 3 ^ 40 * 518458 * 2
def baseEnd_518458 : Nat := 236638358372300235013921

theorem tailTrace_518458 : CollatzResearch.WordTrace tailWord_518458 prefixEnd_518458 236638358372300235013921 := by
  unfold tailWord_518458
  simp only [CollatzResearch.WordTrace]
  refine ⟨4727429188930671605509007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12606477837148457614690685 4727429188930671605509007)
  ·
    refine ⟨7091143783396007408263511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4727429188930671605509007 7091143783396007408263511)
    ·
      refine ⟨10636715675094011112395267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7091143783396007408263511 10636715675094011112395267)
      ·
        refine ⟨15955073512641016668592901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10636715675094011112395267 15955073512641016668592901)
        ·
          refine ⟨2991576283620190625361169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15955073512641016668592901 2991576283620190625361169)
          ·
            refine ⟨2243682212715142969020877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2991576283620190625361169 2243682212715142969020877)
            ·
              refine ⟨841380829768178613382829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2243682212715142969020877 841380829768178613382829)
              ·
                refine ⟨315517811163066980018561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 841380829768178613382829 315517811163066980018561)
                ·
                  refine ⟨236638358372300235013921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 315517811163066980018561 236638358372300235013921)
                  ·
                    rfl

theorem cell20_518458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 3, 2].length) (baseStart_518458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518458 prefixEnd_518458 := by exact prefixLift 518458
  have htrace : WordTrace (prefixWord ++ tailWord_518458) baseStart_518458 baseEnd_518458 := by
    simpa [prefixWord, tailWord_518458, baseEnd_518458] using wordTrace_append hprefix tailTrace_518458
  have hstable : (prefixWord ++ tailWord_518458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518458).length < 2 ^ (prefixWord ++ tailWord_518458).sum := by decide
  have hdescent : baseEnd_518458 < baseStart_518458 := by decide
  rcases family_descends (prefixWord ++ tailWord_518458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518465 : List Nat := [1, 2, 5, 2, 2, 2, 6]
def baseStart_518465 : Nat := 118140960795 + 518465 * 2 ^ 59
def prefixEnd_518465 : Nat := 4983230072969 + 3 ^ 40 * 518465 * 2
def baseEnd_518465 : Nat := 26293505929226591308951

theorem tailTrace_518465 : CollatzResearch.WordTrace tailWord_518465 prefixEnd_518465 26293505929226591308951 := by
  unfold tailWord_518465
  simp only [CollatzResearch.WordTrace]
  refine ⟨18909972066697326617540849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12606648044464884411693899 18909972066697326617540849)
  ·
    refine ⟨14182479050022994963155637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18909972066697326617540849 14182479050022994963155637)
    ·
      refine ⟨1329607410939655777795841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14182479050022994963155637 1329607410939655777795841)
      ·
        refine ⟨997205558204741833346881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1329607410939655777795841 997205558204741833346881)
        ·
          refine ⟨747904168653556375010161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 997205558204741833346881 747904168653556375010161)
          ·
            refine ⟨560928126490167281257621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 747904168653556375010161 560928126490167281257621)
            ·
              refine ⟨26293505929226591308951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 560928126490167281257621 26293505929226591308951)
              ·
                rfl

theorem cell20_518465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 6].length) (baseStart_518465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518465 prefixEnd_518465 := by exact prefixLift 518465
  have htrace : WordTrace (prefixWord ++ tailWord_518465) baseStart_518465 baseEnd_518465 := by
    simpa [prefixWord, tailWord_518465, baseEnd_518465] using wordTrace_append hprefix tailTrace_518465
  have hstable : (prefixWord ++ tailWord_518465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518465).length < 2 ^ (prefixWord ++ tailWord_518465).sum := by decide
  have hdescent : baseEnd_518465 < baseStart_518465 := by decide
  rcases family_descends (prefixWord ++ tailWord_518465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518500 : List Nat := [2, 3, 1, 1, 3, 1, 2, 1, 6]
def baseStart_518500 : Nat := 118140960795 + 518500 * 2 ^ 59
def prefixEnd_518500 : Nat := 4983230072969 + 3 ^ 40 * 518500 * 2
def baseEnd_518500 : Nat := 236657528316734755613749

theorem tailTrace_518500 : CollatzResearch.WordTrace tailWord_518500 prefixEnd_518500 236657528316734755613749 := by
  unfold tailWord_518500
  simp only [CollatzResearch.WordTrace]
  refine ⟨9455624310785263797532477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12607499081047018396709969 9455624310785263797532477)
  ·
    refine ⟨3545859116544473924074679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9455624310785263797532477 3545859116544473924074679)
    ·
      refine ⟨5318788674816710886112019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3545859116544473924074679 5318788674816710886112019)
      ·
        refine ⟨7978183012225066329168029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5318788674816710886112019 7978183012225066329168029)
        ·
          refine ⟨2991818629584399873438011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7978183012225066329168029 2991818629584399873438011)
          ·
            refine ⟨4487727944376599810157017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2991818629584399873438011 4487727944376599810157017)
            ·
              refine ⟨3365795958282449857617763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4487727944376599810157017 3365795958282449857617763)
              ·
                refine ⟨5048693937423674786426645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3365795958282449857617763 5048693937423674786426645)
                ·
                  refine ⟨236657528316734755613749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5048693937423674786426645 236657528316734755613749)
                  ·
                    rfl

theorem cell20_518500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_518500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518500 prefixEnd_518500 := by exact prefixLift 518500
  have htrace : WordTrace (prefixWord ++ tailWord_518500) baseStart_518500 baseEnd_518500 := by
    simpa [prefixWord, tailWord_518500, baseEnd_518500] using wordTrace_append hprefix tailTrace_518500
  have hstable : (prefixWord ++ tailWord_518500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518500).length < 2 ^ (prefixWord ++ tailWord_518500).sum := by decide
  have hdescent : baseEnd_518500 < baseStart_518500 := by decide
  rcases family_descends (prefixWord ++ tailWord_518500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518530 : List Nat := [3, 4, 2, 1, 2, 1, 1, 4, 2]
def baseStart_518530 : Nat := 118140960795 + 518530 * 2 ^ 59
def prefixEnd_518530 : Nat := 4983230072969 + 3 ^ 40 * 518530 * 2
def baseEnd_518530 : Nat := 236671221134187984613627

theorem tailTrace_518530 : CollatzResearch.WordTrace tailWord_518530 prefixEnd_518530 236671221134187984613627 := by
  unfold tailWord_518530
  simp only [CollatzResearch.WordTrace]
  refine ⟨4728085702865460679664261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12608228540974561812438029 4728085702865460679664261)
  ·
    refine ⟨886516069287273877437049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4728085702865460679664261 886516069287273877437049)
    ·
      refine ⟨664887051965455408077787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 886516069287273877437049 664887051965455408077787)
      ·
        refine ⟨997330577948183112116681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664887051965455408077787 997330577948183112116681)
        ·
          refine ⟨747997933461137334087511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 997330577948183112116681 747997933461137334087511)
          ·
            refine ⟨1121996900191706001131267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747997933461137334087511 1121996900191706001131267)
            ·
              refine ⟨1682995350287559001696901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1121996900191706001131267 1682995350287559001696901)
              ·
                refine ⟨315561628178917312818169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1682995350287559001696901 315561628178917312818169)
                ·
                  refine ⟨236671221134187984613627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 315561628178917312818169 236671221134187984613627)
                  ·
                    rfl

theorem cell20_518530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_518530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518530 prefixEnd_518530 := by exact prefixLift 518530
  have htrace : WordTrace (prefixWord ++ tailWord_518530) baseStart_518530 baseEnd_518530 := by
    simpa [prefixWord, tailWord_518530, baseEnd_518530] using wordTrace_append hprefix tailTrace_518530
  have hstable : (prefixWord ++ tailWord_518530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518530).length < 2 ^ (prefixWord ++ tailWord_518530).sum := by decide
  have hdescent : baseEnd_518530 < baseStart_518530 := by decide
  rcases family_descends (prefixWord ++ tailWord_518530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518558 : List Nat := [4, 3, 1, 2, 1, 2, 3, 4]
def baseStart_518558 : Nat := 118140960795 + 518558 * 2 ^ 59
def prefixEnd_518558 : Nat := 4983230072969 + 3 ^ 40 * 518558 * 2
def baseEnd_518558 : Nat := 78894667032381443893393

theorem tailTrace_518558 : CollatzResearch.WordTrace tailWord_518558 prefixEnd_518558 78894667032381443893393 := by
  unfold tailWord_518558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2364170506920050437584541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12608909370240269000450885 2364170506920050437584541)
  ·
    refine ⟨886563940095018914094203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2364170506920050437584541 886563940095018914094203)
    ·
      refine ⟨1329845910142528371141305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 886563940095018914094203 1329845910142528371141305)
      ·
        refine ⟨997384432606896278355979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1329845910142528371141305 997384432606896278355979)
        ·
          refine ⟨1496076648910344417533969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 997384432606896278355979 1496076648910344417533969)
          ·
            refine ⟨1122057486682758313150477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1496076648910344417533969 1122057486682758313150477)
            ·
              refine ⟨420771557506034367431429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1122057486682758313150477 420771557506034367431429)
              ·
                refine ⟨78894667032381443893393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 420771557506034367431429 78894667032381443893393)
                ·
                  rfl

theorem cell20_518558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_518558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518558 prefixEnd_518558 := by exact prefixLift 518558
  have htrace : WordTrace (prefixWord ++ tailWord_518558) baseStart_518558 baseEnd_518558 := by
    simpa [prefixWord, tailWord_518558, baseEnd_518558] using wordTrace_append hprefix tailTrace_518558
  have hstable : (prefixWord ++ tailWord_518558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518558).length < 2 ^ (prefixWord ++ tailWord_518558).sum := by decide
  have hdescent : baseEnd_518558 < baseStart_518558 := by decide
  rcases family_descends (prefixWord ++ tailWord_518558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518583 : List Nat := [1, 1, 3, 1, 3, 4, 7]
def baseStart_518583 : Nat := 118140960795 + 518583 * 2 ^ 59
def prefixEnd_518583 : Nat := 4983230072969 + 3 ^ 40 * 518583 * 2
def baseEnd_518583 : Nat := 26299490197595039538527

theorem tailTrace_518583 : CollatzResearch.WordTrace tailWord_518583 prefixEnd_518583 26299490197595039538527 := by
  unfold tailWord_518583
  simp only [CollatzResearch.WordTrace]
  refine ⟨18914275880269832770336403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12609517253513221846890935 18914275880269832770336403)
  ·
    refine ⟨28371413820404749155504605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18914275880269832770336403 28371413820404749155504605)
    ·
      refine ⟨10639280182651780933314227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28371413820404749155504605 10639280182651780933314227)
      ·
        refine ⟨15958920273977671399971341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10639280182651780933314227 15958920273977671399971341)
        ·
          refine ⟨5984595102741626774989253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15958920273977671399971341 5984595102741626774989253)
          ·
            refine ⟨1122111581764055020310485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5984595102741626774989253 1122111581764055020310485)
            ·
              refine ⟨26299490197595039538527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1122111581764055020310485 26299490197595039538527)
              ·
                rfl

theorem cell20_518583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 7].length) (baseStart_518583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518583 prefixEnd_518583 := by exact prefixLift 518583
  have htrace : WordTrace (prefixWord ++ tailWord_518583) baseStart_518583 baseEnd_518583 := by
    simpa [prefixWord, tailWord_518583, baseEnd_518583] using wordTrace_append hprefix tailTrace_518583
  have hstable : (prefixWord ++ tailWord_518583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518583).length < 2 ^ (prefixWord ++ tailWord_518583).sum := by decide
  have hdescent : baseEnd_518583 < baseStart_518583 := by decide
  rcases family_descends (prefixWord ++ tailWord_518583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518627 : List Nat := [1, 1, 1, 6, 3, 2, 1, 3, 2]
def baseStart_518627 : Nat := 118140960795 + 518627 * 2 ^ 59
def prefixEnd_518627 : Nat := 4983230072969 + 3 ^ 40 * 518627 * 2
def baseEnd_518627 : Nat := 236715494577286758379897

theorem tailTrace_518627 : CollatzResearch.WordTrace tailWord_518627 prefixEnd_518627 236715494577286758379897 := by
  unfold tailWord_518627
  simp only [CollatzResearch.WordTrace]
  refine ⟨18915880692110428284938135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12610587128073618856625423 18915880692110428284938135)
  ·
    refine ⟨28373821038165642427407203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18915880692110428284938135 28373821038165642427407203)
    ·
      refine ⟨42560731557248463641110805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28373821038165642427407203 42560731557248463641110805)
      ·
        refine ⟨1995034291746021733177069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42560731557248463641110805 1995034291746021733177069)
        ·
          refine ⟨748137859404758149941401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1995034291746021733177069 748137859404758149941401)
          ·
            refine ⟨561103394553568612456051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 748137859404758149941401 561103394553568612456051)
            ·
              refine ⟨841655091830352918684077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561103394553568612456051 841655091830352918684077)
              ·
                refine ⟨315620659436382344506529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 841655091830352918684077 315620659436382344506529)
                ·
                  refine ⟨236715494577286758379897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 315620659436382344506529 236715494577286758379897)
                  ·
                    rfl

theorem cell20_518627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 3, 2].length) (baseStart_518627 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518627 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518627 prefixEnd_518627 := by exact prefixLift 518627
  have htrace : WordTrace (prefixWord ++ tailWord_518627) baseStart_518627 baseEnd_518627 := by
    simpa [prefixWord, tailWord_518627, baseEnd_518627] using wordTrace_append hprefix tailTrace_518627
  have hstable : (prefixWord ++ tailWord_518627).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518627).length < 2 ^ (prefixWord ++ tailWord_518627).sum := by decide
  have hdescent : baseEnd_518627 < baseStart_518627 := by decide
  rcases family_descends (prefixWord ++ tailWord_518627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518638 : List Nat := [4, 1, 2, 1, 2, 4, 6]
def baseStart_518638 : Nat := 118140960795 + 518638 * 2 ^ 59
def prefixEnd_518638 : Nat := 4983230072969 + 3 ^ 40 * 518638 * 2
def baseEnd_518638 : Nat := 26302279475224401001465

theorem tailTrace_518638 : CollatzResearch.WordTrace tailWord_518638 prefixEnd_518638 26302279475224401001465 := by
  unfold tailWord_518638
  simp only [CollatzResearch.WordTrace]
  refine ⟨2364535236883822145448571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12610854596713718109059045 2364535236883822145448571)
  ·
    refine ⟨3546802855325733218172857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2364535236883822145448571 3546802855325733218172857)
    ·
      refine ⟨2660102141494299913629643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3546802855325733218172857 2660102141494299913629643)
      ·
        refine ⟨3990153212241449870444465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2660102141494299913629643 3990153212241449870444465)
        ·
          refine ⟨2992614909181087402833349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3990153212241449870444465 2992614909181087402833349)
          ·
            refine ⟨561115295471453888031253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2992614909181087402833349 561115295471453888031253)
            ·
              refine ⟨26302279475224401001465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 561115295471453888031253 26302279475224401001465)
              ·
                rfl

theorem cell20_518638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 6].length) (baseStart_518638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518638 prefixEnd_518638 := by exact prefixLift 518638
  have htrace : WordTrace (prefixWord ++ tailWord_518638) baseStart_518638 baseEnd_518638 := by
    simpa [prefixWord, tailWord_518638, baseEnd_518638] using wordTrace_append hprefix tailTrace_518638
  have hstable : (prefixWord ++ tailWord_518638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518638).length < 2 ^ (prefixWord ++ tailWord_518638).sum := by decide
  have hdescent : baseEnd_518638 < baseStart_518638 := by decide
  rcases family_descends (prefixWord ++ tailWord_518638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518648 : List Nat := [2, 1, 2, 1, 1, 4, 5, 2, 2]
def baseStart_518648 : Nat := 118140960795 + 518648 * 2 ^ 59
def prefixEnd_518648 : Nat := 4983230072969 + 3 ^ 40 * 518648 * 2
def baseEnd_518648 : Nat := 236725079549504018679811

theorem tailTrace_518648 : CollatzResearch.WordTrace tailWord_518648 prefixEnd_518648 236725079549504018679811 := by
  unfold tailWord_518648
  simp only [CollatzResearch.WordTrace]
  refine ⟨9458323312517174435726299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12611097750022899247635065 9458323312517174435726299)
  ·
    refine ⟨14187484968775761653589449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9458323312517174435726299 14187484968775761653589449)
    ·
      refine ⟨10640613726581821240192087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14187484968775761653589449 10640613726581821240192087)
      ·
        refine ⟨15960920589872731860288131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10640613726581821240192087 15960920589872731860288131)
        ·
          refine ⟨23941380884809097790432197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15960920589872731860288131 23941380884809097790432197)
          ·
            refine ⟨4489008915901705835706037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23941380884809097790432197 4489008915901705835706037)
            ·
              refine ⟨420844585865784922097441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4489008915901705835706037 420844585865784922097441)
              ·
                refine ⟨315633439399338691573081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 420844585865784922097441 315633439399338691573081)
                ·
                  refine ⟨236725079549504018679811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 315633439399338691573081 236725079549504018679811)
                  ·
                    rfl

theorem cell20_518648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 2, 2].length) (baseStart_518648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518648 prefixEnd_518648 := by exact prefixLift 518648
  have htrace : WordTrace (prefixWord ++ tailWord_518648) baseStart_518648 baseEnd_518648 := by
    simpa [prefixWord, tailWord_518648, baseEnd_518648] using wordTrace_append hprefix tailTrace_518648
  have hstable : (prefixWord ++ tailWord_518648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518648).length < 2 ^ (prefixWord ++ tailWord_518648).sum := by decide
  have hdescent : baseEnd_518648 < baseStart_518648 := by decide
  rcases family_descends (prefixWord ++ tailWord_518648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518659 : List Nat := [1, 1, 1, 3, 2, 1, 6, 5]
def baseStart_518659 : Nat := 118140960795 + 518659 * 2 ^ 59
def prefixEnd_518659 : Nat := 4983230072969 + 3 ^ 40 * 518659 * 2
def baseEnd_518659 : Nat := 78910033416412289771033

theorem tailTrace_518659 : CollatzResearch.WordTrace tailWord_518659 prefixEnd_518659 78910033416412289771033 := by
  unfold tailWord_518659
  simp only [CollatzResearch.WordTrace]
  refine ⟨18917047827994497750103031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12611365218662998500068687 18917047827994497750103031)
  ·
    refine ⟨28375571741991746625154547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18917047827994497750103031 28375571741991746625154547)
    ·
      refine ⟨42563357612987619937731821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28375571741991746625154547 42563357612987619937731821)
      ·
        refine ⟨15961259104870357476649433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42563357612987619937731821 15961259104870357476649433)
        ·
          refine ⟨11970944328652768107487075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15961259104870357476649433 11970944328652768107487075)
          ·
            refine ⟨17956416492979152161230613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11970944328652768107487075 17956416492979152161230613)
            ·
              refine ⟨841707023108397757557685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17956416492979152161230613 841707023108397757557685)
              ·
                refine ⟨78910033416412289771033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 841707023108397757557685 78910033416412289771033)
                ·
                  rfl

theorem cell20_518659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 5].length) (baseStart_518659 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518659 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518659 prefixEnd_518659 := by exact prefixLift 518659
  have htrace : WordTrace (prefixWord ++ tailWord_518659) baseStart_518659 baseEnd_518659 := by
    simpa [prefixWord, tailWord_518659, baseEnd_518659] using wordTrace_append hprefix tailTrace_518659
  have hstable : (prefixWord ++ tailWord_518659).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518659).length < 2 ^ (prefixWord ++ tailWord_518659).sum := by decide
  have hdescent : baseEnd_518659 < baseStart_518659 := by decide
  rcases family_descends (prefixWord ++ tailWord_518659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518704 : List Nat := [2, 1, 1, 1, 2, 3, 2, 3, 5]
def baseStart_518704 : Nat := 118140960795 + 518704 * 2 ^ 59
def prefixEnd_518704 : Nat := 4983230072969 + 3 ^ 40 * 518704 * 2
def baseEnd_518704 : Nat := 236750639475416712812915

theorem tailTrace_518704 : CollatzResearch.WordTrace tailWord_518704 prefixEnd_518704 236750639475416712812915 := by
  unfold tailWord_518704
  simp only [CollatzResearch.WordTrace]
  refine ⟨9459344556415735217745583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12612459408554313623660777 9459344556415735217745583)
  ·
    refine ⟨14189016834623602826618375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9459344556415735217745583 14189016834623602826618375)
    ·
      refine ⟨21283525251935404239927563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14189016834623602826618375 21283525251935404239927563)
      ·
        refine ⟨31925287877903106359891345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21283525251935404239927563 31925287877903106359891345)
        ·
          refine ⟨23943965908427329769918509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31925287877903106359891345 23943965908427329769918509)
          ·
            refine ⟨8978987215660248663719441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23943965908427329769918509 8978987215660248663719441)
            ·
              refine ⟨6734240411745186497789581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8978987215660248663719441 6734240411745186497789581)
              ·
                refine ⟨2525340154404444936671093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6734240411745186497789581 2525340154404444936671093)
                ·
                  refine ⟨236750639475416712812915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2525340154404444936671093 236750639475416712812915)
                  ·
                    rfl

theorem cell20_518704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_518704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518704 prefixEnd_518704 := by exact prefixLift 518704
  have htrace : WordTrace (prefixWord ++ tailWord_518704) baseStart_518704 baseEnd_518704 := by
    simpa [prefixWord, tailWord_518704, baseEnd_518704] using wordTrace_append hprefix tailTrace_518704
  have hstable : (prefixWord ++ tailWord_518704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518704).length < 2 ^ (prefixWord ++ tailWord_518704).sum := by decide
  have hdescent : baseEnd_518704 < baseStart_518704 := by decide
  rcases family_descends (prefixWord ++ tailWord_518704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518707 : List Nat := [1, 1, 1, 2, 4, 2, 3, 4, 2]
def baseStart_518707 : Nat := 118140960795 + 518707 * 2 ^ 59
def prefixEnd_518707 : Nat := 4983230072969 + 3 ^ 40 * 518707 * 2
def baseEnd_518707 : Nat := 236752008757162035712903

theorem tailTrace_518707 : CollatzResearch.WordTrace tailWord_518707 prefixEnd_518707 236752008757162035712903 := by
  unfold tailWord_518707
  simp only [CollatzResearch.WordTrace]
  refine ⟨18918798531820601947850375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12612532354547067965233583 18918798531820601947850375)
  ·
    refine ⟨28378197797730902921775563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18918798531820601947850375 28378197797730902921775563)
    ·
      refine ⟨42567296696596354382663345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28378197797730902921775563 42567296696596354382663345)
      ·
        refine ⟨31925472522447265786997509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42567296696596354382663345 31925472522447265786997509)
        ·
          refine ⟨5986026097958862335062033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31925472522447265786997509 5986026097958862335062033)
          ·
            refine ⟨4489519573469146751296525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5986026097958862335062033 4489519573469146751296525)
            ·
              refine ⟨1683569840050930031736197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4489519573469146751296525 1683569840050930031736197)
              ·
                refine ⟨315669345009549380950537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1683569840050930031736197 315669345009549380950537)
                ·
                  refine ⟨236752008757162035712903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 315669345009549380950537 236752008757162035712903)
                  ·
                    rfl

theorem cell20_518707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 4, 2].length) (baseStart_518707 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518707 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518707 prefixEnd_518707 := by exact prefixLift 518707
  have htrace : WordTrace (prefixWord ++ tailWord_518707) baseStart_518707 baseEnd_518707 := by
    simpa [prefixWord, tailWord_518707, baseEnd_518707] using wordTrace_append hprefix tailTrace_518707
  have hstable : (prefixWord ++ tailWord_518707).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518707).length < 2 ^ (prefixWord ++ tailWord_518707).sum := by decide
  have hdescent : baseEnd_518707 < baseStart_518707 := by decide
  rcases family_descends (prefixWord ++ tailWord_518707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518714 : List Nat := [3, 1, 1, 1, 3, 5, 1, 5]
def baseStart_518714 : Nat := 118140960795 + 518714 * 2 ^ 59
def prefixEnd_518714 : Nat := 4983230072969 + 3 ^ 40 * 518714 * 2
def baseEnd_518714 : Nat := 78918401249300374159847

theorem tailTrace_518714 : CollatzResearch.WordTrace tailWord_518714 prefixEnd_518714 78918401249300374159847 := by
  unfold tailWord_518714
  simp only [CollatzResearch.WordTrace]
  refine ⟨4729763460698810535838799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12612702561863494762236797 4729763460698810535838799)
  ·
    refine ⟨7094645191048215803758199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4729763460698810535838799 7094645191048215803758199)
    ·
      refine ⟨10641967786572323705637299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7094645191048215803758199 10641967786572323705637299)
      ·
        refine ⟨15962951679858485558455949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10641967786572323705637299 15962951679858485558455949)
        ·
          refine ⟨5986106879946932084420981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15962951679858485558455949 5986106879946932084420981)
          ·
            refine ⟨561197519995024882914467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5986106879946932084420981 561197519995024882914467)
            ·
              refine ⟨841796279992537324371701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561197519995024882914467 841796279992537324371701)
              ·
                refine ⟨78918401249300374159847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 841796279992537324371701 78918401249300374159847)
                ·
                  rfl

theorem cell20_518714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_518714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518714 prefixEnd_518714 := by exact prefixLift 518714
  have htrace : WordTrace (prefixWord ++ tailWord_518714) baseStart_518714 baseEnd_518714 := by
    simpa [prefixWord, tailWord_518714, baseEnd_518714] using wordTrace_append hprefix tailTrace_518714
  have hstable : (prefixWord ++ tailWord_518714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518714).length < 2 ^ (prefixWord ++ tailWord_518714).sum := by decide
  have hdescent : baseEnd_518714 < baseStart_518714 := by decide
  rcases family_descends (prefixWord ++ tailWord_518714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518814 : List Nat := [4, 3, 1, 1, 1, 1, 2, 4, 3]
def baseStart_518814 : Nat := 118140960795 + 518814 * 2 ^ 59
def prefixEnd_518814 : Nat := 4983230072969 + 3 ^ 40 * 518814 * 2
def baseEnd_518814 : Nat := 236800846472745219145799

theorem tailTrace_518814 : CollatzResearch.WordTrace tailWord_518814 prefixEnd_518814 236800846472745219145799 := by
  unfold tailWord_518814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2365337642804119902749437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12615134094955306147996997 2365337642804119902749437)
  ·
    refine ⟨887001616051544963531039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2365337642804119902749437 887001616051544963531039)
    ·
      refine ⟨1330502424077317445296559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 887001616051544963531039 1330502424077317445296559)
      ·
        refine ⟨1995753636115976167944839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1330502424077317445296559 1995753636115976167944839)
        ·
          refine ⟨2993630454173964251917259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1995753636115976167944839 2993630454173964251917259)
          ·
            refine ⟨4490445681260946377875889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2993630454173964251917259 4490445681260946377875889)
            ·
              refine ⟨3367834260945709783406917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4490445681260946377875889 3367834260945709783406917)
              ·
                refine ⟨631468923927320584388797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3367834260945709783406917 631468923927320584388797)
                ·
                  refine ⟨236800846472745219145799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 631468923927320584388797 236800846472745219145799)
                  ·
                    rfl

theorem cell20_518814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_518814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518814 prefixEnd_518814 := by exact prefixLift 518814
  have htrace : WordTrace (prefixWord ++ tailWord_518814) baseStart_518814 baseEnd_518814 := by
    simpa [prefixWord, tailWord_518814, baseEnd_518814] using wordTrace_append hprefix tailTrace_518814
  have hstable : (prefixWord ++ tailWord_518814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518814).length < 2 ^ (prefixWord ++ tailWord_518814).sum := by decide
  have hdescent : baseEnd_518814 < baseStart_518814 := by decide
  rcases family_descends (prefixWord ++ tailWord_518814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518817 : List Nat := [1, 2, 3, 3, 3, 1, 3, 2, 2]
def baseStart_518817 : Nat := 118140960795 + 518817 * 2 ^ 59
def prefixEnd_518817 : Nat := 4983230072969 + 3 ^ 40 * 518817 * 2
def baseEnd_518817 : Nat := 236802215754490542045787

theorem tailTrace_518817 : CollatzResearch.WordTrace tailWord_518817 prefixEnd_518817 236802215754490542045787 := by
  unfold tailWord_518817
  simp only [CollatzResearch.WordTrace]
  refine ⟨18922810561422090734354705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12615207040948060489569803 18922810561422090734354705)
  ·
    refine ⟨14192107921066568050766029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18922810561422090734354705 14192107921066568050766029)
    ·
      refine ⟨5322040470399963019037261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14192107921066568050766029 5322040470399963019037261)
      ·
        refine ⟨1995765176399986132138973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5322040470399963019037261 1995765176399986132138973)
        ·
          refine ⟨748411941149994799552115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1995765176399986132138973 748411941149994799552115)
          ·
            refine ⟨1122617911724992199328173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748411941149994799552115 1122617911724992199328173)
            ·
              refine ⟨420981716896872074748065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1122617911724992199328173 420981716896872074748065)
              ·
                refine ⟨315736287672654056061049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 420981716896872074748065 315736287672654056061049)
                ·
                  refine ⟨236802215754490542045787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 315736287672654056061049 236802215754490542045787)
                  ·
                    rfl

theorem cell20_518817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 2, 2].length) (baseStart_518817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518817 prefixEnd_518817 := by exact prefixLift 518817
  have htrace : WordTrace (prefixWord ++ tailWord_518817) baseStart_518817 baseEnd_518817 := by
    simpa [prefixWord, tailWord_518817, baseEnd_518817] using wordTrace_append hprefix tailTrace_518817
  have hstable : (prefixWord ++ tailWord_518817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518817).length < 2 ^ (prefixWord ++ tailWord_518817).sum := by decide
  have hdescent : baseEnd_518817 < baseStart_518817 := by decide
  rcases family_descends (prefixWord ++ tailWord_518817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518835 : List Nat := [1, 1, 1, 2, 3, 5, 1, 3, 3]
def baseStart_518835 : Nat := 118140960795 + 518835 * 2 ^ 59
def prefixEnd_518835 : Nat := 4983230072969 + 3 ^ 40 * 518835 * 2
def baseEnd_518835 : Nat := 236810431444962479445713

theorem tailTrace_518835 : CollatzResearch.WordTrace tailWord_518835 prefixEnd_518835 236810431444962479445713 := by
  unfold tailWord_518835
  simp only [CollatzResearch.WordTrace]
  refine ⟨18923467075356879808509959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12615644716904586539006639 18923467075356879808509959)
  ·
    refine ⟨28385200613035319712764939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18923467075356879808509959 28385200613035319712764939)
    ·
      refine ⟨42577800919552979569147409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28385200613035319712764939 42577800919552979569147409)
      ·
        refine ⟨31933350689664734676860557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42577800919552979569147409 31933350689664734676860557)
        ·
          refine ⟨11975006508624275503822709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31933350689664734676860557 11975006508624275503822709)
          ·
            refine ⟨1122656860183525828483379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11975006508624275503822709 1122656860183525828483379)
            ·
              refine ⟨1683985290275288742725069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1122656860183525828483379 1683985290275288742725069)
              ·
                refine ⟨631494483853233278521901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1683985290275288742725069 631494483853233278521901)
                ·
                  refine ⟨236810431444962479445713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 631494483853233278521901 236810431444962479445713)
                  ·
                    rfl

theorem cell20_518835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 3].length) (baseStart_518835 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518835 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518835 prefixEnd_518835 := by exact prefixLift 518835
  have htrace : WordTrace (prefixWord ++ tailWord_518835) baseStart_518835 baseEnd_518835 := by
    simpa [prefixWord, tailWord_518835, baseEnd_518835] using wordTrace_append hprefix tailTrace_518835
  have hstable : (prefixWord ++ tailWord_518835).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518835).length < 2 ^ (prefixWord ++ tailWord_518835).sum := by decide
  have hdescent : baseEnd_518835 < baseStart_518835 := by decide
  rcases family_descends (prefixWord ++ tailWord_518835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518866 : List Nat := [3, 2, 2, 2, 4, 7]
def baseStart_518866 : Nat := 118140960795 + 518866 * 2 ^ 59
def prefixEnd_518866 : Nat := 4983230072969 + 3 ^ 40 * 518866 * 2
def baseEnd_518866 : Nat := 8771280766283857385639

theorem tailTrace_518866 : CollatzResearch.WordTrace tailWord_518866 prefixEnd_518866 8771280766283857385639 := by
  unfold tailWord_518866
  simp only [CollatzResearch.WordTrace]
  refine ⟨4731149434561143025722113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12616398492163048068592301 4731149434561143025722113)
  ·
    refine ⟨3548362075920857269291585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4731149434561143025722113 3548362075920857269291585)
    ·
      refine ⟨2661271556940642951968689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3548362075920857269291585 2661271556940642951968689)
      ·
        refine ⟨1995953667705482213976517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2661271556940642951968689 1995953667705482213976517)
        ·
          refine ⟨374241312694777915120597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1995953667705482213976517 374241312694777915120597)
          ·
            refine ⟨8771280766283857385639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 374241312694777915120597 8771280766283857385639)
            ·
              rfl

theorem cell20_518866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 7].length) (baseStart_518866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518866 prefixEnd_518866 := by exact prefixLift 518866
  have htrace : WordTrace (prefixWord ++ tailWord_518866) baseStart_518866 baseEnd_518866 := by
    simpa [prefixWord, tailWord_518866, baseEnd_518866] using wordTrace_append hprefix tailTrace_518866
  have hstable : (prefixWord ++ tailWord_518866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518866).length < 2 ^ (prefixWord ++ tailWord_518866).sum := by decide
  have hdescent : baseEnd_518866 < baseStart_518866 := by decide
  rcases family_descends (prefixWord ++ tailWord_518866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518869 : List Nat := [1, 3, 2, 5, 1, 1, 2, 2, 3]
def baseStart_518869 : Nat := 118140960795 + 518869 * 2 ^ 59
def prefixEnd_518869 : Nat := 4983230072969 + 3 ^ 40 * 518869 * 2
def baseEnd_518869 : Nat := 236825949971409472312241

theorem tailTrace_518869 : CollatzResearch.WordTrace tailWord_518869 prefixEnd_518869 236825949971409472312241 := by
  unfold tailWord_518869
  simp only [CollatzResearch.WordTrace]
  refine ⟨18924707157233703615247661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12616471438155802410165107 18924707157233703615247661)
  ·
    refine ⟨7096765183962638855717873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18924707157233703615247661 7096765183962638855717873)
    ·
      refine ⟨5322573887971979141788405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7096765183962638855717873 5322573887971979141788405)
      ·
        refine ⟨498991301997373044542663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5322573887971979141788405 498991301997373044542663)
        ·
          refine ⟨748486952996059566813995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498991301997373044542663 748486952996059566813995)
          ·
            refine ⟨1122730429494089350220993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748486952996059566813995 1122730429494089350220993)
            ·
              refine ⟨842047822120567012665745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1122730429494089350220993 842047822120567012665745)
              ·
                refine ⟨631535866590425259499309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 842047822120567012665745 631535866590425259499309)
                ·
                  refine ⟨236825949971409472312241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 631535866590425259499309 236825949971409472312241)
                  ·
                    rfl

theorem cell20_518869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 3].length) (baseStart_518869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518869 prefixEnd_518869 := by exact prefixLift 518869
  have htrace : WordTrace (prefixWord ++ tailWord_518869) baseStart_518869 baseEnd_518869 := by
    simpa [prefixWord, tailWord_518869, baseEnd_518869] using wordTrace_append hprefix tailTrace_518869
  have hstable : (prefixWord ++ tailWord_518869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518869).length < 2 ^ (prefixWord ++ tailWord_518869).sum := by decide
  have hdescent : baseEnd_518869 < baseStart_518869 := by decide
  rcases family_descends (prefixWord ++ tailWord_518869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518873 : List Nat := [1, 2, 1, 2, 3, 2, 4, 2, 3]
def baseStart_518873 : Nat := 118140960795 + 518873 * 2 ^ 59
def prefixEnd_518873 : Nat := 4983230072969 + 3 ^ 40 * 518873 * 2
def baseEnd_518873 : Nat := 236827775680403236178891

theorem tailTrace_518873 : CollatzResearch.WordTrace tailWord_518873 prefixEnd_518873 236827775680403236178891 := by
  unfold tailWord_518873
  simp only [CollatzResearch.WordTrace]
  refine ⟨18924853049219212298393273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12616568699479474865595515 18924853049219212298393273)
  ·
    refine ⟨14193639786914409223794955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18924853049219212298393273 14193639786914409223794955)
    ·
      refine ⟨21290459680371613835692433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14193639786914409223794955 21290459680371613835692433)
      ·
        refine ⟨15967844760278710376769325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21290459680371613835692433 15967844760278710376769325)
        ·
          refine ⟨5987941785104516391288497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15967844760278710376769325 5987941785104516391288497)
          ·
            refine ⟨4490956338828387293466373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5987941785104516391288497 4490956338828387293466373)
            ·
              refine ⟨842054313530322617524945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4490956338828387293466373 842054313530322617524945)
              ·
                refine ⟨631540735147741963143709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 842054313530322617524945 631540735147741963143709)
                ·
                  refine ⟨236827775680403236178891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 631540735147741963143709 236827775680403236178891)
                  ·
                    rfl

theorem cell20_518873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 3].length) (baseStart_518873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518873 prefixEnd_518873 := by exact prefixLift 518873
  have htrace : WordTrace (prefixWord ++ tailWord_518873) baseStart_518873 baseEnd_518873 := by
    simpa [prefixWord, tailWord_518873, baseEnd_518873] using wordTrace_append hprefix tailTrace_518873
  have hstable : (prefixWord ++ tailWord_518873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518873).length < 2 ^ (prefixWord ++ tailWord_518873).sum := by decide
  have hdescent : baseEnd_518873 < baseStart_518873 := by decide
  rcases family_descends (prefixWord ++ tailWord_518873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518914 : List Nat := [3, 4, 1, 1, 1, 2, 1, 5, 2]
def baseStart_518914 : Nat := 118140960795 + 518914 * 2 ^ 59
def prefixEnd_518914 : Nat := 4983230072969 + 3 ^ 40 * 518914 * 2
def baseEnd_518914 : Nat := 236846489197589315812057

theorem tailTrace_518914 : CollatzResearch.WordTrace tailWord_518914 prefixEnd_518914 236846489197589315812057 := by
  unfold tailWord_518914
  simp only [CollatzResearch.WordTrace]
  refine ⟨4731587110517669075158949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12617565628047117533757197 4731587110517669075158949)
  ·
    refine ⟨887172583222062951592303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4731587110517669075158949 887172583222062951592303)
    ·
      refine ⟨1330758874833094427388455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 887172583222062951592303 1330758874833094427388455)
      ·
        refine ⟨1996138312249641641082683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1330758874833094427388455 1996138312249641641082683)
        ·
          refine ⟨2994207468374462461624025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1996138312249641641082683 2994207468374462461624025)
          ·
            refine ⟨2245655601280846846218019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2994207468374462461624025 2245655601280846846218019)
            ·
              refine ⟨3368483401921270269327029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2245655601280846846218019 3368483401921270269327029)
              ·
                refine ⟨315795318930119087749409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3368483401921270269327029 315795318930119087749409)
                ·
                  refine ⟨236846489197589315812057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 315795318930119087749409 236846489197589315812057)
                  ·
                    rfl

theorem cell20_518914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_518914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518914 prefixEnd_518914 := by exact prefixLift 518914
  have htrace : WordTrace (prefixWord ++ tailWord_518914) baseStart_518914 baseEnd_518914 := by
    simpa [prefixWord, tailWord_518914, baseEnd_518914] using wordTrace_append hprefix tailTrace_518914
  have hstable : (prefixWord ++ tailWord_518914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518914).length < 2 ^ (prefixWord ++ tailWord_518914).sum := by decide
  have hdescent : baseEnd_518914 < baseStart_518914 := by decide
  rcases family_descends (prefixWord ++ tailWord_518914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518935 : List Nat := [1, 1, 3, 4, 3, 1, 2, 1, 4]
def baseStart_518935 : Nat := 118140960795 + 518935 * 2 ^ 59
def prefixEnd_518935 : Nat := 4983230072969 + 3 ^ 40 * 518935 * 2
def baseEnd_518935 : Nat := 236856074169806576111971

theorem tailTrace_518935 : CollatzResearch.WordTrace tailWord_518935 prefixEnd_518935 236856074169806576111971 := by
  unfold tailWord_518935
  simp only [CollatzResearch.WordTrace]
  refine ⟨18927114374994596887150259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12618076249996397924766839 18927114374994596887150259)
  ·
    refine ⟨28390671562491895330725389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18927114374994596887150259 28390671562491895330725389)
    ·
      refine ⟨10646501835934460749022021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28390671562491895330725389 10646501835934460749022021)
      ·
        refine ⟨1996219094237711390441629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10646501835934460749022021 1996219094237711390441629)
        ·
          refine ⟨748582160339141771415611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1996219094237711390441629 748582160339141771415611)
          ·
            refine ⟨1122873240508712657123417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748582160339141771415611 1122873240508712657123417)
            ·
              refine ⟨842154930381534492842563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1122873240508712657123417 842154930381534492842563)
              ·
                refine ⟨1263232395572301739263845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 842154930381534492842563 1263232395572301739263845)
                ·
                  refine ⟨236856074169806576111971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1263232395572301739263845 236856074169806576111971)
                  ·
                    rfl

theorem cell20_518935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 4].length) (baseStart_518935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518935 prefixEnd_518935 := by exact prefixLift 518935
  have htrace : WordTrace (prefixWord ++ tailWord_518935) baseStart_518935 baseEnd_518935 := by
    simpa [prefixWord, tailWord_518935, baseEnd_518935] using wordTrace_append hprefix tailTrace_518935
  have hstable : (prefixWord ++ tailWord_518935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518935).length < 2 ^ (prefixWord ++ tailWord_518935).sum := by decide
  have hdescent : baseEnd_518935 < baseStart_518935 := by decide
  rcases family_descends (prefixWord ++ tailWord_518935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_518963 : List Nat := [1, 1, 1, 2, 6, 2, 1, 6]
def baseStart_518963 : Nat := 118140960795 + 518963 * 2 ^ 59
def prefixEnd_518963 : Nat := 4983230072969 + 3 ^ 40 * 518963 * 2
def baseEnd_518963 : Nat := 78956284710920974392841

theorem tailTrace_518963 : CollatzResearch.WordTrace tailWord_518963 prefixEnd_518963 78956284710920974392841 := by
  unfold tailWord_518963
  simp only [CollatzResearch.WordTrace]
  refine ⟨18928135618893157669169543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12618757079262105112779695 18928135618893157669169543)
  ·
    refine ⟨28392203428339736503754315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18928135618893157669169543 28392203428339736503754315)
    ·
      refine ⟨42588305142509604755631473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28392203428339736503754315 42588305142509604755631473)
      ·
        refine ⟨31941228856882203566723605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42588305142509604755631473 31941228856882203566723605)
        ·
          refine ⟨1497245102666353292190169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31941228856882203566723605 1497245102666353292190169)
          ·
            refine ⟨1122933826999764969142627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1497245102666353292190169 1122933826999764969142627)
            ·
              refine ⟨1684400740499647453713941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1122933826999764969142627 1684400740499647453713941)
              ·
                refine ⟨78956284710920974392841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1684400740499647453713941 78956284710920974392841)
                ·
                  rfl

theorem cell20_518963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 6].length) (baseStart_518963 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_518963 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_518963 prefixEnd_518963 := by exact prefixLift 518963
  have htrace : WordTrace (prefixWord ++ tailWord_518963) baseStart_518963 baseEnd_518963 := by
    simpa [prefixWord, tailWord_518963, baseEnd_518963] using wordTrace_append hprefix tailTrace_518963
  have hstable : (prefixWord ++ tailWord_518963).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_518963).length < 2 ^ (prefixWord ++ tailWord_518963).sum := by decide
  have hdescent : baseEnd_518963 < baseStart_518963 := by decide
  rcases family_descends (prefixWord ++ tailWord_518963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519001 : List Nat := [1, 2, 1, 2, 2, 5, 2, 5]
def baseStart_519001 : Nat := 118140960795 + 519001 * 2 ^ 59
def prefixEnd_519001 : Nat := 4983230072969 + 3 ^ 40 * 519001 * 2
def baseEnd_519001 : Nat := 78962066122734559970567

theorem tailTrace_519001 : CollatzResearch.WordTrace tailWord_519001 prefixEnd_519001 78962066122734559970567 := by
  unfold tailWord_519001
  simp only [CollatzResearch.WordTrace]
  refine ⟨18929521592755490159052857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12619681061836993439368571 18929521592755490159052857)
  ·
    refine ⟨14197141194566617619289643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18929521592755490159052857 14197141194566617619289643)
    ·
      refine ⟨21295711791849926428934465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14197141194566617619289643 21295711791849926428934465)
      ·
        refine ⟨15971783843887444821700849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21295711791849926428934465 15971783843887444821700849)
        ·
          refine ⟨11978837882915583616275637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15971783843887444821700849 11978837882915583616275637)
          ·
            refine ⟨1123016051523335964025841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11978837882915583616275637 1123016051523335964025841)
            ·
              refine ⟨842262038642501973019381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1123016051523335964025841 842262038642501973019381)
              ·
                refine ⟨78962066122734559970567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 842262038642501973019381 78962066122734559970567)
                ·
                  rfl

theorem cell20_519001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 5].length) (baseStart_519001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519001 prefixEnd_519001 := by exact prefixLift 519001
  have htrace : WordTrace (prefixWord ++ tailWord_519001) baseStart_519001 baseEnd_519001 := by
    simpa [prefixWord, tailWord_519001, baseEnd_519001] using wordTrace_append hprefix tailTrace_519001
  have hstable : (prefixWord ++ tailWord_519001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519001).length < 2 ^ (prefixWord ++ tailWord_519001).sum := by decide
  have hdescent : baseEnd_519001 < baseStart_519001 := by decide
  rcases family_descends (prefixWord ++ tailWord_519001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519004 : List Nat := [2, 2, 4, 2, 1, 2, 1, 3, 3]
def baseStart_519004 : Nat := 118140960795 + 519004 * 2 ^ 59
def prefixEnd_519004 : Nat := 4983230072969 + 3 ^ 40 * 519004 * 2
def baseEnd_519004 : Nat := 236887567649949002811689

theorem tailTrace_519004 : CollatzResearch.WordTrace tailWord_519004 prefixEnd_519004 236887567649949002811689 := by
  unfold tailWord_519004
  simp only [CollatzResearch.WordTrace]
  refine ⟨9464815505872310835706033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12619754007829747780941377 9464815505872310835706033)
  ·
    refine ⟨7098611629404233126779525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9464815505872310835706033 7098611629404233126779525)
    ·
      refine ⟨1330989680513293711271161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7098611629404233126779525 1330989680513293711271161)
      ·
        refine ⟨998242260384970283453371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1330989680513293711271161 998242260384970283453371)
        ·
          refine ⟨1497363390577455425180057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 998242260384970283453371 1497363390577455425180057)
          ·
            refine ⟨1123022542933091568885043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1497363390577455425180057 1123022542933091568885043)
            ·
              refine ⟨1684533814399637353327565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1123022542933091568885043 1684533814399637353327565)
              ·
                refine ⟨631700180399864007497837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1684533814399637353327565 631700180399864007497837)
                ·
                  refine ⟨236887567649949002811689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 631700180399864007497837 236887567649949002811689)
                  ·
                    rfl

theorem cell20_519004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_519004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519004 prefixEnd_519004 := by exact prefixLift 519004
  have htrace : WordTrace (prefixWord ++ tailWord_519004) baseStart_519004 baseEnd_519004 := by
    simpa [prefixWord, tailWord_519004, baseEnd_519004] using wordTrace_append hprefix tailTrace_519004
  have hstable : (prefixWord ++ tailWord_519004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519004).length < 2 ^ (prefixWord ++ tailWord_519004).sum := by decide
  have hdescent : baseEnd_519004 < baseStart_519004 := by decide
  rcases family_descends (prefixWord ++ tailWord_519004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519049 : List Nat := [1, 2, 1, 1, 5, 3, 1, 4, 2]
def baseStart_519049 : Nat := 118140960795 + 519049 * 2 ^ 59
def prefixEnd_519049 : Nat := 4983230072969 + 3 ^ 40 * 519049 * 2
def baseEnd_519049 : Nat := 236908106876128846311505

theorem tailTrace_519049 : CollatzResearch.WordTrace tailWord_519049 prefixEnd_519049 236908106876128846311505 := by
  unfold tailWord_519049
  simp only [CollatzResearch.WordTrace]
  refine ⟨18931272296581594356800201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12620848197721062904533467 18931272296581594356800201)
  ·
    refine ⟨14198454222436195767600151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18931272296581594356800201 14198454222436195767600151)
    ·
      refine ⟨21297681333654293651400227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14198454222436195767600151 21297681333654293651400227)
      ·
        refine ⟨31946522000481440477100341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21297681333654293651400227 31946522000481440477100341)
        ·
          refine ⟨2994986437545135044728157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31946522000481440477100341 2994986437545135044728157)
          ·
            refine ⟨1123119914079425641773059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2994986437545135044728157 1123119914079425641773059)
            ·
              refine ⟨1684679871119138462659589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1123119914079425641773059 1684679871119138462659589)
              ·
                refine ⟨315877475834838461748673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1684679871119138462659589 315877475834838461748673)
                ·
                  refine ⟨236908106876128846311505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 315877475834838461748673 236908106876128846311505)
                  ·
                    rfl

theorem cell20_519049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 4, 2].length) (baseStart_519049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519049 prefixEnd_519049 := by exact prefixLift 519049
  have htrace : WordTrace (prefixWord ++ tailWord_519049) baseStart_519049 baseEnd_519049 := by
    simpa [prefixWord, tailWord_519049, baseEnd_519049] using wordTrace_append hprefix tailTrace_519049
  have hstable : (prefixWord ++ tailWord_519049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519049).length < 2 ^ (prefixWord ++ tailWord_519049).sum := by decide
  have hdescent : baseEnd_519049 < baseStart_519049 := by decide
  rcases family_descends (prefixWord ++ tailWord_519049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519098 : List Nat := [3, 1, 1, 1, 2, 1, 11]
def baseStart_519098 : Nat := 118140960795 + 519098 * 2 ^ 59
def prefixEnd_519098 : Nat := 4983230072969 + 3 ^ 40 * 519098 * 2
def baseEnd_519098 : Nat := 26325607979033605964219

theorem tailTrace_519098 : CollatzResearch.WordTrace tailWord_519098 prefixEnd_519098 26325607979033605964219 := by
  unfold tailWord_519098
  simp only [CollatzResearch.WordTrace]
  refine ⟨4733264868351018931333487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12622039648936050483555965 4733264868351018931333487)
  ·
    refine ⟨7099897302526528397000231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4733264868351018931333487 7099897302526528397000231)
    ·
      refine ⟨10649845953789792595500347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7099897302526528397000231 10649845953789792595500347)
      ·
        refine ⟨15974768930684688893250521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10649845953789792595500347 15974768930684688893250521)
        ·
          refine ⟨11981076698013516669937891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15974768930684688893250521 11981076698013516669937891)
          ·
            refine ⟨17971615047020275004906837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11981076698013516669937891 17971615047020275004906837)
            ·
              refine ⟨26325607979033605964219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 17971615047020275004906837 26325607979033605964219)
              ·
                rfl

theorem cell20_519098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 11].length) (baseStart_519098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519098 prefixEnd_519098 := by exact prefixLift 519098
  have htrace : WordTrace (prefixWord ++ tailWord_519098) baseStart_519098 baseEnd_519098 := by
    simpa [prefixWord, tailWord_519098, baseEnd_519098] using wordTrace_append hprefix tailTrace_519098
  have hstable : (prefixWord ++ tailWord_519098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519098).length < 2 ^ (prefixWord ++ tailWord_519098).sum := by decide
  have hdescent : baseEnd_519098 < baseStart_519098 := by decide
  rcases family_descends (prefixWord ++ tailWord_519098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519101 : List Nat := [1, 4, 1, 2, 4, 1, 1, 1, 5]
def baseStart_519101 : Nat := 118140960795 + 519101 * 2 ^ 59
def prefixEnd_519101 : Nat := 4983230072969 + 3 ^ 40 * 519101 * 2
def baseEnd_519101 : Nat := 236931841093047776577959

theorem tailTrace_519101 : CollatzResearch.WordTrace tailWord_519101 prefixEnd_519101 236931841093047776577959 := by
  unfold tailWord_519101
  simp only [CollatzResearch.WordTrace]
  refine ⟨18933168892393207237693157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12622112594928804825128771 18933168892393207237693157)
  ·
    refine ⟨3549969167323726357067467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18933168892393207237693157 3549969167323726357067467)
    ·
      refine ⟨5324953750985589535601201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3549969167323726357067467 5324953750985589535601201)
      ·
        refine ⟨3993715313239192151700901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5324953750985589535601201 3993715313239192151700901)
        ·
          refine ⟨748821621232348528443919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3993715313239192151700901 748821621232348528443919)
          ·
            refine ⟨1123232431848522792665879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748821621232348528443919 1123232431848522792665879)
            ·
              refine ⟨1684848647772784188998819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1123232431848522792665879 1684848647772784188998819)
              ·
                refine ⟨2527272971659176283498229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1684848647772784188998819 2527272971659176283498229)
                ·
                  refine ⟨236931841093047776577959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2527272971659176283498229 236931841093047776577959)
                  ·
                    rfl

theorem cell20_519101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_519101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519101 prefixEnd_519101 := by exact prefixLift 519101
  have htrace : WordTrace (prefixWord ++ tailWord_519101) baseStart_519101 baseEnd_519101 := by
    simpa [prefixWord, tailWord_519101, baseEnd_519101] using wordTrace_append hprefix tailTrace_519101
  have hstable : (prefixWord ++ tailWord_519101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519101).length < 2 ^ (prefixWord ++ tailWord_519101).sum := by decide
  have hdescent : baseEnd_519101 < baseStart_519101 := by decide
  rcases family_descends (prefixWord ++ tailWord_519101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519110 : List Nat := [6, 1, 3, 1, 1, 1, 3, 1, 3]
def baseStart_519110 : Nat := 118140960795 + 519110 * 2 ^ 59
def prefixEnd_519110 : Nat := 4983230072969 + 3 ^ 40 * 519110 * 2
def baseEnd_519110 : Nat := 236935948938283745277923

theorem tailTrace_519110 : CollatzResearch.WordTrace tailWord_519110 prefixEnd_519110 236935948938283745277923 := by
  unfold tailWord_519110
  simp only [CollatzResearch.WordTrace]
  refine ⟨591671785917518805461587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12622331432907067849847189 591671785917518805461587)
  ·
    refine ⟨887507678876278208192381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 591671785917518805461587 887507678876278208192381)
    ·
      refine ⟨332815379578604328072143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 887507678876278208192381 332815379578604328072143)
      ·
        refine ⟨499223069367906492108215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332815379578604328072143 499223069367906492108215)
        ·
          refine ⟨748834604051859738162323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499223069367906492108215 748834604051859738162323)
          ·
            refine ⟨1123251906077789607243485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748834604051859738162323 1123251906077789607243485)
            ·
              refine ⟨421219464779171102716307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1123251906077789607243485 421219464779171102716307)
              ·
                refine ⟨631829197168756654074461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421219464779171102716307 631829197168756654074461)
                ·
                  refine ⟨236935948938283745277923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 631829197168756654074461 236935948938283745277923)
                  ·
                    rfl

theorem cell20_519110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_519110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519110 prefixEnd_519110 := by exact prefixLift 519110
  have htrace : WordTrace (prefixWord ++ tailWord_519110) baseStart_519110 baseEnd_519110 := by
    simpa [prefixWord, tailWord_519110, baseEnd_519110] using wordTrace_append hprefix tailTrace_519110
  have hstable : (prefixWord ++ tailWord_519110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519110).length < 2 ^ (prefixWord ++ tailWord_519110).sum := by decide
  have hdescent : baseEnd_519110 < baseStart_519110 := by decide
  rcases family_descends (prefixWord ++ tailWord_519110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519118 : List Nat := [4, 1, 1, 1, 2, 4, 3, 1, 3]
def baseStart_519118 : Nat := 118140960795 + 519118 * 2 ^ 59
def prefixEnd_519118 : Nat := 4983230072969 + 3 ^ 40 * 519118 * 2
def baseEnd_519118 : Nat := 236939600356271273011223

theorem tailTrace_519118 : CollatzResearch.WordTrace tailWord_519118 prefixEnd_519118 236939600356271273011223 := by
  unfold tailWord_519118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2366723616666452392632751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12622525955554412760708005 2366723616666452392632751)
  ·
    refine ⟨3550085424999678588949127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2366723616666452392632751 3550085424999678588949127)
    ·
      refine ⟨5325128137499517883423691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3550085424999678588949127 5325128137499517883423691)
      ·
        refine ⟨7987692206249276825135537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5325128137499517883423691 7987692206249276825135537)
        ·
          refine ⟨5990769154686957618851653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7987692206249276825135537 5990769154686957618851653)
          ·
            refine ⟨1123269216503804553534685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5990769154686957618851653 1123269216503804553534685)
            ·
              refine ⟨421225956188926707575507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1123269216503804553534685 421225956188926707575507)
              ·
                refine ⟨631838934283390061363261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421225956188926707575507 631838934283390061363261)
                ·
                  refine ⟨236939600356271273011223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 631838934283390061363261 236939600356271273011223)
                  ·
                    rfl

theorem cell20_519118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_519118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519118 prefixEnd_519118 := by exact prefixLift 519118
  have htrace : WordTrace (prefixWord ++ tailWord_519118) baseStart_519118 baseEnd_519118 := by
    simpa [prefixWord, tailWord_519118, baseEnd_519118] using wordTrace_append hprefix tailTrace_519118
  have hstable : (prefixWord ++ tailWord_519118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519118).length < 2 ^ (prefixWord ++ tailWord_519118).sum := by decide
  have hdescent : baseEnd_519118 < baseStart_519118 := by decide
  rcases family_descends (prefixWord ++ tailWord_519118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519153 : List Nat := [1, 2, 2, 2, 4, 3, 6]
def baseStart_519153 : Nat := 118140960795 + 519153 * 2 ^ 59
def prefixEnd_519153 : Nat := 4983230072969 + 3 ^ 40 * 519153 * 2
def baseEnd_519153 : Nat := 26328397256662967427157

theorem tailTrace_519153 : CollatzResearch.WordTrace tailWord_519153 prefixEnd_519153 26328397256662967427157 := by
  unfold tailWord_519153
  simp only [CollatzResearch.WordTrace]
  refine ⟨18935065488204820118586113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12623376992136546745724075 18935065488204820118586113)
  ·
    refine ⟨14201299116153615088939585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18935065488204820118586113 14201299116153615088939585)
    ·
      refine ⟨10650974337115211316704689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14201299116153615088939585 10650974337115211316704689)
      ·
        refine ⟨7988230752836408487528517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10650974337115211316704689 7988230752836408487528517)
        ·
          refine ⟨1497793266156826591411597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7988230752836408487528517 1497793266156826591411597)
          ·
            refine ⟨561672474808809971779349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1497793266156826591411597 561672474808809971779349)
            ·
              refine ⟨26328397256662967427157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 561672474808809971779349 26328397256662967427157)
              ·
                rfl

theorem cell20_519153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 6].length) (baseStart_519153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519153 prefixEnd_519153 := by exact prefixLift 519153
  have htrace : WordTrace (prefixWord ++ tailWord_519153) baseStart_519153 baseEnd_519153 := by
    simpa [prefixWord, tailWord_519153, baseEnd_519153] using wordTrace_append hprefix tailTrace_519153
  have hstable : (prefixWord ++ tailWord_519153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519153).length < 2 ^ (prefixWord ++ tailWord_519153).sum := by decide
  have hdescent : baseEnd_519153 < baseStart_519153 := by decide
  rcases family_descends (prefixWord ++ tailWord_519153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519160 : List Nat := [2, 1, 2, 1, 1, 3, 1, 6, 3]
def baseStart_519160 : Nat := 118140960795 + 519160 * 2 ^ 59
def prefixEnd_519160 : Nat := 4983230072969 + 3 ^ 40 * 519160 * 2
def baseEnd_519160 : Nat := 236958770300705793611051

theorem tailTrace_519160 : CollatzResearch.WordTrace tailWord_519160 prefixEnd_519160 236958770300705793611051 := by
  unfold tailWord_519160
  simp only [CollatzResearch.WordTrace]
  refine ⟨9467660399589730157045467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12623547199452973542727289 9467660399589730157045467)
  ·
    refine ⟨14201490599384595235568201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9467660399589730157045467 14201490599384595235568201)
    ·
      refine ⟨10651117949538446426676151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14201490599384595235568201 10651117949538446426676151)
      ·
        refine ⟨15976676924307669640014227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10651117949538446426676151 15976676924307669640014227)
        ·
          refine ⟨23965015386461504460021341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15976676924307669640014227 23965015386461504460021341)
          ·
            refine ⟨8986880769923064172508003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23965015386461504460021341 8986880769923064172508003)
            ·
              refine ⟨13480321154884596258762005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8986880769923064172508003 13480321154884596258762005)
              ·
                refine ⟨631890054135215449629469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13480321154884596258762005 631890054135215449629469)
                ·
                  refine ⟨236958770300705793611051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 631890054135215449629469 236958770300705793611051)
                  ·
                    rfl

theorem cell20_519160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 3].length) (baseStart_519160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519160 prefixEnd_519160 := by exact prefixLift 519160
  have htrace : WordTrace (prefixWord ++ tailWord_519160) baseStart_519160 baseEnd_519160 := by
    simpa [prefixWord, tailWord_519160, baseEnd_519160] using wordTrace_append hprefix tailTrace_519160
  have hstable : (prefixWord ++ tailWord_519160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519160).length < 2 ^ (prefixWord ++ tailWord_519160).sum := by decide
  have hdescent : baseEnd_519160 < baseStart_519160 := by decide
  rcases family_descends (prefixWord ++ tailWord_519160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519191 : List Nat := [1, 1, 3, 5, 1, 1, 2, 6]
def baseStart_519191 : Nat := 118140960795 + 519191 * 2 ^ 59
def prefixEnd_519191 : Nat := 4983230072969 + 3 ^ 40 * 519191 * 2
def baseEnd_519191 : Nat := 78990973181802487859197

theorem tailTrace_519191 : CollatzResearch.WordTrace tailWord_519191 prefixEnd_519191 78990973181802487859197 := by
  unfold tailWord_519191
  simp only [CollatzResearch.WordTrace]
  refine ⟨18936451462067152608469427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12624300974711435072312951 18936451462067152608469427)
  ·
    refine ⟨28404677193100728912704141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18936451462067152608469427 28404677193100728912704141)
    ·
      refine ⟨10651753947412773342264053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28404677193100728912704141 10651753947412773342264053)
      ·
        refine ⟨998601932569947500837255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10651753947412773342264053 998601932569947500837255)
        ·
          refine ⟨1497902898854921251255883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 998601932569947500837255 1497902898854921251255883)
          ·
            refine ⟨2246854348282381876883825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1497902898854921251255883 2246854348282381876883825)
            ·
              refine ⟨1685140761211786407662869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2246854348282381876883825 1685140761211786407662869)
              ·
                refine ⟨78990973181802487859197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1685140761211786407662869 78990973181802487859197)
                ·
                  rfl

theorem cell20_519191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 6].length) (baseStart_519191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519191 prefixEnd_519191 := by exact prefixLift 519191
  have htrace : WordTrace (prefixWord ++ tailWord_519191) baseStart_519191 baseEnd_519191 := by
    simpa [prefixWord, tailWord_519191, baseEnd_519191] using wordTrace_append hprefix tailTrace_519191
  have hstable : (prefixWord ++ tailWord_519191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519191).length < 2 ^ (prefixWord ++ tailWord_519191).sum := by decide
  have hdescent : baseEnd_519191 < baseStart_519191 := by decide
  rcases family_descends (prefixWord ++ tailWord_519191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519229 : List Nat := [1, 4, 1, 3, 1, 2, 3, 5]
def baseStart_519229 : Nat := 118140960795 + 519229 * 2 ^ 59
def prefixEnd_519229 : Nat := 4983230072969 + 3 ^ 40 * 519229 * 2
def baseEnd_519229 : Nat := 78996754593616073436923

theorem tailTrace_519229 : CollatzResearch.WordTrace tailWord_519229 prefixEnd_519229 78996754593616073436923 := by
  unfold tailWord_519229
  simp only [CollatzResearch.WordTrace]
  refine ⟨18937837435929485098352741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12625224957286323398901827 18937837435929485098352741)
  ·
    refine ⟨3550844519236778455941139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18937837435929485098352741 3550844519236778455941139)
    ·
      refine ⟨5326266778855167683911709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3550844519236778455941139 5326266778855167683911709)
      ·
        refine ⟨1997350042070687881466891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5326266778855167683911709 1997350042070687881466891)
        ·
          refine ⟨2996025063106031822200337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1997350042070687881466891 2996025063106031822200337)
          ·
            refine ⟨2247018797329523866650253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2996025063106031822200337 2247018797329523866650253)
            ·
              refine ⟨842632048998571449993845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2247018797329523866650253 842632048998571449993845)
              ·
                refine ⟨78996754593616073436923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 842632048998571449993845 78996754593616073436923)
                ·
                  rfl

theorem cell20_519229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 5].length) (baseStart_519229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519229 prefixEnd_519229 := by exact prefixLift 519229
  have htrace : WordTrace (prefixWord ++ tailWord_519229) baseStart_519229 baseEnd_519229 := by
    simpa [prefixWord, tailWord_519229, baseEnd_519229] using wordTrace_append hprefix tailTrace_519229
  have hstable : (prefixWord ++ tailWord_519229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519229).length < 2 ^ (prefixWord ++ tailWord_519229).sum := by decide
  have hdescent : baseEnd_519229 < baseStart_519229 := by decide
  rcases family_descends (prefixWord ++ tailWord_519229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519277 : List Nat := [1, 5, 1, 1, 2, 2, 2, 4, 2]
def baseStart_519277 : Nat := 118140960795 + 519277 * 2 ^ 59
def prefixEnd_519277 : Nat := 4983230072969 + 3 ^ 40 * 519277 * 2
def baseEnd_519277 : Nat := 237012172288773386710573

theorem tailTrace_519277 : CollatzResearch.WordTrace tailWord_519277 prefixEnd_519277 237012172288773386710573 := by
  unfold tailWord_519277
  simp only [CollatzResearch.WordTrace]
  refine ⟨18939588139755589296100085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12626392093170392864066723 18939588139755589296100085)
  ·
    refine ⟨1775586388102086496509383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18939588139755589296100085 1775586388102086496509383)
    ·
      refine ⟨2663379582153129744764075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1775586388102086496509383 2663379582153129744764075)
      ·
        refine ⟨3995069373229694617146113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2663379582153129744764075 3995069373229694617146113)
        ·
          refine ⟨2996302029922270962859585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3995069373229694617146113 2996302029922270962859585)
          ·
            refine ⟨2247226522441703222144689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2996302029922270962859585 2247226522441703222144689)
            ·
              refine ⟨1685419891831277416608517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2247226522441703222144689 1685419891831277416608517)
              ·
                refine ⟨316016229718364515614097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1685419891831277416608517 316016229718364515614097)
                ·
                  refine ⟨237012172288773386710573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316016229718364515614097 237012172288773386710573)
                  ·
                    rfl

theorem cell20_519277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_519277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519277 prefixEnd_519277 := by exact prefixLift 519277
  have htrace : WordTrace (prefixWord ++ tailWord_519277) baseStart_519277 baseEnd_519277 := by
    simpa [prefixWord, tailWord_519277, baseEnd_519277] using wordTrace_append hprefix tailTrace_519277
  have hstable : (prefixWord ++ tailWord_519277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519277).length < 2 ^ (prefixWord ++ tailWord_519277).sum := by decide
  have hdescent : baseEnd_519277 < baseStart_519277 := by decide
  rcases family_descends (prefixWord ++ tailWord_519277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519301 : List Nat := [1, 3, 1, 1, 7, 1, 2, 4]
def baseStart_519301 : Nat := 118140960795 + 519301 * 2 ^ 59
def prefixEnd_519301 : Nat := 4983230072969 + 3 ^ 40 * 519301 * 2
def baseEnd_519301 : Nat := 79007708847578656636825

theorem tailTrace_519301 : CollatzResearch.WordTrace tailWord_519301 prefixEnd_519301 79007708847578656636825 := by
  unfold tailWord_519301
  simp only [CollatzResearch.WordTrace]
  refine ⟨18940463491668641394973757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12626975661112427596649171 18940463491668641394973757)
  ·
    refine ⟨7102673809375740523115159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18940463491668641394973757 7102673809375740523115159)
    ·
      refine ⟨10654010714063610784672739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7102673809375740523115159 10654010714063610784672739)
      ·
        refine ⟨15981016071095416177009109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10654010714063610784672739 15981016071095416177009109)
        ·
          refine ⟨374555064166298816648651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 15981016071095416177009109 374555064166298816648651)
          ·
            refine ⟨561832596249448224972977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374555064166298816648651 561832596249448224972977)
            ·
              refine ⟨421374447187086168729733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 561832596249448224972977 421374447187086168729733)
              ·
                refine ⟨79007708847578656636825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 421374447187086168729733 79007708847578656636825)
                ·
                  rfl

theorem cell20_519301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 4].length) (baseStart_519301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519301 prefixEnd_519301 := by exact prefixLift 519301
  have htrace : WordTrace (prefixWord ++ tailWord_519301) baseStart_519301 baseEnd_519301 := by
    simpa [prefixWord, tailWord_519301, baseEnd_519301] using wordTrace_append hprefix tailTrace_519301
  have hstable : (prefixWord ++ tailWord_519301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519301).length < 2 ^ (prefixWord ++ tailWord_519301).sum := by decide
  have hdescent : baseEnd_519301 < baseStart_519301 := by decide
  rcases family_descends (prefixWord ++ tailWord_519301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519305 : List Nat := [1, 2, 1, 1, 4, 3, 4, 4]
def baseStart_519305 : Nat := 118140960795 + 519305 * 2 ^ 59
def prefixEnd_519305 : Nat := 4983230072969 + 3 ^ 40 * 519305 * 2
def baseEnd_519305 : Nat := 79008317417243244592375

theorem tailTrace_519305 : CollatzResearch.WordTrace tailWord_519305 prefixEnd_519305 79008317417243244592375 := by
  unfold tailWord_519305
  simp only [CollatzResearch.WordTrace]
  refine ⟨18940609383654150078119369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12627072922436100052079579 18940609383654150078119369)
  ·
    refine ⟨14205457037740612558589527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18940609383654150078119369 14205457037740612558589527)
    ·
      refine ⟨21308185556610918837884291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14205457037740612558589527 21308185556610918837884291)
      ·
        refine ⟨31962278334916378256826437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21308185556610918837884291 31962278334916378256826437)
        ·
          refine ⟨5992927187796820923154957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31962278334916378256826437 5992927187796820923154957)
          ·
            refine ⟨2247347695423807846183109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5992927187796820923154957 2247347695423807846183109)
            ·
              refine ⟨421377692891963971159333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2247347695423807846183109 421377692891963971159333)
              ·
                refine ⟨79008317417243244592375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 421377692891963971159333 79008317417243244592375)
                ·
                  rfl

theorem cell20_519305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 4].length) (baseStart_519305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519305 prefixEnd_519305 := by exact prefixLift 519305
  have htrace : WordTrace (prefixWord ++ tailWord_519305) baseStart_519305 baseEnd_519305 := by
    simpa [prefixWord, tailWord_519305, baseEnd_519305] using wordTrace_append hprefix tailTrace_519305
  have hstable : (prefixWord ++ tailWord_519305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519305).length < 2 ^ (prefixWord ++ tailWord_519305).sum := by decide
  have hdescent : baseEnd_519305 < baseStart_519305 := by decide
  rcases family_descends (prefixWord ++ tailWord_519305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519332 : List Nat := [2, 3, 1, 2, 3, 2, 3, 2, 2]
def baseStart_519332 : Nat := 118140960795 + 519332 * 2 ^ 59
def prefixEnd_519332 : Nat := 4983230072969 + 3 ^ 40 * 519332 * 2
def baseEnd_519332 : Nat := 237037275787437639877015

theorem tailTrace_519332 : CollatzResearch.WordTrace tailWord_519332 prefixEnd_519332 237037275787437639877015 := by
  unfold tailWord_519332
  simp only [CollatzResearch.WordTrace]
  refine ⟨9470797077278166844676125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12627729436370889126234833 9470797077278166844676125)
  ·
    refine ⟨3551548903979312566753547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9470797077278166844676125 3551548903979312566753547)
    ·
      refine ⟨5327323355968968850130321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3551548903979312566753547 5327323355968968850130321)
      ·
        refine ⟨3995492516976726637597741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5327323355968968850130321 3995492516976726637597741)
        ·
          refine ⟨1498309693866272489099153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3995492516976726637597741 1498309693866272489099153)
          ·
            refine ⟨1123732270399704366824365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1498309693866272489099153 1123732270399704366824365)
            ·
              refine ⟨421399601399889137559137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1123732270399704366824365 421399601399889137559137)
              ·
                refine ⟨316049701049916853169353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 421399601399889137559137 316049701049916853169353)
                ·
                  refine ⟨237037275787437639877015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316049701049916853169353 237037275787437639877015)
                  ·
                    rfl

theorem cell20_519332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_519332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519332 prefixEnd_519332 := by exact prefixLift 519332
  have htrace : WordTrace (prefixWord ++ tailWord_519332) baseStart_519332 baseEnd_519332 := by
    simpa [prefixWord, tailWord_519332, baseEnd_519332] using wordTrace_append hprefix tailTrace_519332
  have hstable : (prefixWord ++ tailWord_519332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519332).length < 2 ^ (prefixWord ++ tailWord_519332).sum := by decide
  have hdescent : baseEnd_519332 < baseStart_519332 := by decide
  rcases family_descends (prefixWord ++ tailWord_519332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519346 : List Nat := [3, 2, 1, 1, 1, 6, 2, 1, 3]
def baseStart_519346 : Nat := 118140960795 + 519346 * 2 ^ 59
def prefixEnd_519346 : Nat := 4983230072969 + 3 ^ 40 * 519346 * 2
def baseEnd_519346 : Nat := 237043665768915813410291

theorem tailTrace_519346 : CollatzResearch.WordTrace tailWord_519346 prefixEnd_519346 237043665768915813410291 := by
  unfold tailWord_519346
  simp only [CollatzResearch.WordTrace]
  refine ⟨4735526194126403520090473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12628069851003742720241261 4735526194126403520090473)
  ·
    refine ⟨3551644645594802640067855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4735526194126403520090473 3551644645594802640067855)
    ·
      refine ⟨5327466968392203960101783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3551644645594802640067855 5327466968392203960101783)
      ·
        refine ⟨7991200452588305940152675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5327466968392203960101783 7991200452588305940152675)
        ·
          refine ⟨11986800678882458910229013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7991200452588305940152675 11986800678882458910229013)
          ·
            refine ⟨561881281822615261416985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11986800678882458910229013 561881281822615261416985)
            ·
              refine ⟨421410961366961446062739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 561881281822615261416985 421410961366961446062739)
              ·
                refine ⟨632116442050442169094109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 421410961366961446062739 632116442050442169094109)
                ·
                  refine ⟨237043665768915813410291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 632116442050442169094109 237043665768915813410291)
                  ·
                    rfl

theorem cell20_519346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_519346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519346 prefixEnd_519346 := by exact prefixLift 519346
  have htrace : WordTrace (prefixWord ++ tailWord_519346) baseStart_519346 baseEnd_519346 := by
    simpa [prefixWord, tailWord_519346, baseEnd_519346] using wordTrace_append hprefix tailTrace_519346
  have hstable : (prefixWord ++ tailWord_519346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519346).length < 2 ^ (prefixWord ++ tailWord_519346).sum := by decide
  have hdescent : baseEnd_519346 < baseStart_519346 := by decide
  rcases family_descends (prefixWord ++ tailWord_519346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519357 : List Nat := [1, 4, 1, 2, 1, 1, 2, 4, 4]
def baseStart_519357 : Nat := 118140960795 + 519357 * 2 ^ 59
def prefixEnd_519357 : Nat := 4983230072969 + 3 ^ 40 * 519357 * 2
def baseEnd_519357 : Nat := 237048686468648664043579

theorem tailTrace_519357 : CollatzResearch.WordTrace tailWord_519357 prefixEnd_519357 237048686468648664043579 := by
  unfold tailWord_519357
  simp only [CollatzResearch.WordTrace]
  refine ⟨18942505979465762959012325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12628337319643841972674883 18942505979465762959012325)
  ·
    refine ⟨3551719871149830554814811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18942505979465762959012325 3551719871149830554814811)
    ·
      refine ⟨5327579806724745832222217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3551719871149830554814811 5327579806724745832222217)
      ·
        refine ⟨3995684855043559374166663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5327579806724745832222217 3995684855043559374166663)
        ·
          refine ⟨5993527282565339061249995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3995684855043559374166663 5993527282565339061249995)
          ·
            refine ⟨8990290923848008591874993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5993527282565339061249995 8990290923848008591874993)
            ·
              refine ⟨6742718192886006443906245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8990290923848008591874993 6742718192886006443906245)
              ·
                refine ⟨1264259661166126208232421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6742718192886006443906245 1264259661166126208232421)
                ·
                  refine ⟨237048686468648664043579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1264259661166126208232421 237048686468648664043579)
                  ·
                    rfl

theorem cell20_519357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_519357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519357 prefixEnd_519357 := by exact prefixLift 519357
  have htrace : WordTrace (prefixWord ++ tailWord_519357) baseStart_519357 baseEnd_519357 := by
    simpa [prefixWord, tailWord_519357, baseEnd_519357] using wordTrace_append hprefix tailTrace_519357
  have hstable : (prefixWord ++ tailWord_519357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519357).length < 2 ^ (prefixWord ++ tailWord_519357).sum := by decide
  have hdescent : baseEnd_519357 < baseStart_519357 := by decide
  rcases family_descends (prefixWord ++ tailWord_519357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519371 : List Nat := [1, 1, 1, 1, 3, 2, 2, 4, 5]
def baseStart_519371 : Nat := 118140960795 + 519371 * 2 ^ 59
def prefixEnd_519371 : Nat := 4983230072969 + 3 ^ 40 * 519371 * 2
def baseEnd_519371 : Nat := 237055076450126837576855

theorem tailTrace_519371 : CollatzResearch.WordTrace tailWord_519371 prefixEnd_519371 237055076450126837576855 := by
  unfold tailWord_519371
  simp only [CollatzResearch.WordTrace]
  refine ⟨18943016601415043350021967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12628677734276695566681311 18943016601415043350021967)
  ·
    refine ⟨28414524902122565025032951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18943016601415043350021967 28414524902122565025032951)
    ·
      refine ⟨42621787353183847537549427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28414524902122565025032951 42621787353183847537549427)
      ·
        refine ⟨63932681029775771306324141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42621787353183847537549427 63932681029775771306324141)
        ·
          refine ⟨23974755386165914239871553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63932681029775771306324141 23974755386165914239871553)
          ·
            refine ⟨17981066539624435679903665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23974755386165914239871553 17981066539624435679903665)
            ·
              refine ⟨13485799904718326759927749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17981066539624435679903665 13485799904718326759927749)
              ·
                refine ⟨2528587482134686267486453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13485799904718326759927749 2528587482134686267486453)
                ·
                  refine ⟨237055076450126837576855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2528587482134686267486453 237055076450126837576855)
                  ·
                    rfl

theorem cell20_519371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 5].length) (baseStart_519371 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519371 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519371 prefixEnd_519371 := by exact prefixLift 519371
  have htrace : WordTrace (prefixWord ++ tailWord_519371) baseStart_519371 baseEnd_519371 := by
    simpa [prefixWord, tailWord_519371, baseEnd_519371] using wordTrace_append hprefix tailTrace_519371
  have hstable : (prefixWord ++ tailWord_519371).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519371).length < 2 ^ (prefixWord ++ tailWord_519371).sum := by decide
  have hdescent : baseEnd_519371 < baseStart_519371 := by decide
  rcases family_descends (prefixWord ++ tailWord_519371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519391 : List Nat := [1, 1, 2, 3, 2, 1, 6, 2, 2]
def baseStart_519391 : Nat := 118140960795 + 519391 * 2 ^ 59
def prefixEnd_519391 : Nat := 4983230072969 + 3 ^ 40 * 519391 * 2
def baseEnd_519391 : Nat := 237064204995095656910107

theorem tailTrace_519391 : CollatzResearch.WordTrace tailWord_519391 prefixEnd_519391 237064204995095656910107 := by
  unfold tailWord_519391
  simp only [CollatzResearch.WordTrace]
  refine ⟨18943746061342586765750027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12629164040895057843833351 18943746061342586765750027)
  ·
    refine ⟨28415619092013880148625041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18943746061342586765750027 28415619092013880148625041)
    ·
      refine ⟨21311714319010410111468781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28415619092013880148625041 21311714319010410111468781)
      ·
        refine ⟨7991892869628903791800793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21311714319010410111468781 7991892869628903791800793)
        ·
          refine ⟨5993919652221677843850595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7991892869628903791800793 5993919652221677843850595)
          ·
            refine ⟨8990879478332516765775893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5993919652221677843850595 8990879478332516765775893)
            ·
              refine ⟨421447475546836723395745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8990879478332516765775893 421447475546836723395745)
              ·
                refine ⟨316085606660127542546809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 421447475546836723395745 316085606660127542546809)
                ·
                  refine ⟨237064204995095656910107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316085606660127542546809 237064204995095656910107)
                  ·
                    rfl

theorem cell20_519391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 2, 2].length) (baseStart_519391 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519391 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519391 prefixEnd_519391 := by exact prefixLift 519391
  have htrace : WordTrace (prefixWord ++ tailWord_519391) baseStart_519391 baseEnd_519391 := by
    simpa [prefixWord, tailWord_519391, baseEnd_519391] using wordTrace_append hprefix tailTrace_519391
  have hstable : (prefixWord ++ tailWord_519391).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519391).length < 2 ^ (prefixWord ++ tailWord_519391).sum := by decide
  have hdescent : baseEnd_519391 < baseStart_519391 := by decide
  rcases family_descends (prefixWord ++ tailWord_519391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519405 : List Nat := [1, 5, 1, 2, 2, 1, 2, 3, 3]
def baseStart_519405 : Nat := 118140960795 + 519405 * 2 ^ 59
def prefixEnd_519405 : Nat := 4983230072969 + 3 ^ 40 * 519405 * 2
def baseEnd_519405 : Nat := 237070594976573830443383

theorem tailTrace_519405 : CollatzResearch.WordTrace tailWord_519405 prefixEnd_519405 237070594976573830443383 := by
  unfold tailWord_519405
  simp only [CollatzResearch.WordTrace]
  refine ⟨18944256683291867156759669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12629504455527911437839779 18944256683291867156759669)
  ·
    refine ⟨1776024064058612545946219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18944256683291867156759669 1776024064058612545946219)
    ·
      refine ⟨2664036096087918818919329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1776024064058612545946219 2664036096087918818919329)
      ·
        refine ⟨1998027072065939114189497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2664036096087918818919329 1998027072065939114189497)
        ·
          refine ⟨1498520304049454335642123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1998027072065939114189497 1498520304049454335642123)
          ·
            refine ⟨2247780456074181503463185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1498520304049454335642123 2247780456074181503463185)
            ·
              refine ⟨1685835342055636127597389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2247780456074181503463185 1685835342055636127597389)
              ·
                refine ⟨632188253270863547849021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1685835342055636127597389 632188253270863547849021)
                ·
                  refine ⟨237070594976573830443383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 632188253270863547849021 237070594976573830443383)
                  ·
                    rfl

theorem cell20_519405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_519405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519405 prefixEnd_519405 := by exact prefixLift 519405
  have htrace : WordTrace (prefixWord ++ tailWord_519405) baseStart_519405 baseEnd_519405 := by
    simpa [prefixWord, tailWord_519405, baseEnd_519405] using wordTrace_append hprefix tailTrace_519405
  have hstable : (prefixWord ++ tailWord_519405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519405).length < 2 ^ (prefixWord ++ tailWord_519405).sum := by decide
  have hdescent : baseEnd_519405 < baseStart_519405 := by decide
  rcases family_descends (prefixWord ++ tailWord_519405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519409 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 7]
def baseStart_519409 : Nat := 118140960795 + 519409 * 2 ^ 59
def prefixEnd_519409 : Nat := 4983230072969 + 3 ^ 40 * 519409 * 2
def baseEnd_519409 : Nat := 237072420685567594310033

theorem tailTrace_519409 : CollatzResearch.WordTrace tailWord_519409 prefixEnd_519409 237072420685567594310033 := by
  unfold tailWord_519409
  simp only [CollatzResearch.WordTrace]
  refine ⟨18944402575277375839905281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12629601716851583893270187 18944402575277375839905281)
  ·
    refine ⟨14208301931458031879928961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18944402575277375839905281 14208301931458031879928961)
    ·
      refine ⟨10656226448593523909946721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14208301931458031879928961 10656226448593523909946721)
      ·
        refine ⟨7992169836445142932460041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10656226448593523909946721 7992169836445142932460041)
        ·
          refine ⟨5994127377333857199345031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7992169836445142932460041 5994127377333857199345031)
          ·
            refine ⟨8991191066000785799017547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5994127377333857199345031 8991191066000785799017547)
            ·
              refine ⟨13486786599001178698526321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8991191066000785799017547 13486786599001178698526321)
              ·
                refine ⟨10115089949250884023894741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13486786599001178698526321 10115089949250884023894741)
                ·
                  refine ⟨237072420685567594310033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10115089949250884023894741 237072420685567594310033)
                  ·
                    rfl

theorem cell20_519409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_519409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519409 prefixEnd_519409 := by exact prefixLift 519409
  have htrace : WordTrace (prefixWord ++ tailWord_519409) baseStart_519409 baseEnd_519409 := by
    simpa [prefixWord, tailWord_519409, baseEnd_519409] using wordTrace_append hprefix tailTrace_519409
  have hstable : (prefixWord ++ tailWord_519409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519409).length < 2 ^ (prefixWord ++ tailWord_519409).sum := by decide
  have hdescent : baseEnd_519409 < baseStart_519409 := by decide
  rcases family_descends (prefixWord ++ tailWord_519409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519450 : List Nat := [3, 1, 1, 3, 3, 2, 2, 1, 4]
def baseStart_519450 : Nat := 118140960795 + 519450 * 2 ^ 59
def prefixEnd_519450 : Nat := 4983230072969 + 3 ^ 40 * 519450 * 2
def baseEnd_519450 : Nat := 237091134202753673943199

theorem tailTrace_519450 : CollatzResearch.WordTrace tailWord_519450 prefixEnd_519450 237091134202753673943199 := by
  unfold tailWord_519450
  simp only [CollatzResearch.WordTrace]
  refine ⟨4736474492032209960536951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12630598645419226561431869 4736474492032209960536951)
  ·
    refine ⟨7104711738048314940805427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4736474492032209960536951 7104711738048314940805427)
    ·
      refine ⟨10657067607072472411208141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7104711738048314940805427 10657067607072472411208141)
      ·
        refine ⟨3996400352652177154203053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10657067607072472411208141 3996400352652177154203053)
        ·
          refine ⟨1498650132244566432826145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3996400352652177154203053 1498650132244566432826145)
          ·
            refine ⟨1123987599183424824619609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1498650132244566432826145 1123987599183424824619609)
            ·
              refine ⟨842990699387568618464707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1123987599183424824619609 842990699387568618464707)
              ·
                refine ⟨1264486049081352927697061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 842990699387568618464707 1264486049081352927697061)
                ·
                  refine ⟨237091134202753673943199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1264486049081352927697061 237091134202753673943199)
                  ·
                    rfl

theorem cell20_519450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_519450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519450 prefixEnd_519450 := by exact prefixLift 519450
  have htrace : WordTrace (prefixWord ++ tailWord_519450) baseStart_519450 baseEnd_519450 := by
    simpa [prefixWord, tailWord_519450, baseEnd_519450] using wordTrace_append hprefix tailTrace_519450
  have hstable : (prefixWord ++ tailWord_519450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519450).length < 2 ^ (prefixWord ++ tailWord_519450).sum := by decide
  have hdescent : baseEnd_519450 < baseStart_519450 := by decide
  rcases family_descends (prefixWord ++ tailWord_519450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519474 : List Nat := [3, 2, 1, 1, 4, 3, 2, 4]
def baseStart_519474 : Nat := 118140960795 + 519474 * 2 ^ 59
def prefixEnd_519474 : Nat := 4983230072969 + 3 ^ 40 * 519474 * 2
def baseEnd_519474 : Nat := 79034029485572085714367

theorem tailTrace_519474 : CollatzResearch.WordTrace tailWord_519474 prefixEnd_519474 79034029485572085714367 := by
  unfold tailWord_519474
  simp only [CollatzResearch.WordTrace]
  refine ⟨4736693330010472985255369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12631182213361261294014317 4736693330010472985255369)
  ·
    refine ⟨3552519997507854738941527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4736693330010472985255369 3552519997507854738941527)
    ·
      refine ⟨5328779996261782108412291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3552519997507854738941527 5328779996261782108412291)
      ·
        refine ⟨7993169994392673162618437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5328779996261782108412291 7993169994392673162618437)
        ·
          refine ⟨1498719373948626217990957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7993169994392673162618437 1498719373948626217990957)
          ·
            refine ⟨562019765230734831746609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1498719373948626217990957 562019765230734831746609)
            ·
              refine ⟨421514823923051123809957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 562019765230734831746609 421514823923051123809957)
              ·
                refine ⟨79034029485572085714367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 421514823923051123809957 79034029485572085714367)
                ·
                  rfl

theorem cell20_519474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_519474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519474 prefixEnd_519474 := by exact prefixLift 519474
  have htrace : WordTrace (prefixWord ++ tailWord_519474) baseStart_519474 baseEnd_519474 := by
    simpa [prefixWord, tailWord_519474, baseEnd_519474] using wordTrace_append hprefix tailTrace_519474
  have hstable : (prefixWord ++ tailWord_519474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519474).length < 2 ^ (prefixWord ++ tailWord_519474).sum := by decide
  have hdescent : baseEnd_519474 < baseStart_519474 := by decide
  rcases family_descends (prefixWord ++ tailWord_519474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519501 : List Nat := [1, 6, 1, 3, 2, 1, 1, 1, 4]
def baseStart_519501 : Nat := 118140960795 + 519501 * 2 ^ 59
def prefixEnd_519501 : Nat := 4983230072969 + 3 ^ 40 * 519501 * 2
def baseEnd_519501 : Nat := 237114411992424163242991

theorem tailTrace_519501 : CollatzResearch.WordTrace tailWord_519501 prefixEnd_519501 237114411992424163242991 := by
  unfold tailWord_519501
  simp only [CollatzResearch.WordTrace]
  refine ⟨18947758090944075552254357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12631838727296050368169571 18947758090944075552254357)
  ·
    refine ⟨888176160513003541511923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18947758090944075552254357 888176160513003541511923)
    ·
      refine ⟨1332264240769505312267885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 888176160513003541511923 1332264240769505312267885)
      ·
        refine ⟨499599090288564492100457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1332264240769505312267885 499599090288564492100457)
        ·
          refine ⟨374699317716423369075343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499599090288564492100457 374699317716423369075343)
          ·
            refine ⟨562048976574635053613015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374699317716423369075343 562048976574635053613015)
            ·
              refine ⟨843073464861952580419523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562048976574635053613015 843073464861952580419523)
              ·
                refine ⟨1264610197292928870629285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 843073464861952580419523 1264610197292928870629285)
                ·
                  refine ⟨237114411992424163242991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1264610197292928870629285 237114411992424163242991)
                  ·
                    rfl

theorem cell20_519501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_519501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519501 prefixEnd_519501 := by exact prefixLift 519501
  have htrace : WordTrace (prefixWord ++ tailWord_519501) baseStart_519501 baseEnd_519501 := by
    simpa [prefixWord, tailWord_519501, baseEnd_519501] using wordTrace_append hprefix tailTrace_519501
  have hstable : (prefixWord ++ tailWord_519501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519501).length < 2 ^ (prefixWord ++ tailWord_519501).sum := by decide
  have hdescent : baseEnd_519501 < baseStart_519501 := by decide
  rcases family_descends (prefixWord ++ tailWord_519501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519502 : List Nat := [4, 1, 1, 1, 1, 1, 4, 4, 3]
def baseStart_519502 : Nat := 118140960795 + 519502 * 2 ^ 59
def prefixEnd_519502 : Nat := 4983230072969 + 3 ^ 40 * 519502 * 2
def baseEnd_519502 : Nat := 237114868419672604209653

theorem tailTrace_519502 : CollatzResearch.WordTrace tailWord_519502 prefixEnd_519502 237114868419672604209653 := by
  unfold tailWord_519502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2368474320492556590380095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12631863042626968482027173 2368474320492556590380095)
  ·
    refine ⟨3552711480738834885570143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2368474320492556590380095 3552711480738834885570143)
    ·
      refine ⟨5329067221108252328355215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3552711480738834885570143 5329067221108252328355215)
      ·
        refine ⟨7993600831662378492532823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5329067221108252328355215 7993600831662378492532823)
        ·
          refine ⟨11990401247493567738799235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7993600831662378492532823 11990401247493567738799235)
          ·
            refine ⟨17985601871240351608198853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11990401247493567738799235 17985601871240351608198853)
            ·
              refine ⟨3372300350857565926537285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17985601871240351608198853 3372300350857565926537285)
              ·
                refine ⟨632306315785793611225741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3372300350857565926537285 632306315785793611225741)
                ·
                  refine ⟨237114868419672604209653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 632306315785793611225741 237114868419672604209653)
                  ·
                    rfl

theorem cell20_519502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_519502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519502 prefixEnd_519502 := by exact prefixLift 519502
  have htrace : WordTrace (prefixWord ++ tailWord_519502) baseStart_519502 baseEnd_519502 := by
    simpa [prefixWord, tailWord_519502, baseEnd_519502] using wordTrace_append hprefix tailTrace_519502
  have hstable : (prefixWord ++ tailWord_519502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519502).length < 2 ^ (prefixWord ++ tailWord_519502).sum := by decide
  have hdescent : baseEnd_519502 < baseStart_519502 := by decide
  rcases family_descends (prefixWord ++ tailWord_519502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519505 : List Nat := [1, 2, 2, 1, 4, 1, 5, 2, 2]
def baseStart_519505 : Nat := 118140960795 + 519505 * 2 ^ 59
def prefixEnd_519505 : Nat := 4983230072969 + 3 ^ 40 * 519505 * 2
def baseEnd_519505 : Nat := 237116237701417927109641

theorem tailTrace_519505 : CollatzResearch.WordTrace tailWord_519505 prefixEnd_519505 237116237701417927109641 := by
  unfold tailWord_519505
  simp only [CollatzResearch.WordTrace]
  refine ⟨18947903982929584235399969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12631935988619722823599979 18947903982929584235399969)
  ·
    refine ⟨14210927987197188176549977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18947903982929584235399969 14210927987197188176549977)
    ·
      refine ⟨10658195990397891132412483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14210927987197188176549977 10658195990397891132412483)
      ·
        refine ⟨15987293985596836698618725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10658195990397891132412483 15987293985596836698618725)
        ·
          refine ⟨2997617622299406880991011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15987293985596836698618725 2997617622299406880991011)
          ·
            refine ⟨4496426433449110321486517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2997617622299406880991011 4496426433449110321486517)
            ·
              refine ⟨421539978135854092639361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4496426433449110321486517 421539978135854092639361)
              ·
                refine ⟨316154983601890569479521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 421539978135854092639361 316154983601890569479521)
                ·
                  refine ⟨237116237701417927109641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316154983601890569479521 237116237701417927109641)
                  ·
                    rfl

theorem cell20_519505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 2, 2].length) (baseStart_519505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519505 prefixEnd_519505 := by exact prefixLift 519505
  have htrace : WordTrace (prefixWord ++ tailWord_519505) baseStart_519505 baseEnd_519505 := by
    simpa [prefixWord, tailWord_519505, baseEnd_519505] using wordTrace_append hprefix tailTrace_519505
  have hstable : (prefixWord ++ tailWord_519505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519505).length < 2 ^ (prefixWord ++ tailWord_519505).sum := by decide
  have hdescent : baseEnd_519505 < baseStart_519505 := by decide
  rcases family_descends (prefixWord ++ tailWord_519505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519550 : List Nat := [4, 2, 3, 2, 1, 8]
def baseStart_519550 : Nat := 118140960795 + 519550 * 2 ^ 59
def prefixEnd_519550 : Nat := 4983230072969 + 3 ^ 40 * 519550 * 2
def baseEnd_519550 : Nat := 8782843589911028541091

theorem tailTrace_519550 : CollatzResearch.WordTrace tailWord_519550 prefixEnd_519550 8782843589911028541091 := by
  unfold tailWord_519550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2368693158470819615098513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12633030178511037947192069 2368693158470819615098513)
  ·
    refine ⟨1776519868853114711323885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2368693158470819615098513 1776519868853114711323885)
    ·
      refine ⟨666194950819918016746457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1776519868853114711323885 666194950819918016746457)
      ·
        refine ⟨499646213114938512559843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 666194950819918016746457 499646213114938512559843)
        ·
          refine ⟨749469319672407768839765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499646213114938512559843 749469319672407768839765)
          ·
            refine ⟨8782843589911028541091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 749469319672407768839765 8782843589911028541091)
            ·
              rfl

theorem cell20_519550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 8].length) (baseStart_519550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519550 prefixEnd_519550 := by exact prefixLift 519550
  have htrace : WordTrace (prefixWord ++ tailWord_519550) baseStart_519550 baseEnd_519550 := by
    simpa [prefixWord, tailWord_519550, baseEnd_519550] using wordTrace_append hprefix tailTrace_519550
  have hstable : (prefixWord ++ tailWord_519550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519550).length < 2 ^ (prefixWord ++ tailWord_519550).sum := by decide
  have hdescent : baseEnd_519550 < baseStart_519550 := by decide
  rcases family_descends (prefixWord ++ tailWord_519550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519560 : List Nat := [2, 1, 3, 3, 1, 4, 2, 2, 2]
def baseStart_519560 : Nat := 118140960795 + 519560 * 2 ^ 59
def prefixEnd_519560 : Nat := 4983230072969 + 3 ^ 40 * 519560 * 2
def baseEnd_519560 : Nat := 237141341200082180276083

theorem tailTrace_519560 : CollatzResearch.WordTrace tailWord_519560 prefixEnd_519560 237141341200082180276083 := by
  unfold tailWord_519560
  simp only [CollatzResearch.WordTrace]
  refine ⟨9474954998865164314326067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12633273331820219085768089 9474954998865164314326067)
  ·
    refine ⟨14212432498297746471489101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9474954998865164314326067 14212432498297746471489101)
    ·
      refine ⟨5329662186861654926808413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14212432498297746471489101 5329662186861654926808413)
      ·
        refine ⟨1998623320073120597553155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5329662186861654926808413 1998623320073120597553155)
        ·
          refine ⟨2997934980109680896329733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1998623320073120597553155 2997934980109680896329733)
          ·
            refine ⟨562112808770565168061825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2997934980109680896329733 562112808770565168061825)
            ·
              refine ⟨421584606577923876046369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 562112808770565168061825 421584606577923876046369)
              ·
                refine ⟨316188454933442907034777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 421584606577923876046369 316188454933442907034777)
                ·
                  refine ⟨237141341200082180276083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316188454933442907034777 237141341200082180276083)
                  ·
                    rfl

theorem cell20_519560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 2, 2].length) (baseStart_519560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519560 prefixEnd_519560 := by exact prefixLift 519560
  have htrace : WordTrace (prefixWord ++ tailWord_519560) baseStart_519560 baseEnd_519560 := by
    simpa [prefixWord, tailWord_519560, baseEnd_519560] using wordTrace_append hprefix tailTrace_519560
  have hstable : (prefixWord ++ tailWord_519560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519560).length < 2 ^ (prefixWord ++ tailWord_519560).sum := by decide
  have hdescent : baseEnd_519560 < baseStart_519560 := by decide
  rcases family_descends (prefixWord ++ tailWord_519560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519564 : List Nat := [2, 2, 1, 2, 1, 3, 3, 4, 2]
def baseStart_519564 : Nat := 118140960795 + 519564 * 2 ^ 59
def prefixEnd_519564 : Nat := 4983230072969 + 3 ^ 40 * 519564 * 2
def baseEnd_519564 : Nat := 237143166909075944142733

theorem tailTrace_519564 : CollatzResearch.WordTrace tailWord_519564 prefixEnd_519564 237143166909075944142733 := by
  unfold tailWord_519564
  simp only [CollatzResearch.WordTrace]
  refine ⟨9475027944857918655898873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12633370593143891541198497 9475027944857918655898873)
  ·
    refine ⟨7106270958643438991924155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9475027944857918655898873 7106270958643438991924155)
    ·
      refine ⟨10659406437965158487886233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7106270958643438991924155 10659406437965158487886233)
      ·
        refine ⟨7994554828473868865914675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10659406437965158487886233 7994554828473868865914675)
        ·
          refine ⟨11991832242710803298872013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7994554828473868865914675 11991832242710803298872013)
          ·
            refine ⟨4496937091016551237077005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11991832242710803298872013 4496937091016551237077005)
            ·
              refine ⟨1686351409131206713903877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4496937091016551237077005 1686351409131206713903877)
              ·
                refine ⟨316190889212101258856977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1686351409131206713903877 316190889212101258856977)
                ·
                  refine ⟨237143166909075944142733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316190889212101258856977 237143166909075944142733)
                  ·
                    rfl

theorem cell20_519564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 4, 2].length) (baseStart_519564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519564 prefixEnd_519564 := by exact prefixLift 519564
  have htrace : WordTrace (prefixWord ++ tailWord_519564) baseStart_519564 baseEnd_519564 := by
    simpa [prefixWord, tailWord_519564, baseEnd_519564] using wordTrace_append hprefix tailTrace_519564
  have hstable : (prefixWord ++ tailWord_519564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519564).length < 2 ^ (prefixWord ++ tailWord_519564).sum := by decide
  have hdescent : baseEnd_519564 < baseStart_519564 := by decide
  rcases family_descends (prefixWord ++ tailWord_519564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519578 : List Nat := [3, 1, 1, 4, 1, 1, 1, 5, 3]
def baseStart_519578 : Nat := 118140960795 + 519578 * 2 ^ 59
def prefixEnd_519578 : Nat := 4983230072969 + 3 ^ 40 * 519578 * 2
def baseEnd_519578 : Nat := 237149556890554117676009

theorem tailTrace_519578 : CollatzResearch.WordTrace tailWord_519578 prefixEnd_519578 237149556890554117676009 := by
  unfold tailWord_519578
  simp only [CollatzResearch.WordTrace]
  refine ⟨4737641627916279425701847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12633711007776745135204925 4737641627916279425701847)
  ·
    refine ⟨7106462441874419138552771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4737641627916279425701847 7106462441874419138552771)
    ·
      refine ⟨10659693662811628707829157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7106462441874419138552771 10659693662811628707829157)
      ·
        refine ⟨1998692561777180382717967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10659693662811628707829157 1998692561777180382717967)
        ·
          refine ⟨2998038842665770574076951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1998692561777180382717967 2998038842665770574076951)
          ·
            refine ⟨4497058263998655861115427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2998038842665770574076951 4497058263998655861115427)
            ·
              refine ⟨6745587395997983791673141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4497058263998655861115427 6745587395997983791673141)
              ·
                refine ⟨632398818374810980469357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6745587395997983791673141 632398818374810980469357)
                ·
                  refine ⟨237149556890554117676009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 632398818374810980469357 237149556890554117676009)
                  ·
                    rfl

theorem cell20_519578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_519578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519578 prefixEnd_519578 := by exact prefixLift 519578
  have htrace : WordTrace (prefixWord ++ tailWord_519578) baseStart_519578 baseEnd_519578 := by
    simpa [prefixWord, tailWord_519578, baseEnd_519578] using wordTrace_append hprefix tailTrace_519578
  have hstable : (prefixWord ++ tailWord_519578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519578).length < 2 ^ (prefixWord ++ tailWord_519578).sum := by decide
  have hdescent : baseEnd_519578 < baseStart_519578 := by decide
  rcases family_descends (prefixWord ++ tailWord_519578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519612 : List Nat := [2, 2, 2, 4, 2, 2, 1, 2, 3]
def baseStart_519612 : Nat := 118140960795 + 519612 * 2 ^ 59
def prefixEnd_519612 : Nat := 4983230072969 + 3 ^ 40 * 519612 * 2
def baseEnd_519612 : Nat := 237165075417001110542537

theorem tailTrace_519612 : CollatzResearch.WordTrace tailWord_519612 prefixEnd_519612 237165075417001110542537 := by
  unfold tailWord_519612
  simp only [CollatzResearch.WordTrace]
  refine ⟨9475903296770970754772545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12634537729027961006363393 9475903296770970754772545)
  ·
    refine ⟨7106927472578228066079409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9475903296770970754772545 7106927472578228066079409)
    ·
      refine ⟨5330195604433671049559557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7106927472578228066079409 5330195604433671049559557)
      ·
        refine ⟨999411675831313321792417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5330195604433671049559557 999411675831313321792417)
        ·
          refine ⟨749558756873484991344313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 999411675831313321792417 749558756873484991344313)
          ·
            refine ⟨562169067655113743508235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 749558756873484991344313 562169067655113743508235)
            ·
              refine ⟨843253601482670615262353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562169067655113743508235 843253601482670615262353)
              ·
                refine ⟨632440201112002961446765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 843253601482670615262353 632440201112002961446765)
                ·
                  refine ⟨237165075417001110542537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 632440201112002961446765 237165075417001110542537)
                  ·
                    rfl

theorem cell20_519612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 3].length) (baseStart_519612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519612 prefixEnd_519612 := by exact prefixLift 519612
  have htrace : WordTrace (prefixWord ++ tailWord_519612) baseStart_519612 baseEnd_519612 := by
    simpa [prefixWord, tailWord_519612, baseEnd_519612] using wordTrace_append hprefix tailTrace_519612
  have hstable : (prefixWord ++ tailWord_519612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519612).length < 2 ^ (prefixWord ++ tailWord_519612).sum := by decide
  have hdescent : baseEnd_519612 < baseStart_519612 := by decide
  rcases family_descends (prefixWord ++ tailWord_519612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519616 : List Nat := [2, 1, 1, 2, 3, 1, 5, 2, 3]
def baseStart_519616 : Nat := 118140960795 + 519616 * 2 ^ 59
def prefixEnd_519616 : Nat := 4983230072969 + 3 ^ 40 * 519616 * 2
def baseEnd_519616 : Nat := 237166901125994874409187

theorem tailTrace_519616 : CollatzResearch.WordTrace tailWord_519616 prefixEnd_519616 237166901125994874409187 := by
  unfold tailWord_519616
  simp only [CollatzResearch.WordTrace]
  refine ⟨9475976242763725096345351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12634634990351633461793801 9475976242763725096345351)
  ·
    refine ⟨14213964364145587644518027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9475976242763725096345351 14213964364145587644518027)
    ·
      refine ⟨21320946546218381466777041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14213964364145587644518027 21320946546218381466777041)
      ·
        refine ⟨15990709909663786100082781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21320946546218381466777041 15990709909663786100082781)
        ·
          refine ⟨5996516216123919787531043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15990709909663786100082781 5996516216123919787531043)
          ·
            refine ⟨8994774324185879681296565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5996516216123919787531043 8994774324185879681296565)
            ·
              refine ⟨843260092892426220121553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8994774324185879681296565 843260092892426220121553)
              ·
                refine ⟨632445069669319665091165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 843260092892426220121553 632445069669319665091165)
                ·
                  refine ⟨237166901125994874409187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 632445069669319665091165 237166901125994874409187)
                  ·
                    rfl

theorem cell20_519616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 3].length) (baseStart_519616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519616 prefixEnd_519616 := by exact prefixLift 519616
  have htrace : WordTrace (prefixWord ++ tailWord_519616) baseStart_519616 baseEnd_519616 := by
    simpa [prefixWord, tailWord_519616, baseEnd_519616] using wordTrace_append hprefix tailTrace_519616
  have hstable : (prefixWord ++ tailWord_519616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519616).length < 2 ^ (prefixWord ++ tailWord_519616).sum := by decide
  have hdescent : baseEnd_519616 < baseStart_519616 := by decide
  rcases family_descends (prefixWord ++ tailWord_519616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519623 : List Nat := [1, 1, 4, 1, 1, 3, 4, 1, 4]
def baseStart_519623 : Nat := 118140960795 + 519623 * 2 ^ 59
def prefixEnd_519623 : Nat := 4983230072969 + 3 ^ 40 * 519623 * 2
def baseEnd_519623 : Nat := 237170096116733961175825

theorem tailTrace_519623 : CollatzResearch.WordTrace tailWord_519623 prefixEnd_519623 237170096116733961175825 := by
  unfold tailWord_519623
  simp only [CollatzResearch.WordTrace]
  refine ⟨18952207796502090388195523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12634805197668060258797015 18952207796502090388195523)
  ·
    refine ⟨28428311694753135582293285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18952207796502090388195523 28428311694753135582293285)
    ·
      refine ⟨5330308442766212921679991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28428311694753135582293285 5330308442766212921679991)
      ·
        refine ⟨7995462664149319382519987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5330308442766212921679991 7995462664149319382519987)
        ·
          refine ⟨11993193996223979073779981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7995462664149319382519987 11993193996223979073779981)
          ·
            refine ⟨4497447748583992152667493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11993193996223979073779981 4497447748583992152667493)
            ·
              refine ⟨843271452859498528625155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4497447748583992152667493 843271452859498528625155)
              ·
                refine ⟨1264907179289247792937733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 843271452859498528625155 1264907179289247792937733)
                ·
                  refine ⟨237170096116733961175825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1264907179289247792937733 237170096116733961175825)
                  ·
                    rfl

theorem cell20_519623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 4].length) (baseStart_519623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519623 prefixEnd_519623 := by exact prefixLift 519623
  have htrace : WordTrace (prefixWord ++ tailWord_519623) baseStart_519623 baseEnd_519623 := by
    simpa [prefixWord, tailWord_519623, baseEnd_519623] using wordTrace_append hprefix tailTrace_519623
  have hstable : (prefixWord ++ tailWord_519623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519623).length < 2 ^ (prefixWord ++ tailWord_519623).sum := by decide
  have hdescent : baseEnd_519623 < baseStart_519623 := by decide
  rcases family_descends (prefixWord ++ tailWord_519623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519733 : List Nat := [1, 3, 3, 1, 1, 3, 4, 2, 2]
def baseStart_519733 : Nat := 118140960795 + 519733 * 2 ^ 59
def prefixEnd_519733 : Nat := 4983230072969 + 3 ^ 40 * 519733 * 2
def baseEnd_519733 : Nat := 237220303114062467508709

theorem tailTrace_519733 : CollatzResearch.WordTrace tailWord_519733 prefixEnd_519733 237220303114062467508709 := by
  unfold tailWord_519733
  simp only [CollatzResearch.WordTrace]
  refine ⟨18956219826103579174699853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12637479884069052783133235 18956219826103579174699853)
  ·
    refine ⟨7108582434788842190512445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18956219826103579174699853 7108582434788842190512445)
    ·
      refine ⟨2665718413045815821442167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7108582434788842190512445 2665718413045815821442167)
      ·
        refine ⟨3998577619568723732163251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2665718413045815821442167 3998577619568723732163251)
        ·
          refine ⟨5997866429353085598244877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3998577619568723732163251 5997866429353085598244877)
          ·
            refine ⟨2249199911007407099341829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5997866429353085598244877 2249199911007407099341829)
            ·
              refine ⟨421724983313888831126593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2249199911007407099341829 421724983313888831126593)
              ·
                refine ⟨316293737485416623344945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 421724983313888831126593 316293737485416623344945)
                ·
                  refine ⟨237220303114062467508709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316293737485416623344945 237220303114062467508709)
                  ·
                    rfl

theorem cell20_519733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 4, 2, 2].length) (baseStart_519733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519733 prefixEnd_519733 := by exact prefixLift 519733
  have htrace : WordTrace (prefixWord ++ tailWord_519733) baseStart_519733 baseEnd_519733 := by
    simpa [prefixWord, tailWord_519733, baseEnd_519733] using wordTrace_append hprefix tailTrace_519733
  have hstable : (prefixWord ++ tailWord_519733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519733).length < 2 ^ (prefixWord ++ tailWord_519733).sum := by decide
  have hdescent : baseEnd_519733 < baseStart_519733 := by decide
  rcases family_descends (prefixWord ++ tailWord_519733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519740 : List Nat := [2, 2, 2, 2, 5, 1, 1, 5]
def baseStart_519740 : Nat := 118140960795 + 519740 * 2 ^ 59
def prefixEnd_519740 : Nat := 4983230072969 + 3 ^ 40 * 519740 * 2
def baseEnd_519740 : Nat := 79074499368267184758449

theorem tailTrace_519740 : CollatzResearch.WordTrace tailWord_519740 prefixEnd_519740 79074499368267184758449 := by
  unfold tailWord_519740
  simp only [CollatzResearch.WordTrace]
  refine ⟨9478237568539109685102337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12637650091385479580136449 9478237568539109685102337)
  ·
    refine ⟨7108678176404332263826753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9478237568539109685102337 7108678176404332263826753)
    ·
      refine ⟨5331508632303249197870065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7108678176404332263826753 5331508632303249197870065)
      ·
        refine ⟨3998631474227436898402549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5331508632303249197870065 3998631474227436898402549)
        ·
          refine ⟨374871700708822209225239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3998631474227436898402549 374871700708822209225239)
          ·
            refine ⟨562307551063233313837859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374871700708822209225239 562307551063233313837859)
            ·
              refine ⟨843461326594849970756789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562307551063233313837859 843461326594849970756789)
              ·
                refine ⟨79074499368267184758449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 843461326594849970756789 79074499368267184758449)
                ·
                  rfl

theorem cell20_519740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 5].length) (baseStart_519740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519740 prefixEnd_519740 := by exact prefixLift 519740
  have htrace : WordTrace (prefixWord ++ tailWord_519740) baseStart_519740 baseEnd_519740 := by
    simpa [prefixWord, tailWord_519740, baseEnd_519740] using wordTrace_append hprefix tailTrace_519740
  have hstable : (prefixWord ++ tailWord_519740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519740).length < 2 ^ (prefixWord ++ tailWord_519740).sum := by decide
  have hdescent : baseEnd_519740 < baseStart_519740 := by decide
  rcases family_descends (prefixWord ++ tailWord_519740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519792 : List Nat := [2, 1, 1, 1, 6, 1, 2, 4, 2]
def baseStart_519792 : Nat := 118140960795 + 519792 * 2 ^ 59
def prefixEnd_519792 : Nat := 4983230072969 + 3 ^ 40 * 519792 * 2
def baseEnd_519792 : Nat := 237247232321720484541801

theorem tailTrace_519792 : CollatzResearch.WordTrace tailWord_519792 prefixEnd_519792 237247232321720484541801 := by
  unfold tailWord_519792
  simp only [CollatzResearch.WordTrace]
  refine ⟨9479185866444916125548815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12638914488593221500731753 9479185866444916125548815)
  ·
    refine ⟨14218778799667374188323223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9479185866444916125548815 14218778799667374188323223)
    ·
      refine ⟨21328168199501061282484835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14218778799667374188323223 21328168199501061282484835)
      ·
        refine ⟨31992252299251591923727253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21328168199501061282484835 31992252299251591923727253)
        ·
          refine ⟨1499636826527418371424715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31992252299251591923727253 1499636826527418371424715)
          ·
            refine ⟨2249455239791127557137073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1499636826527418371424715 2249455239791127557137073)
            ·
              refine ⟨1687091429843345667852805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2249455239791127557137073 1687091429843345667852805)
              ·
                refine ⟨316329643095627312722401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1687091429843345667852805 316329643095627312722401)
                ·
                  refine ⟨237247232321720484541801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316329643095627312722401 237247232321720484541801)
                  ·
                    rfl

theorem cell20_519792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 4, 2].length) (baseStart_519792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519792 prefixEnd_519792 := by exact prefixLift 519792
  have htrace : WordTrace (prefixWord ++ tailWord_519792) baseStart_519792 baseEnd_519792 := by
    simpa [prefixWord, tailWord_519792, baseEnd_519792] using wordTrace_append hprefix tailTrace_519792
  have hstable : (prefixWord ++ tailWord_519792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519792).length < 2 ^ (prefixWord ++ tailWord_519792).sum := by decide
  have hdescent : baseEnd_519792 < baseStart_519792 := by decide
  rcases family_descends (prefixWord ++ tailWord_519792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519803 : List Nat := [1, 1, 1, 1, 1, 4, 4, 7]
def baseStart_519803 : Nat := 118140960795 + 519803 * 2 ^ 59
def prefixEnd_519803 : Nat := 4983230072969 + 3 ^ 40 * 519803 * 2
def baseEnd_519803 : Nat := 79084084340484445058363

theorem tailTrace_519803 : CollatzResearch.WordTrace tailWord_519803 prefixEnd_519803 79084084340484445058363 := by
  unfold tailWord_519803
  simp only [CollatzResearch.WordTrace]
  refine ⟨18958772935849981129748063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12639181957233320753165375 18958772935849981129748063)
  ·
    refine ⟨28438159403774971694622095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18958772935849981129748063 28438159403774971694622095)
    ·
      refine ⟨42657239105662457541933143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28438159403774971694622095 42657239105662457541933143)
      ·
        refine ⟨63985858658493686312899715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42657239105662457541933143 63985858658493686312899715)
        ·
          refine ⟨95978787987740529469349573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63985858658493686312899715 95978787987740529469349573)
          ·
            refine ⟨17996022747701349275503045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95978787987740529469349573 17996022747701349275503045)
            ·
              refine ⟨3374254265194002989156821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17996022747701349275503045 3374254265194002989156821)
              ·
                refine ⟨79084084340484445058363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3374254265194002989156821 79084084340484445058363)
                ·
                  rfl

theorem cell20_519803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 7].length) (baseStart_519803 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519803 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519803 prefixEnd_519803 := by exact prefixLift 519803
  have htrace : WordTrace (prefixWord ++ tailWord_519803) baseStart_519803 baseEnd_519803 := by
    simpa [prefixWord, tailWord_519803, baseEnd_519803] using wordTrace_append hprefix tailTrace_519803
  have hstable : (prefixWord ++ tailWord_519803).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519803).length < 2 ^ (prefixWord ++ tailWord_519803).sum := by decide
  have hdescent : baseEnd_519803 < baseStart_519803 := by decide
  rcases family_descends (prefixWord ++ tailWord_519803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519826 : List Nat := [3, 2, 3, 1, 3, 2, 1, 3, 2]
def baseStart_519826 : Nat := 118140960795 + 519826 * 2 ^ 59
def prefixEnd_519826 : Nat := 4983230072969 + 3 ^ 40 * 519826 * 2
def baseEnd_519826 : Nat := 237262750848167477408329

theorem tailTrace_519826 : CollatzResearch.WordTrace tailWord_519826 prefixEnd_519826 237262750848167477408329 := by
  unfold tailWord_519826
  simp only [CollatzResearch.WordTrace]
  refine ⟨4739902953691664014458833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12639741209844437371890221 4739902953691664014458833)
  ·
    refine ⟨3554927215268748010844125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4739902953691664014458833 3554927215268748010844125)
    ·
      refine ⟨1333097705725780504066547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3554927215268748010844125 1333097705725780504066547)
      ·
        refine ⟨1999646558588670756099821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1333097705725780504066547 1999646558588670756099821)
        ·
          refine ⟨749867459470751533537433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1999646558588670756099821 749867459470751533537433)
          ·
            refine ⟨562400594603063650153075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 749867459470751533537433 562400594603063650153075)
            ·
              refine ⟨843600891904595475229613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562400594603063650153075 843600891904595475229613)
              ·
                refine ⟨316350334464223303211105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 843600891904595475229613 316350334464223303211105)
                ·
                  refine ⟨237262750848167477408329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316350334464223303211105 237262750848167477408329)
                  ·
                    rfl

theorem cell20_519826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_519826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519826 prefixEnd_519826 := by exact prefixLift 519826
  have htrace : WordTrace (prefixWord ++ tailWord_519826) baseStart_519826 baseEnd_519826 := by
    simpa [prefixWord, tailWord_519826, baseEnd_519826] using wordTrace_append hprefix tailTrace_519826
  have hstable : (prefixWord ++ tailWord_519826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519826).length < 2 ^ (prefixWord ++ tailWord_519826).sum := by decide
  have hdescent : baseEnd_519826 < baseStart_519826 := by decide
  rcases family_descends (prefixWord ++ tailWord_519826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519854 : List Nat := [4, 1, 4, 1, 2, 1, 2, 5]
def baseStart_519854 : Nat := 118140960795 + 519854 * 2 ^ 59
def prefixEnd_519854 : Nat := 4983230072969 + 3 ^ 40 * 519854 * 2
def baseEnd_519854 : Nat := 79091843603707941491627

theorem tailTrace_519854 : CollatzResearch.WordTrace tailWord_519854 prefixEnd_519854 79091843603707941491627 := by
  unfold tailWord_519854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2370079132333152104981827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12640422039110144559903077 2370079132333152104981827)
  ·
    refine ⟨3555118698499728157472741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2370079132333152104981827 3555118698499728157472741)
    ·
      refine ⟨666584755968699029526139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3555118698499728157472741 666584755968699029526139)
      ·
        refine ⟨999877133953048544289209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666584755968699029526139 999877133953048544289209)
        ·
          refine ⟨749907850464786408216907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 999877133953048544289209 749907850464786408216907)
          ·
            refine ⟨1124861775697179612325361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749907850464786408216907 1124861775697179612325361)
            ·
              refine ⟨843646331772884709244021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1124861775697179612325361 843646331772884709244021)
              ·
                refine ⟨79091843603707941491627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 843646331772884709244021 79091843603707941491627)
                ·
                  rfl

theorem cell20_519854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_519854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519854 prefixEnd_519854 := by exact prefixLift 519854
  have htrace : WordTrace (prefixWord ++ tailWord_519854) baseStart_519854 baseEnd_519854 := by
    simpa [prefixWord, tailWord_519854, baseEnd_519854] using wordTrace_append hprefix tailTrace_519854
  have hstable : (prefixWord ++ tailWord_519854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519854).length < 2 ^ (prefixWord ++ tailWord_519854).sum := by decide
  have hdescent : baseEnd_519854 < baseStart_519854 := by decide
  rcases family_descends (prefixWord ++ tailWord_519854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519861 : List Nat := [1, 3, 3, 3, 2, 1, 1, 3, 3]
def baseStart_519861 : Nat := 118140960795 + 519861 * 2 ^ 59
def prefixEnd_519861 : Nat := 4983230072969 + 3 ^ 40 * 519861 * 2
def baseEnd_519861 : Nat := 237278725801862911241519

theorem tailTrace_519861 : CollatzResearch.WordTrace tailWord_519861 prefixEnd_519861 237278725801862911241519 := by
  unfold tailWord_519861
  simp only [CollatzResearch.WordTrace]
  refine ⟨18960888369639857035359437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12640592246426571356906291 18960888369639857035359437)
  ·
    refine ⟨7110333138614946388259789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18960888369639857035359437 7110333138614946388259789)
    ·
      refine ⟨2666374926980604895597421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7110333138614946388259789 2666374926980604895597421)
      ·
        refine ⟨999890597617726835849033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2666374926980604895597421 999890597617726835849033)
        ·
          refine ⟨749917948213295126886775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 999890597617726835849033 749917948213295126886775)
          ·
            refine ⟨1124876922319942690330163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749917948213295126886775 1124876922319942690330163)
            ·
              refine ⟨1687315383479914035495245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1124876922319942690330163 1687315383479914035495245)
              ·
                refine ⟨632743268804967763310717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1687315383479914035495245 632743268804967763310717)
                ·
                  refine ⟨237278725801862911241519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 632743268804967763310717 237278725801862911241519)
                  ·
                    rfl

theorem cell20_519861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_519861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519861 prefixEnd_519861 := by exact prefixLift 519861
  have htrace : WordTrace (prefixWord ++ tailWord_519861) baseStart_519861 baseEnd_519861 := by
    simpa [prefixWord, tailWord_519861, baseEnd_519861] using wordTrace_append hprefix tailTrace_519861
  have hstable : (prefixWord ++ tailWord_519861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519861).length < 2 ^ (prefixWord ++ tailWord_519861).sum := by decide
  have hdescent : baseEnd_519861 < baseStart_519861 := by decide
  rcases family_descends (prefixWord ++ tailWord_519861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519872 : List Nat := [2, 1, 1, 2, 4, 1, 2, 1, 6]
def baseStart_519872 : Nat := 118140960795 + 519872 * 2 ^ 59
def prefixEnd_519872 : Nat := 4983230072969 + 3 ^ 40 * 519872 * 2
def baseEnd_519872 : Nat := 237283746501595761874807

theorem tailTrace_519872 : CollatzResearch.WordTrace tailWord_519872 prefixEnd_519872 237283746501595761874807 := by
  unfold tailWord_519872
  simp only [CollatzResearch.WordTrace]
  refine ⟨9480644786300002957004935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12640859715066670609339913 9480644786300002957004935)
  ·
    refine ⟨14220967179450004435507403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9480644786300002957004935 14220967179450004435507403)
    ·
      refine ⟨21331450769175006653261105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14220967179450004435507403 21331450769175006653261105)
      ·
        refine ⟨15998588076881254989945829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21331450769175006653261105 15998588076881254989945829)
        ·
          refine ⟨2999735264415235310614843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15998588076881254989945829 2999735264415235310614843)
          ·
            refine ⟨4499602896622852965922265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2999735264415235310614843 4499602896622852965922265)
            ·
              refine ⟨3374702172467139724441699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4499602896622852965922265 3374702172467139724441699)
              ·
                refine ⟨5062053258700709586662549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3374702172467139724441699 5062053258700709586662549)
                ·
                  refine ⟨237283746501595761874807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5062053258700709586662549 237283746501595761874807)
                  ·
                    rfl

theorem cell20_519872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_519872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519872 prefixEnd_519872 := by exact prefixLift 519872
  have htrace : WordTrace (prefixWord ++ tailWord_519872) baseStart_519872 baseEnd_519872 := by
    simpa [prefixWord, tailWord_519872, baseEnd_519872] using wordTrace_append hprefix tailTrace_519872
  have hstable : (prefixWord ++ tailWord_519872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519872).length < 2 ^ (prefixWord ++ tailWord_519872).sum := by decide
  have hdescent : baseEnd_519872 < baseStart_519872 := by decide
  rcases family_descends (prefixWord ++ tailWord_519872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519879 : List Nat := [1, 1, 4, 1, 1, 1, 3, 8]
def baseStart_519879 : Nat := 118140960795 + 519879 * 2 ^ 59
def prefixEnd_519879 : Nat := 4983230072969 + 3 ^ 40 * 519879 * 2
def baseEnd_519879 : Nat := 79095647164111616213815

theorem tailTrace_519879 : CollatzResearch.WordTrace tailWord_519879 prefixEnd_519879 79095647164111616213815 := by
  unfold tailWord_519879
  simp only [CollatzResearch.WordTrace]
  refine ⟨18961544883574646109514691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12641029922383097406343127 18961544883574646109514691)
  ·
    refine ⟨28442317325361969164272037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18961544883574646109514691 28442317325361969164272037)
    ·
      refine ⟨5332934498505369218301007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28442317325361969164272037 5332934498505369218301007)
      ·
        refine ⟨7999401747758053827451511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5332934498505369218301007 7999401747758053827451511)
        ·
          refine ⟨11999102621637080741177267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7999401747758053827451511 11999102621637080741177267)
          ·
            refine ⟨17998653932455621111765901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11999102621637080741177267 17998653932455621111765901)
            ·
              refine ⟨6749495224670857916912213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17998653932455621111765901 6749495224670857916912213)
              ·
                refine ⟨79095647164111616213815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6749495224670857916912213 79095647164111616213815)
                ·
                  rfl

theorem cell20_519879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 8].length) (baseStart_519879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519879 prefixEnd_519879 := by exact prefixLift 519879
  have htrace : WordTrace (prefixWord ++ tailWord_519879) baseStart_519879 baseEnd_519879 := by
    simpa [prefixWord, tailWord_519879, baseEnd_519879] using wordTrace_append hprefix tailTrace_519879
  have hstable : (prefixWord ++ tailWord_519879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519879).length < 2 ^ (prefixWord ++ tailWord_519879).sum := by decide
  have hdescent : baseEnd_519879 < baseStart_519879 := by decide
  rcases family_descends (prefixWord ++ tailWord_519879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519944 : List Nat := [2, 1, 3, 2, 2, 1, 4, 3, 2]
def baseStart_519944 : Nat := 118140960795 + 519944 * 2 ^ 59
def prefixEnd_519944 : Nat := 4983230072969 + 3 ^ 40 * 519944 * 2
def baseEnd_519944 : Nat := 237316609263483511474513

theorem tailTrace_519944 : CollatzResearch.WordTrace tailWord_519944 prefixEnd_519944 237316609263483511474513 := by
  unfold tailWord_519944
  simp only [CollatzResearch.WordTrace]
  refine ⟨9481957814169581105315443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12642610418892774807087257 9481957814169581105315443)
  ·
    refine ⟨14222936721254371657973165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9481957814169581105315443 14222936721254371657973165)
    ·
      refine ⟨5333601270470389371739937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14222936721254371657973165 5333601270470389371739937)
      ·
        refine ⟨4000200952852792028804953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5333601270470389371739937 4000200952852792028804953)
        ·
          refine ⟨3000150714639594021603715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4000200952852792028804953 3000150714639594021603715)
          ·
            refine ⟨4500226071959391032405573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3000150714639594021603715 4500226071959391032405573)
            ·
              refine ⟨843792388492385818576045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4500226071959391032405573 843792388492385818576045)
              ·
                refine ⟨316422145684644681966017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 843792388492385818576045 316422145684644681966017)
                ·
                  refine ⟨237316609263483511474513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316422145684644681966017 237316609263483511474513)
                  ·
                    rfl

theorem cell20_519944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 3, 2].length) (baseStart_519944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519944 prefixEnd_519944 := by exact prefixLift 519944
  have htrace : WordTrace (prefixWord ++ tailWord_519944) baseStart_519944 baseEnd_519944 := by
    simpa [prefixWord, tailWord_519944, baseEnd_519944] using wordTrace_append hprefix tailTrace_519944
  have hstable : (prefixWord ++ tailWord_519944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519944).length < 2 ^ (prefixWord ++ tailWord_519944).sum := by decide
  have hdescent : baseEnd_519944 < baseStart_519944 := by decide
  rcases family_descends (prefixWord ++ tailWord_519944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519954 : List Nat := [3, 2, 4, 1, 1, 3, 1, 2, 3]
def baseStart_519954 : Nat := 118140960795 + 519954 * 2 ^ 59
def prefixEnd_519954 : Nat := 4983230072969 + 3 ^ 40 * 519954 * 2
def baseEnd_519954 : Nat := 237321173535967921141139

theorem tailTrace_519954 : CollatzResearch.WordTrace tailWord_519954 prefixEnd_519954 237321173535967921141139 := by
  unfold tailWord_519954
  simp only [CollatzResearch.WordTrace]
  refine ⟨4741070089575733479623729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12642853572201955945663277 4741070089575733479623729)
  ·
    refine ⟨3555802567181800109717797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4741070089575733479623729 3555802567181800109717797)
    ·
      refine ⟨666712981346587520572087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3555802567181800109717797 666712981346587520572087)
      ·
        refine ⟨1000069472019881280858131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666712981346587520572087 1000069472019881280858131)
        ·
          refine ⟨1500104208029821921287197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1000069472019881280858131 1500104208029821921287197)
          ·
            refine ⟨562539078011183220482699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1500104208029821921287197 562539078011183220482699)
            ·
              refine ⟨843808617016774830724049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562539078011183220482699 843808617016774830724049)
              ·
                refine ⟨632856462762581123043037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 843808617016774830724049 632856462762581123043037)
                ·
                  refine ⟨237321173535967921141139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 632856462762581123043037 237321173535967921141139)
                  ·
                    rfl

theorem cell20_519954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_519954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519954 prefixEnd_519954 := by exact prefixLift 519954
  have htrace : WordTrace (prefixWord ++ tailWord_519954) baseStart_519954 baseEnd_519954 := by
    simpa [prefixWord, tailWord_519954, baseEnd_519954] using wordTrace_append hprefix tailTrace_519954
  have hstable : (prefixWord ++ tailWord_519954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519954).length < 2 ^ (prefixWord ++ tailWord_519954).sum := by decide
  have hdescent : baseEnd_519954 < baseStart_519954 := by decide
  rcases family_descends (prefixWord ++ tailWord_519954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_519999 : List Nat := [1, 1, 2, 2, 6, 2, 1, 3, 2]
def baseStart_519999 : Nat := 118140960795 + 519999 * 2 ^ 59
def prefixEnd_519999 : Nat := 4983230072969 + 3 ^ 40 * 519999 * 2
def baseEnd_519999 : Nat := 237341712762147764640955

theorem tailTrace_519999 : CollatzResearch.WordTrace tailWord_519999 prefixEnd_519999 237341712762147764640955 := by
  unfold tailWord_519999
  simp only [CollatzResearch.WordTrace]
  refine ⟨18965921643139906603883051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12643947762093271069255367 18965921643139906603883051)
  ·
    refine ⟨28448882464709859905824577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18965921643139906603883051 28448882464709859905824577)
    ·
      refine ⟨21336661848532394929368433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28448882464709859905824577 21336661848532394929368433)
      ·
        refine ⟨16002496386399296197026325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21336661848532394929368433 16002496386399296197026325)
        ·
          refine ⟨750117018112467009235609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16002496386399296197026325 750117018112467009235609)
          ·
            refine ⟨562587763584350256926707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 750117018112467009235609 562587763584350256926707)
            ·
              refine ⟨843881645376525385390061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562587763584350256926707 843881645376525385390061)
              ·
                refine ⟨316455617016197019521273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 843881645376525385390061 316455617016197019521273)
                ·
                  refine ⟨237341712762147764640955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316455617016197019521273 237341712762147764640955)
                  ·
                    rfl

theorem cell20_519999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 3, 2].length) (baseStart_519999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_519999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_519999 prefixEnd_519999 := by exact prefixLift 519999
  have htrace : WordTrace (prefixWord ++ tailWord_519999) baseStart_519999 baseEnd_519999 := by
    simpa [prefixWord, tailWord_519999, baseEnd_519999] using wordTrace_append hprefix tailTrace_519999
  have hstable : (prefixWord ++ tailWord_519999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_519999).length < 2 ^ (prefixWord ++ tailWord_519999).sum := by decide
  have hdescent : baseEnd_519999 < baseStart_519999 := by decide
  rcases family_descends (prefixWord ++ tailWord_519999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520006 : List Nat := [6, 1, 1, 2, 1, 3, 6]
def baseStart_520006 : Nat := 118140960795 + 520006 * 2 ^ 59
def prefixEnd_520006 : Nat := 4983230072969 + 3 ^ 40 * 520006 * 2
def baseEnd_520006 : Nat := 26371656416987427934177

theorem tailTrace_520006 : CollatzResearch.WordTrace tailWord_520006 prefixEnd_520006 26371656416987427934177 := by
  unfold tailWord_520006
  simp only [CollatzResearch.WordTrace]
  refine ⟨592693029816079587480871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12644117969409697866258581 592693029816079587480871)
  ·
    refine ⟨889039544724119381221307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 592693029816079587480871 889039544724119381221307)
    ·
      refine ⟨1333559317086179071831961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 889039544724119381221307 1333559317086179071831961)
      ·
        refine ⟨1000169487814634303873971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1333559317086179071831961 1000169487814634303873971)
        ·
          refine ⟨1500254231721951455810957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1000169487814634303873971 1500254231721951455810957)
          ·
            refine ⟨562595336895731795929109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1500254231721951455810957 562595336895731795929109)
            ·
              refine ⟨26371656416987427934177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 562595336895731795929109 26371656416987427934177)
              ·
                rfl

theorem cell20_520006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 6].length) (baseStart_520006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520006 prefixEnd_520006 := by exact prefixLift 520006
  have htrace : WordTrace (prefixWord ++ tailWord_520006) baseStart_520006 baseEnd_520006 := by
    simpa [prefixWord, tailWord_520006, baseEnd_520006] using wordTrace_append hprefix tailTrace_520006
  have hstable : (prefixWord ++ tailWord_520006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520006).length < 2 ^ (prefixWord ++ tailWord_520006).sum := by decide
  have hdescent : baseEnd_520006 < baseStart_520006 := by decide
  rcases family_descends (prefixWord ++ tailWord_520006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520017 : List Nat := [1, 2, 2, 1, 5, 1, 2, 1, 5]
def baseStart_520017 : Nat := 118140960795 + 520017 * 2 ^ 59
def prefixEnd_520017 : Nat := 4983230072969 + 3 ^ 40 * 520017 * 2
def baseEnd_520017 : Nat := 237349928452619702040881

theorem tailTrace_520017 : CollatzResearch.WordTrace tailWord_520017 prefixEnd_520017 237349928452619702040881 := by
  unfold tailWord_520017
  simp only [CollatzResearch.WordTrace]
  refine ⟨18966578157074695678038305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12644385438049797118692203 18966578157074695678038305)
  ·
    refine ⟨14224933617806021758528729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18966578157074695678038305 14224933617806021758528729)
    ·
      refine ⟨10668700213354516318896547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14224933617806021758528729 10668700213354516318896547)
      ·
        refine ⟨16003050320031774478344821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10668700213354516318896547 16003050320031774478344821)
        ·
          refine ⟨1500285967502978857344827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16003050320031774478344821 1500285967502978857344827)
          ·
            refine ⟨2250428951254468286017241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1500285967502978857344827 2250428951254468286017241)
            ·
              refine ⟨1687821713440851214512931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2250428951254468286017241 1687821713440851214512931)
              ·
                refine ⟨2531732570161276821769397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1687821713440851214512931 2531732570161276821769397)
                ·
                  refine ⟨237349928452619702040881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2531732570161276821769397 237349928452619702040881)
                  ·
                    rfl

theorem cell20_520017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_520017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520017 prefixEnd_520017 := by exact prefixLift 520017
  have htrace : WordTrace (prefixWord ++ tailWord_520017) baseStart_520017 baseEnd_520017 := by
    simpa [prefixWord, tailWord_520017, baseEnd_520017] using wordTrace_append hprefix tailTrace_520017
  have hstable : (prefixWord ++ tailWord_520017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520017).length < 2 ^ (prefixWord ++ tailWord_520017).sum := by decide
  have hdescent : baseEnd_520017 < baseStart_520017 := by decide
  rcases family_descends (prefixWord ++ tailWord_520017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520020 : List Nat := [2, 4, 1, 1, 3, 3, 1, 1, 4]
def baseStart_520020 : Nat := 118140960795 + 520020 * 2 ^ 59
def prefixEnd_520020 : Nat := 4983230072969 + 3 ^ 40 * 520020 * 2
def baseEnd_520020 : Nat := 237351297734365024940869

theorem tailTrace_520020 : CollatzResearch.WordTrace tailWord_520020 prefixEnd_520020 237351297734365024940869 := by
  unfold tailWord_520020
  simp only [CollatzResearch.WordTrace]
  refine ⟨9483343788031913595198757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12644458384042551460265009 9483343788031913595198757)
  ·
    refine ⟨1778126960255983799099767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9483343788031913595198757 1778126960255983799099767)
    ·
      refine ⟨2667190440383975698649651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1778126960255983799099767 2667190440383975698649651)
      ·
        refine ⟨4000785660575963547974477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2667190440383975698649651 4000785660575963547974477)
        ·
          refine ⟨1500294622715986330490429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4000785660575963547974477 1500294622715986330490429)
          ·
            refine ⟨562610483518494873933911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1500294622715986330490429 562610483518494873933911)
            ·
              refine ⟨843915725277742310900867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562610483518494873933911 843915725277742310900867)
              ·
                refine ⟨1265873587916613466351301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 843915725277742310900867 1265873587916613466351301)
                ·
                  refine ⟨237351297734365024940869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1265873587916613466351301 237351297734365024940869)
                  ·
                    rfl

theorem cell20_520020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_520020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520020 prefixEnd_520020 := by exact prefixLift 520020
  have htrace : WordTrace (prefixWord ++ tailWord_520020) baseStart_520020 baseEnd_520020 := by
    simpa [prefixWord, tailWord_520020, baseEnd_520020] using wordTrace_append hprefix tailTrace_520020
  have hstable : (prefixWord ++ tailWord_520020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520020).length < 2 ^ (prefixWord ++ tailWord_520020).sum := by decide
  have hdescent : baseEnd_520020 < baseStart_520020 := by decide
  rcases family_descends (prefixWord ++ tailWord_520020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520031 : List Nat := [1, 1, 2, 3, 1, 4, 1, 7]
def baseStart_520031 : Nat := 118140960795 + 520031 * 2 ^ 59
def prefixEnd_520031 : Nat := 4983230072969 + 3 ^ 40 * 520031 * 2
def baseEnd_520031 : Nat := 79118772811365958524719

theorem tailTrace_520031 : CollatzResearch.WordTrace tailWord_520031 prefixEnd_520031 79118772811365958524719 := by
  unfold tailWord_520031
  simp only [CollatzResearch.WordTrace]
  refine ⟨18967088779023976069047947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12644725852682650712698631 18967088779023976069047947)
  ·
    refine ⟨28450633168535964103571921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18967088779023976069047947 28450633168535964103571921)
    ·
      refine ⟨21337974876401973077678941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28450633168535964103571921 21337974876401973077678941)
      ·
        refine ⟨8001740578650739904129603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21337974876401973077678941 8001740578650739904129603)
        ·
          refine ⟨12002610867976109856194405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8001740578650739904129603 12002610867976109856194405)
          ·
            refine ⟨2250489537745520598036451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12002610867976109856194405 2250489537745520598036451)
            ·
              refine ⟨3375734306618280897054677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2250489537745520598036451 3375734306618280897054677)
              ·
                refine ⟨79118772811365958524719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3375734306618280897054677 79118772811365958524719)
                ·
                  rfl

theorem cell20_520031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 7].length) (baseStart_520031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520031 prefixEnd_520031 := by exact prefixLift 520031
  have htrace : WordTrace (prefixWord ++ tailWord_520031) baseStart_520031 baseEnd_520031 := by
    simpa [prefixWord, tailWord_520031, baseEnd_520031] using wordTrace_append hprefix tailTrace_520031
  have hstable : (prefixWord ++ tailWord_520031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520031).length < 2 ^ (prefixWord ++ tailWord_520031).sum := by decide
  have hdescent : baseEnd_520031 < baseStart_520031 := by decide
  rcases family_descends (prefixWord ++ tailWord_520031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520065 : List Nat := [1, 2, 4, 4, 2, 7]
def baseStart_520065 : Nat := 118140960795 + 520065 * 2 ^ 59
def prefixEnd_520065 : Nat := 4983230072969 + 3 ^ 40 * 520065 * 2
def baseEnd_520065 : Nat := 8791549517057217349655

theorem tailTrace_520065 : CollatzResearch.WordTrace tailWord_520065 prefixEnd_520065 8791549517057217349655 := by
  unfold tailWord_520065
  simp only [CollatzResearch.WordTrace]
  refine ⟨18968328860900799875785649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12645552573933866583857099 18968328860900799875785649)
  ·
    refine ⟨14226246645675599906839237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18968328860900799875785649 14226246645675599906839237)
    ·
      refine ⟨2667421246064174982532357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14226246645675599906839237 2667421246064174982532357)
      ·
        refine ⟨500141483637032809224817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2667421246064174982532357 500141483637032809224817)
        ·
          refine ⟨375106112727774606918613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 500141483637032809224817 375106112727774606918613)
          ·
            refine ⟨8791549517057217349655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 375106112727774606918613 8791549517057217349655)
            ·
              rfl

theorem cell20_520065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 7].length) (baseStart_520065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520065 prefixEnd_520065 := by exact prefixLift 520065
  have htrace : WordTrace (prefixWord ++ tailWord_520065) baseStart_520065 baseEnd_520065 := by
    simpa [prefixWord, tailWord_520065, baseEnd_520065] using wordTrace_append hprefix tailTrace_520065
  have hstable : (prefixWord ++ tailWord_520065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520065).length < 2 ^ (prefixWord ++ tailWord_520065).sum := by decide
  have hdescent : baseEnd_520065 < baseStart_520065 := by decide
  rcases family_descends (prefixWord ++ tailWord_520065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520100 : List Nat := [2, 3, 1, 2, 1, 3, 1, 1, 6]
def baseStart_520100 : Nat := 118140960795 + 520100 * 2 ^ 59
def prefixEnd_520100 : Nat := 4983230072969 + 3 ^ 40 * 520100 * 2
def baseEnd_520100 : Nat := 237387811914240302273875

theorem tailTrace_520100 : CollatzResearch.WordTrace tailWord_520100 prefixEnd_520100 237387811914240302273875 := by
  unfold tailWord_520100
  simp only [CollatzResearch.WordTrace]
  refine ⟨9484802707887000426654877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12646403610516000568873169 9484802707887000426654877)
  ·
    refine ⟨3556801015457625159995579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9484802707887000426654877 3556801015457625159995579)
    ·
      refine ⟨5335201523186437739993369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3556801015457625159995579 5335201523186437739993369)
      ·
        refine ⟨4001401142389828304995027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5335201523186437739993369 4001401142389828304995027)
        ·
          refine ⟨6002101713584742457492541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4001401142389828304995027 6002101713584742457492541)
          ·
            refine ⟨2250788142594278421559703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6002101713584742457492541 2250788142594278421559703)
            ·
              refine ⟨3376182213891417632339555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2250788142594278421559703 3376182213891417632339555)
              ·
                refine ⟨5064273320837126448509333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3376182213891417632339555 5064273320837126448509333)
                ·
                  refine ⟨237387811914240302273875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5064273320837126448509333 237387811914240302273875)
                  ·
                    rfl

theorem cell20_520100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_520100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520100 prefixEnd_520100 := by exact prefixLift 520100
  have htrace : WordTrace (prefixWord ++ tailWord_520100) baseStart_520100 baseEnd_520100 := by
    simpa [prefixWord, tailWord_520100, baseEnd_520100] using wordTrace_append hprefix tailTrace_520100
  have hstable : (prefixWord ++ tailWord_520100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520100).length < 2 ^ (prefixWord ++ tailWord_520100).sum := by decide
  have hdescent : baseEnd_520100 < baseStart_520100 := by decide
  rcases family_descends (prefixWord ++ tailWord_520100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520103 : List Nat := [1, 1, 6, 1, 2, 2, 3, 4]
def baseStart_520103 : Nat := 118140960795 + 520103 * 2 ^ 59
def prefixEnd_520103 : Nat := 4983230072969 + 3 ^ 40 * 520103 * 2
def baseEnd_520103 : Nat := 79129727065328541724621

theorem tailTrace_520103 : CollatzResearch.WordTrace tailWord_520103 prefixEnd_520103 79129727065328541724621 := by
  unfold tailWord_520103
  simp only [CollatzResearch.WordTrace]
  refine ⟨18969714834763132365668963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12646476556508754910445975 18969714834763132365668963)
  ·
    refine ⟨28454572252144698548503445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18969714834763132365668963 28454572252144698548503445)
    ·
      refine ⟨1333808074319282744461099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28454572252144698548503445 1333808074319282744461099)
      ·
        refine ⟨2000712111478924116691649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1333808074319282744461099 2000712111478924116691649)
        ·
          refine ⟨1500534083609193087518737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2000712111478924116691649 1500534083609193087518737)
          ·
            refine ⟨1125400562706894815639053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1500534083609193087518737 1125400562706894815639053)
            ·
              refine ⟨422025211015085555864645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1125400562706894815639053 422025211015085555864645)
              ·
                refine ⟨79129727065328541724621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 422025211015085555864645 79129727065328541724621)
                ·
                  rfl

theorem cell20_520103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 4].length) (baseStart_520103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520103 prefixEnd_520103 := by exact prefixLift 520103
  have htrace : WordTrace (prefixWord ++ tailWord_520103) baseStart_520103 baseEnd_520103 := by
    simpa [prefixWord, tailWord_520103, baseEnd_520103] using wordTrace_append hprefix tailTrace_520103
  have hstable : (prefixWord ++ tailWord_520103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520103).length < 2 ^ (prefixWord ++ tailWord_520103).sum := by decide
  have hdescent : baseEnd_520103 < baseStart_520103 := by decide
  rcases family_descends (prefixWord ++ tailWord_520103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520138 : List Nat := [3, 1, 2, 1, 2, 1, 3, 3, 4]
def baseStart_520138 : Nat := 118140960795 + 520138 * 2 ^ 59
def prefixEnd_520138 : Nat := 4983230072969 + 3 ^ 40 * 520138 * 2
def baseEnd_520138 : Nat := 237405156149681059007053

theorem tailTrace_520138 : CollatzResearch.WordTrace tailWord_520138 prefixEnd_520138 237405156149681059007053 := by
  unfold tailWord_520138
  simp only [CollatzResearch.WordTrace]
  refine ⟨4742747847409083335798267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12647327593090888895462045 4742747847409083335798267)
  ·
    refine ⟨7114121771113625003697401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4742747847409083335798267 7114121771113625003697401)
    ·
      refine ⟨5335591328335218752773051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7114121771113625003697401 5335591328335218752773051)
      ·
        refine ⟨8003386992502828129159577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5335591328335218752773051 8003386992502828129159577)
        ·
          refine ⟨6002540244377121096869683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8003386992502828129159577 6002540244377121096869683)
          ·
            refine ⟨9003810366565681645304525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6002540244377121096869683 9003810366565681645304525)
            ·
              refine ⟨3376428887462130616989197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9003810366565681645304525 3376428887462130616989197)
              ·
                refine ⟨1266160832798298981370949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3376428887462130616989197 1266160832798298981370949)
                ·
                  refine ⟨237405156149681059007053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1266160832798298981370949 237405156149681059007053)
                  ·
                    rfl

theorem cell20_520138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_520138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520138 prefixEnd_520138 := by exact prefixLift 520138
  have htrace : WordTrace (prefixWord ++ tailWord_520138) baseStart_520138 baseEnd_520138 := by
    simpa [prefixWord, tailWord_520138, baseEnd_520138] using wordTrace_append hprefix tailTrace_520138
  have hstable : (prefixWord ++ tailWord_520138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520138).length < 2 ^ (prefixWord ++ tailWord_520138).sum := by decide
  have hdescent : baseEnd_520138 < baseStart_520138 := by decide
  rcases family_descends (prefixWord ++ tailWord_520138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520235 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 8]
def baseStart_520235 : Nat := 118140960795 + 520235 * 2 ^ 59
def prefixEnd_520235 : Nat := 4983230072969 + 3 ^ 40 * 520235 * 2
def baseEnd_520235 : Nat := 237449429592779832773323

theorem tailTrace_520235 : CollatzResearch.WordTrace tailWord_520235 prefixEnd_520235 237449429592779832773323 := by
  unfold tailWord_520235
  simp only [CollatzResearch.WordTrace]
  refine ⟨18974529270284918909474159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12649686180189945939649439 18974529270284918909474159)
  ·
    refine ⟨28461793905427378364211239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18974529270284918909474159 28461793905427378364211239)
    ·
      refine ⟨42692690858141067546316859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28461793905427378364211239 42692690858141067546316859)
      ·
        refine ⟨64039036287211601319475289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42692690858141067546316859 64039036287211601319475289)
        ·
          refine ⟨48029277215408700989606467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64039036287211601319475289 48029277215408700989606467)
          ·
            refine ⟨72043915823113051484409701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48029277215408700989606467 72043915823113051484409701)
            ·
              refine ⟨13508234216833697153326819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72043915823113051484409701 13508234216833697153326819)
              ·
                refine ⟨20262351325250545729990229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13508234216833697153326819 20262351325250545729990229)
                ·
                  refine ⟨237449429592779832773323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20262351325250545729990229 237449429592779832773323)
                  ·
                    rfl

theorem cell20_520235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 8].length) (baseStart_520235 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520235 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520235 prefixEnd_520235 := by exact prefixLift 520235
  have htrace : WordTrace (prefixWord ++ tailWord_520235) baseStart_520235 baseEnd_520235 := by
    simpa [prefixWord, tailWord_520235, baseEnd_520235] using wordTrace_append hprefix tailTrace_520235
  have hstable : (prefixWord ++ tailWord_520235).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520235).length < 2 ^ (prefixWord ++ tailWord_520235).sum := by decide
  have hdescent : baseEnd_520235 < baseStart_520235 := by decide
  rcases family_descends (prefixWord ++ tailWord_520235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520245 : List Nat := [1, 3, 3, 1, 1, 1, 3, 4, 3]
def baseStart_520245 : Nat := 118140960795 + 520245 * 2 ^ 59
def prefixEnd_520245 : Nat := 4983230072969 + 3 ^ 40 * 520245 * 2
def baseEnd_520245 : Nat := 237453993865264242439949

theorem tailTrace_520245 : CollatzResearch.WordTrace tailWord_520245 prefixEnd_520245 237453993865264242439949 := by
  unfold tailWord_520245
  simp only [CollatzResearch.WordTrace]
  refine ⟨18974894000248690617338189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12649929333499127078225459 18974894000248690617338189)
  ·
    refine ⟨7115585250093258981501821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18974894000248690617338189 7115585250093258981501821)
    ·
      refine ⟨2668344468784972118063183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7115585250093258981501821 2668344468784972118063183)
      ·
        refine ⟨4002516703177458177094775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2668344468784972118063183 4002516703177458177094775)
        ·
          refine ⟨6003775054766187265642163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4002516703177458177094775 6003775054766187265642163)
          ·
            refine ⟨9005662582149280898463245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6003775054766187265642163 9005662582149280898463245)
            ·
              refine ⟨3377123468305980336923717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9005662582149280898463245 3377123468305980336923717)
              ·
                refine ⟨633210650307371313173197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3377123468305980336923717 633210650307371313173197)
                ·
                  refine ⟨237453993865264242439949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 633210650307371313173197 237453993865264242439949)
                  ·
                    rfl

theorem cell20_520245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_520245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520245 prefixEnd_520245 := by exact prefixLift 520245
  have htrace : WordTrace (prefixWord ++ tailWord_520245) baseStart_520245 baseEnd_520245 := by
    simpa [prefixWord, tailWord_520245, baseEnd_520245] using wordTrace_append hprefix tailTrace_520245
  have hstable : (prefixWord ++ tailWord_520245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520245).length < 2 ^ (prefixWord ++ tailWord_520245).sum := by decide
  have hdescent : baseEnd_520245 < baseStart_520245 := by decide
  rcases family_descends (prefixWord ++ tailWord_520245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520248 : List Nat := [2, 1, 2, 1, 6, 1, 1, 4, 2]
def baseStart_520248 : Nat := 118140960795 + 520248 * 2 ^ 59
def prefixEnd_520248 : Nat := 4983230072969 + 3 ^ 40 * 520248 * 2
def baseEnd_520248 : Nat := 237455363147009565339937

theorem tailTrace_520248 : CollatzResearch.WordTrace tailWord_520248 prefixEnd_520248 237455363147009565339937 := by
  unfold tailWord_520248
  simp only [CollatzResearch.WordTrace]
  refine ⟨9487501709618911064848699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12650002279491881419798265 9487501709618911064848699)
  ·
    refine ⟨14231252564428366597273049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9487501709618911064848699 14231252564428366597273049)
    ·
      refine ⟨10673439423321274947954787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14231252564428366597273049 10673439423321274947954787)
      ·
        refine ⟨16010159134981912421932181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10673439423321274947954787 16010159134981912421932181)
        ·
          refine ⟨750476209452277144778071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16010159134981912421932181 750476209452277144778071)
          ·
            refine ⟨1125714314178415717167107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 750476209452277144778071 1125714314178415717167107)
            ·
              refine ⟨1688571471267623575750661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1125714314178415717167107 1688571471267623575750661)
              ·
                refine ⟨316607150862679420453249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1688571471267623575750661 316607150862679420453249)
                ·
                  refine ⟨237455363147009565339937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316607150862679420453249 237455363147009565339937)
                  ·
                    rfl

theorem cell20_520248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 4, 2].length) (baseStart_520248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520248 prefixEnd_520248 := by exact prefixLift 520248
  have htrace : WordTrace (prefixWord ++ tailWord_520248) baseStart_520248 baseEnd_520248 := by
    simpa [prefixWord, tailWord_520248, baseEnd_520248] using wordTrace_append hprefix tailTrace_520248
  have hstable : (prefixWord ++ tailWord_520248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520248).length < 2 ^ (prefixWord ++ tailWord_520248).sum := by decide
  have hdescent : baseEnd_520248 < baseStart_520248 := by decide
  rcases family_descends (prefixWord ++ tailWord_520248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520252 : List Nat := [2, 2, 2, 2, 2, 1, 2, 3, 4]
def baseStart_520252 : Nat := 118140960795 + 520252 * 2 ^ 59
def prefixEnd_520252 : Nat := 4983230072969 + 3 ^ 40 * 520252 * 2
def baseEnd_520252 : Nat := 237457188856003329206587

theorem tailTrace_520252 : CollatzResearch.WordTrace tailWord_520252 prefixEnd_520252 237457188856003329206587 := by
  unfold tailWord_520252
  simp only [CollatzResearch.WordTrace]
  refine ⟨9487574655611665406421505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12650099540815553875228673 9487574655611665406421505)
  ·
    refine ⟨7115680991708749054816129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9487574655611665406421505 7115680991708749054816129)
    ·
      refine ⟨5336760743781561791112097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7115680991708749054816129 5336760743781561791112097)
      ·
        refine ⟨4002570557836171343334073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5336760743781561791112097 4002570557836171343334073)
        ·
          refine ⟨3001927918377128507500555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4002570557836171343334073 3001927918377128507500555)
          ·
            refine ⟨4502891877565692761250833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3001927918377128507500555 4502891877565692761250833)
            ·
              refine ⟨3377168908174269570938125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4502891877565692761250833 3377168908174269570938125)
              ·
                refine ⟨1266438340565351089101797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3377168908174269570938125 1266438340565351089101797)
                ·
                  refine ⟨237457188856003329206587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1266438340565351089101797 237457188856003329206587)
                  ·
                    rfl

theorem cell20_520252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_520252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520252 prefixEnd_520252 := by exact prefixLift 520252
  have htrace : WordTrace (prefixWord ++ tailWord_520252) baseStart_520252 baseEnd_520252 := by
    simpa [prefixWord, tailWord_520252, baseEnd_520252] using wordTrace_append hprefix tailTrace_520252
  have hstable : (prefixWord ++ tailWord_520252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520252).length < 2 ^ (prefixWord ++ tailWord_520252).sum := by decide
  have hdescent : baseEnd_520252 < baseStart_520252 := by decide
  rcases family_descends (prefixWord ++ tailWord_520252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520266 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 7]
def baseStart_520266 : Nat := 118140960795 + 520266 * 2 ^ 59
def prefixEnd_520266 : Nat := 4983230072969 + 3 ^ 40 * 520266 * 2
def baseEnd_520266 : Nat := 237463578837481502739863

theorem tailTrace_520266 : CollatzResearch.WordTrace tailWord_520266 prefixEnd_520266 237463578837481502739863 := by
  unfold tailWord_520266
  simp only [CollatzResearch.WordTrace]
  refine ⟨4743914983293152800963163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12650439955448407469235101 4743914983293152800963163)
  ·
    refine ⟨7115872474939729201444745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4743914983293152800963163 7115872474939729201444745)
    ·
      refine ⟨5336904356204796901083559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7115872474939729201444745 5336904356204796901083559)
      ·
        refine ⟨8005356534307195351625339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5336904356204796901083559 8005356534307195351625339)
        ·
          refine ⟨12008034801460793027438009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8005356534307195351625339 12008034801460793027438009)
          ·
            refine ⟨9006026101095594770578507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12008034801460793027438009 9006026101095594770578507)
            ·
              refine ⟨13509039151643392155867761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9006026101095594770578507 13509039151643392155867761)
              ·
                refine ⟨10131779363732544116900821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13509039151643392155867761 10131779363732544116900821)
                ·
                  refine ⟨237463578837481502739863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10131779363732544116900821 237463578837481502739863)
                  ·
                    rfl

theorem cell20_520266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_520266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520266 prefixEnd_520266 := by exact prefixLift 520266
  have htrace : WordTrace (prefixWord ++ tailWord_520266) baseStart_520266 baseEnd_520266 := by
    simpa [prefixWord, tailWord_520266, baseEnd_520266] using wordTrace_append hprefix tailTrace_520266
  have hstable : (prefixWord ++ tailWord_520266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520266).length < 2 ^ (prefixWord ++ tailWord_520266).sum := by decide
  have hdescent : baseEnd_520266 < baseStart_520266 := by decide
  rcases family_descends (prefixWord ++ tailWord_520266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520269 : List Nat := [1, 6, 1, 1, 1, 1, 3, 2, 4]
def baseStart_520269 : Nat := 118140960795 + 520269 * 2 ^ 59
def prefixEnd_520269 : Nat := 4983230072969 + 3 ^ 40 * 520269 * 2
def baseEnd_520269 : Nat := 237464948119226825639851

theorem tailTrace_520269 : CollatzResearch.WordTrace tailWord_520269 prefixEnd_520269 237464948119226825639851 := by
  unfold tailWord_520269
  simp only [CollatzResearch.WordTrace]
  refine ⟨18975769352161742716211861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12650512901441161810807907 18975769352161742716211861)
  ·
    refine ⟨889489188382581689822431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18975769352161742716211861 889489188382581689822431)
    ·
      refine ⟨1334233782573872534733647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 889489188382581689822431 1334233782573872534733647)
      ·
        refine ⟨2001350673860808802100471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1334233782573872534733647 2001350673860808802100471)
        ·
          refine ⟨3002026010791213203150707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2001350673860808802100471 3002026010791213203150707)
          ·
            refine ⟨4503039016186819804726061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3002026010791213203150707 4503039016186819804726061)
            ·
              refine ⟨1688639631070057426772273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4503039016186819804726061 1688639631070057426772273)
              ·
                refine ⟨1266479723302543070079205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1688639631070057426772273 1266479723302543070079205)
                ·
                  refine ⟨237464948119226825639851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1266479723302543070079205 237464948119226825639851)
                  ·
                    rfl

theorem cell20_520269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_520269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520269 prefixEnd_520269 := by exact prefixLift 520269
  have htrace : WordTrace (prefixWord ++ tailWord_520269) baseStart_520269 baseEnd_520269 := by
    simpa [prefixWord, tailWord_520269, baseEnd_520269] using wordTrace_append hprefix tailTrace_520269
  have hstable : (prefixWord ++ tailWord_520269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520269).length < 2 ^ (prefixWord ++ tailWord_520269).sum := by decide
  have hdescent : baseEnd_520269 < baseStart_520269 := by decide
  rcases family_descends (prefixWord ++ tailWord_520269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520300 : List Nat := [2, 2, 1, 1, 3, 5, 1, 2, 3]
def baseStart_520300 : Nat := 118140960795 + 520300 * 2 ^ 59
def prefixEnd_520300 : Nat := 4983230072969 + 3 ^ 40 * 520300 * 2
def baseEnd_520300 : Nat := 237479097363928495606391

theorem tailTrace_520300 : CollatzResearch.WordTrace tailWord_520300 prefixEnd_520300 237479097363928495606391 := by
  unfold tailWord_520300
  simp only [CollatzResearch.WordTrace]
  refine ⟨9488450007524717505295177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12651266676699623340393569 9488450007524717505295177)
  ·
    refine ⟨7116337505643538128971383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9488450007524717505295177 7116337505643538128971383)
    ·
      refine ⟨10674506258465307193457075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7116337505643538128971383 10674506258465307193457075)
      ·
        refine ⟨16011759387697960790185613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10674506258465307193457075 16011759387697960790185613)
        ·
          refine ⟨6004409770386735296319605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16011759387697960790185613 6004409770386735296319605)
          ·
            refine ⟨562913415973756434029963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6004409770386735296319605 562913415973756434029963)
            ·
              refine ⟨844370123960634651044945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562913415973756434029963 844370123960634651044945)
              ·
                refine ⟨633277592970475988283709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 844370123960634651044945 633277592970475988283709)
                ·
                  refine ⟨237479097363928495606391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 633277592970475988283709 237479097363928495606391)
                  ·
                    rfl

theorem cell20_520300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 3].length) (baseStart_520300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520300 prefixEnd_520300 := by exact prefixLift 520300
  have htrace : WordTrace (prefixWord ++ tailWord_520300) baseStart_520300 baseEnd_520300 := by
    simpa [prefixWord, tailWord_520300, baseEnd_520300] using wordTrace_append hprefix tailTrace_520300
  have hstable : (prefixWord ++ tailWord_520300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520300).length < 2 ^ (prefixWord ++ tailWord_520300).sum := by decide
  have hdescent : baseEnd_520300 < baseStart_520300 := by decide
  rcases family_descends (prefixWord ++ tailWord_520300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520442 : List Nat := [3, 1, 1, 1, 1, 6, 1, 2, 4]
def baseStart_520442 : Nat := 118140960795 + 520442 * 2 ^ 59
def prefixEnd_520442 : Nat := 4983230072969 + 3 ^ 40 * 520442 * 2
def baseEnd_520442 : Nat := 237543910033207112872477

theorem tailTrace_520442 : CollatzResearch.WordTrace tailWord_520442 prefixEnd_520442 237543910033207112872477 := by
  unfold tailWord_520442
  simp only [CollatzResearch.WordTrace]
  refine ⟨4745519795133748315564895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12654719453689995508173053 4745519795133748315564895)
  ·
    refine ⟨7118279692700622473347343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4745519795133748315564895 7118279692700622473347343)
    ·
      refine ⟨10677419539050933710021015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7118279692700622473347343 10677419539050933710021015)
      ·
        refine ⟨16016129308576400565031523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10677419539050933710021015 16016129308576400565031523)
        ·
          refine ⟨24024193962864600847547285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16016129308576400565031523 24024193962864600847547285)
          ·
            refine ⟨1126134092009278164728779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24024193962864600847547285 1126134092009278164728779)
            ·
              refine ⟨1689201138013917247093169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1126134092009278164728779 1689201138013917247093169)
              ·
                refine ⟨1266900853510437935319877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1689201138013917247093169 1266900853510437935319877)
                ·
                  refine ⟨237543910033207112872477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1266900853510437935319877 237543910033207112872477)
                  ·
                    rfl

theorem cell20_520442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_520442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520442 prefixEnd_520442 := by exact prefixLift 520442
  have htrace : WordTrace (prefixWord ++ tailWord_520442) baseStart_520442 baseEnd_520442 := by
    simpa [prefixWord, tailWord_520442, baseEnd_520442] using wordTrace_append hprefix tailTrace_520442
  have hstable : (prefixWord ++ tailWord_520442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520442).length < 2 ^ (prefixWord ++ tailWord_520442).sum := by decide
  have hdescent : baseEnd_520442 < baseStart_520442 := by decide
  rcases family_descends (prefixWord ++ tailWord_520442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520455 : List Nat := [1, 1, 4, 5, 1, 1, 2, 3, 2]
def baseStart_520455 : Nat := 118140960795 + 520455 * 2 ^ 59
def prefixEnd_520455 : Nat := 4983230072969 + 3 ^ 40 * 520455 * 2
def baseEnd_520455 : Nat := 237549843587436845439091

theorem tailTrace_520455 : CollatzResearch.WordTrace tailWord_520455 prefixEnd_520455 237549843587436845439091 := by
  unfold tailWord_520455
  simp only [CollatzResearch.WordTrace]
  refine ⟨18982553329487896482482819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12655035552991930988321879 18982553329487896482482819)
  ·
    refine ⟨28473829994231844723724229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18982553329487896482482819 28473829994231844723724229)
    ·
      refine ⟨5338843123918470885698293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28473829994231844723724229 5338843123918470885698293)
      ·
        refine ⟨500516542867356645534215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5338843123918470885698293 500516542867356645534215)
        ·
          refine ⟨750774814301034968301323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500516542867356645534215 750774814301034968301323)
          ·
            refine ⟨1126162221451552452451985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 750774814301034968301323 1126162221451552452451985)
            ·
              refine ⟨844621666088664339338989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1126162221451552452451985 844621666088664339338989)
              ·
                refine ⟨316733124783249127252121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 844621666088664339338989 316733124783249127252121)
                ·
                  refine ⟨237549843587436845439091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316733124783249127252121 237549843587436845439091)
                  ·
                    rfl

theorem cell20_520455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 3, 2].length) (baseStart_520455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520455 prefixEnd_520455 := by exact prefixLift 520455
  have htrace : WordTrace (prefixWord ++ tailWord_520455) baseStart_520455 baseEnd_520455 := by
    simpa [prefixWord, tailWord_520455, baseEnd_520455] using wordTrace_append hprefix tailTrace_520455
  have hstable : (prefixWord ++ tailWord_520455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520455).length < 2 ^ (prefixWord ++ tailWord_520455).sum := by decide
  have hdescent : baseEnd_520455 < baseStart_520455 := by decide
  rcases family_descends (prefixWord ++ tailWord_520455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520459 : List Nat := [1, 1, 1, 1, 5, 2, 4, 3, 2]
def baseStart_520459 : Nat := 118140960795 + 520459 * 2 ^ 59
def prefixEnd_520459 : Nat := 4983230072969 + 3 ^ 40 * 520459 * 2
def baseEnd_520459 : Nat := 237551669296430609305741

theorem tailTrace_520459 : CollatzResearch.WordTrace tailWord_520459 prefixEnd_520459 237551669296430609305741 := by
  unfold tailWord_520459
  simp only [CollatzResearch.WordTrace]
  refine ⟨18982699221473405165628431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12655132814315603443752287 18982699221473405165628431)
  ·
    refine ⟨28474048832210107748442647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18982699221473405165628431 28474048832210107748442647)
    ·
      refine ⟨42711073248315161622663971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28474048832210107748442647 42711073248315161622663971)
      ·
        refine ⟨64066609872472742433995957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42711073248315161622663971 64066609872472742433995957)
        ·
          refine ⟨6006244675544319603187121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64066609872472742433995957 6006244675544319603187121)
          ·
            refine ⟨4504683506658239702390341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6006244675544319603187121 4504683506658239702390341)
            ·
              refine ⟨844628157498419944198189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4504683506658239702390341 844628157498419944198189)
              ·
                refine ⟨316735559061907479074321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 844628157498419944198189 316735559061907479074321)
                ·
                  refine ⟨237551669296430609305741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316735559061907479074321 237551669296430609305741)
                  ·
                    rfl

theorem cell20_520459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 3, 2].length) (baseStart_520459 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520459 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520459 prefixEnd_520459 := by exact prefixLift 520459
  have htrace : WordTrace (prefixWord ++ tailWord_520459) baseStart_520459 baseEnd_520459 := by
    simpa [prefixWord, tailWord_520459, baseEnd_520459] using wordTrace_append hprefix tailTrace_520459
  have hstable : (prefixWord ++ tailWord_520459).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520459).length < 2 ^ (prefixWord ++ tailWord_520459).sum := by decide
  have hdescent : baseEnd_520459 < baseStart_520459 := by decide
  rcases family_descends (prefixWord ++ tailWord_520459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520480 : List Nat := [2, 1, 1, 5, 2, 1, 1, 3, 4]
def baseStart_520480 : Nat := 118140960795 + 520480 * 2 ^ 59
def prefixEnd_520480 : Nat := 4983230072969 + 3 ^ 40 * 520480 * 2
def baseEnd_520480 : Nat := 237561254268647869605655

theorem tailTrace_520480 : CollatzResearch.WordTrace tailWord_520480 prefixEnd_520480 237561254268647869605655 := by
  unfold tailWord_520480
  simp only [CollatzResearch.WordTrace]
  refine ⟨9491732577198662876071447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12655643436264883834761929 9491732577198662876071447)
  ·
    refine ⟨14237598865797994314107171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9491732577198662876071447 14237598865797994314107171)
    ·
      refine ⟨21356398298696991471160757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14237598865797994314107171 21356398298696991471160757)
      ·
        refine ⟨2002162340502842950421321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21356398298696991471160757 2002162340502842950421321)
        ·
          refine ⟨1501621755377132212815991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2002162340502842950421321 1501621755377132212815991)
          ·
            refine ⟨2252432633065698319223987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1501621755377132212815991 2252432633065698319223987)
            ·
              refine ⟨3378648949598547478835981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2252432633065698319223987 3378648949598547478835981)
              ·
                refine ⟨1266993356099455304563493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3378648949598547478835981 1266993356099455304563493)
                ·
                  refine ⟨237561254268647869605655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1266993356099455304563493 237561254268647869605655)
                  ·
                    rfl

theorem cell20_520480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_520480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520480 prefixEnd_520480 := by exact prefixLift 520480
  have htrace : WordTrace (prefixWord ++ tailWord_520480) baseStart_520480 baseEnd_520480 := by
    simpa [prefixWord, tailWord_520480, baseEnd_520480] using wordTrace_append hprefix tailTrace_520480
  have hstable : (prefixWord ++ tailWord_520480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520480).length < 2 ^ (prefixWord ++ tailWord_520480).sum := by decide
  have hdescent : baseEnd_520480 < baseStart_520480 := by decide
  rcases family_descends (prefixWord ++ tailWord_520480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520549 : List Nat := [1, 3, 1, 3, 1, 4, 1, 3, 3]
def baseStart_520549 : Nat := 118140960795 + 520549 * 2 ^ 59
def prefixEnd_520549 : Nat := 4983230072969 + 3 ^ 40 * 520549 * 2
def baseEnd_520549 : Nat := 237592747748790296305373

theorem tailTrace_520549 : CollatzResearch.WordTrace tailWord_520549 prefixEnd_520549 237592747748790296305373 := by
  unfold tailWord_520549
  simp only [CollatzResearch.WordTrace]
  refine ⟨18985981791147350536404701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12657321194098233690936467 18985981791147350536404701)
  ·
    refine ⟨7119743171680256451151763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18985981791147350536404701 7119743171680256451151763)
    ·
      refine ⟨10679614757520384676727645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7119743171680256451151763 10679614757520384676727645)
      ·
        refine ⟨4004855534070144253772867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10679614757520384676727645 4004855534070144253772867)
        ·
          refine ⟨6007283301105216380659301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4004855534070144253772867 6007283301105216380659301)
          ·
            refine ⟨1126365618957228071373619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6007283301105216380659301 1126365618957228071373619)
            ·
              refine ⟨1689548428435842107060429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1126365618957228071373619 1689548428435842107060429)
              ·
                refine ⟨633580660663440790147661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1689548428435842107060429 633580660663440790147661)
                ·
                  refine ⟨237592747748790296305373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 633580660663440790147661 237592747748790296305373)
                  ·
                    rfl

theorem cell20_520549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_520549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520549 prefixEnd_520549 := by exact prefixLift 520549
  have htrace : WordTrace (prefixWord ++ tailWord_520549) baseStart_520549 baseEnd_520549 := by
    simpa [prefixWord, tailWord_520549, baseEnd_520549] using wordTrace_append hprefix tailTrace_520549
  have hstable : (prefixWord ++ tailWord_520549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520549).length < 2 ^ (prefixWord ++ tailWord_520549).sum := by decide
  have hdescent : baseEnd_520549 < baseStart_520549 := by decide
  rcases family_descends (prefixWord ++ tailWord_520549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520586 : List Nat := [3, 1, 2, 5, 1, 2, 2, 2, 2]
def baseStart_520586 : Nat := 118140960795 + 520586 * 2 ^ 59
def prefixEnd_520586 : Nat := 4983230072969 + 3 ^ 40 * 520586 * 2
def baseEnd_520586 : Nat := 237609635556982612071889

theorem tailTrace_520586 : CollatzResearch.WordTrace tailWord_520586 prefixEnd_520586 237609635556982612071889 := by
  unfold tailWord_520586
  simp only [CollatzResearch.WordTrace]
  refine ⟨4746832823003326463875403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12658220861342203903667741 4746832823003326463875403)
  ·
    refine ⟨7120249234504989695813105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4746832823003326463875403 7120249234504989695813105)
    ·
      refine ⟨5340186925878742271859829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7120249234504989695813105 5340186925878742271859829)
      ·
        refine ⟨500642524301132087986859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5340186925878742271859829 500642524301132087986859)
        ·
          refine ⟨750963786451698131980289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500642524301132087986859 750963786451698131980289)
          ·
            refine ⟨563222839838773598985217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 750963786451698131980289 563222839838773598985217)
            ·
              refine ⟨422417129879080199238913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 563222839838773598985217 422417129879080199238913)
              ·
                refine ⟨316812847409310149429185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 422417129879080199238913 316812847409310149429185)
                ·
                  refine ⟨237609635556982612071889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316812847409310149429185 237609635556982612071889)
                  ·
                    rfl

theorem cell20_520586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 2, 2].length) (baseStart_520586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520586 prefixEnd_520586 := by exact prefixLift 520586
  have htrace : WordTrace (prefixWord ++ tailWord_520586) baseStart_520586 baseEnd_520586 := by
    simpa [prefixWord, tailWord_520586, baseEnd_520586] using wordTrace_append hprefix tailTrace_520586
  have hstable : (prefixWord ++ tailWord_520586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520586).length < 2 ^ (prefixWord ++ tailWord_520586).sum := by decide
  have hdescent : baseEnd_520586 < baseStart_520586 := by decide
  rcases family_descends (prefixWord ++ tailWord_520586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520587 : List Nat := [1, 1, 1, 1, 4, 5, 2, 2, 3]
def baseStart_520587 : Nat := 118140960795 + 520587 * 2 ^ 59
def prefixEnd_520587 : Nat := 4983230072969 + 3 ^ 40 * 520587 * 2
def baseEnd_520587 : Nat := 237610091984231053038551

theorem tailTrace_520587 : CollatzResearch.WordTrace tailWord_520587 prefixEnd_520587 237610091984231053038551 := by
  unfold tailWord_520587
  simp only [CollatzResearch.WordTrace]
  refine ⟨18987367765009683026288015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12658245176673122017525343 18987367765009683026288015)
  ·
    refine ⟨28481051647514524539432023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18987367765009683026288015 28481051647514524539432023)
    ·
      refine ⟨42721577471271786809148035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28481051647514524539432023 42721577471271786809148035)
      ·
        refine ⟨64082366206907680213722053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42721577471271786809148035 64082366206907680213722053)
        ·
          refine ⟨12015443663795190040072885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64082366206907680213722053 12015443663795190040072885)
          ·
            refine ⟨1126447843480799066256833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12015443663795190040072885 1126447843480799066256833)
            ·
              refine ⟨844835882610599299692625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1126447843480799066256833 844835882610599299692625)
              ·
                refine ⟨633626911957949474769469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 844835882610599299692625 633626911957949474769469)
                ·
                  refine ⟨237610091984231053038551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 633626911957949474769469 237610091984231053038551)
                  ·
                    rfl

theorem cell20_520587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 3].length) (baseStart_520587 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520587 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520587 prefixEnd_520587 := by exact prefixLift 520587
  have htrace : WordTrace (prefixWord ++ tailWord_520587) baseStart_520587 baseEnd_520587 := by
    simpa [prefixWord, tailWord_520587, baseEnd_520587] using wordTrace_append hprefix tailTrace_520587
  have hstable : (prefixWord ++ tailWord_520587).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520587).length < 2 ^ (prefixWord ++ tailWord_520587).sum := by decide
  have hdescent : baseEnd_520587 < baseStart_520587 := by decide
  rcases family_descends (prefixWord ++ tailWord_520587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520590 : List Nat := [4, 1, 1, 4, 1, 2, 1, 4, 2]
def baseStart_520590 : Nat := 118140960795 + 520590 * 2 ^ 59
def prefixEnd_520590 : Nat := 4983230072969 + 3 ^ 40 * 520590 * 2
def baseEnd_520590 : Nat := 237611461265976375938539

theorem tailTrace_520590 : CollatzResearch.WordTrace tailWord_520590 prefixEnd_520590 237611461265976375938539 := by
  unfold tailWord_520590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2373434647999851817330903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12658318122665876359098149 2373434647999851817330903)
  ·
    refine ⟨3560151971999777725996355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2373434647999851817330903 3560151971999777725996355)
    ·
      refine ⟨5340227957999666588994533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3560151971999777725996355 5340227957999666588994533)
      ·
        refine ⟨1001292742124937485436475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5340227957999666588994533 1001292742124937485436475)
        ·
          refine ⟨1501939113187406228154713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1001292742124937485436475 1501939113187406228154713)
          ·
            refine ⟨1126454334890554671116035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1501939113187406228154713 1126454334890554671116035)
            ·
              refine ⟨1689681502335832006674053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1126454334890554671116035 1689681502335832006674053)
              ·
                refine ⟨316815281687968501251385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1689681502335832006674053 316815281687968501251385)
                ·
                  refine ⟨237611461265976375938539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316815281687968501251385 237611461265976375938539)
                  ·
                    rfl

theorem cell20_520590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_520590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520590 prefixEnd_520590 := by exact prefixLift 520590
  have htrace : WordTrace (prefixWord ++ tailWord_520590) baseStart_520590 baseEnd_520590 := by
    simpa [prefixWord, tailWord_520590, baseEnd_520590] using wordTrace_append hprefix tailTrace_520590
  have hstable : (prefixWord ++ tailWord_520590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520590).length < 2 ^ (prefixWord ++ tailWord_520590).sum := by decide
  have hdescent : baseEnd_520590 < baseStart_520590 := by decide
  rcases family_descends (prefixWord ++ tailWord_520590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520715 : List Nat := [1, 1, 1, 1, 7, 2, 2, 5]
def baseStart_520715 : Nat := 118140960795 + 520715 * 2 ^ 59
def prefixEnd_520715 : Nat := 4983230072969 + 3 ^ 40 * 520715 * 2
def baseEnd_520715 : Nat := 79222838224010498923787

theorem tailTrace_520715 : CollatzResearch.WordTrace tailWord_520715 prefixEnd_520715 79222838224010498923787 := by
  unfold tailWord_520715
  simp only [CollatzResearch.WordTrace]
  refine ⟨18992036308545960886947599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12661357539030640591298399 18992036308545960886947599)
  ·
    refine ⟨28488054462818941330421399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18992036308545960886947599 28488054462818941330421399)
    ·
      refine ⟨42732081694228411995632099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28488054462818941330421399 42732081694228411995632099)
      ·
        refine ⟨64098122541342617993448149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42732081694228411995632099 64098122541342617993448149)
        ·
          refine ⟨1502299747062717609221441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 64098122541342617993448149 1502299747062717609221441)
          ·
            refine ⟨1126724810297038206916081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1502299747062717609221441 1126724810297038206916081)
            ·
              refine ⟨845043607722778655187061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1126724810297038206916081 845043607722778655187061)
              ·
                refine ⟨79222838224010498923787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 845043607722778655187061 79222838224010498923787)
                ·
                  rfl

theorem cell20_520715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 5].length) (baseStart_520715 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520715 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520715 prefixEnd_520715 := by exact prefixLift 520715
  have htrace : WordTrace (prefixWord ++ tailWord_520715) baseStart_520715 baseEnd_520715 := by
    simpa [prefixWord, tailWord_520715, baseEnd_520715] using wordTrace_append hprefix tailTrace_520715
  have hstable : (prefixWord ++ tailWord_520715).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520715).length < 2 ^ (prefixWord ++ tailWord_520715).sum := by decide
  have hdescent : baseEnd_520715 < baseStart_520715 := by decide
  rcases family_descends (prefixWord ++ tailWord_520715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520718 : List Nat := [4, 1, 1, 2, 3, 1, 4, 1, 3]
def baseStart_520718 : Nat := 118140960795 + 520718 * 2 ^ 59
def prefixEnd_520718 : Nat := 4983230072969 + 3 ^ 40 * 520718 * 2
def baseEnd_520718 : Nat := 237669883953776819671349

theorem tailTrace_520718 : CollatzResearch.WordTrace tailWord_520718 prefixEnd_520718 237669883953776819671349 := by
  unfold tailWord_520718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2374018215941886549913351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12661430485023394932871205 2374018215941886549913351)
  ·
    refine ⟨3561027323912829824870027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2374018215941886549913351 3561027323912829824870027)
    ·
      refine ⟨5341540985869244737305041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3561027323912829824870027 5341540985869244737305041)
      ·
        refine ⟨4006155739401933552978781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5341540985869244737305041 4006155739401933552978781)
        ·
          refine ⟨1502308402275725082367043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4006155739401933552978781 1502308402275725082367043)
          ·
            refine ⟨2253462603413587623550565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1502308402275725082367043 2253462603413587623550565)
            ·
              refine ⟨422524238140047679415731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2253462603413587623550565 422524238140047679415731)
              ·
                refine ⟨633786357210071519123597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 422524238140047679415731 633786357210071519123597)
                ·
                  refine ⟨237669883953776819671349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 633786357210071519123597 237669883953776819671349)
                  ·
                    rfl

theorem cell20_520718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_520718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520718 prefixEnd_520718 := by exact prefixLift 520718
  have htrace : WordTrace (prefixWord ++ tailWord_520718) baseStart_520718 baseEnd_520718 := by
    simpa [prefixWord, tailWord_520718, baseEnd_520718] using wordTrace_append hprefix tailTrace_520718
  have hstable : (prefixWord ++ tailWord_520718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520718).length < 2 ^ (prefixWord ++ tailWord_520718).sum := by decide
  have hdescent : baseEnd_520718 < baseStart_520718 := by decide
  rcases family_descends (prefixWord ++ tailWord_520718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520749 : List Nat := [1, 5, 4, 1, 1, 8]
def baseStart_520749 : Nat := 118140960795 + 520749 * 2 ^ 59
def prefixEnd_520749 : Nat := 4983230072969 + 3 ^ 40 * 520749 * 2
def baseEnd_520749 : Nat := 8803112340684388505107

theorem tailTrace_520749 : CollatzResearch.WordTrace tailWord_520749 prefixEnd_520749 8803112340684388505107 := by
  unfold tailWord_520749
  simp only [CollatzResearch.WordTrace]
  refine ⟨18993276390422784693685301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12662184260281856462456867 18993276390422784693685301)
  ·
    refine ⟨1780619661602136065032997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18993276390422784693685301 1780619661602136065032997)
    ·
      refine ⟨333866186550400512193687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1780619661602136065032997 333866186550400512193687)
      ·
        refine ⟨500799279825600768290531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333866186550400512193687 500799279825600768290531)
        ·
          refine ⟨751198919738401152435797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500799279825600768290531 751198919738401152435797)
          ·
            refine ⟨8803112340684388505107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 751198919738401152435797 8803112340684388505107)
            ·
              rfl

theorem cell20_520749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 8].length) (baseStart_520749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520749 prefixEnd_520749 := by exact prefixLift 520749
  have htrace : WordTrace (prefixWord ++ tailWord_520749) baseStart_520749 baseEnd_520749 := by
    simpa [prefixWord, tailWord_520749, baseEnd_520749] using wordTrace_append hprefix tailTrace_520749
  have hstable : (prefixWord ++ tailWord_520749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520749).length < 2 ^ (prefixWord ++ tailWord_520749).sum := by decide
  have hdescent : baseEnd_520749 < baseStart_520749 := by decide
  rcases family_descends (prefixWord ++ tailWord_520749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520766 : List Nat := [4, 2, 1, 4, 2, 1, 1, 5]
def baseStart_520766 : Nat := 118140960795 + 520766 * 2 ^ 59
def prefixEnd_520766 : Nat := 4983230072969 + 3 ^ 40 * 520766 * 2
def baseEnd_520766 : Nat := 79230597487233995357051

theorem tailTrace_520766 : CollatzResearch.WordTrace tailWord_520766 prefixEnd_520766 79230597487233995357051 := by
  unfold tailWord_520766
  simp only [CollatzResearch.WordTrace]
  refine ⟨2374237053920149574631769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12662597620907464398036101 2374237053920149574631769)
  ·
    refine ⟨1780677790440112180973827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2374237053920149574631769 1780677790440112180973827)
    ·
      refine ⟨2671016685660168271460741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1780677790440112180973827 2671016685660168271460741)
      ·
        refine ⟨500815628561281550898889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2671016685660168271460741 500815628561281550898889)
        ·
          refine ⟨375611721420961163174167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 500815628561281550898889 375611721420961163174167)
          ·
            refine ⟨563417582131441744761251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375611721420961163174167 563417582131441744761251)
            ·
              refine ⟨845126373197162617141877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563417582131441744761251 845126373197162617141877)
              ·
                refine ⟨79230597487233995357051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 845126373197162617141877 79230597487233995357051)
                ·
                  rfl

theorem cell20_520766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_520766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520766 prefixEnd_520766 := by exact prefixLift 520766
  have htrace : WordTrace (prefixWord ++ tailWord_520766) baseStart_520766 baseEnd_520766 := by
    simpa [prefixWord, tailWord_520766, baseEnd_520766] using wordTrace_append hprefix tailTrace_520766
  have hstable : (prefixWord ++ tailWord_520766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520766).length < 2 ^ (prefixWord ++ tailWord_520766).sum := by decide
  have hdescent : baseEnd_520766 < baseStart_520766 := by decide
  rcases family_descends (prefixWord ++ tailWord_520766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520767 : List Nat := [1, 1, 2, 2, 3, 2, 2, 3, 4]
def baseStart_520767 : Nat := 118140960795 + 520767 * 2 ^ 59
def prefixEnd_520767 : Nat := 4983230072969 + 3 ^ 40 * 520767 * 2
def baseEnd_520767 : Nat := 237692248888950427037815

theorem tailTrace_520767 : CollatzResearch.WordTrace tailWord_520767 prefixEnd_520767 237692248888950427037815 := by
  unfold tailWord_520767
  simp only [CollatzResearch.WordTrace]
  refine ⟨18993932904357573767840555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12662621936238382511893703 18993932904357573767840555)
  ·
    refine ⟨28490899356536360651760833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18993932904357573767840555 28490899356536360651760833)
    ·
      refine ⟨21368174517402270488820625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28490899356536360651760833 21368174517402270488820625)
      ·
        refine ⟨16026130888051702866615469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21368174517402270488820625 16026130888051702866615469)
        ·
          refine ⟨6009799083019388574980801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16026130888051702866615469 6009799083019388574980801)
          ·
            refine ⟨4507349312264541431235601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6009799083019388574980801 4507349312264541431235601)
            ·
              refine ⟨3380511984198406073426701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4507349312264541431235601 3380511984198406073426701)
              ·
                refine ⟨1267691994074402277535013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3380511984198406073426701 1267691994074402277535013)
                ·
                  refine ⟨237692248888950427037815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1267691994074402277535013 237692248888950427037815)
                  ·
                    rfl

theorem cell20_520767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 4].length) (baseStart_520767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520767 prefixEnd_520767 := by exact prefixLift 520767
  have htrace : WordTrace (prefixWord ++ tailWord_520767) baseStart_520767 baseEnd_520767 := by
    simpa [prefixWord, tailWord_520767, baseEnd_520767] using wordTrace_append hprefix tailTrace_520767
  have hstable : (prefixWord ++ tailWord_520767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520767).length < 2 ^ (prefixWord ++ tailWord_520767).sum := by decide
  have hdescent : baseEnd_520767 < baseStart_520767 := by decide
  rcases family_descends (prefixWord ++ tailWord_520767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520791 : List Nat := [1, 1, 3, 2, 2, 2, 5, 4]
def baseStart_520791 : Nat := 118140960795 + 520791 * 2 ^ 59
def prefixEnd_520791 : Nat := 4983230072969 + 3 ^ 40 * 520791 * 2
def baseEnd_520791 : Nat := 79234401047637670079239

theorem tailTrace_520791 : CollatzResearch.WordTrace tailWord_520791 prefixEnd_520791 79234401047637670079239 := by
  unfold tailWord_520791
  simp only [CollatzResearch.WordTrace]
  refine ⟨18994808256270625866714227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12663205504180417244476151 18994808256270625866714227)
  ·
    refine ⟨28492212384405938800071341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18994808256270625866714227 28492212384405938800071341)
    ·
      refine ⟨10684579644152227050026753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28492212384405938800071341 10684579644152227050026753)
      ·
        refine ⟨8013434733114170287520065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10684579644152227050026753 8013434733114170287520065)
        ·
          refine ⟨6010076049835627715640049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8013434733114170287520065 6010076049835627715640049)
          ·
            refine ⟨4507557037376720786730037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6010076049835627715640049 4507557037376720786730037)
            ·
              refine ⟨422583472254067573755941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4507557037376720786730037 422583472254067573755941)
              ·
                refine ⟨79234401047637670079239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 422583472254067573755941 79234401047637670079239)
                ·
                  rfl

theorem cell20_520791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 4].length) (baseStart_520791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520791 prefixEnd_520791 := by exact prefixLift 520791
  have htrace : WordTrace (prefixWord ++ tailWord_520791) baseStart_520791 baseEnd_520791 := by
    simpa [prefixWord, tailWord_520791, baseEnd_520791] using wordTrace_append hprefix tailTrace_520791
  have hstable : (prefixWord ++ tailWord_520791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520791).length < 2 ^ (prefixWord ++ tailWord_520791).sum := by decide
  have hdescent : baseEnd_520791 < baseStart_520791 := by decide
  rcases family_descends (prefixWord ++ tailWord_520791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520801 : List Nat := [1, 2, 3, 1, 1, 5, 2, 3, 2]
def baseStart_520801 : Nat := 118140960795 + 520801 * 2 ^ 59
def prefixEnd_520801 : Nat := 4983230072969 + 3 ^ 40 * 520801 * 2
def baseEnd_520801 : Nat := 237707767415397419904343

theorem tailTrace_520801 : CollatzResearch.WordTrace tailWord_520801 prefixEnd_520801 237707767415397419904343 := by
  unfold tailWord_520801
  simp only [CollatzResearch.WordTrace]
  refine ⟨18995172986234397574578257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12663448657489598383052171 18995172986234397574578257)
  ·
    refine ⟨14246379739675798180933693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18995172986234397574578257 14246379739675798180933693)
    ·
      refine ⟨5342392402378424317850135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14246379739675798180933693 5342392402378424317850135)
      ·
        refine ⟨8013588603567636476775203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5342392402378424317850135 8013588603567636476775203)
        ·
          refine ⟨12020382905351454715162805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8013588603567636476775203 12020382905351454715162805)
          ·
            refine ⟨1126910897376698879546513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12020382905351454715162805 1126910897376698879546513)
            ·
              refine ⟨845183173032524159659885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1126910897376698879546513 845183173032524159659885)
              ·
                refine ⟨316943689887196559872457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 845183173032524159659885 316943689887196559872457)
                ·
                  refine ⟨237707767415397419904343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316943689887196559872457 237707767415397419904343)
                  ·
                    rfl

theorem cell20_520801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 3, 2].length) (baseStart_520801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520801 prefixEnd_520801 := by exact prefixLift 520801
  have htrace : WordTrace (prefixWord ++ tailWord_520801) baseStart_520801 baseEnd_520801 := by
    simpa [prefixWord, tailWord_520801, baseEnd_520801] using wordTrace_append hprefix tailTrace_520801
  have hstable : (prefixWord ++ tailWord_520801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520801).length < 2 ^ (prefixWord ++ tailWord_520801).sum := by decide
  have hdescent : baseEnd_520801 < baseStart_520801 := by decide
  rcases family_descends (prefixWord ++ tailWord_520801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520857 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 7]
def baseStart_520857 : Nat := 118140960795 + 520857 * 2 ^ 59
def prefixEnd_520857 : Nat := 4983230072969 + 3 ^ 40 * 520857 * 2
def baseEnd_520857 : Nat := 237733327341310114037447

theorem tailTrace_520857 : CollatzResearch.WordTrace tailWord_520857 prefixEnd_520857 237733327341310114037447 := by
  unfold tailWord_520857
  simp only [CollatzResearch.WordTrace]
  refine ⟨18997215474031519138616825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12664810316021012759077883 18997215474031519138616825)
  ·
    refine ⟨14247911605523639353962619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18997215474031519138616825 14247911605523639353962619)
    ·
      refine ⟨21371867408285459030943929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14247911605523639353962619 21371867408285459030943929)
      ·
        refine ⟨16028900556214094273207947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21371867408285459030943929 16028900556214094273207947)
        ·
          refine ⟨24043350834321141409811921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16028900556214094273207947 24043350834321141409811921)
          ·
            refine ⟨18032513125740856057358941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24043350834321141409811921 18032513125740856057358941)
            ·
              refine ⟨6762192422152821021509603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18032513125740856057358941 6762192422152821021509603)
              ·
                refine ⟨10143288633229231532264405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6762192422152821021509603 10143288633229231532264405)
                ·
                  refine ⟨237733327341310114037447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10143288633229231532264405 237733327341310114037447)
                  ·
                    rfl

theorem cell20_520857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_520857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520857 prefixEnd_520857 := by exact prefixLift 520857
  have htrace : WordTrace (prefixWord ++ tailWord_520857) baseStart_520857 baseEnd_520857 := by
    simpa [prefixWord, tailWord_520857, baseEnd_520857] using wordTrace_append hprefix tailTrace_520857
  have hstable : (prefixWord ++ tailWord_520857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520857).length < 2 ^ (prefixWord ++ tailWord_520857).sum := by decide
  have hdescent : baseEnd_520857 < baseStart_520857 := by decide
  rcases family_descends (prefixWord ++ tailWord_520857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520877 : List Nat := [1, 5, 2, 1, 1, 4, 1, 1, 4]
def baseStart_520877 : Nat := 118140960795 + 520877 * 2 ^ 59
def prefixEnd_520877 : Nat := 4983230072969 + 3 ^ 40 * 520877 * 2
def baseEnd_520877 : Nat := 237742455886278933370699

theorem tailTrace_520877 : CollatzResearch.WordTrace tailWord_520877 prefixEnd_520877 237742455886278933370699 := by
  unfold tailWord_520877
  simp only [CollatzResearch.WordTrace]
  refine ⟨18997944933959062554344885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12665296622639375036229923 18997944933959062554344885)
  ·
    refine ⟨1781057337558662114469833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18997944933959062554344885 1781057337558662114469833)
    ·
      refine ⟨1335793003168996585852375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1781057337558662114469833 1335793003168996585852375)
      ·
        refine ⟨2003689504753494878778563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1335793003168996585852375 2003689504753494878778563)
        ·
          refine ⟨3005534257130242318167845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2003689504753494878778563 3005534257130242318167845)
          ·
            refine ⟨563537673211920434656471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3005534257130242318167845 563537673211920434656471)
            ·
              refine ⟨845306509817880651984707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563537673211920434656471 845306509817880651984707)
              ·
                refine ⟨1267959764726820977977061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 845306509817880651984707 1267959764726820977977061)
                ·
                  refine ⟨237742455886278933370699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1267959764726820977977061 237742455886278933370699)
                  ·
                    rfl

theorem cell20_520877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_520877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520877 prefixEnd_520877 := by exact prefixLift 520877
  have htrace : WordTrace (prefixWord ++ tailWord_520877) baseStart_520877 baseEnd_520877 := by
    simpa [prefixWord, tailWord_520877, baseEnd_520877] using wordTrace_append hprefix tailTrace_520877
  have hstable : (prefixWord ++ tailWord_520877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520877).length < 2 ^ (prefixWord ++ tailWord_520877).sum := by decide
  have hdescent : baseEnd_520877 < baseStart_520877 := by decide
  rcases family_descends (prefixWord ++ tailWord_520877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520887 : List Nat := [1, 1, 3, 1, 7, 1, 2, 1, 3]
def baseStart_520887 : Nat := 118140960795 + 520887 * 2 ^ 59
def prefixEnd_520887 : Nat := 4983230072969 + 3 ^ 40 * 520887 * 2
def baseEnd_520887 : Nat := 237747020158763343037325

theorem tailTrace_520887 : CollatzResearch.WordTrace tailWord_520887 prefixEnd_520887 237747020158763343037325 := by
  unfold tailWord_520887
  simp only [CollatzResearch.WordTrace]
  refine ⟨18998309663922834262208915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12665539775948556174805943 18998309663922834262208915)
  ·
    refine ⟨28497464495884251393313373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18998309663922834262208915 28497464495884251393313373)
    ·
      refine ⟨10686549185956594272492515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28497464495884251393313373 10686549185956594272492515)
      ·
        refine ⟨16029823778934891408738773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10686549185956594272492515 16029823778934891408738773)
        ·
          refine ⟨375698994818786517392315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 16029823778934891408738773 375698994818786517392315)
          ·
            refine ⟨563548492228179776088473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375698994818786517392315 563548492228179776088473)
            ·
              refine ⟨422661369171134832066355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 563548492228179776088473 422661369171134832066355)
              ·
                refine ⟨633992053756702248099533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 422661369171134832066355 633992053756702248099533)
                ·
                  refine ⟨237747020158763343037325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 633992053756702248099533 237747020158763343037325)
                  ·
                    rfl

theorem cell20_520887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 3].length) (baseStart_520887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520887 prefixEnd_520887 := by exact prefixLift 520887
  have htrace : WordTrace (prefixWord ++ tailWord_520887) baseStart_520887 baseEnd_520887 := by
    simpa [prefixWord, tailWord_520887, baseEnd_520887] using wordTrace_append hprefix tailTrace_520887
  have hstable : (prefixWord ++ tailWord_520887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520887).length < 2 ^ (prefixWord ++ tailWord_520887).sum := by decide
  have hdescent : baseEnd_520887 < baseStart_520887 := by decide
  rcases family_descends (prefixWord ++ tailWord_520887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520929 : List Nat := [1, 2, 3, 1, 4, 2, 2, 2, 3]
def baseStart_520929 : Nat := 118140960795 + 520929 * 2 ^ 59
def prefixEnd_520929 : Nat := 4983230072969 + 3 ^ 40 * 520929 * 2
def baseEnd_520929 : Nat := 237766190103197863637153

theorem tailTrace_520929 : CollatzResearch.WordTrace tailWord_520929 prefixEnd_520929 237766190103197863637153 := by
  unfold tailWord_520929
  simp only [CollatzResearch.WordTrace]
  refine ⟨18999841529770675435237841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12666561019847116956825227 18999841529770675435237841)
  ·
    refine ⟨14249881147328006576428381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18999841529770675435237841 14249881147328006576428381)
    ·
      refine ⟨5343705430248002466160643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14249881147328006576428381 5343705430248002466160643)
      ·
        refine ⟨8015558145372003699240965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5343705430248002466160643 8015558145372003699240965)
        ·
          refine ⟨1502917152257250693607681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8015558145372003699240965 1502917152257250693607681)
          ·
            refine ⟨1127187864192938020205761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1502917152257250693607681 1127187864192938020205761)
            ·
              refine ⟨845390898144703515154321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1127187864192938020205761 845390898144703515154321)
              ·
                refine ⟨634043173608527636365741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 845390898144703515154321 634043173608527636365741)
                ·
                  refine ⟨237766190103197863637153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 634043173608527636365741 237766190103197863637153)
                  ·
                    rfl

theorem cell20_520929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 3].length) (baseStart_520929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520929 prefixEnd_520929 := by exact prefixLift 520929
  have htrace : WordTrace (prefixWord ++ tailWord_520929) baseStart_520929 baseEnd_520929 := by
    simpa [prefixWord, tailWord_520929, baseEnd_520929] using wordTrace_append hprefix tailTrace_520929
  have hstable : (prefixWord ++ tailWord_520929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520929).length < 2 ^ (prefixWord ++ tailWord_520929).sum := by decide
  have hdescent : baseEnd_520929 < baseStart_520929 := by decide
  rcases family_descends (prefixWord ++ tailWord_520929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520932 : List Nat := [2, 3, 1, 1, 1, 6, 2, 2, 2]
def baseStart_520932 : Nat := 118140960795 + 520932 * 2 ^ 59
def prefixEnd_520932 : Nat := 4983230072969 + 3 ^ 40 * 520932 * 2
def baseEnd_520932 : Nat := 237767559384943186537141

theorem tailTrace_520932 : CollatzResearch.WordTrace tailWord_520932 prefixEnd_520932 237767559384943186537141 := by
  unfold tailWord_520932
  simp only [CollatzResearch.WordTrace]
  refine ⟨9499975474379903473798525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12666633965839871298398033 9499975474379903473798525)
  ·
    refine ⟨3562490802892463802674447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9499975474379903473798525 3562490802892463802674447)
    ·
      refine ⟨5343736204338695704011671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3562490802892463802674447 5343736204338695704011671)
      ·
        refine ⟨8015604306508043556017507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5343736204338695704011671 8015604306508043556017507)
        ·
          refine ⟨12023406459762065334026261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8015604306508043556017507 12023406459762065334026261)
          ·
            refine ⟨563597177801346812532481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12023406459762065334026261 563597177801346812532481)
            ·
              refine ⟨422697883351010109399361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 563597177801346812532481 422697883351010109399361)
              ·
                refine ⟨317023412513257582049521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 422697883351010109399361 317023412513257582049521)
                ·
                  refine ⟨237767559384943186537141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 317023412513257582049521 237767559384943186537141)
                  ·
                    rfl

theorem cell20_520932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_520932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520932 prefixEnd_520932 := by exact prefixLift 520932
  have htrace : WordTrace (prefixWord ++ tailWord_520932) baseStart_520932 baseEnd_520932 := by
    simpa [prefixWord, tailWord_520932, baseEnd_520932] using wordTrace_append hprefix tailTrace_520932
  have hstable : (prefixWord ++ tailWord_520932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520932).length < 2 ^ (prefixWord ++ tailWord_520932).sum := by decide
  have hdescent : baseEnd_520932 < baseStart_520932 := by decide
  rcases family_descends (prefixWord ++ tailWord_520932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520943 : List Nat := [1, 1, 2, 1, 5, 4, 1, 5]
def baseStart_520943 : Nat := 118140960795 + 520943 * 2 ^ 59
def prefixEnd_520943 : Nat := 4983230072969 + 3 ^ 40 * 520943 * 2
def baseEnd_520943 : Nat := 79257526694892012390143

theorem tailTrace_520943 : CollatzResearch.WordTrace tailWord_520943 prefixEnd_520943 79257526694892012390143 := by
  unfold tailWord_520943
  simp only [CollatzResearch.WordTrace]
  refine ⟨19000352151719955826247483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12666901434479970550831655 19000352151719955826247483)
  ·
    refine ⟨28500528227579933739371225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19000352151719955826247483 28500528227579933739371225)
    ·
      refine ⟨21375396170684950304528419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28500528227579933739371225 21375396170684950304528419)
      ·
        refine ⟨32063094256027425456792629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21375396170684950304528419 32063094256027425456792629)
        ·
          refine ⟨3005915086502571136574309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32063094256027425456792629 3005915086502571136574309)
          ·
            refine ⟨563609078719232088107683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3005915086502571136574309 563609078719232088107683)
            ·
              refine ⟨845413618078848132161525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563609078719232088107683 845413618078848132161525)
              ·
                refine ⟨79257526694892012390143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 845413618078848132161525 79257526694892012390143)
                ·
                  rfl

theorem cell20_520943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 5].length) (baseStart_520943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520943 prefixEnd_520943 := by exact prefixLift 520943
  have htrace : WordTrace (prefixWord ++ tailWord_520943) baseStart_520943 baseEnd_520943 := by
    simpa [prefixWord, tailWord_520943, baseEnd_520943] using wordTrace_append hprefix tailTrace_520943
  have hstable : (prefixWord ++ tailWord_520943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520943).length < 2 ^ (prefixWord ++ tailWord_520943).sum := by decide
  have hdescent : baseEnd_520943 < baseStart_520943 := by decide
  rcases family_descends (prefixWord ++ tailWord_520943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520957 : List Nat := [1, 4, 1, 1, 1, 1, 5, 2, 4]
def baseStart_520957 : Nat := 118140960795 + 520957 * 2 ^ 59
def prefixEnd_520957 : Nat := 4983230072969 + 3 ^ 40 * 520957 * 2
def baseEnd_520957 : Nat := 237778970066154210703705

theorem tailTrace_520957 : CollatzResearch.WordTrace tailWord_520957 prefixEnd_520957 237778970066154210703705 := by
  unfold tailWord_520957
  simp only [CollatzResearch.WordTrace]
  refine ⟨19000862773669236217257125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12667241849112824144838083 19000862773669236217257125)
  ·
    refine ⟨3562661770062981790735711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19000862773669236217257125 3562661770062981790735711)
    ·
      refine ⟨5343992655094472686103567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3562661770062981790735711 5343992655094472686103567)
      ·
        refine ⟨8015988982641709029155351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5343992655094472686103567 8015988982641709029155351)
        ·
          refine ⟨12023983473962563543733027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8015988982641709029155351 12023983473962563543733027)
          ·
            refine ⟨18035975210943845315599541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12023983473962563543733027 18035975210943845315599541)
            ·
              refine ⟨1690872676025985498337457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18035975210943845315599541 1690872676025985498337457)
              ·
                refine ⟨1268154507019489123753093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1690872676025985498337457 1268154507019489123753093)
                ·
                  refine ⟨237778970066154210703705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1268154507019489123753093 237778970066154210703705)
                  ·
                    rfl

theorem cell20_520957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_520957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520957 prefixEnd_520957 := by exact prefixLift 520957
  have htrace : WordTrace (prefixWord ++ tailWord_520957) baseStart_520957 baseEnd_520957 := by
    simpa [prefixWord, tailWord_520957, baseEnd_520957] using wordTrace_append hprefix tailTrace_520957
  have hstable : (prefixWord ++ tailWord_520957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520957).length < 2 ^ (prefixWord ++ tailWord_520957).sum := by decide
  have hdescent : baseEnd_520957 < baseStart_520957 := by decide
  rcases family_descends (prefixWord ++ tailWord_520957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520971 : List Nat := [1, 1, 1, 1, 5, 1, 1, 4, 5]
def baseStart_520971 : Nat := 118140960795 + 520971 * 2 ^ 59
def prefixEnd_520971 : Nat := 4983230072969 + 3 ^ 40 * 520971 * 2
def baseEnd_520971 : Nat := 237785360047632384236981

theorem tailTrace_520971 : CollatzResearch.WordTrace tailWord_520971 prefixEnd_520971 237785360047632384236981 := by
  unfold tailWord_520971
  simp only [CollatzResearch.WordTrace]
  refine ⟨19001373395618516608266767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12667582263745677738844511 19001373395618516608266767)
  ·
    refine ⟨28502060093427774912400151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19001373395618516608266767 28502060093427774912400151)
    ·
      refine ⟨42753090140141662368600227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28502060093427774912400151 42753090140141662368600227)
      ·
        refine ⟨64129635210212493552900341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42753090140141662368600227 64129635210212493552900341)
        ·
          refine ⟨6012153300957421270584407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64129635210212493552900341 6012153300957421270584407)
          ·
            refine ⟨9018229951436131905876611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6012153300957421270584407 9018229951436131905876611)
            ·
              refine ⟨13527344927154197858814917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9018229951436131905876611 13527344927154197858814917)
              ·
                refine ⟨2536377173841412098527797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13527344927154197858814917 2536377173841412098527797)
                ·
                  refine ⟨237785360047632384236981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2536377173841412098527797 237785360047632384236981)
                  ·
                    rfl

theorem cell20_520971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 5].length) (baseStart_520971 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520971 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520971 prefixEnd_520971 := by exact prefixLift 520971
  have htrace : WordTrace (prefixWord ++ tailWord_520971) baseStart_520971 baseEnd_520971 := by
    simpa [prefixWord, tailWord_520971, baseEnd_520971] using wordTrace_append hprefix tailTrace_520971
  have hstable : (prefixWord ++ tailWord_520971).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520971).length < 2 ^ (prefixWord ++ tailWord_520971).sum := by decide
  have hdescent : baseEnd_520971 < baseStart_520971 := by decide
  rcases family_descends (prefixWord ++ tailWord_520971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_520988 : List Nat := [2, 2, 3, 1, 1, 4, 1, 1, 5]
def baseStart_520988 : Nat := 118140960795 + 520988 * 2 ^ 59
def prefixEnd_520988 : Nat := 4983230072969 + 3 ^ 40 * 520988 * 2
def baseEnd_520988 : Nat := 237793119310855880670245

theorem tailTrace_520988 : CollatzResearch.WordTrace tailWord_520988 prefixEnd_520988 237793119310855880670245 := by
  unfold tailWord_520988
  simp only [CollatzResearch.WordTrace]
  refine ⟨9500996718278464255817809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12667995624371285674423745 9500996718278464255817809)
  ·
    refine ⟨7125747538708848191863357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9500996718278464255817809 7125747538708848191863357)
    ·
      refine ⟨2672155327015818071948759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7125747538708848191863357 2672155327015818071948759)
      ·
        refine ⟨4008232990523727107923139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2672155327015818071948759 4008232990523727107923139)
        ·
          refine ⟨6012349485785590661884709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4008232990523727107923139 6012349485785590661884709)
          ·
            refine ⟨1127315528584798249103383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6012349485785590661884709 1127315528584798249103383)
            ·
              refine ⟨1690973292877197373655075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1127315528584798249103383 1690973292877197373655075)
              ·
                refine ⟨2536459939315796060482613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1690973292877197373655075 2536459939315796060482613)
                ·
                  refine ⟨237793119310855880670245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2536459939315796060482613 237793119310855880670245)
                  ·
                    rfl

theorem cell20_520988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_520988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_520988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_520988 prefixEnd_520988 := by exact prefixLift 520988
  have htrace : WordTrace (prefixWord ++ tailWord_520988) baseStart_520988 baseEnd_520988 := by
    simpa [prefixWord, tailWord_520988, baseEnd_520988] using wordTrace_append hprefix tailTrace_520988
  have hstable : (prefixWord ++ tailWord_520988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_520988).length < 2 ^ (prefixWord ++ tailWord_520988).sum := by decide
  have hdescent : baseEnd_520988 < baseStart_520988 := by decide
  rcases family_descends (prefixWord ++ tailWord_520988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521025 : List Nat := [1, 2, 5, 3, 1, 2, 1, 3, 2]
def baseStart_521025 : Nat := 118140960795 + 521025 * 2 ^ 59
def prefixEnd_521025 : Nat := 4983230072969 + 3 ^ 40 * 521025 * 2
def baseEnd_521025 : Nat := 237810007119048196436761

theorem tailTrace_521025 : CollatzResearch.WordTrace tailWord_521025 prefixEnd_521025 237810007119048196436761 := by
  unfold tailWord_521025
  simp only [CollatzResearch.WordTrace]
  refine ⟨19003342937422883830732529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12668895291615255887155019 19003342937422883830732529)
  ·
    refine ⟨14252507203067162873049397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19003342937422883830732529 14252507203067162873049397)
    ·
      refine ⟨1336172550287546519348381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14252507203067162873049397 1336172550287546519348381)
      ·
        refine ⟨501064706357829944755643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1336172550287546519348381 501064706357829944755643)
        ·
          refine ⟨751597059536744917133465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501064706357829944755643 751597059536744917133465)
          ·
            refine ⟨563697794652558687850099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 751597059536744917133465 563697794652558687850099)
            ·
              refine ⟨845546691978838031775149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563697794652558687850099 845546691978838031775149)
              ·
                refine ⟨317080009492064261915681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 845546691978838031775149 317080009492064261915681)
                ·
                  refine ⟨237810007119048196436761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 317080009492064261915681 237810007119048196436761)
                  ·
                    rfl

theorem cell20_521025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 3, 2].length) (baseStart_521025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521025 prefixEnd_521025 := by exact prefixLift 521025
  have htrace : WordTrace (prefixWord ++ tailWord_521025) baseStart_521025 baseEnd_521025 := by
    simpa [prefixWord, tailWord_521025, baseEnd_521025] using wordTrace_append hprefix tailTrace_521025
  have hstable : (prefixWord ++ tailWord_521025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521025).length < 2 ^ (prefixWord ++ tailWord_521025).sum := by decide
  have hdescent : baseEnd_521025 < baseStart_521025 := by decide
  rcases family_descends (prefixWord ++ tailWord_521025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521050 : List Nat := [3, 1, 1, 2, 1, 6, 1, 1, 4]
def baseStart_521050 : Nat := 118140960795 + 521050 * 2 ^ 59
def prefixEnd_521050 : Nat := 4983230072969 + 3 ^ 40 * 521050 * 2
def baseEnd_521050 : Nat := 237821417800259220603325

theorem tailTrace_521050 : CollatzResearch.WordTrace tailWord_521050 prefixEnd_521050 237821417800259220603325 := by
  unfold tailWord_521050
  simp only [CollatzResearch.WordTrace]
  refine ⟨4751063690583078275098151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12669503174888208733595069 4751063690583078275098151)
  ·
    refine ⟨7126595535874617412647227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4751063690583078275098151 7126595535874617412647227)
    ·
      refine ⟨10689893303811926118970841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7126595535874617412647227 10689893303811926118970841)
      ·
        refine ⟨8017419977858944589228131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10689893303811926118970841 8017419977858944589228131)
        ·
          refine ⟨12026129966788416883842197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8017419977858944589228131 12026129966788416883842197)
          ·
            refine ⟨563724842193207041430103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12026129966788416883842197 563724842193207041430103)
            ·
              refine ⟨845587263289810562145155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563724842193207041430103 845587263289810562145155)
              ·
                refine ⟨1268380894934715843217733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 845587263289810562145155 1268380894934715843217733)
                ·
                  refine ⟨237821417800259220603325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1268380894934715843217733 237821417800259220603325)
                  ·
                    rfl

theorem cell20_521050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 4].length) (baseStart_521050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521050 prefixEnd_521050 := by exact prefixLift 521050
  have htrace : WordTrace (prefixWord ++ tailWord_521050) baseStart_521050 baseEnd_521050 := by
    simpa [prefixWord, tailWord_521050, baseEnd_521050] using wordTrace_append hprefix tailTrace_521050
  have hstable : (prefixWord ++ tailWord_521050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521050).length < 2 ^ (prefixWord ++ tailWord_521050).sum := by decide
  have hdescent : baseEnd_521050 < baseStart_521050 := by decide
  rcases family_descends (prefixWord ++ tailWord_521050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521060 : List Nat := [2, 3, 1, 1, 4, 3, 2, 1, 3]
def baseStart_521060 : Nat := 118140960795 + 521060 * 2 ^ 59
def prefixEnd_521060 : Nat := 4983230072969 + 3 ^ 40 * 521060 * 2
def baseEnd_521060 : Nat := 237825982072743630269951

theorem tailTrace_521060 : CollatzResearch.WordTrace tailWord_521060 prefixEnd_521060 237825982072743630269951 := by
  unfold tailWord_521060
  simp only [CollatzResearch.WordTrace]
  refine ⟨9502309746148042404128317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12669746328197389872171089 9502309746148042404128317)
  ·
    refine ⟨3563366154805515901548119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9502309746148042404128317 3563366154805515901548119)
    ·
      refine ⟨5345049232208273852322179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3563366154805515901548119 5345049232208273852322179)
      ·
        refine ⟨8017573848312410778483269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5345049232208273852322179 8017573848312410778483269)
        ·
          refine ⟨1503295096558577020965613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8017573848312410778483269 1503295096558577020965613)
          ·
            refine ⟨563735661209466382862105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1503295096558577020965613 563735661209466382862105)
            ·
              refine ⟨422801745907099787146579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 563735661209466382862105 422801745907099787146579)
              ·
                refine ⟨634202618860649680719869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 422801745907099787146579 634202618860649680719869)
                ·
                  refine ⟨237825982072743630269951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 634202618860649680719869 237825982072743630269951)
                  ·
                    rfl

theorem cell20_521060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_521060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521060 prefixEnd_521060 := by exact prefixLift 521060
  have htrace : WordTrace (prefixWord ++ tailWord_521060) baseStart_521060 baseEnd_521060 := by
    simpa [prefixWord, tailWord_521060, baseEnd_521060] using wordTrace_append hprefix tailTrace_521060
  have hstable : (prefixWord ++ tailWord_521060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521060).length < 2 ^ (prefixWord ++ tailWord_521060).sum := by decide
  have hdescent : baseEnd_521060 < baseStart_521060 := by decide
  rcases family_descends (prefixWord ++ tailWord_521060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521085 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 7]
def baseStart_521085 : Nat := 118140960795 + 521085 * 2 ^ 59
def prefixEnd_521085 : Nat := 4983230072969 + 3 ^ 40 * 521085 * 2
def baseEnd_521085 : Nat := 237837392753954654436515

theorem tailTrace_521085 : CollatzResearch.WordTrace tailWord_521085 prefixEnd_521085 237837392753954654436515 := by
  unfold tailWord_521085
  simp only [CollatzResearch.WordTrace]
  refine ⟨19005531317205514077916709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12670354211470342718611139 19005531317205514077916709)
  ·
    refine ⟨3563537121976033889609383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19005531317205514077916709 3563537121976033889609383)
    ·
      refine ⟨5345305682964050834414075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3563537121976033889609383 5345305682964050834414075)
      ·
        refine ⟨8017958524446076251621113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5345305682964050834414075 8017958524446076251621113)
        ·
          refine ⟨6013468893334557188715835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8017958524446076251621113 6013468893334557188715835)
          ·
            refine ⟨9020203340001835783073753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6013468893334557188715835 9020203340001835783073753)
            ·
              refine ⟨6765152505001376837305315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9020203340001835783073753 6765152505001376837305315)
              ·
                refine ⟨10147728757502065255957973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6765152505001376837305315 10147728757502065255957973)
                ·
                  refine ⟨237837392753954654436515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10147728757502065255957973 237837392753954654436515)
                  ·
                    rfl

theorem cell20_521085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_521085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521085 prefixEnd_521085 := by exact prefixLift 521085
  have htrace : WordTrace (prefixWord ++ tailWord_521085) baseStart_521085 baseEnd_521085 := by
    simpa [prefixWord, tailWord_521085, baseEnd_521085] using wordTrace_append hprefix tailTrace_521085
  have hstable : (prefixWord ++ tailWord_521085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521085).length < 2 ^ (prefixWord ++ tailWord_521085).sum := by decide
  have hdescent : baseEnd_521085 < baseStart_521085 := by decide
  rcases family_descends (prefixWord ++ tailWord_521085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521164 : List Nat := [2, 2, 1, 4, 1, 1, 1, 6, 2]
def baseStart_521164 : Nat := 118140960795 + 521164 * 2 ^ 59
def prefixEnd_521164 : Nat := 4983230072969 + 3 ^ 40 * 521164 * 2
def baseEnd_521164 : Nat := 237873450506581490802859

theorem tailTrace_521164 : CollatzResearch.WordTrace tailWord_521164 prefixEnd_521164 237873450506581490802859 := by
  unfold tailWord_521164
  simp only [CollatzResearch.WordTrace]
  refine ⟨9504206341959655285021273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12672275122612873713361697 9504206341959655285021273)
  ·
    refine ⟨7128154756469741463765955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9504206341959655285021273 7128154756469741463765955)
    ·
      refine ⟨10692232134704612195648933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7128154756469741463765955 10692232134704612195648933)
      ·
        refine ⟨2004793525257114786684175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10692232134704612195648933 2004793525257114786684175)
        ·
          refine ⟨3007190287885672180026263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2004793525257114786684175 3007190287885672180026263)
          ·
            refine ⟨4510785431828508270039395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3007190287885672180026263 4510785431828508270039395)
            ·
              refine ⟨6766178147742762405059093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4510785431828508270039395 6766178147742762405059093)
              ·
                refine ⟨317164600675441987737145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6766178147742762405059093 317164600675441987737145)
                ·
                  refine ⟨237873450506581490802859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 317164600675441987737145 237873450506581490802859)
                  ·
                    rfl

theorem cell20_521164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 6, 2].length) (baseStart_521164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521164 prefixEnd_521164 := by exact prefixLift 521164
  have htrace : WordTrace (prefixWord ++ tailWord_521164) baseStart_521164 baseEnd_521164 := by
    simpa [prefixWord, tailWord_521164, baseEnd_521164] using wordTrace_append hprefix tailTrace_521164
  have hstable : (prefixWord ++ tailWord_521164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521164).length < 2 ^ (prefixWord ++ tailWord_521164).sum := by decide
  have hdescent : baseEnd_521164 < baseStart_521164 := by decide
  rcases family_descends (prefixWord ++ tailWord_521164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521198 : List Nat := [4, 1, 2, 1, 4, 2, 1, 3, 2]
def baseStart_521198 : Nat := 118140960795 + 521198 * 2 ^ 59
def prefixEnd_521198 : Nat := 4983230072969 + 3 ^ 40 * 521198 * 2
def baseEnd_521198 : Nat := 237888969033028483669387

theorem tailTrace_521198 : CollatzResearch.WordTrace tailWord_521198 prefixEnd_521198 237888969033028483669387 := by
  unfold tailWord_521198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2376206595724516797097531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12673101843864089584520165 2376206595724516797097531)
  ·
    refine ⟨3564309893586775195646297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2376206595724516797097531 3564309893586775195646297)
    ·
      refine ⟨2673232420190081396734723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3564309893586775195646297 2673232420190081396734723)
      ·
        refine ⟨4009848630285122095102085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2673232420190081396734723 4009848630285122095102085)
        ·
          refine ⟨751846618178460392831641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4009848630285122095102085 751846618178460392831641)
          ·
            refine ⟨563884963633845294623731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 751846618178460392831641 563884963633845294623731)
            ·
              refine ⟨845827445450767941935597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 563884963633845294623731 845827445450767941935597)
              ·
                refine ⟨317185292044037978225849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 845827445450767941935597 317185292044037978225849)
                ·
                  refine ⟨237888969033028483669387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 317185292044037978225849 237888969033028483669387)
                  ·
                    rfl

theorem cell20_521198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_521198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521198 prefixEnd_521198 := by exact prefixLift 521198
  have htrace : WordTrace (prefixWord ++ tailWord_521198) baseStart_521198 baseEnd_521198 := by
    simpa [prefixWord, tailWord_521198, baseEnd_521198] using wordTrace_append hprefix tailTrace_521198
  have hstable : (prefixWord ++ tailWord_521198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521198).length < 2 ^ (prefixWord ++ tailWord_521198).sum := by decide
  have hdescent : baseEnd_521198 < baseStart_521198 := by decide
  rcases family_descends (prefixWord ++ tailWord_521198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521199 : List Nat := [1, 1, 2, 1, 4, 3, 1, 2, 5]
def baseStart_521199 : Nat := 118140960795 + 521199 * 2 ^ 59
def prefixEnd_521199 : Nat := 4983230072969 + 3 ^ 40 * 521199 * 2
def baseEnd_521199 : Nat := 237889425460276924636049

theorem tailTrace_521199 : CollatzResearch.WordTrace tailWord_521199 prefixEnd_521199 237889425460276924636049 := by
  unfold tailWord_521199
  simp only [CollatzResearch.WordTrace]
  refine ⟨19009689238792511547566651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12673126159195007698377767 19009689238792511547566651)
  ·
    refine ⟨28514533858188767321349977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19009689238792511547566651 28514533858188767321349977)
    ·
      refine ⟨21385900393641575491012483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28514533858188767321349977 21385900393641575491012483)
      ·
        refine ⟨32078850590462363236518725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21385900393641575491012483 32078850590462363236518725)
        ·
          refine ⟨6014784485711693106847261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32078850590462363236518725 6014784485711693106847261)
          ·
            refine ⟨2255544182141884915067723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6014784485711693106847261 2255544182141884915067723)
            ·
              refine ⟨3383316273212827372601585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2255544182141884915067723 3383316273212827372601585)
              ·
                refine ⟨2537487204909620529451189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3383316273212827372601585 2537487204909620529451189)
                ·
                  refine ⟨237889425460276924636049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2537487204909620529451189 237889425460276924636049)
                  ·
                    rfl

theorem cell20_521199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 5].length) (baseStart_521199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521199 prefixEnd_521199 := by exact prefixLift 521199
  have htrace : WordTrace (prefixWord ++ tailWord_521199) baseStart_521199 baseEnd_521199 := by
    simpa [prefixWord, tailWord_521199, baseEnd_521199] using wordTrace_append hprefix tailTrace_521199
  have hstable : (prefixWord ++ tailWord_521199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521199).length < 2 ^ (prefixWord ++ tailWord_521199).sum := by decide
  have hdescent : baseEnd_521199 < baseStart_521199 := by decide
  rcases family_descends (prefixWord ++ tailWord_521199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521205 : List Nat := [1, 3, 5, 2, 2, 1, 6]
def baseStart_521205 : Nat := 118140960795 + 521205 * 2 ^ 59
def prefixEnd_521205 : Nat := 4983230072969 + 3 ^ 40 * 521205 * 2
def baseEnd_521205 : Nat := 26432462669307507826225

theorem tailTrace_521205 : CollatzResearch.WordTrace tailWord_521205 prefixEnd_521205 26432462669307507826225 := by
  unfold tailWord_521205
  simp only [CollatzResearch.WordTrace]
  refine ⟨19009908076770774572285069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12673272051180516381523379 19009908076770774572285069)
  ·
    refine ⟨7128715528789040464606901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19009908076770774572285069 7128715528789040464606901)
    ·
      refine ⟨668317080823972543556897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7128715528789040464606901 668317080823972543556897)
      ·
        refine ⟨501237810617979407667673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 668317080823972543556897 501237810617979407667673)
        ·
          refine ⟨375928357963484555750755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 501237810617979407667673 375928357963484555750755)
          ·
            refine ⟨563892536945226833626133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375928357963484555750755 563892536945226833626133)
            ·
              refine ⟨26432462669307507826225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 563892536945226833626133 26432462669307507826225)
              ·
                rfl

theorem cell20_521205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 6].length) (baseStart_521205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521205 prefixEnd_521205 := by exact prefixLift 521205
  have htrace : WordTrace (prefixWord ++ tailWord_521205) baseStart_521205 baseEnd_521205 := by
    simpa [prefixWord, tailWord_521205, baseEnd_521205] using wordTrace_append hprefix tailTrace_521205
  have hstable : (prefixWord ++ tailWord_521205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521205).length < 2 ^ (prefixWord ++ tailWord_521205).sum := by decide
  have hdescent : baseEnd_521205 < baseStart_521205 := by decide
  rcases family_descends (prefixWord ++ tailWord_521205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521230 : List Nat := [4, 1, 1, 2, 2, 2, 1, 7]
def baseStart_521230 : Nat := 118140960795 + 521230 * 2 ^ 59
def prefixEnd_521230 : Nat := 4983230072969 + 3 ^ 40 * 521230 * 2
def baseEnd_521230 : Nat := 79301191568326198200863

theorem tailTrace_521230 : CollatzResearch.WordTrace tailWord_521230 prefixEnd_521230 79301191568326198200863 := by
  unfold tailWord_521230
  simp only [CollatzResearch.WordTrace]
  refine ⟨2376352487710025480243143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12673879934453469227963429 2376352487710025480243143)
  ·
    refine ⟨3564528731565038220364715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2376352487710025480243143 3564528731565038220364715)
    ·
      refine ⟨5346793097347557330547073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3564528731565038220364715 5346793097347557330547073)
      ·
        refine ⟨4010094823010667997910305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5346793097347557330547073 4010094823010667997910305)
        ·
          refine ⟨3007571117258000998432729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4010094823010667997910305 3007571117258000998432729)
          ·
            refine ⟨2255678337943500748824547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3007571117258000998432729 2255678337943500748824547)
            ·
              refine ⟨3383517506915251123236821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2255678337943500748824547 3383517506915251123236821)
              ·
                refine ⟨79301191568326198200863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3383517506915251123236821 79301191568326198200863)
                ·
                  rfl

theorem cell20_521230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_521230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521230 prefixEnd_521230 := by exact prefixLift 521230
  have htrace : WordTrace (prefixWord ++ tailWord_521230) baseStart_521230 baseEnd_521230 := by
    simpa [prefixWord, tailWord_521230, baseEnd_521230] using wordTrace_append hprefix tailTrace_521230
  have hstable : (prefixWord ++ tailWord_521230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521230).length < 2 ^ (prefixWord ++ tailWord_521230).sum := by decide
  have hdescent : baseEnd_521230 < baseStart_521230 := by decide
  rcases family_descends (prefixWord ++ tailWord_521230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521289 : List Nat := [1, 2, 1, 1, 2, 2, 2, 9]
def baseStart_521289 : Nat := 118140960795 + 521289 * 2 ^ 59
def prefixEnd_521289 : Nat := 4983230072969 + 3 ^ 40 * 521289 * 2
def baseEnd_521289 : Nat := 79310167970878870545227

theorem tailTrace_521289 : CollatzResearch.WordTrace tailWord_521289 prefixEnd_521289 79310167970878870545227 := by
  unfold tailWord_521289
  simp only [CollatzResearch.WordTrace]
  refine ⟨19012971808466456918342921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12675314538977637945561947 19012971808466456918342921)
  ·
    refine ⟨14259728856349842688757191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19012971808466456918342921 14259728856349842688757191)
    ·
      refine ⟨21389593284524764033135787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14259728856349842688757191 21389593284524764033135787)
      ·
        refine ⟨32084389926787146049703681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21389593284524764033135787 32084389926787146049703681)
        ·
          refine ⟨24063292445090359537277761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32084389926787146049703681 24063292445090359537277761)
          ·
            refine ⟨18047469333817769652958321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24063292445090359537277761 18047469333817769652958321)
            ·
              refine ⟨13535602000363327239718741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18047469333817769652958321 13535602000363327239718741)
              ·
                refine ⟨79310167970878870545227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13535602000363327239718741 79310167970878870545227)
                ·
                  rfl

theorem cell20_521289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 9].length) (baseStart_521289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521289 prefixEnd_521289 := by exact prefixLift 521289
  have htrace : WordTrace (prefixWord ++ tailWord_521289) baseStart_521289 baseEnd_521289 := by
    simpa [prefixWord, tailWord_521289, baseEnd_521289] using wordTrace_append hprefix tailTrace_521289
  have hstable : (prefixWord ++ tailWord_521289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521289).length < 2 ^ (prefixWord ++ tailWord_521289).sum := by decide
  have hdescent : baseEnd_521289 < baseStart_521289 := by decide
  rcases family_descends (prefixWord ++ tailWord_521289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521327 : List Nat := [1, 1, 2, 1, 3, 3, 9]
def baseStart_521327 : Nat := 118140960795 + 521327 * 2 ^ 59
def prefixEnd_521327 : Nat := 4983230072969 + 3 ^ 40 * 521327 * 2
def baseEnd_521327 : Nat := 26438649794230818707651

theorem tailTrace_521327 : CollatzResearch.WordTrace tailWord_521327 prefixEnd_521327 26438649794230818707651 := by
  unfold tailWord_521327
  simp only [CollatzResearch.WordTrace]
  refine ⟨19014357782328789408226235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12676238521552526272150823 19014357782328789408226235)
  ·
    refine ⟨28521536673493184112339353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19014357782328789408226235 28521536673493184112339353)
    ·
      refine ⟨21391152505119888084254515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28521536673493184112339353 21391152505119888084254515)
      ·
        refine ⟨32086728757679832126381773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21391152505119888084254515 32086728757679832126381773)
        ·
          refine ⟨12032523284129937047393165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32086728757679832126381773 12032523284129937047393165)
          ·
            refine ⟨4512196231548726392772437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12032523284129937047393165 4512196231548726392772437)
            ·
              refine ⟨26438649794230818707651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4512196231548726392772437 26438649794230818707651)
              ·
                rfl

theorem cell20_521327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 9].length) (baseStart_521327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521327 prefixEnd_521327 := by exact prefixLift 521327
  have htrace : WordTrace (prefixWord ++ tailWord_521327) baseStart_521327 baseEnd_521327 := by
    simpa [prefixWord, tailWord_521327, baseEnd_521327] using wordTrace_append hprefix tailTrace_521327
  have hstable : (prefixWord ++ tailWord_521327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521327).length < 2 ^ (prefixWord ++ tailWord_521327).sum := by decide
  have hdescent : baseEnd_521327 < baseStart_521327 := by decide
  rcases family_descends (prefixWord ++ tailWord_521327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521333 : List Nat := [1, 3, 4, 3, 1, 1, 2, 1, 4]
def baseStart_521333 : Nat := 118140960795 + 521333 * 2 ^ 59
def prefixEnd_521333 : Nat := 4983230072969 + 3 ^ 40 * 521333 * 2
def baseEnd_521333 : Nat := 237950586711568014168835

theorem tailTrace_521333 : CollatzResearch.WordTrace tailWord_521333 prefixEnd_521333 237950586711568014168835 := by
  unfold tailWord_521333
  simp only [CollatzResearch.WordTrace]
  refine ⟨19014576620307052432944653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12676384413538034955296435 19014576620307052432944653)
  ·
    refine ⟨7130466232615144662354245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19014576620307052432944653 7130466232615144662354245)
    ·
      refine ⟨1336962418615339624191421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7130466232615144662354245 1336962418615339624191421)
      ·
        refine ⟨501360906980752359071783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1336962418615339624191421 501360906980752359071783)
        ·
          refine ⟨752041360471128538607675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501360906980752359071783 752041360471128538607675)
          ·
            refine ⟨1128062040706692807911513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752041360471128538607675 1128062040706692807911513)
            ·
              refine ⟨846046530530019605933635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1128062040706692807911513 846046530530019605933635)
              ·
                refine ⟨1269069795795029408900453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 846046530530019605933635 1269069795795029408900453)
                ·
                  refine ⟨237950586711568014168835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1269069795795029408900453 237950586711568014168835)
                  ·
                    rfl

theorem cell20_521333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 4].length) (baseStart_521333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521333 prefixEnd_521333 := by exact prefixLift 521333
  have htrace : WordTrace (prefixWord ++ tailWord_521333) baseStart_521333 baseEnd_521333 := by
    simpa [prefixWord, tailWord_521333, baseEnd_521333] using wordTrace_append hprefix tailTrace_521333
  have hstable : (prefixWord ++ tailWord_521333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521333).length < 2 ^ (prefixWord ++ tailWord_521333).sum := by decide
  have hdescent : baseEnd_521333 < baseStart_521333 := by decide
  rcases family_descends (prefixWord ++ tailWord_521333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521378 : List Nat := [3, 3, 1, 3, 3, 1, 6]
def baseStart_521378 : Nat := 118140960795 + 521378 * 2 ^ 59
def prefixEnd_521378 : Nat := 4983230072969 + 3 ^ 40 * 521378 * 2
def baseEnd_521378 : Nat := 26441236215305317518739

theorem tailTrace_521378 : CollatzResearch.WordTrace tailWord_521378 prefixEnd_521378 26441236215305317518739 := by
  unfold tailWord_521378
  simp only [CollatzResearch.WordTrace]
  refine ⟨4754054476286006279583197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12677478603429350078888525 4754054476286006279583197)
  ·
    refine ⟨1782770428607252354843699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4754054476286006279583197 1782770428607252354843699)
    ·
      refine ⟨2674155642910878532265549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1782770428607252354843699 2674155642910878532265549)
      ·
        refine ⟨1002808366091579449599581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2674155642910878532265549 1002808366091579449599581)
        ·
          refine ⟨376053137284342293599843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1002808366091579449599581 376053137284342293599843)
          ·
            refine ⟨564079705926513440399765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376053137284342293599843 564079705926513440399765)
            ·
              refine ⟨26441236215305317518739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 564079705926513440399765 26441236215305317518739)
              ·
                rfl

theorem cell20_521378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 6].length) (baseStart_521378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521378 prefixEnd_521378 := by exact prefixLift 521378
  have htrace : WordTrace (prefixWord ++ tailWord_521378) baseStart_521378 baseEnd_521378 := by
    simpa [prefixWord, tailWord_521378, baseEnd_521378] using wordTrace_append hprefix tailTrace_521378
  have hstable : (prefixWord ++ tailWord_521378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521378).length < 2 ^ (prefixWord ++ tailWord_521378).sum := by decide
  have hdescent : baseEnd_521378 < baseStart_521378 := by decide
  rcases family_descends (prefixWord ++ tailWord_521378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521398 : List Nat := [5, 1, 3, 2, 1, 2, 2, 1, 3]
def baseStart_521398 : Nat := 118140960795 + 521398 * 2 ^ 59
def prefixEnd_521398 : Nat := 4983230072969 + 3 ^ 40 * 521398 * 2
def baseEnd_521398 : Nat := 237980254482716677001903

theorem tailTrace_521398 : CollatzResearch.WordTrace tailWord_521398 prefixEnd_521398 237980254482716677001903 := by
  unfold tailWord_521398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1188559210316973033378803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12677964910047712356040565 1188559210316973033378803)
  ·
    refine ⟨1782838815475459550068205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1188559210316973033378803 1782838815475459550068205)
    ·
      refine ⟨668564555803297331275577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1782838815475459550068205 668564555803297331275577)
      ·
        refine ⟨501423416852472998456683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 668564555803297331275577 501423416852472998456683)
        ·
          refine ⟨752135125278709497685025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501423416852472998456683 752135125278709497685025)
          ·
            refine ⟨564101343959032123263769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 752135125278709497685025 564101343959032123263769)
            ·
              refine ⟨423076007969274092447827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 564101343959032123263769 423076007969274092447827)
              ·
                refine ⟨634614011953911138671741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423076007969274092447827 634614011953911138671741)
                ·
                  refine ⟨237980254482716677001903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 634614011953911138671741 237980254482716677001903)
                  ·
                    rfl

theorem cell20_521398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_521398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521398 prefixEnd_521398 := by exact prefixLift 521398
  have htrace : WordTrace (prefixWord ++ tailWord_521398) baseStart_521398 baseEnd_521398 := by
    simpa [prefixWord, tailWord_521398, baseEnd_521398] using wordTrace_append hprefix tailTrace_521398
  have hstable : (prefixWord ++ tailWord_521398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521398).length < 2 ^ (prefixWord ++ tailWord_521398).sum := by decide
  have hdescent : baseEnd_521398 < baseStart_521398 := by decide
  rcases family_descends (prefixWord ++ tailWord_521398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521437 : List Nat := [1, 4, 3, 2, 3, 7]
def baseStart_521437 : Nat := 118140960795 + 521437 * 2 ^ 59
def prefixEnd_521437 : Nat := 4983230072969 + 3 ^ 40 * 521437 * 2
def baseEnd_521437 : Nat := 8814742783163180544509

theorem tailTrace_521437 : CollatzResearch.WordTrace tailWord_521437 prefixEnd_521437 8814742783163180544509 := by
  unfold tailWord_521437
  simp only [CollatzResearch.WordTrace]
  refine ⟨19018369811930278194730565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12678913207953518796487043 19018369811930278194730565)
  ·
    refine ⟨3565944339736927161511981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19018369811930278194730565 3565944339736927161511981)
    ·
      refine ⟨1337229127401347685566993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3565944339736927161511981 1337229127401347685566993)
      ·
        refine ⟨1002921845551010764175245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1337229127401347685566993 1002921845551010764175245)
        ·
          refine ⟨376095692081629036565717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1002921845551010764175245 376095692081629036565717)
          ·
            refine ⟨8814742783163180544509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 376095692081629036565717 8814742783163180544509)
            ·
              rfl

theorem cell20_521437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 7].length) (baseStart_521437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521437 prefixEnd_521437 := by exact prefixLift 521437
  have htrace : WordTrace (prefixWord ++ tailWord_521437) baseStart_521437 baseEnd_521437 := by
    simpa [prefixWord, tailWord_521437, baseEnd_521437] using wordTrace_append hprefix tailTrace_521437
  have hstable : (prefixWord ++ tailWord_521437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521437).length < 2 ^ (prefixWord ++ tailWord_521437).sum := by decide
  have hdescent : baseEnd_521437 < baseStart_521437 := by decide
  rcases family_descends (prefixWord ++ tailWord_521437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521441 : List Nat := [1, 2, 3, 1, 3, 10]
def baseStart_521441 : Nat := 118140960795 + 521441 * 2 ^ 59
def prefixEnd_521441 : Nat := 4983230072969 + 3 ^ 40 * 521441 * 2
def baseEnd_521441 : Nat := 8814810402014801428459

theorem tailTrace_521441 : CollatzResearch.WordTrace tailWord_521441 prefixEnd_521441 8814810402014801428459 := by
  unfold tailWord_521441
  simp only [CollatzResearch.WordTrace]
  refine ⟨19018515703915786877876177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12679010469277191251917451 19018515703915786877876177)
  ·
    refine ⟨14263886777936840158407133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19018515703915786877876177 14263886777936840158407133)
    ·
      refine ⟨5348957541726315059402675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14263886777936840158407133 5348957541726315059402675)
      ·
        refine ⟨8023436312589472589104013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5348957541726315059402675 8023436312589472589104013)
        ·
          refine ⟨3008788617221052220914005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8023436312589472589104013 3008788617221052220914005)
          ·
            refine ⟨8814810402014801428459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3008788617221052220914005 8814810402014801428459)
            ·
              rfl

theorem cell20_521441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 10].length) (baseStart_521441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521441 prefixEnd_521441 := by exact prefixLift 521441
  have htrace : WordTrace (prefixWord ++ tailWord_521441) baseStart_521441 baseEnd_521441 := by
    simpa [prefixWord, tailWord_521441, baseEnd_521441] using wordTrace_append hprefix tailTrace_521441
  have hstable : (prefixWord ++ tailWord_521441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521441).length < 2 ^ (prefixWord ++ tailWord_521441).sum := by decide
  have hdescent : baseEnd_521441 < baseStart_521441 := by decide
  rcases family_descends (prefixWord ++ tailWord_521441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521447 : List Nat := [1, 1, 5, 3, 2, 1, 1, 4, 2]
def baseStart_521447 : Nat := 118140960795 + 521447 * 2 ^ 59
def prefixEnd_521447 : Nat := 4983230072969 + 3 ^ 40 * 521447 * 2
def baseEnd_521447 : Nat := 238002619417890284368369

theorem tailTrace_521447 : CollatzResearch.WordTrace tailWord_521447 prefixEnd_521447 238002619417890284368369 := by
  unfold tailWord_521447
  simp only [CollatzResearch.WordTrace]
  refine ⟨19018734541894049902594595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12679156361262699935063063 19018734541894049902594595)
  ·
    refine ⟨28528101812841074853891893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19018734541894049902594595 28528101812841074853891893)
    ·
      refine ⟨2674509544953850767552365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28528101812841074853891893 2674509544953850767552365)
      ·
        refine ⟨1002941079357694037832137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2674509544953850767552365 1002941079357694037832137)
        ·
          refine ⟨752205809518270528374103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1002941079357694037832137 752205809518270528374103)
          ·
            refine ⟨1128308714277405792561155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752205809518270528374103 1128308714277405792561155)
            ·
              refine ⟨1692463071416108688841733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1128308714277405792561155 1692463071416108688841733)
              ·
                refine ⟨317336825890520379157825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1692463071416108688841733 317336825890520379157825)
                ·
                  refine ⟨238002619417890284368369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 317336825890520379157825 238002619417890284368369)
                  ·
                    rfl

theorem cell20_521447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 4, 2].length) (baseStart_521447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521447 prefixEnd_521447 := by exact prefixLift 521447
  have htrace : WordTrace (prefixWord ++ tailWord_521447) baseStart_521447 baseEnd_521447 := by
    simpa [prefixWord, tailWord_521447, baseEnd_521447] using wordTrace_append hprefix tailTrace_521447
  have hstable : (prefixWord ++ tailWord_521447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521447).length < 2 ^ (prefixWord ++ tailWord_521447).sum := by decide
  have hdescent : baseEnd_521447 < baseStart_521447 := by decide
  rcases family_descends (prefixWord ++ tailWord_521447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521465 : List Nat := [1, 2, 1, 3, 1, 1, 3, 5, 3]
def baseStart_521465 : Nat := 118140960795 + 521465 * 2 ^ 59
def prefixEnd_521465 : Nat := 4983230072969 + 3 ^ 40 * 521465 * 2
def baseEnd_521465 : Nat := 238010835108362221768295

theorem tailTrace_521465 : CollatzResearch.WordTrace tailWord_521465 prefixEnd_521465 238010835108362221768295 := by
  unfold tailWord_521465
  simp only [CollatzResearch.WordTrace]
  refine ⟨19019391055828838976749849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12679594037219225984499899 19019391055828838976749849)
  ·
    refine ⟨14264543291871629232562387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19019391055828838976749849 14264543291871629232562387)
    ·
      refine ⟨21396814937807443848843581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14264543291871629232562387 21396814937807443848843581)
      ·
        refine ⟨8023805601677791443316343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21396814937807443848843581 8023805601677791443316343)
        ·
          refine ⟨12035708402516687164974515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8023805601677791443316343 12035708402516687164974515)
          ·
            refine ⟨18053562603775030747461773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12035708402516687164974515 18053562603775030747461773)
            ·
              refine ⟨6770085976415636530298165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18053562603775030747461773 6770085976415636530298165)
              ·
                refine ⟨634695560288965924715453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6770085976415636530298165 634695560288965924715453)
                ·
                  refine ⟨238010835108362221768295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 634695560288965924715453 238010835108362221768295)
                  ·
                    rfl

theorem cell20_521465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 5, 3].length) (baseStart_521465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521465 prefixEnd_521465 := by exact prefixLift 521465
  have htrace : WordTrace (prefixWord ++ tailWord_521465) baseStart_521465 baseEnd_521465 := by
    simpa [prefixWord, tailWord_521465, baseEnd_521465] using wordTrace_append hprefix tailTrace_521465
  have hstable : (prefixWord ++ tailWord_521465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521465).length < 2 ^ (prefixWord ++ tailWord_521465).sum := by decide
  have hdescent : baseEnd_521465 < baseStart_521465 := by decide
  rcases family_descends (prefixWord ++ tailWord_521465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521506 : List Nat := [3, 3, 1, 1, 4, 1, 2, 1, 4]
def baseStart_521506 : Nat := 118140960795 + 521506 * 2 ^ 59
def prefixEnd_521506 : Nat := 4983230072969 + 3 ^ 40 * 521506 * 2
def baseEnd_521506 : Nat := 238029548625548301401461

theorem tailTrace_521506 : CollatzResearch.WordTrace tailWord_521506 prefixEnd_521506 238029548625548301401461 := by
  unfold tailWord_521506
  simp only [CollatzResearch.WordTrace]
  refine ⟨4755221612170075744748093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12680590965786868652661581 4755221612170075744748093)
  ·
    refine ⟨1783208104563778404280535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4755221612170075744748093 1783208104563778404280535)
    ·
      refine ⟨2674812156845667606420803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1783208104563778404280535 2674812156845667606420803)
      ·
        refine ⟨4012218235268501409631205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2674812156845667606420803 4012218235268501409631205)
        ·
          refine ⟨752290919112844014305851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4012218235268501409631205 752290919112844014305851)
          ·
            refine ⟨1128436378669266021458777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752290919112844014305851 1128436378669266021458777)
            ·
              refine ⟨846327284001949516094083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1128436378669266021458777 846327284001949516094083)
              ·
                refine ⟨1269490926002924274141125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 846327284001949516094083 1269490926002924274141125)
                ·
                  refine ⟨238029548625548301401461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1269490926002924274141125 238029548625548301401461)
                  ·
                    rfl

theorem cell20_521506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_521506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521506 prefixEnd_521506 := by exact prefixLift 521506
  have htrace : WordTrace (prefixWord ++ tailWord_521506) baseStart_521506 baseEnd_521506 := by
    simpa [prefixWord, tailWord_521506, baseEnd_521506] using wordTrace_append hprefix tailTrace_521506
  have hstable : (prefixWord ++ tailWord_521506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521506).length < 2 ^ (prefixWord ++ tailWord_521506).sum := by decide
  have hdescent : baseEnd_521506 < baseStart_521506 := by decide
  rcases family_descends (prefixWord ++ tailWord_521506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521520 : List Nat := [2, 1, 1, 1, 2, 2, 7, 1, 3]
def baseStart_521520 : Nat := 118140960795 + 521520 * 2 ^ 59
def prefixEnd_521520 : Nat := 4983230072969 + 3 ^ 40 * 521520 * 2
def baseEnd_521520 : Nat := 238035938607026474934737

theorem tailTrace_521520 : CollatzResearch.WordTrace tailWord_521520 prefixEnd_521520 238035938607026474934737 := by
  unfold tailWord_521520
  simp only [CollatzResearch.WordTrace]
  refine ⟨9510698535314791685001007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12680931380419722246668009 9510698535314791685001007)
  ·
    refine ⟨14266047802972187527501511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9510698535314791685001007 14266047802972187527501511)
    ·
      refine ⟨21399071704458281291252267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14266047802972187527501511 21399071704458281291252267)
      ·
        refine ⟨32098607556687421936878401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21399071704458281291252267 32098607556687421936878401)
        ·
          refine ⟨24073955667515566452658801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32098607556687421936878401 24073955667515566452658801)
          ·
            refine ⟨18055466750636674839494101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24073955667515566452658801 18055466750636674839494101)
            ·
              refine ⟨423175001968047066550643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 18055466750636674839494101 423175001968047066550643)
              ·
                refine ⟨634762502952070599825965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423175001968047066550643 634762502952070599825965)
                ·
                  refine ⟨238035938607026474934737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 634762502952070599825965 238035938607026474934737)
                  ·
                    rfl

theorem cell20_521520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 3].length) (baseStart_521520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521520 prefixEnd_521520 := by exact prefixLift 521520
  have htrace : WordTrace (prefixWord ++ tailWord_521520) baseStart_521520 baseEnd_521520 := by
    simpa [prefixWord, tailWord_521520, baseEnd_521520] using wordTrace_append hprefix tailTrace_521520
  have hstable : (prefixWord ++ tailWord_521520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521520).length < 2 ^ (prefixWord ++ tailWord_521520).sum := by decide
  have hdescent : baseEnd_521520 < baseStart_521520 := by decide
  rcases family_descends (prefixWord ++ tailWord_521520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521526 : List Nat := [5, 1, 2, 3, 2, 1, 2, 4]
def baseStart_521526 : Nat := 118140960795 + 521526 * 2 ^ 59
def prefixEnd_521526 : Nat := 4983230072969 + 3 ^ 40 * 521526 * 2
def baseEnd_521526 : Nat := 79346225723505706911571

theorem tailTrace_521526 : CollatzResearch.WordTrace tailWord_521526 prefixEnd_521526 79346225723505706911571 := by
  unfold tailWord_521526
  simp only [CollatzResearch.WordTrace]
  refine ⟨1188850994287990399670027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12681077272405230929813621 1188850994287990399670027)
  ·
    refine ⟨1783276491431985599505041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1188850994287990399670027 1783276491431985599505041)
    ·
      refine ⟨1337457368573989199628781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1783276491431985599505041 1337457368573989199628781)
      ·
        refine ⟨501546513215245949860793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1337457368573989199628781 501546513215245949860793)
        ·
          refine ⟨376159884911434462395595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 501546513215245949860793 376159884911434462395595)
          ·
            refine ⟨564239827367151693593393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376159884911434462395595 564239827367151693593393)
            ·
              refine ⟨423179870525363770195045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 564239827367151693593393 423179870525363770195045)
              ·
                refine ⟨79346225723505706911571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 423179870525363770195045 79346225723505706911571)
                ·
                  rfl

theorem cell20_521526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_521526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521526 prefixEnd_521526 := by exact prefixLift 521526
  have htrace : WordTrace (prefixWord ++ tailWord_521526) baseStart_521526 baseEnd_521526 := by
    simpa [prefixWord, tailWord_521526, baseEnd_521526] using wordTrace_append hprefix tailTrace_521526
  have hstable : (prefixWord ++ tailWord_521526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521526).length < 2 ^ (prefixWord ++ tailWord_521526).sum := by decide
  have hdescent : baseEnd_521526 < baseStart_521526 := by decide
  rcases family_descends (prefixWord ++ tailWord_521526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521534 : List Nat := [4, 2, 1, 2, 1, 1, 3, 6]
def baseStart_521534 : Nat := 118140960795 + 521534 * 2 ^ 59
def prefixEnd_521534 : Nat := 4983230072969 + 3 ^ 40 * 521534 * 2
def baseEnd_521534 : Nat := 79347442862834882822671

theorem tailTrace_521534 : CollatzResearch.WordTrace tailWord_521534 prefixEnd_521534 79347442862834882822671 := by
  unfold tailWord_521534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2377738461572357970126457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12681271795052575840674437 2377738461572357970126457)
  ·
    refine ⟨1783303846179268477594843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2377738461572357970126457 1783303846179268477594843)
    ·
      refine ⟨2674955769268902716392265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1783303846179268477594843 2674955769268902716392265)
      ·
        refine ⟨2006216826951677037294199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2674955769268902716392265 2006216826951677037294199)
        ·
          refine ⟨3009325240427515555941299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2006216826951677037294199 3009325240427515555941299)
          ·
            refine ⟨4513987860641273333911949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3009325240427515555941299 4513987860641273333911949)
            ·
              refine ⟨1692745447740477500216981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4513987860641273333911949 1692745447740477500216981)
              ·
                refine ⟨79347442862834882822671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1692745447740477500216981 79347442862834882822671)
                ·
                  rfl

theorem cell20_521534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_521534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521534 prefixEnd_521534 := by exact prefixLift 521534
  have htrace : WordTrace (prefixWord ++ tailWord_521534) baseStart_521534 baseEnd_521534 := by
    simpa [prefixWord, tailWord_521534, baseEnd_521534] using wordTrace_append hprefix tailTrace_521534
  have hstable : (prefixWord ++ tailWord_521534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521534).length < 2 ^ (prefixWord ++ tailWord_521534).sum := by decide
  have hdescent : baseEnd_521534 < baseStart_521534 := by decide
  rcases family_descends (prefixWord ++ tailWord_521534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521540 : List Nat := [2, 3, 4, 1, 1, 3, 1, 3, 2]
def baseStart_521540 : Nat := 118140960795 + 521540 * 2 ^ 59
def prefixEnd_521540 : Nat := 4983230072969 + 3 ^ 40 * 521540 * 2
def baseEnd_521540 : Nat := 238045067151995294267989

theorem tailTrace_521540 : CollatzResearch.WordTrace tailWord_521540 prefixEnd_521540 238045067151995294267989 := by
  unfold tailWord_521540
  simp only [CollatzResearch.WordTrace]
  refine ⟨9511063265278563392865037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12681417687038084523820049 9511063265278563392865037)
  ·
    refine ⟨3566648724479461272324389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9511063265278563392865037 3566648724479461272324389)
    ·
      refine ⟨668746635839898988560823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3566648724479461272324389 668746635839898988560823)
      ·
        refine ⟨1003119953759848482841235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 668746635839898988560823 1003119953759848482841235)
        ·
          refine ⟨1504679930639772724261853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1003119953759848482841235 1504679930639772724261853)
          ·
            refine ⟨564254973989914771598195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1504679930639772724261853 564254973989914771598195)
            ·
              refine ⟨846382460984872157397293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564254973989914771598195 846382460984872157397293)
              ·
                refine ⟨317393422869327059023985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 846382460984872157397293 317393422869327059023985)
                ·
                  refine ⟨238045067151995294267989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 317393422869327059023985 238045067151995294267989)
                  ·
                    rfl

theorem cell20_521540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_521540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521540 prefixEnd_521540 := by exact prefixLift 521540
  have htrace : WordTrace (prefixWord ++ tailWord_521540) baseStart_521540 baseEnd_521540 := by
    simpa [prefixWord, tailWord_521540, baseEnd_521540] using wordTrace_append hprefix tailTrace_521540
  have hstable : (prefixWord ++ tailWord_521540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521540).length < 2 ^ (prefixWord ++ tailWord_521540).sum := by decide
  have hdescent : baseEnd_521540 < baseStart_521540 := by decide
  rcases family_descends (prefixWord ++ tailWord_521540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521572 : List Nat := [2, 3, 1, 1, 3, 3, 2, 5]
def baseStart_521572 : Nat := 118140960795 + 521572 * 2 ^ 59
def prefixEnd_521572 : Nat := 4983230072969 + 3 ^ 40 * 521572 * 2
def baseEnd_521572 : Nat := 79353224274648468400397

theorem tailTrace_521572 : CollatzResearch.WordTrace tailWord_521572 prefixEnd_521572 79353224274648468400397 := by
  unfold tailWord_521572
  simp only [CollatzResearch.WordTrace]
  refine ⟨9511646833220598125447485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12682195777627464167263313 9511646833220598125447485)
  ·
    refine ⟨3566867562457724297042807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9511646833220598125447485 3566867562457724297042807)
    ·
      refine ⟨5350301343686586445564211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3566867562457724297042807 5350301343686586445564211)
      ·
        refine ⟨8025452015529879668346317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5350301343686586445564211 8025452015529879668346317)
        ·
          refine ⟨3009544505823704875629869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8025452015529879668346317 3009544505823704875629869)
          ·
            refine ⟨1128579189683889328361201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3009544505823704875629869 1128579189683889328361201)
            ·
              refine ⟨846434392262916996270901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1128579189683889328361201 846434392262916996270901)
              ·
                refine ⟨79353224274648468400397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 846434392262916996270901 79353224274648468400397)
                ·
                  rfl

theorem cell20_521572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 5].length) (baseStart_521572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521572 prefixEnd_521572 := by exact prefixLift 521572
  have htrace : WordTrace (prefixWord ++ tailWord_521572) baseStart_521572 baseEnd_521572 := by
    simpa [prefixWord, tailWord_521572, baseEnd_521572] using wordTrace_append hprefix tailTrace_521572
  have hstable : (prefixWord ++ tailWord_521572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521572).length < 2 ^ (prefixWord ++ tailWord_521572).sum := by decide
  have hdescent : baseEnd_521572 < baseStart_521572 := by decide
  rcases family_descends (prefixWord ++ tailWord_521572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521586 : List Nat := [3, 2, 1, 2, 1, 2, 2, 1, 6]
def baseStart_521586 : Nat := 118140960795 + 521586 * 2 ^ 59
def prefixEnd_521586 : Nat := 4983230072969 + 3 ^ 40 * 521586 * 2
def baseEnd_521586 : Nat := 238066062805423578734467

theorem tailTrace_521586 : CollatzResearch.WordTrace tailWord_521586 prefixEnd_521586 238066062805423578734467 := by
  unfold tailWord_521586
  simp only [CollatzResearch.WordTrace]
  refine ⟨4755951072097619160476153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12682536192260317761269741 4755951072097619160476153)
  ·
    refine ⟨3566963304073214370357115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4755951072097619160476153 3566963304073214370357115)
    ·
      refine ⟨5350444956109821555535673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3566963304073214370357115 5350444956109821555535673)
      ·
        refine ⟨4012833717082366166651755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5350444956109821555535673 4012833717082366166651755)
        ·
          refine ⟨6019250575623549249977633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4012833717082366166651755 6019250575623549249977633)
          ·
            refine ⟨4514437931717661937483225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6019250575623549249977633 4514437931717661937483225)
            ·
              refine ⟨3385828448788246453112419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4514437931717661937483225 3385828448788246453112419)
              ·
                refine ⟨5078742673182369679668629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3385828448788246453112419 5078742673182369679668629)
                ·
                  refine ⟨238066062805423578734467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5078742673182369679668629 238066062805423578734467)
                  ·
                    rfl

theorem cell20_521586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_521586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521586 prefixEnd_521586 := by exact prefixLift 521586
  have htrace : WordTrace (prefixWord ++ tailWord_521586) baseStart_521586 baseEnd_521586 := by
    simpa [prefixWord, tailWord_521586, baseEnd_521586] using wordTrace_append hprefix tailTrace_521586
  have hstable : (prefixWord ++ tailWord_521586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521586).length < 2 ^ (prefixWord ++ tailWord_521586).sum := by decide
  have hdescent : baseEnd_521586 < baseStart_521586 := by decide
  rcases family_descends (prefixWord ++ tailWord_521586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521593 : List Nat := [1, 2, 1, 3, 2, 1, 4, 6]
def baseStart_521593 : Nat := 118140960795 + 521593 * 2 ^ 59
def prefixEnd_521593 : Nat := 4983230072969 + 3 ^ 40 * 521593 * 2
def baseEnd_521593 : Nat := 79356419265387555167035

theorem tailTrace_521593 : CollatzResearch.WordTrace tailWord_521593 prefixEnd_521593 79356419265387555167035 := by
  unfold tailWord_521593
  simp only [CollatzResearch.WordTrace]
  refine ⟨19024059599365116837409433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12682706399576744558272955 19024059599365116837409433)
  ·
    refine ⟨14268044699523837628057075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19024059599365116837409433 14268044699523837628057075)
    ·
      refine ⟨21402067049285756442085613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14268044699523837628057075 21402067049285756442085613)
      ·
        refine ⟨8025775143482158665782105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21402067049285756442085613 8025775143482158665782105)
        ·
          refine ⟨6019331357611618999336579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8025775143482158665782105 6019331357611618999336579)
          ·
            refine ⟨9028997036417428499004869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6019331357611618999336579 9028997036417428499004869)
            ·
              refine ⟨1692936944328267843563413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9028997036417428499004869 1692936944328267843563413)
              ·
                refine ⟨79356419265387555167035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1692936944328267843563413 79356419265387555167035)
                ·
                  rfl

theorem cell20_521593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 6].length) (baseStart_521593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521593 prefixEnd_521593 := by exact prefixLift 521593
  have htrace : WordTrace (prefixWord ++ tailWord_521593) baseStart_521593 baseEnd_521593 := by
    simpa [prefixWord, tailWord_521593, baseEnd_521593] using wordTrace_append hprefix tailTrace_521593
  have hstable : (prefixWord ++ tailWord_521593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521593).length < 2 ^ (prefixWord ++ tailWord_521593).sum := by decide
  have hdescent : baseEnd_521593 < baseStart_521593 := by decide
  rcases family_descends (prefixWord ++ tailWord_521593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521600 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 7]
def baseStart_521600 : Nat := 118140960795 + 521600 * 2 ^ 59
def prefixEnd_521600 : Nat := 4983230072969 + 3 ^ 40 * 521600 * 2
def baseEnd_521600 : Nat := 238072452786901752267743

theorem tailTrace_521600 : CollatzResearch.WordTrace tailWord_521600 prefixEnd_521600 238072452786901752267743 := by
  unfold tailWord_521600
  simp only [CollatzResearch.WordTrace]
  refine ⟨9512157455169878516457127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12682876606893171355276169 9512157455169878516457127)
  ·
    refine ⟨14268236182754817774685691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9512157455169878516457127 14268236182754817774685691)
    ·
      refine ⟨21402354274132226662028537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14268236182754817774685691 21402354274132226662028537)
      ·
        refine ⟨16051765705599169996521403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21402354274132226662028537 16051765705599169996521403)
        ·
          refine ⟨24077648558398754994782105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16051765705599169996521403 24077648558398754994782105)
          ·
            refine ⟨18058236418799066246086579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24077648558398754994782105 18058236418799066246086579)
            ·
              refine ⟨27087354628198599369129869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18058236418799066246086579 27087354628198599369129869)
              ·
                refine ⟨10157757985574474763423701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27087354628198599369129869 10157757985574474763423701)
                ·
                  refine ⟨238072452786901752267743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10157757985574474763423701 238072452786901752267743)
                  ·
                    rfl

theorem cell20_521600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_521600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521600 prefixEnd_521600 := by exact prefixLift 521600
  have htrace : WordTrace (prefixWord ++ tailWord_521600) baseStart_521600 baseEnd_521600 := by
    simpa [prefixWord, tailWord_521600, baseEnd_521600] using wordTrace_append hprefix tailTrace_521600
  have hstable : (prefixWord ++ tailWord_521600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521600).length < 2 ^ (prefixWord ++ tailWord_521600).sum := by decide
  have hdescent : baseEnd_521600 < baseStart_521600 := by decide
  rcases family_descends (prefixWord ++ tailWord_521600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521634 : List Nat := [3, 3, 1, 2, 1, 2, 2, 3, 3]
def baseStart_521634 : Nat := 118140960795 + 521634 * 2 ^ 59
def prefixEnd_521634 : Nat := 4983230072969 + 3 ^ 40 * 521634 * 2
def baseEnd_521634 : Nat := 238087971313348745134271

theorem tailTrace_521634 : CollatzResearch.WordTrace tailWord_521634 prefixEnd_521634 238087971313348745134271 := by
  unfold tailWord_521634
  simp only [CollatzResearch.WordTrace]
  refine ⟨4756388748054145209912989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12683703328144387226434637 4756388748054145209912989)
  ·
    refine ⟨1783645780520304453717371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4756388748054145209912989 1783645780520304453717371)
    ·
      refine ⟨2675468670780456680576057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1783645780520304453717371 2675468670780456680576057)
      ·
        refine ⟨2006601503085342510432043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2675468670780456680576057 2006601503085342510432043)
        ·
          refine ⟨3009902254628013765648065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2006601503085342510432043 3009902254628013765648065)
          ·
            refine ⟨2257426690971010324236049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3009902254628013765648065 2257426690971010324236049)
            ·
              refine ⟨1693070018228257743177037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2257426690971010324236049 1693070018228257743177037)
              ·
                refine ⟨634901256835596653691389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1693070018228257743177037 634901256835596653691389)
                ·
                  refine ⟨238087971313348745134271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 634901256835596653691389 238087971313348745134271)
                  ·
                    rfl

theorem cell20_521634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_521634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521634 prefixEnd_521634 := by exact prefixLift 521634
  have htrace : WordTrace (prefixWord ++ tailWord_521634) baseStart_521634 baseEnd_521634 := by
    simpa [prefixWord, tailWord_521634, baseEnd_521634] using wordTrace_append hprefix tailTrace_521634
  have hstable : (prefixWord ++ tailWord_521634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521634).length < 2 ^ (prefixWord ++ tailWord_521634).sum := by decide
  have hdescent : baseEnd_521634 < baseStart_521634 := by decide
  rcases family_descends (prefixWord ++ tailWord_521634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521662 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 8]
def baseStart_521662 : Nat := 118140960795 + 521662 * 2 ^ 59
def prefixEnd_521662 : Nat := 4983230072969 + 3 ^ 40 * 521662 * 2
def baseEnd_521662 : Nat := 238100751276305092200823

theorem tailTrace_521662 : CollatzResearch.WordTrace tailWord_521662 prefixEnd_521662 238100751276305092200823 := by
  unfold tailWord_521662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2378322029514392702708905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12684384157410094414447493 2378322029514392702708905)
  ·
    refine ⟨1783741522135794527031679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2378322029514392702708905 1783741522135794527031679)
    ·
      refine ⟨2675612283203691790547519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1783741522135794527031679 2675612283203691790547519)
      ·
        refine ⟨4013418424805537685821279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2675612283203691790547519 4013418424805537685821279)
        ·
          refine ⟨6020127637208306528731919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4013418424805537685821279 6020127637208306528731919)
          ·
            refine ⟨9030191455812459793097879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6020127637208306528731919 9030191455812459793097879)
            ·
              refine ⟨13545287183718689689646819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9030191455812459793097879 13545287183718689689646819)
              ·
                refine ⟨20317930775578034534470229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13545287183718689689646819 20317930775578034534470229)
                ·
                  refine ⟨238100751276305092200823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20317930775578034534470229 238100751276305092200823)
                  ·
                    rfl

theorem cell20_521662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_521662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521662 prefixEnd_521662 := by exact prefixLift 521662
  have htrace : WordTrace (prefixWord ++ tailWord_521662) baseStart_521662 baseEnd_521662 := by
    simpa [prefixWord, tailWord_521662, baseEnd_521662] using wordTrace_append hprefix tailTrace_521662
  have hstable : (prefixWord ++ tailWord_521662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521662).length < 2 ^ (prefixWord ++ tailWord_521662).sum := by decide
  have hdescent : baseEnd_521662 < baseStart_521662 := by decide
  rcases family_descends (prefixWord ++ tailWord_521662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521679 : List Nat := [1, 1, 2, 1, 1, 4, 4, 4, 2]
def baseStart_521679 : Nat := 118140960795 + 521679 * 2 ^ 59
def prefixEnd_521679 : Nat := 4983230072969 + 3 ^ 40 * 521679 * 2
def baseEnd_521679 : Nat := 238108510539528588634087

theorem tailTrace_521679 : CollatzResearch.WordTrace tailWord_521679 prefixEnd_521679 238108510539528588634087 := by
  unfold tailWord_521679
  simp only [CollatzResearch.WordTrace]
  refine ⟨19027196277053553525040091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12684797518035702350026727 19027196277053553525040091)
  ·
    refine ⟨28540794415580330287560137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19027196277053553525040091 28540794415580330287560137)
    ·
      refine ⟨21405595811685247715670103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28540794415580330287560137 21405595811685247715670103)
      ·
        refine ⟨32108393717527871573505155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21405595811685247715670103 32108393717527871573505155)
        ·
          refine ⟨48162590576291807360257733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32108393717527871573505155 48162590576291807360257733)
          ·
            refine ⟨9030485733054713880048325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48162590576291807360257733 9030485733054713880048325)
            ·
              refine ⟨1693216074947758852509061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9030485733054713880048325 1693216074947758852509061)
              ·
                refine ⟨317478014052704784845449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1693216074947758852509061 317478014052704784845449)
                ·
                  refine ⟨238108510539528588634087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 317478014052704784845449 238108510539528588634087)
                  ·
                    rfl

theorem cell20_521679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 4, 2].length) (baseStart_521679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521679 prefixEnd_521679 := by exact prefixLift 521679
  have htrace : WordTrace (prefixWord ++ tailWord_521679) baseStart_521679 baseEnd_521679 := by
    simpa [prefixWord, tailWord_521679, baseEnd_521679] using wordTrace_append hprefix tailTrace_521679
  have hstable : (prefixWord ++ tailWord_521679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521679).length < 2 ^ (prefixWord ++ tailWord_521679).sum := by decide
  have hdescent : baseEnd_521679 < baseStart_521679 := by decide
  rcases family_descends (prefixWord ++ tailWord_521679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521703 : List Nat := [1, 1, 5, 2, 1, 4, 2, 4]
def baseStart_521703 : Nat := 118140960795 + 521703 * 2 ^ 59
def prefixEnd_521703 : Nat := 4983230072969 + 3 ^ 40 * 521703 * 2
def baseEnd_521703 : Nat := 79373154931163723944663

theorem tailTrace_521703 : CollatzResearch.WordTrace tailWord_521703 prefixEnd_521703 79373154931163723944663 := by
  unfold tailWord_521703
  simp only [CollatzResearch.WordTrace]
  refine ⟨19028071628966605623913763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12685381085977737082609175 19028071628966605623913763)
  ·
    refine ⟨28542107443449908435870645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19028071628966605623913763 28542107443449908435870645)
    ·
      refine ⟨2675822572823428915862873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28542107443449908435870645 2675822572823428915862873)
      ·
        refine ⟨2006866929617571686897155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2675822572823428915862873 2006866929617571686897155)
        ·
          refine ⟨3010300394426357530345733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2006866929617571686897155 3010300394426357530345733)
          ·
            refine ⟨564431323954942036939825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3010300394426357530345733 564431323954942036939825)
            ·
              refine ⟨423323492966206527704869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 564431323954942036939825 423323492966206527704869)
              ·
                refine ⟨79373154931163723944663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 423323492966206527704869 79373154931163723944663)
                ·
                  rfl

theorem cell20_521703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 4].length) (baseStart_521703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521703 prefixEnd_521703 := by exact prefixLift 521703
  have htrace : WordTrace (prefixWord ++ tailWord_521703) baseStart_521703 baseEnd_521703 := by
    simpa [prefixWord, tailWord_521703, baseEnd_521703] using wordTrace_append hprefix tailTrace_521703
  have hstable : (prefixWord ++ tailWord_521703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521703).length < 2 ^ (prefixWord ++ tailWord_521703).sum := by decide
  have hdescent : baseEnd_521703 < baseStart_521703 := by decide
  rcases family_descends (prefixWord ++ tailWord_521703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521730 : List Nat := [3, 4, 1, 2, 1, 2, 3, 2, 2]
def baseStart_521730 : Nat := 118140960795 + 521730 * 2 ^ 59
def prefixEnd_521730 : Nat := 4983230072969 + 3 ^ 40 * 521730 * 2
def baseEnd_521730 : Nat := 238131788329199077933879

theorem tailTrace_521730 : CollatzResearch.WordTrace tailWord_521730 prefixEnd_521730 238131788329199077933879 := by
  unfold tailWord_521730
  simp only [CollatzResearch.WordTrace]
  refine ⟨4757264099967197308786661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12686037599912526156764429 4757264099967197308786661)
  ·
    refine ⟨891987018743849495397499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4757264099967197308786661 891987018743849495397499)
    ·
      refine ⟨1337980528115774243096249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 891987018743849495397499 1337980528115774243096249)
      ·
        refine ⟨1003485396086830682322187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1337980528115774243096249 1003485396086830682322187)
        ·
          refine ⟨1505228094130246023483281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1003485396086830682322187 1505228094130246023483281)
          ·
            refine ⟨1128921070597684517612461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1505228094130246023483281 1128921070597684517612461)
            ·
              refine ⟨423345401474131694104673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1128921070597684517612461 423345401474131694104673)
              ·
                refine ⟨317509051105598770578505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 423345401474131694104673 317509051105598770578505)
                ·
                  refine ⟨238131788329199077933879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 317509051105598770578505 238131788329199077933879)
                  ·
                    rfl

theorem cell20_521730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_521730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521730 prefixEnd_521730 := by exact prefixLift 521730
  have htrace : WordTrace (prefixWord ++ tailWord_521730) baseStart_521730 baseEnd_521730 := by
    simpa [prefixWord, tailWord_521730, baseEnd_521730] using wordTrace_append hprefix tailTrace_521730
  have hstable : (prefixWord ++ tailWord_521730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521730).length < 2 ^ (prefixWord ++ tailWord_521730).sum := by decide
  have hdescent : baseEnd_521730 < baseStart_521730 := by decide
  rcases family_descends (prefixWord ++ tailWord_521730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521745 : List Nat := [1, 2, 2, 1, 1, 2, 6, 5]
def baseStart_521745 : Nat := 118140960795 + 521745 * 2 ^ 59
def prefixEnd_521745 : Nat := 4983230072969 + 3 ^ 40 * 521745 * 2
def baseEnd_521745 : Nat := 79379544912641897477939

theorem tailTrace_521745 : CollatzResearch.WordTrace tailWord_521745 prefixEnd_521745 79379544912641897477939 := by
  unfold tailWord_521745
  simp only [CollatzResearch.WordTrace]
  refine ⟨19029603494814446796942689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12686402329876297864628459 19029603494814446796942689)
  ·
    refine ⟨14272202621110835097707017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19029603494814446796942689 14272202621110835097707017)
    ·
      refine ⟨10704151965833126323280263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14272202621110835097707017 10704151965833126323280263)
      ·
        refine ⟨16056227948749689484920395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10704151965833126323280263 16056227948749689484920395)
        ·
          refine ⟨24084341923124534227380593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16056227948749689484920395 24084341923124534227380593)
          ·
            refine ⟨18063256442343400670535445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24084341923124534227380593 18063256442343400670535445)
            ·
              refine ⟨846715145734846906431349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18063256442343400670535445 846715145734846906431349)
              ·
                refine ⟨79379544912641897477939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 846715145734846906431349 79379544912641897477939)
                ·
                  rfl

theorem cell20_521745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 5].length) (baseStart_521745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521745 prefixEnd_521745 := by exact prefixLift 521745
  have htrace : WordTrace (prefixWord ++ tailWord_521745) baseStart_521745 baseEnd_521745 := by
    simpa [prefixWord, tailWord_521745, baseEnd_521745] using wordTrace_append hprefix tailTrace_521745
  have hstable : (prefixWord ++ tailWord_521745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521745).length < 2 ^ (prefixWord ++ tailWord_521745).sum := by decide
  have hdescent : baseEnd_521745 < baseStart_521745 := by decide
  rcases family_descends (prefixWord ++ tailWord_521745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521831 : List Nat := [1, 1, 5, 1, 1, 1, 3, 5, 2]
def baseStart_521831 : Nat := 118140960795 + 521831 * 2 ^ 59
def prefixEnd_521831 : Nat := 4983230072969 + 3 ^ 40 * 521831 * 2
def baseEnd_521831 : Nat := 238177887481291615566799

theorem tailTrace_521831 : CollatzResearch.WordTrace tailWord_521831 prefixEnd_521831 238177887481291615566799 := by
  unfold tailWord_521831
  simp only [CollatzResearch.WordTrace]
  refine ⟨19032740172502883484573347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12688493448335255656382231 19032740172502883484573347)
  ·
    refine ⟨28549110258754325226860021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19032740172502883484573347 28549110258754325226860021)
    ·
      refine ⟨2676479086758217990018127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28549110258754325226860021 2676479086758217990018127)
      ·
        refine ⟨4014718630137326985027191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2676479086758217990018127 4014718630137326985027191)
        ·
          refine ⟨6022077945205990477540787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4014718630137326985027191 6022077945205990477540787)
          ·
            refine ⟨9033116917808985716311181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6022077945205990477540787 9033116917808985716311181)
            ·
              refine ⟨3387418844178369643616693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9033116917808985716311181 3387418844178369643616693)
              ·
                refine ⟨317570516641722154089065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3387418844178369643616693 317570516641722154089065)
                ·
                  refine ⟨238177887481291615566799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 317570516641722154089065 238177887481291615566799)
                  ·
                    rfl

theorem cell20_521831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 5, 2].length) (baseStart_521831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521831 prefixEnd_521831 := by exact prefixLift 521831
  have htrace : WordTrace (prefixWord ++ tailWord_521831) baseStart_521831 baseEnd_521831 := by
    simpa [prefixWord, tailWord_521831, baseEnd_521831] using wordTrace_append hprefix tailTrace_521831
  have hstable : (prefixWord ++ tailWord_521831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521831).length < 2 ^ (prefixWord ++ tailWord_521831).sum := by decide
  have hdescent : baseEnd_521831 < baseStart_521831 := by decide
  rcases family_descends (prefixWord ++ tailWord_521831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521838 : List Nat := [4, 1, 2, 2, 3, 1, 7]
def baseStart_521838 : Nat := 118140960795 + 521838 * 2 ^ 59
def prefixEnd_521838 : Nat := 4983230072969 + 3 ^ 40 * 521838 * 2
def baseEnd_521838 : Nat := 26464564719114522481493

theorem tailTrace_521838 : CollatzResearch.WordTrace tailWord_521838 prefixEnd_521838 26464564719114522481493 := by
  unfold tailWord_521838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2379124435434690460009771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12688663655651682453385445 2379124435434690460009771)
  ·
    refine ⟨3568686653152035690014657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2379124435434690460009771 3568686653152035690014657)
    ·
      refine ⟨2676514989864026767510993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3568686653152035690014657 2676514989864026767510993)
      ·
        refine ⟨2007386242398020075633245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2676514989864026767510993 2007386242398020075633245)
        ·
          refine ⟨752769840899257528362467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2007386242398020075633245 752769840899257528362467)
          ·
            refine ⟨1129154761348886292543701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752769840899257528362467 1129154761348886292543701)
            ·
              refine ⟨26464564719114522481493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1129154761348886292543701 26464564719114522481493)
              ·
                rfl

theorem cell20_521838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 7].length) (baseStart_521838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521838 prefixEnd_521838 := by exact prefixLift 521838
  have htrace : WordTrace (prefixWord ++ tailWord_521838) baseStart_521838 baseEnd_521838 := by
    simpa [prefixWord, tailWord_521838, baseEnd_521838] using wordTrace_append hprefix tailTrace_521838
  have hstable : (prefixWord ++ tailWord_521838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521838).length < 2 ^ (prefixWord ++ tailWord_521838).sum := by decide
  have hdescent : baseEnd_521838 < baseStart_521838 := by decide
  rcases family_descends (prefixWord ++ tailWord_521838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521873 : List Nat := [1, 2, 2, 1, 1, 1, 1, 5, 6]
def baseStart_521873 : Nat := 118140960795 + 521873 * 2 ^ 59
def prefixEnd_521873 : Nat := 4983230072969 + 3 ^ 40 * 521873 * 2
def baseEnd_521873 : Nat := 238197057425726136166627

theorem tailTrace_521873 : CollatzResearch.WordTrace tailWord_521873 prefixEnd_521873 238197057425726136166627 := by
  unfold tailWord_521873
  simp only [CollatzResearch.WordTrace]
  refine ⟨19034272038350724657602273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12689514692233816438401515 19034272038350724657602273)
  ·
    refine ⟨14275704028763043493201705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19034272038350724657602273 14275704028763043493201705)
    ·
      refine ⟨10706778021572282619901279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14275704028763043493201705 10706778021572282619901279)
      ·
        refine ⟨16060167032358423929851919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10706778021572282619901279 16060167032358423929851919)
        ·
          refine ⟨24090250548537635894777879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16060167032358423929851919 24090250548537635894777879)
          ·
            refine ⟨36135375822806453842166819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24090250548537635894777879 36135375822806453842166819)
            ·
              refine ⟨54203063734209680763250229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36135375822806453842166819 54203063734209680763250229)
              ·
                refine ⟨5081537225082157571554709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54203063734209680763250229 5081537225082157571554709)
                ·
                  refine ⟨238197057425726136166627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5081537225082157571554709 238197057425726136166627)
                  ·
                    rfl

theorem cell20_521873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_521873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521873 prefixEnd_521873 := by exact prefixLift 521873
  have htrace : WordTrace (prefixWord ++ tailWord_521873) baseStart_521873 baseEnd_521873 := by
    simpa [prefixWord, tailWord_521873, baseEnd_521873] using wordTrace_append hprefix tailTrace_521873
  have hstable : (prefixWord ++ tailWord_521873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521873).length < 2 ^ (prefixWord ++ tailWord_521873).sum := by decide
  have hdescent : baseEnd_521873 < baseStart_521873 := by decide
  rcases family_descends (prefixWord ++ tailWord_521873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521904 : List Nat := [2, 1, 1, 1, 2, 1, 6, 1, 5]
def baseStart_521904 : Nat := 118140960795 + 521904 * 2 ^ 59
def prefixEnd_521904 : Nat := 4983230072969 + 3 ^ 40 * 521904 * 2
def baseEnd_521904 : Nat := 238211206670427806133167

theorem tailTrace_521904 : CollatzResearch.WordTrace tailWord_521904 prefixEnd_521904 238211206670427806133167 := by
  unfold tailWord_521904
  simp only [CollatzResearch.WordTrace]
  refine ⟨9517701350619208475990383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12690268467492277967987177 9517701350619208475990383)
  ·
    refine ⟨14276552025928812713985575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9517701350619208475990383 14276552025928812713985575)
    ·
      refine ⟨21414828038893219070978363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14276552025928812713985575 21414828038893219070978363)
      ·
        refine ⟨32122242058339828606467545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21414828038893219070978363 32122242058339828606467545)
        ·
          refine ⟨24091681543754871454850659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32122242058339828606467545 24091681543754871454850659)
          ·
            refine ⟨36137522315632307182275989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24091681543754871454850659 36137522315632307182275989)
            ·
              refine ⟨1693946358545264399169187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 36137522315632307182275989 1693946358545264399169187)
              ·
                refine ⟨2540919537817896598753781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1693946358545264399169187 2540919537817896598753781)
                ·
                  refine ⟨238211206670427806133167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2540919537817896598753781 238211206670427806133167)
                  ·
                    rfl

theorem cell20_521904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_521904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521904 prefixEnd_521904 := by exact prefixLift 521904
  have htrace : WordTrace (prefixWord ++ tailWord_521904) baseStart_521904 baseEnd_521904 := by
    simpa [prefixWord, tailWord_521904, baseEnd_521904] using wordTrace_append hprefix tailTrace_521904
  have hstable : (prefixWord ++ tailWord_521904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521904).length < 2 ^ (prefixWord ++ tailWord_521904).sum := by decide
  have hdescent : baseEnd_521904 < baseStart_521904 := by decide
  rcases family_descends (prefixWord ++ tailWord_521904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521962 : List Nat := [3, 1, 3, 1, 1, 1, 6, 2, 2]
def baseStart_521962 : Nat := 118140960795 + 521962 * 2 ^ 59
def prefixEnd_521962 : Nat := 4983230072969 + 3 ^ 40 * 521962 * 2
def baseEnd_521962 : Nat := 238237679450837382199597

theorem tailTrace_521962 : CollatzResearch.WordTrace tailWord_521962 prefixEnd_521962 238237679450837382199597 := by
  unfold tailWord_521962
  simp only [CollatzResearch.WordTrace]
  refine ⟨4759379533757073214398035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12691678756685528571728093 4759379533757073214398035)
  ·
    refine ⟨7139069300635609821597053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4759379533757073214398035 7139069300635609821597053)
    ·
      refine ⟨2677150987738353683098895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7139069300635609821597053 2677150987738353683098895)
      ·
        refine ⟨4015726481607530524648343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2677150987738353683098895 4015726481607530524648343)
        ·
          refine ⟨6023589722411295786972515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4015726481607530524648343 6023589722411295786972515)
          ·
            refine ⟨9035384583616943680458773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6023589722411295786972515 9035384583616943680458773)
            ·
              refine ⟨423533652357044235021505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9035384583616943680458773 423533652357044235021505)
              ·
                refine ⟨317650239267783176266129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 423533652357044235021505 317650239267783176266129)
                ·
                  refine ⟨238237679450837382199597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 317650239267783176266129 238237679450837382199597)
                  ·
                    rfl

theorem cell20_521962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 2, 2].length) (baseStart_521962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521962 prefixEnd_521962 := by exact prefixLift 521962
  have htrace : WordTrace (prefixWord ++ tailWord_521962) baseStart_521962 baseEnd_521962 := by
    simpa [prefixWord, tailWord_521962, baseEnd_521962] using wordTrace_append hprefix tailTrace_521962
  have hstable : (prefixWord ++ tailWord_521962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521962).length < 2 ^ (prefixWord ++ tailWord_521962).sum := by decide
  have hdescent : baseEnd_521962 < baseStart_521962 := by decide
  rcases family_descends (prefixWord ++ tailWord_521962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521966 : List Nat := [4, 1, 2, 1, 1, 2, 2, 3, 4]
def baseStart_521966 : Nat := 118140960795 + 521966 * 2 ^ 59
def prefixEnd_521966 : Nat := 4983230072969 + 3 ^ 40 * 521966 * 2
def baseEnd_521966 : Nat := 238239505159831146066247

theorem tailTrace_521966 : CollatzResearch.WordTrace tailWord_521966 prefixEnd_521966 238239505159831146066247 := by
  unfold tailWord_521966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2379708003376725192592219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12691776018009201027158501 2379708003376725192592219)
  ·
    refine ⟨3569562005065087788888329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2379708003376725192592219 3569562005065087788888329)
    ·
      refine ⟨2677171503798815841666247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3569562005065087788888329 2677171503798815841666247)
      ·
        refine ⟨4015757255698223762499371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2677171503798815841666247 4015757255698223762499371)
        ·
          refine ⟨6023635883547335643749057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4015757255698223762499371 6023635883547335643749057)
          ·
            refine ⟨4517726912660501732811793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6023635883547335643749057 4517726912660501732811793)
            ·
              refine ⟨3388295184495376299608845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4517726912660501732811793 3388295184495376299608845)
              ·
                refine ⟨1270610694185766112353317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3388295184495376299608845 1270610694185766112353317)
                ·
                  refine ⟨238239505159831146066247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1270610694185766112353317 238239505159831146066247)
                  ·
                    rfl

theorem cell20_521966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_521966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521966 prefixEnd_521966 := by exact prefixLift 521966
  have htrace : WordTrace (prefixWord ++ tailWord_521966) baseStart_521966 baseEnd_521966 := by
    simpa [prefixWord, tailWord_521966, baseEnd_521966] using wordTrace_append hprefix tailTrace_521966
  have hstable : (prefixWord ++ tailWord_521966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521966).length < 2 ^ (prefixWord ++ tailWord_521966).sum := by decide
  have hdescent : baseEnd_521966 < baseStart_521966 := by decide
  rcases family_descends (prefixWord ++ tailWord_521966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_521987 : List Nat := [1, 1, 1, 3, 2, 2, 3, 1, 6]
def baseStart_521987 : Nat := 118140960795 + 521987 * 2 ^ 59
def prefixEnd_521987 : Nat := 4983230072969 + 3 ^ 40 * 521987 * 2
def baseEnd_521987 : Nat := 238249090132048406366161

theorem tailTrace_521987 : CollatzResearch.WordTrace tailWord_521987 prefixEnd_521987 238249090132048406366161 := by
  unfold tailWord_521987
  simp only [CollatzResearch.WordTrace]
  refine ⟨19038429959937722127252215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12692286639958481418168143 19038429959937722127252215)
  ·
    refine ⟨28557644939906583190878323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19038429959937722127252215 28557644939906583190878323)
    ·
      refine ⟨42836467409859874786317485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28557644939906583190878323 42836467409859874786317485)
      ·
        refine ⟨16063675278697453044869057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42836467409859874786317485 16063675278697453044869057)
        ·
          refine ⟨12047756459023089783651793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16063675278697453044869057 12047756459023089783651793)
          ·
            refine ⟨9035817344267317337738845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12047756459023089783651793 9035817344267317337738845)
            ·
              refine ⟨3388431504100244001652067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9035817344267317337738845 3388431504100244001652067)
              ·
                refine ⟨5082647256150366002478101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3388431504100244001652067 5082647256150366002478101)
                ·
                  refine ⟨238249090132048406366161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5082647256150366002478101 238249090132048406366161)
                  ·
                    rfl

theorem cell20_521987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 6].length) (baseStart_521987 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_521987 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_521987 prefixEnd_521987 := by exact prefixLift 521987
  have htrace : WordTrace (prefixWord ++ tailWord_521987) baseStart_521987 baseEnd_521987 := by
    simpa [prefixWord, tailWord_521987, baseEnd_521987] using wordTrace_append hprefix tailTrace_521987
  have hstable : (prefixWord ++ tailWord_521987).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_521987).length < 2 ^ (prefixWord ++ tailWord_521987).sum := by decide
  have hdescent : baseEnd_521987 < baseStart_521987 := by decide
  rcases family_descends (prefixWord ++ tailWord_521987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522021 : List Nat := [1, 3, 1, 2, 3, 2, 2, 4, 2]
def baseStart_522021 : Nat := 118140960795 + 522021 * 2 ^ 59
def prefixEnd_522021 : Nat := 4983230072969 + 3 ^ 40 * 522021 * 2
def baseEnd_522021 : Nat := 238264608658495399232689

theorem tailTrace_522021 : CollatzResearch.WordTrace tailWord_522021 prefixEnd_522021 238264608658495399232689 := by
  unfold tailWord_522021
  simp only [CollatzResearch.WordTrace]
  refine ⟨19039670041814545933989917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12693113361209697289326611 19039670041814545933989917)
  ·
    refine ⟨7139876265680454725246219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19039670041814545933989917 7139876265680454725246219)
    ·
      refine ⟨10709814398520682087869329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7139876265680454725246219 10709814398520682087869329)
      ·
        refine ⟨8032360798890511565901997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10709814398520682087869329 8032360798890511565901997)
        ·
          refine ⟨3012135299583941837213249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8032360798890511565901997 3012135299583941837213249)
          ·
            refine ⟨2259101474687956377909937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3012135299583941837213249 2259101474687956377909937)
            ·
              refine ⟨1694326106015967283432453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2259101474687956377909937 1694326106015967283432453)
              ·
                refine ⟨317686144877993865643585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1694326106015967283432453 317686144877993865643585)
                ·
                  refine ⟨238264608658495399232689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 317686144877993865643585 238264608658495399232689)
                  ·
                    rfl

theorem cell20_522021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 4, 2].length) (baseStart_522021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522021 prefixEnd_522021 := by exact prefixLift 522021
  have htrace : WordTrace (prefixWord ++ tailWord_522021) baseStart_522021 baseEnd_522021 := by
    simpa [prefixWord, tailWord_522021, baseEnd_522021] using wordTrace_append hprefix tailTrace_522021
  have hstable : (prefixWord ++ tailWord_522021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522021).length < 2 ^ (prefixWord ++ tailWord_522021).sum := by decide
  have hdescent : baseEnd_522021 < baseStart_522021 := by decide
  rcases family_descends (prefixWord ++ tailWord_522021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522042 : List Nat := [3, 1, 1, 1, 5, 1, 2, 2, 4]
def baseStart_522042 : Nat := 118140960795 + 522042 * 2 ^ 59
def prefixEnd_522042 : Nat := 4983230072969 + 3 ^ 40 * 522042 * 2
def baseEnd_522042 : Nat := 238274193630712659532603

theorem tailTrace_522042 : CollatzResearch.WordTrace tailWord_522042 prefixEnd_522042 238274193630712659532603 := by
  unfold tailWord_522042
  simp only [CollatzResearch.WordTrace]
  refine ⟨4760108993684616630126095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12693623983158977680336253 4760108993684616630126095)
  ·
    refine ⟨7140163490526924945189143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4760108993684616630126095 7140163490526924945189143)
    ·
      refine ⟨10710245235790387417783715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7140163490526924945189143 10710245235790387417783715)
      ·
        refine ⟨16065367853685581126675573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10710245235790387417783715 16065367853685581126675573)
        ·
          refine ⟨1506128236283023230625835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16065367853685581126675573 1506128236283023230625835)
          ·
            refine ⟨2259192354424534845938753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1506128236283023230625835 2259192354424534845938753)
            ·
              refine ⟨1694394265818401134454065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2259192354424534845938753 1694394265818401134454065)
              ·
                refine ⟨1270795699363800850840549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1694394265818401134454065 1270795699363800850840549)
                ·
                  refine ⟨238274193630712659532603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1270795699363800850840549 238274193630712659532603)
                  ·
                    rfl

theorem cell20_522042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_522042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522042 prefixEnd_522042 := by exact prefixLift 522042
  have htrace : WordTrace (prefixWord ++ tailWord_522042) baseStart_522042 baseEnd_522042 := by
    simpa [prefixWord, tailWord_522042, baseEnd_522042] using wordTrace_append hprefix tailTrace_522042
  have hstable : (prefixWord ++ tailWord_522042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522042).length < 2 ^ (prefixWord ++ tailWord_522042).sum := by decide
  have hdescent : baseEnd_522042 < baseStart_522042 := by decide
  rcases family_descends (prefixWord ++ tailWord_522042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522045 : List Nat := [1, 4, 1, 4, 1, 3, 2, 4]
def baseStart_522045 : Nat := 118140960795 + 522045 * 2 ^ 59
def prefixEnd_522045 : Nat := 4983230072969 + 3 ^ 40 * 522045 * 2
def baseEnd_522045 : Nat := 79425187637485994144197

theorem tailTrace_522045 : CollatzResearch.WordTrace tailWord_522045 prefixEnd_522045 79425187637485994144197 := by
  unfold tailWord_522045
  simp only [CollatzResearch.WordTrace]
  refine ⟨19040545393727598032863589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12693696929151732021909059 19040545393727598032863589)
  ·
    refine ⟨3570102261323924631161923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19040545393727598032863589 3570102261323924631161923)
    ·
      refine ⟨5355153391985886946742885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3570102261323924631161923 5355153391985886946742885)
      ·
        refine ⟨1004091260997353802514291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5355153391985886946742885 1004091260997353802514291)
        ·
          refine ⟨1506136891496030703771437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1004091260997353802514291 1506136891496030703771437)
          ·
            refine ⟨564801334311011513914289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1506136891496030703771437 564801334311011513914289)
            ·
              refine ⟨423601000733258635435717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 564801334311011513914289 423601000733258635435717)
              ·
                refine ⟨79425187637485994144197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 423601000733258635435717 79425187637485994144197)
                ·
                  rfl

theorem cell20_522045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 4].length) (baseStart_522045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522045 prefixEnd_522045 := by exact prefixLift 522045
  have htrace : WordTrace (prefixWord ++ tailWord_522045) baseStart_522045 baseEnd_522045 := by
    simpa [prefixWord, tailWord_522045, baseEnd_522045] using wordTrace_append hprefix tailTrace_522045
  have hstable : (prefixWord ++ tailWord_522045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522045).length < 2 ^ (prefixWord ++ tailWord_522045).sum := by decide
  have hdescent : baseEnd_522045 < baseStart_522045 := by decide
  rcases family_descends (prefixWord ++ tailWord_522045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522056 : List Nat := [2, 1, 3, 1, 1, 4, 1, 2, 5]
def baseStart_522056 : Nat := 118140960795 + 522056 * 2 ^ 59
def prefixEnd_522056 : Nat := 4983230072969 + 3 ^ 40 * 522056 * 2
def baseEnd_522056 : Nat := 238280583612190833065879

theorem tailTrace_522056 : CollatzResearch.WordTrace tailWord_522056 prefixEnd_522056 238280583612190833065879 := by
  unfold tailWord_522056
  simp only [CollatzResearch.WordTrace]
  refine ⟨9520473298343873455757011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12693964397791831274342681 9520473298343873455757011)
  ·
    refine ⟨14280709947515810183635517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9520473298343873455757011 14280709947515810183635517)
    ·
      refine ⟨5355266230318428818863319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14280709947515810183635517 5355266230318428818863319)
      ·
        refine ⟨8032899345477643228294979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5355266230318428818863319 8032899345477643228294979)
        ·
          refine ⟨12049349018216464842442469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8032899345477643228294979 12049349018216464842442469)
          ·
            refine ⟨2259252940915587157957963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12049349018216464842442469 2259252940915587157957963)
            ·
              refine ⟨3388879411373380736936945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2259252940915587157957963 3388879411373380736936945)
              ·
                refine ⟨2541659558530035552702709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3388879411373380736936945 2541659558530035552702709)
                ·
                  refine ⟨238280583612190833065879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2541659558530035552702709 238280583612190833065879)
                  ·
                    rfl

theorem cell20_522056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_522056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522056 prefixEnd_522056 := by exact prefixLift 522056
  have htrace : WordTrace (prefixWord ++ tailWord_522056) baseStart_522056 baseEnd_522056 := by
    simpa [prefixWord, tailWord_522056, baseEnd_522056] using wordTrace_append hprefix tailTrace_522056
  have hstable : (prefixWord ++ tailWord_522056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522056).length < 2 ^ (prefixWord ++ tailWord_522056).sum := by decide
  have hdescent : baseEnd_522056 < baseStart_522056 := by decide
  rcases family_descends (prefixWord ++ tailWord_522056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522076 : List Nat := [2, 2, 4, 2, 2, 2, 1, 1, 4]
def baseStart_522076 : Nat := 118140960795 + 522076 * 2 ^ 59
def prefixEnd_522076 : Nat := 4983230072969 + 3 ^ 40 * 522076 * 2
def baseEnd_522076 : Nat := 238289712157159652399131

theorem tailTrace_522076 : CollatzResearch.WordTrace tailWord_522076 prefixEnd_522076 238289712157159652399131 := by
  unfold tailWord_522076
  simp only [CollatzResearch.WordTrace]
  refine ⟨9520838028307645163621041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12694450704410193551494721 9520838028307645163621041)
  ·
    refine ⟨7140628521230733872715781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9520838028307645163621041 7140628521230733872715781)
    ·
      refine ⟨1338867847730762601134209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7140628521230733872715781 1338867847730762601134209)
      ·
        refine ⟨1004150885798071950850657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1338867847730762601134209 1004150885798071950850657)
        ·
          refine ⟨753113164348553963137993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1004150885798071950850657 753113164348553963137993)
          ·
            refine ⟨564834873261415472353495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 753113164348553963137993 564834873261415472353495)
            ·
              refine ⟨847252309892123208530243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564834873261415472353495 847252309892123208530243)
              ·
                refine ⟨1270878464838184812795365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 847252309892123208530243 1270878464838184812795365)
                ·
                  refine ⟨238289712157159652399131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1270878464838184812795365 238289712157159652399131)
                  ·
                    rfl

theorem cell20_522076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 4].length) (baseStart_522076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522076 prefixEnd_522076 := by exact prefixLift 522076
  have htrace : WordTrace (prefixWord ++ tailWord_522076) baseStart_522076 baseEnd_522076 := by
    simpa [prefixWord, tailWord_522076, baseEnd_522076] using wordTrace_append hprefix tailTrace_522076
  have hstable : (prefixWord ++ tailWord_522076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522076).length < 2 ^ (prefixWord ++ tailWord_522076).sum := by decide
  have hdescent : baseEnd_522076 < baseStart_522076 := by decide
  rcases family_descends (prefixWord ++ tailWord_522076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522080 : List Nat := [2, 1, 1, 3, 3, 2, 3, 1, 4]
def baseStart_522080 : Nat := 118140960795 + 522080 * 2 ^ 59
def prefixEnd_522080 : Nat := 4983230072969 + 3 ^ 40 * 522080 * 2
def baseEnd_522080 : Nat := 238291537866153416265781

theorem tailTrace_522080 : CollatzResearch.WordTrace tailWord_522080 prefixEnd_522080 238291537866153416265781 := by
  unfold tailWord_522080
  simp only [CollatzResearch.WordTrace]
  refine ⟨9520910974300399505193847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12694547965733866006925129 9520910974300399505193847)
  ·
    refine ⟨14281366461450599257790771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9520910974300399505193847 14281366461450599257790771)
    ·
      refine ⟨21422049692175898886686157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14281366461450599257790771 21422049692175898886686157)
      ·
        refine ⟨8033268634565962082507309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21422049692175898886686157 8033268634565962082507309)
        ·
          refine ⟨3012475737962235780940241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8033268634565962082507309 3012475737962235780940241)
          ·
            refine ⟨2259356803471676835705181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3012475737962235780940241 2259356803471676835705181)
            ·
              refine ⟨847258801301878813389443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2259356803471676835705181 847258801301878813389443)
              ·
                refine ⟨1270888201952818220084165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 847258801301878813389443 1270888201952818220084165)
                ·
                  refine ⟨238291537866153416265781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1270888201952818220084165 238291537866153416265781)
                  ·
                    rfl

theorem cell20_522080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 4].length) (baseStart_522080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522080 prefixEnd_522080 := by exact prefixLift 522080
  have htrace : WordTrace (prefixWord ++ tailWord_522080) baseStart_522080 baseEnd_522080 := by
    simpa [prefixWord, tailWord_522080, baseEnd_522080] using wordTrace_append hprefix tailTrace_522080
  have hstable : (prefixWord ++ tailWord_522080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522080).length < 2 ^ (prefixWord ++ tailWord_522080).sum := by decide
  have hdescent : baseEnd_522080 < baseStart_522080 := by decide
  rcases family_descends (prefixWord ++ tailWord_522080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522087 : List Nat := [1, 1, 5, 1, 2, 1, 4, 5]
def baseStart_522087 : Nat := 118140960795 + 522087 * 2 ^ 59
def prefixEnd_522087 : Nat := 4983230072969 + 3 ^ 40 * 522087 * 2
def baseEnd_522087 : Nat := 79431577618964167677473

theorem tailTrace_522087 : CollatzResearch.WordTrace tailWord_522087 prefixEnd_522087 79431577618964167677473 := by
  unfold tailWord_522087
  simp only [CollatzResearch.WordTrace]
  refine ⟨19042077259575439205892515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12694718173050292803928343 19042077259575439205892515)
  ·
    refine ⟨28563115889363158808838773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19042077259575439205892515 28563115889363158808838773)
    ·
      refine ⟨2677792114627796138328635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28563115889363158808838773 2677792114627796138328635)
      ·
        refine ⟨4016688171941694207492953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2677792114627796138328635 4016688171941694207492953)
        ·
          refine ⟨3012516128956270655619715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4016688171941694207492953 3012516128956270655619715)
          ·
            refine ⟨4518774193434405983429573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3012516128956270655619715 4518774193434405983429573)
            ·
              refine ⟨847270161268951121893045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4518774193434405983429573 847270161268951121893045)
              ·
                refine ⟨79431577618964167677473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 847270161268951121893045 79431577618964167677473)
                ·
                  rfl

theorem cell20_522087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 5].length) (baseStart_522087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522087 prefixEnd_522087 := by exact prefixLift 522087
  have htrace : WordTrace (prefixWord ++ tailWord_522087) baseStart_522087 baseEnd_522087 := by
    simpa [prefixWord, tailWord_522087, baseEnd_522087] using wordTrace_append hprefix tailTrace_522087
  have hstable : (prefixWord ++ tailWord_522087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522087).length < 2 ^ (prefixWord ++ tailWord_522087).sum := by decide
  have hdescent : baseEnd_522087 < baseStart_522087 := by decide
  rcases family_descends (prefixWord ++ tailWord_522087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522135 : List Nat := [1, 1, 3, 3, 1, 4, 1, 4, 2]
def baseStart_522135 : Nat := 118140960795 + 522135 * 2 ^ 59
def prefixEnd_522135 : Nat := 4983230072969 + 3 ^ 40 * 522135 * 2
def baseEnd_522135 : Nat := 238316641364817669432223

theorem tailTrace_522135 : CollatzResearch.WordTrace tailWord_522135 prefixEnd_522135 238316641364817669432223 := by
  unfold tailWord_522135
  simp only [CollatzResearch.WordTrace]
  refine ⟨19043827963401543403639859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12695885308934362269093239 19043827963401543403639859)
  ·
    refine ⟨28565741945102315105459789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19043827963401543403639859 28565741945102315105459789)
    ·
      refine ⟨10712153229413368164547421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28565741945102315105459789 10712153229413368164547421)
      ·
        refine ⟨4017057461030013061705283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10712153229413368164547421 4017057461030013061705283)
        ·
          refine ⟨6025586191545019592557925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4017057461030013061705283 6025586191545019592557925)
          ·
            refine ⟨1129797410914691173604611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6025586191545019592557925 1129797410914691173604611)
            ·
              refine ⟨1694696116372036760406917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1129797410914691173604611 1694696116372036760406917)
              ·
                refine ⟨317755521819756892576297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1694696116372036760406917 317755521819756892576297)
                ·
                  refine ⟨238316641364817669432223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 317755521819756892576297 238316641364817669432223)
                  ·
                    rfl

theorem cell20_522135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 4, 2].length) (baseStart_522135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522135 prefixEnd_522135 := by exact prefixLift 522135
  have htrace : WordTrace (prefixWord ++ tailWord_522135) baseStart_522135 baseEnd_522135 := by
    simpa [prefixWord, tailWord_522135, baseEnd_522135] using wordTrace_append hprefix tailTrace_522135
  have hstable : (prefixWord ++ tailWord_522135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522135).length < 2 ^ (prefixWord ++ tailWord_522135).sum := by decide
  have hdescent : baseEnd_522135 < baseStart_522135 := by decide
  rcases family_descends (prefixWord ++ tailWord_522135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522152 : List Nat := [2, 1, 6, 2, 1, 1, 1, 2, 4]
def baseStart_522152 : Nat := 118140960795 + 522152 * 2 ^ 59
def prefixEnd_522152 : Nat := 4983230072969 + 3 ^ 40 * 522152 * 2
def baseEnd_522152 : Nat := 238324400628041165865487

theorem tailTrace_522152 : CollatzResearch.WordTrace tailWord_522152 prefixEnd_522152 238324400628041165865487 := by
  unfold tailWord_522152
  simp only [CollatzResearch.WordTrace]
  refine ⟨9522224002169977653504355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12696298669559970204672473 9522224002169977653504355)
  ·
    refine ⟨14283336003254966480256533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9522224002169977653504355 14283336003254966480256533)
    ·
      refine ⟨669531375152576553762025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14283336003254966480256533 669531375152576553762025)
      ·
        refine ⟨502148531364432415321519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 669531375152576553762025 502148531364432415321519)
        ·
          refine ⟨753222797046648622982279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502148531364432415321519 753222797046648622982279)
          ·
            refine ⟨1129834195569972934473419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 753222797046648622982279 1129834195569972934473419)
            ·
              refine ⟨1694751293354959401710129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1129834195569972934473419 1694751293354959401710129)
              ·
                refine ⟨1271063470016219551282597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1694751293354959401710129 1271063470016219551282597)
                ·
                  refine ⟨238324400628041165865487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1271063470016219551282597 238324400628041165865487)
                  ·
                    rfl

theorem cell20_522152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 4].length) (baseStart_522152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522152 prefixEnd_522152 := by exact prefixLift 522152
  have htrace : WordTrace (prefixWord ++ tailWord_522152) baseStart_522152 baseEnd_522152 := by
    simpa [prefixWord, tailWord_522152, baseEnd_522152] using wordTrace_append hprefix tailTrace_522152
  have hstable : (prefixWord ++ tailWord_522152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522152).length < 2 ^ (prefixWord ++ tailWord_522152).sum := by decide
  have hdescent : baseEnd_522152 < baseStart_522152 := by decide
  rcases family_descends (prefixWord ++ tailWord_522152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522163 : List Nat := [1, 1, 1, 2, 3, 1, 7, 4]
def baseStart_522163 : Nat := 118140960795 + 522163 * 2 ^ 59
def prefixEnd_522163 : Nat := 4983230072969 + 3 ^ 40 * 522163 * 2
def baseEnd_522163 : Nat := 79443140442591338832925

theorem tailTrace_522163 : CollatzResearch.WordTrace tailWord_522163 prefixEnd_522163 79443140442591338832925 := by
  unfold tailWord_522163
  simp only [CollatzResearch.WordTrace]
  refine ⟨19044849207300104185659143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12696566138200069457106095 19044849207300104185659143)
  ·
    refine ⟨28567273810950156278488715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19044849207300104185659143 28567273810950156278488715)
    ·
      refine ⟨42850910716425234417733073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28567273810950156278488715 42850910716425234417733073)
      ·
        refine ⟨32138183037318925813299805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42850910716425234417733073 32138183037318925813299805)
        ·
          refine ⟨12051818638994597179987427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32138183037318925813299805 12051818638994597179987427)
          ·
            refine ⟨18077727958491895769981141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12051818638994597179987427 18077727958491895769981141)
            ·
              refine ⟨423696749027153807108933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 18077727958491895769981141 423696749027153807108933)
              ·
                refine ⟨79443140442591338832925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 423696749027153807108933 79443140442591338832925)
                ·
                  rfl

theorem cell20_522163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 4].length) (baseStart_522163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522163 prefixEnd_522163 := by exact prefixLift 522163
  have htrace : WordTrace (prefixWord ++ tailWord_522163) baseStart_522163 baseEnd_522163 := by
    simpa [prefixWord, tailWord_522163, baseEnd_522163] using wordTrace_append hprefix tailTrace_522163
  have hstable : (prefixWord ++ tailWord_522163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522163).length < 2 ^ (prefixWord ++ tailWord_522163).sum := by decide
  have hdescent : baseEnd_522163 < baseStart_522163 := by decide
  rcases family_descends (prefixWord ++ tailWord_522163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522173 : List Nat := [1, 4, 1, 2, 3, 1, 1, 5, 2]
def baseStart_522173 : Nat := 118140960795 + 522173 * 2 ^ 59
def prefixEnd_522173 : Nat := 4983230072969 + 3 ^ 40 * 522173 * 2
def baseEnd_522173 : Nat := 238333985600258426165401

theorem tailTrace_522173 : CollatzResearch.WordTrace tailWord_522173 prefixEnd_522173 238333985600258426165401 := by
  unfold tailWord_522173
  simp only [CollatzResearch.WordTrace]
  refine ⟨19045213937263875893523173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12696809291509250595682115 19045213937263875893523173)
  ·
    refine ⟨3570977613236976730035595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19045213937263875893523173 3570977613236976730035595)
    ·
      refine ⟨5356466419855465095053393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3570977613236976730035595 5356466419855465095053393)
      ·
        refine ⟨4017349814891598821290045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5356466419855465095053393 4017349814891598821290045)
        ·
          refine ⟨1506506180584349557983767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4017349814891598821290045 1506506180584349557983767)
          ·
            refine ⟨2259759270876524336975651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1506506180584349557983767 2259759270876524336975651)
            ·
              refine ⟨3389638906314786505463477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2259759270876524336975651 3389638906314786505463477)
              ·
                refine ⟨317778647467011234887201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3389638906314786505463477 317778647467011234887201)
                ·
                  refine ⟨238333985600258426165401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 317778647467011234887201 238333985600258426165401)
                  ·
                    rfl

theorem cell20_522173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_522173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522173 prefixEnd_522173 := by exact prefixLift 522173
  have htrace : WordTrace (prefixWord ++ tailWord_522173) baseStart_522173 baseEnd_522173 := by
    simpa [prefixWord, tailWord_522173, baseEnd_522173] using wordTrace_append hprefix tailTrace_522173
  have hstable : (prefixWord ++ tailWord_522173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522173).length < 2 ^ (prefixWord ++ tailWord_522173).sum := by decide
  have hdescent : baseEnd_522173 < baseStart_522173 := by decide
  rcases family_descends (prefixWord ++ tailWord_522173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522208 : List Nat := [2, 1, 1, 3, 1, 1, 1, 7, 3]
def baseStart_522208 : Nat := 118140960795 + 522208 * 2 ^ 59
def prefixEnd_522208 : Nat := 4983230072969 + 3 ^ 40 * 522208 * 2
def baseEnd_522208 : Nat := 238349960553953859998591

theorem tailTrace_522208 : CollatzResearch.WordTrace tailWord_522208 prefixEnd_522208 238349960553953859998591 := by
  unfold tailWord_522208
  simp only [CollatzResearch.WordTrace]
  refine ⟨9523245246068538435523639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12697660328091384580698185 9523245246068538435523639)
  ·
    refine ⟨14284867869102807653285459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9523245246068538435523639 14284867869102807653285459)
    ·
      refine ⟨21427301803654211479928189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14284867869102807653285459 21427301803654211479928189)
      ·
        refine ⟨8035238176370329304973071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21427301803654211479928189 8035238176370329304973071)
        ·
          refine ⟨12052857264555493957459607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8035238176370329304973071 12052857264555493957459607)
          ·
            refine ⟨18079285896833240936189411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12052857264555493957459607 18079285896833240936189411)
            ·
              refine ⟨27118928845249861404284117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18079285896833240936189411 27118928845249861404284117)
              ·
                refine ⟨635599894810543626662909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 27118928845249861404284117 635599894810543626662909)
                ·
                  refine ⟨238349960553953859998591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 635599894810543626662909 238349960553953859998591)
                  ·
                    rfl

theorem cell20_522208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 3].length) (baseStart_522208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522208 prefixEnd_522208 := by exact prefixLift 522208
  have htrace : WordTrace (prefixWord ++ tailWord_522208) baseStart_522208 baseEnd_522208 := by
    simpa [prefixWord, tailWord_522208, baseEnd_522208] using wordTrace_append hprefix tailTrace_522208
  have hstable : (prefixWord ++ tailWord_522208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522208).length < 2 ^ (prefixWord ++ tailWord_522208).sum := by decide
  have hdescent : baseEnd_522208 < baseStart_522208 := by decide
  rcases family_descends (prefixWord ++ tailWord_522208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522267 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 7]
def baseStart_522267 : Nat := 118140960795 + 522267 * 2 ^ 59
def prefixEnd_522267 : Nat := 4983230072969 + 3 ^ 40 * 522267 * 2
def baseEnd_522267 : Nat := 238376889761611877031683

theorem tailTrace_522267 : CollatzResearch.WordTrace tailWord_522267 prefixEnd_522267 238376889761611877031683 := by
  unfold tailWord_522267
  simp only [CollatzResearch.WordTrace]
  refine ⟨19048642398923329947445055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12699094932615553298296703 19048642398923329947445055)
  ·
    refine ⟨28572963598384994921167583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19048642398923329947445055 28572963598384994921167583)
    ·
      refine ⟨42859445397577492381751375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28572963598384994921167583 42859445397577492381751375)
      ·
        refine ⟨64289168096366238572627063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42859445397577492381751375 64289168096366238572627063)
        ·
          refine ⟨96433752144549357858940595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64289168096366238572627063 96433752144549357858940595)
          ·
            refine ⟨144650628216824036788410893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96433752144549357858940595 144650628216824036788410893)
            ·
              refine ⟨54243985581309013795654085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144650628216824036788410893 54243985581309013795654085)
              ·
                refine ⟨10170747296495440086685141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54243985581309013795654085 10170747296495440086685141)
                ·
                  refine ⟨238376889761611877031683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10170747296495440086685141 238376889761611877031683)
                  ·
                    rfl

theorem cell20_522267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 7].length) (baseStart_522267 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522267 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522267 prefixEnd_522267 := by exact prefixLift 522267
  have htrace : WordTrace (prefixWord ++ tailWord_522267) baseStart_522267 baseEnd_522267 := by
    simpa [prefixWord, tailWord_522267, baseEnd_522267] using wordTrace_append hprefix tailTrace_522267
  have hstable : (prefixWord ++ tailWord_522267).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522267).length < 2 ^ (prefixWord ++ tailWord_522267).sum := by decide
  have hdescent : baseEnd_522267 < baseStart_522267 := by decide
  rcases family_descends (prefixWord ++ tailWord_522267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522301 : List Nat := [1, 4, 1, 3, 1, 1, 4, 2, 3]
def baseStart_522301 : Nat := 118140960795 + 522301 * 2 ^ 59
def prefixEnd_522301 : Nat := 4983230072969 + 3 ^ 40 * 522301 * 2
def baseEnd_522301 : Nat := 238392408288058869898211

theorem tailTrace_522301 : CollatzResearch.WordTrace tailWord_522301 prefixEnd_522301 238392408288058869898211 := by
  unfold tailWord_522301
  simp only [CollatzResearch.WordTrace]
  refine ⟨19049882480800153754182757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12699921653866769169455171 19049882480800153754182757)
  ·
    refine ⟨3571852965150028828909267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19049882480800153754182757 3571852965150028828909267)
    ·
      refine ⟨5357779447725043243363901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3571852965150028828909267 5357779447725043243363901)
      ·
        refine ⟨2009167292896891216261463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5357779447725043243363901 2009167292896891216261463)
        ·
          refine ⟨3013750939345336824392195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2009167292896891216261463 3013750939345336824392195)
          ·
            refine ⟨4520626409018005236588293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3013750939345336824392195 4520626409018005236588293)
            ·
              refine ⟨847617451690875981860305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4520626409018005236588293 847617451690875981860305)
              ·
                refine ⟨635713088768156986395229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 847617451690875981860305 635713088768156986395229)
                ·
                  refine ⟨238392408288058869898211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 635713088768156986395229 238392408288058869898211)
                  ·
                    rfl

theorem cell20_522301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_522301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522301 prefixEnd_522301 := by exact prefixLift 522301
  have htrace : WordTrace (prefixWord ++ tailWord_522301) baseStart_522301 baseEnd_522301 := by
    simpa [prefixWord, tailWord_522301, baseEnd_522301] using wordTrace_append hprefix tailTrace_522301
  have hstable : (prefixWord ++ tailWord_522301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522301).length < 2 ^ (prefixWord ++ tailWord_522301).sum := by decide
  have hdescent : baseEnd_522301 < baseStart_522301 := by decide
  rcases family_descends (prefixWord ++ tailWord_522301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522304 : List Nat := [2, 1, 1, 2, 2, 6, 2, 2, 2]
def baseStart_522304 : Nat := 118140960795 + 522304 * 2 ^ 59
def prefixEnd_522304 : Nat := 4983230072969 + 3 ^ 40 * 522304 * 2
def baseEnd_522304 : Nat := 238393777569804192798199

theorem tailTrace_522304 : CollatzResearch.WordTrace tailWord_522304 prefixEnd_522304 238393777569804192798199 := by
  unfold tailWord_522304
  simp only [CollatzResearch.WordTrace]
  refine ⟨9524995949894642633270983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12699994599859523511027977 9524995949894642633270983)
  ·
    refine ⟨14287493924841963949906475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9524995949894642633270983 14287493924841963949906475)
    ·
      refine ⟨21431240887262945924859713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14287493924841963949906475 21431240887262945924859713)
      ·
        refine ⟨16073430665447209443644785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21431240887262945924859713 16073430665447209443644785)
        ·
          refine ⟨12055072999085407082733589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16073430665447209443644785 12055072999085407082733589)
          ·
            refine ⟨565081546832128457003137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12055072999085407082733589 565081546832128457003137)
            ·
              refine ⟨423811160124096342752353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 565081546832128457003137 423811160124096342752353)
              ·
                refine ⟨317858370093072257064265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 423811160124096342752353 317858370093072257064265)
                ·
                  refine ⟨238393777569804192798199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 317858370093072257064265 238393777569804192798199)
                  ·
                    rfl

theorem cell20_522304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 2, 2].length) (baseStart_522304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522304 prefixEnd_522304 := by exact prefixLift 522304
  have htrace : WordTrace (prefixWord ++ tailWord_522304) baseStart_522304 baseEnd_522304 := by
    simpa [prefixWord, tailWord_522304, baseEnd_522304] using wordTrace_append hprefix tailTrace_522304
  have hstable : (prefixWord ++ tailWord_522304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522304).length < 2 ^ (prefixWord ++ tailWord_522304).sum := by decide
  have hdescent : baseEnd_522304 < baseStart_522304 := by decide
  rcases family_descends (prefixWord ++ tailWord_522304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522329 : List Nat := [1, 2, 1, 2, 2, 1, 5, 2, 4]
def baseStart_522329 : Nat := 118140960795 + 522329 * 2 ^ 59
def prefixEnd_522329 : Nat := 4983230072969 + 3 ^ 40 * 522329 * 2
def baseEnd_522329 : Nat := 238405188251015216964763

theorem tailTrace_522329 : CollatzResearch.WordTrace tailWord_522329 prefixEnd_522329 238405188251015216964763 := by
  unfold tailWord_522329
  simp only [CollatzResearch.WordTrace]
  refine ⟨19050903724698714536202041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12700602483132476357468027 19050903724698714536202041)
  ·
    refine ⟨14288177793524035902151531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19050903724698714536202041 14288177793524035902151531)
    ·
      refine ⟨21432266690286053853227297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14288177793524035902151531 21432266690286053853227297)
      ·
        refine ⟨16074200017714540389920473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21432266690286053853227297 16074200017714540389920473)
        ·
          refine ⟨12055650013285905292440355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16074200017714540389920473 12055650013285905292440355)
          ·
            refine ⟨18083475019928857938660533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12055650013285905292440355 18083475019928857938660533)
            ·
              refine ⟨1695325783118330431749425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18083475019928857938660533 1695325783118330431749425)
              ·
                refine ⟨1271494337338747823812069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1695325783118330431749425 1271494337338747823812069)
                ·
                  refine ⟨238405188251015216964763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1271494337338747823812069 238405188251015216964763)
                  ·
                    rfl

theorem cell20_522329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_522329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522329 prefixEnd_522329 := by exact prefixLift 522329
  have htrace : WordTrace (prefixWord ++ tailWord_522329) baseStart_522329 baseEnd_522329 := by
    simpa [prefixWord, tailWord_522329, baseEnd_522329] using wordTrace_append hprefix tailTrace_522329
  have hstable : (prefixWord ++ tailWord_522329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522329).length < 2 ^ (prefixWord ++ tailWord_522329).sum := by decide
  have hdescent : baseEnd_522329 < baseStart_522329 := by decide
  rcases family_descends (prefixWord ++ tailWord_522329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522332 : List Nat := [2, 2, 4, 1, 1, 3, 3, 4]
def baseStart_522332 : Nat := 118140960795 + 522332 * 2 ^ 59
def prefixEnd_522332 : Nat := 4983230072969 + 3 ^ 40 * 522332 * 2
def baseEnd_522332 : Nat := 79468852510920179954917

theorem tailTrace_522332 : CollatzResearch.WordTrace tailWord_522332 prefixEnd_522332 79468852510920179954917 := by
  unfold tailWord_522332
  simp only [CollatzResearch.WordTrace]
  refine ⟨9525506571843923024280625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12700675429125230699040833 9525506571843923024280625)
  ·
    refine ⟨7144129928882942268210469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9525506571843923024280625 7144129928882942268210469)
    ·
      refine ⟨1339524361665551675289463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7144129928882942268210469 1339524361665551675289463)
      ·
        refine ⟨2009286542498327512934195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1339524361665551675289463 2009286542498327512934195)
        ·
          refine ⟨3013929813747491269401293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2009286542498327512934195 3013929813747491269401293)
          ·
            refine ⟨1130223680155309226025485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3013929813747491269401293 1130223680155309226025485)
            ·
              refine ⟨423833880058240959759557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1130223680155309226025485 423833880058240959759557)
              ·
                refine ⟨79468852510920179954917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 423833880058240959759557 79468852510920179954917)
                ·
                  rfl

theorem cell20_522332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 4].length) (baseStart_522332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522332 prefixEnd_522332 := by exact prefixLift 522332
  have htrace : WordTrace (prefixWord ++ tailWord_522332) baseStart_522332 baseEnd_522332 := by
    simpa [prefixWord, tailWord_522332, baseEnd_522332] using wordTrace_append hprefix tailTrace_522332
  have hstable : (prefixWord ++ tailWord_522332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522332).length < 2 ^ (prefixWord ++ tailWord_522332).sum := by decide
  have hdescent : baseEnd_522332 < baseStart_522332 := by decide
  rcases family_descends (prefixWord ++ tailWord_522332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522377 : List Nat := [1, 2, 1, 1, 4, 2, 5, 1, 3]
def baseStart_522377 : Nat := 118140960795 + 522377 * 2 ^ 59
def prefixEnd_522377 : Nat := 4983230072969 + 3 ^ 40 * 522377 * 2
def baseEnd_522377 : Nat := 238427096758940383364567

theorem tailTrace_522377 : CollatzResearch.WordTrace tailWord_522377 prefixEnd_522377 238427096758940383364567 := by
  unfold tailWord_522377
  simp only [CollatzResearch.WordTrace]
  refine ⟨19052654428524818733949385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12701769619016545822632923 19052654428524818733949385)
  ·
    refine ⟨14289490821393614050462039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19052654428524818733949385 14289490821393614050462039)
    ·
      refine ⟨21434236232090421075693059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14289490821393614050462039 21434236232090421075693059)
      ·
        refine ⟨32151354348135631613539589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21434236232090421075693059 32151354348135631613539589)
        ·
          refine ⟨6028378940275430927538673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32151354348135631613539589 6028378940275430927538673)
          ·
            refine ⟨4521284205206573195654005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6028378940275430927538673 4521284205206573195654005)
            ·
              refine ⟨423870394238116237092563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4521284205206573195654005 423870394238116237092563)
              ·
                refine ⟨635805591357174355638845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423870394238116237092563 635805591357174355638845)
                ·
                  refine ⟨238427096758940383364567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 635805591357174355638845 238427096758940383364567)
                  ·
                    rfl

theorem cell20_522377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 3].length) (baseStart_522377 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522377 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522377 prefixEnd_522377 := by exact prefixLift 522377
  have htrace : WordTrace (prefixWord ++ tailWord_522377) baseStart_522377 baseEnd_522377 := by
    simpa [prefixWord, tailWord_522377, baseEnd_522377] using wordTrace_append hprefix tailTrace_522377
  have hstable : (prefixWord ++ tailWord_522377).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522377).length < 2 ^ (prefixWord ++ tailWord_522377).sum := by decide
  have hdescent : baseEnd_522377 < baseStart_522377 := by decide
  rcases family_descends (prefixWord ++ tailWord_522377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522391 : List Nat := [1, 1, 3, 3, 4, 1, 1, 6]
def baseStart_522391 : Nat := 118140960795 + 522391 * 2 ^ 59
def prefixEnd_522391 : Nat := 4983230072969 + 3 ^ 40 * 522391 * 2
def baseEnd_522391 : Nat := 79477828913472852299281

theorem tailTrace_522391 : CollatzResearch.WordTrace tailWord_522391 prefixEnd_522391 79477828913472852299281 := by
  unfold tailWord_522391
  simp only [CollatzResearch.WordTrace]
  refine ⟨19053165050474099124959027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12702110033649399416639351 19053165050474099124959027)
  ·
    refine ⟨28579747575711148687438541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19053165050474099124959027 28579747575711148687438541)
    ·
      refine ⟨10717405340891680757789453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28579747575711148687438541 10717405340891680757789453)
      ·
        refine ⟨4019027002834380284171045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10717405340891680757789453 4019027002834380284171045)
        ·
          refine ⟨753567563031446303282071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4019027002834380284171045 753567563031446303282071)
          ·
            refine ⟨1130351344547169454923107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 753567563031446303282071 1130351344547169454923107)
            ·
              refine ⟨1695527016820754182384661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1130351344547169454923107 1695527016820754182384661)
              ·
                refine ⟨79477828913472852299281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1695527016820754182384661 79477828913472852299281)
                ·
                  rfl

theorem cell20_522391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 6].length) (baseStart_522391 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522391 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522391 prefixEnd_522391 := by exact prefixLift 522391
  have htrace : WordTrace (prefixWord ++ tailWord_522391) baseStart_522391 baseEnd_522391 := by
    simpa [prefixWord, tailWord_522391, baseEnd_522391] using wordTrace_append hprefix tailTrace_522391
  have hstable : (prefixWord ++ tailWord_522391).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522391).length < 2 ^ (prefixWord ++ tailWord_522391).sum := by decide
  have hdescent : baseEnd_522391 < baseStart_522391 := by decide
  rcases family_descends (prefixWord ++ tailWord_522391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522401 : List Nat := [1, 2, 3, 3, 1, 2, 3, 3, 2]
def baseStart_522401 : Nat := 118140960795 + 522401 * 2 ^ 59
def prefixEnd_522401 : Nat := 4983230072969 + 3 ^ 40 * 522401 * 2
def baseEnd_522401 : Nat := 238438051012902966564469

theorem tailTrace_522401 : CollatzResearch.WordTrace tailWord_522401 prefixEnd_522401 238438051012902966564469 := by
  unfold tailWord_522401
  simp only [CollatzResearch.WordTrace]
  refine ⟨19053529780437870832823057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12702353186958580555215371 19053529780437870832823057)
  ·
    refine ⟨14290147335328403124617293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19053529780437870832823057 14290147335328403124617293)
    ·
      refine ⟨5358805250748151171731485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14290147335328403124617293 5358805250748151171731485)
      ·
        refine ⟨2009551969030556689399307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5358805250748151171731485 2009551969030556689399307)
        ·
          refine ⟨3014327953545835034098961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2009551969030556689399307 3014327953545835034098961)
          ·
            refine ⟨2260745965159376275574221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3014327953545835034098961 2260745965159376275574221)
            ·
              refine ⟨847779736934766103340333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2260745965159376275574221 847779736934766103340333)
              ·
                refine ⟨317917401350537288752625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 847779736934766103340333 317917401350537288752625)
                ·
                  refine ⟨238438051012902966564469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 317917401350537288752625 238438051012902966564469)
                  ·
                    rfl

theorem cell20_522401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 3, 2].length) (baseStart_522401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522401 prefixEnd_522401 := by exact prefixLift 522401
  have htrace : WordTrace (prefixWord ++ tailWord_522401) baseStart_522401 baseEnd_522401 := by
    simpa [prefixWord, tailWord_522401, baseEnd_522401] using wordTrace_append hprefix tailTrace_522401
  have hstable : (prefixWord ++ tailWord_522401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522401).length < 2 ^ (prefixWord ++ tailWord_522401).sum := by decide
  have hdescent : baseEnd_522401 < baseStart_522401 := by decide
  rcases family_descends (prefixWord ++ tailWord_522401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522414 : List Nat := [4, 1, 4, 2, 1, 1, 3, 2, 2]
def baseStart_522414 : Nat := 118140960795 + 522414 * 2 ^ 59
def prefixEnd_522414 : Nat := 4983230072969 + 3 ^ 40 * 522414 * 2
def baseEnd_522414 : Nat := 238443984567132699131083

theorem tailTrace_522414 : CollatzResearch.WordTrace tailWord_522414 prefixEnd_522414 238443984567132699131083 := by
  unfold tailWord_522414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2381750491173846756630787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12702669286260516035364197 2381750491173846756630787)
  ·
    refine ⟨3572625736760770134946181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2381750491173846756630787 3572625736760770134946181)
    ·
      refine ⟨669867325642644400302409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3572625736760770134946181 669867325642644400302409)
      ·
        refine ⟨502400494231983300226807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 669867325642644400302409 502400494231983300226807)
        ·
          refine ⟨753600741347974950340211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502400494231983300226807 753600741347974950340211)
          ·
            refine ⟨1130401112021962425510317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 753600741347974950340211 1130401112021962425510317)
            ·
              refine ⟨423900417008235909566369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1130401112021962425510317 423900417008235909566369)
              ·
                refine ⟨317925312756176932174777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 423900417008235909566369 317925312756176932174777)
                ·
                  refine ⟨238443984567132699131083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 317925312756176932174777 238443984567132699131083)
                  ·
                    rfl

theorem cell20_522414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_522414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522414 prefixEnd_522414 := by exact prefixLift 522414
  have htrace : WordTrace (prefixWord ++ tailWord_522414) baseStart_522414 baseEnd_522414 := by
    simpa [prefixWord, tailWord_522414, baseEnd_522414] using wordTrace_append hprefix tailTrace_522414
  have hstable : (prefixWord ++ tailWord_522414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522414).length < 2 ^ (prefixWord ++ tailWord_522414).sum := by decide
  have hdescent : baseEnd_522414 < baseStart_522414 := by decide
  rcases family_descends (prefixWord ++ tailWord_522414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522432 : List Nat := [2, 1, 1, 2, 5, 3, 2, 1, 3]
def baseStart_522432 : Nat := 118140960795 + 522432 * 2 ^ 59
def prefixEnd_522432 : Nat := 4983230072969 + 3 ^ 40 * 522432 * 2
def baseEnd_522432 : Nat := 238452200257604636531009

theorem tailTrace_522432 : CollatzResearch.WordTrace tailWord_522432 prefixEnd_522432 238452200257604636531009 := by
  unfold tailWord_522432
  simp only [CollatzResearch.WordTrace]
  refine ⟨9527330221662781563600775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12703106962217042084801033 9527330221662781563600775)
  ·
    refine ⟨14290995332494172345401163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9527330221662781563600775 14290995332494172345401163)
    ·
      refine ⟨21436492998741258518101745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14290995332494172345401163 21436492998741258518101745)
      ·
        refine ⟨16077369749055943888576309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21436492998741258518101745 16077369749055943888576309)
        ·
          refine ⟨1507253413973994739554029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16077369749055943888576309 1507253413973994739554029)
          ·
            refine ⟨565220030240248027332761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1507253413973994739554029 565220030240248027332761)
            ·
              refine ⟨423915022680186020499571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 565220030240248027332761 423915022680186020499571)
              ·
                refine ⟨635872534020279030749357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423915022680186020499571 635872534020279030749357)
                ·
                  refine ⟨238452200257604636531009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 635872534020279030749357 238452200257604636531009)
                  ·
                    rfl

theorem cell20_522432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 3].length) (baseStart_522432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522432 prefixEnd_522432 := by exact prefixLift 522432
  have htrace : WordTrace (prefixWord ++ tailWord_522432) baseStart_522432 baseEnd_522432 := by
    simpa [prefixWord, tailWord_522432, baseEnd_522432] using wordTrace_append hprefix tailTrace_522432
  have hstable : (prefixWord ++ tailWord_522432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522432).length < 2 ^ (prefixWord ++ tailWord_522432).sum := by decide
  have hdescent : baseEnd_522432 < baseStart_522432 := by decide
  rcases family_descends (prefixWord ++ tailWord_522432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522457 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 7]
def baseStart_522457 : Nat := 118140960795 + 522457 * 2 ^ 59
def prefixEnd_522457 : Nat := 4983230072969 + 3 ^ 40 * 522457 * 2
def baseEnd_522457 : Nat := 238463610938815660697573

theorem tailTrace_522457 : CollatzResearch.WordTrace tailWord_522457 prefixEnd_522457 238463610938815660697573 := by
  unfold tailWord_522457
  simp only [CollatzResearch.WordTrace]
  refine ⟨19055572268234992396861625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12703714845489994931241083 19055572268234992396861625)
  ·
    refine ⟨14291679201176244297646219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19055572268234992396861625 14291679201176244297646219)
    ·
      refine ⟨21437518801764366446469329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14291679201176244297646219 21437518801764366446469329)
      ·
        refine ⟨16078139101323274834851997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21437518801764366446469329 16078139101323274834851997)
        ·
          refine ⟨6029302162996228063069499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16078139101323274834851997 6029302162996228063069499)
          ·
            refine ⟨9043953244494342094604249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6029302162996228063069499 9043953244494342094604249)
            ·
              refine ⟨6782964933370756570953187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9043953244494342094604249 6782964933370756570953187)
              ·
                refine ⟨10174447400056134856429781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6782964933370756570953187 10174447400056134856429781)
                ·
                  refine ⟨238463610938815660697573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10174447400056134856429781 238463610938815660697573)
                  ·
                    rfl

theorem cell20_522457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_522457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522457 prefixEnd_522457 := by exact prefixLift 522457
  have htrace : WordTrace (prefixWord ++ tailWord_522457) baseStart_522457 baseEnd_522457 := by
    simpa [prefixWord, tailWord_522457, baseEnd_522457] using wordTrace_append hprefix tailTrace_522457
  have hstable : (prefixWord ++ tailWord_522457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522457).length < 2 ^ (prefixWord ++ tailWord_522457).sum := by decide
  have hdescent : baseEnd_522457 < baseStart_522457 := by decide
  rcases family_descends (prefixWord ++ tailWord_522457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522466 : List Nat := [3, 3, 4, 1, 1, 1, 2, 2, 3]
def baseStart_522466 : Nat := 118140960795 + 522466 * 2 ^ 59
def prefixEnd_522466 : Nat := 4983230072969 + 3 ^ 40 * 522466 * 2
def baseEnd_522466 : Nat := 238467718784051629397537

theorem tailTrace_522466 : CollatzResearch.WordTrace tailWord_522466 prefixEnd_522466 238467718784051629397537 := by
  unfold tailWord_522466
  simp only [CollatzResearch.WordTrace]
  refine ⟨4763975131300596733484813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12703933683468257955959501 4763975131300596733484813)
  ·
    refine ⟨1786490674237723775056805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4763975131300596733484813 1786490674237723775056805)
    ·
      refine ⟨334967001419573207823151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1786490674237723775056805 334967001419573207823151)
      ·
        refine ⟨502450502129359811734727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334967001419573207823151 502450502129359811734727)
        ·
          refine ⟨753675753194039717602091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502450502129359811734727 753675753194039717602091)
          ·
            refine ⟨1130513629791059576403137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 753675753194039717602091 1130513629791059576403137)
            ·
              refine ⟨847885222343294682302353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1130513629791059576403137 847885222343294682302353)
              ·
                refine ⟨635913916757471011726765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 847885222343294682302353 635913916757471011726765)
                ·
                  refine ⟨238467718784051629397537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 635913916757471011726765 238467718784051629397537)
                  ·
                    rfl

theorem cell20_522466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_522466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522466 prefixEnd_522466 := by exact prefixLift 522466
  have htrace : WordTrace (prefixWord ++ tailWord_522466) baseStart_522466 baseEnd_522466 := by
    simpa [prefixWord, tailWord_522466, baseEnd_522466] using wordTrace_append hprefix tailTrace_522466
  have hstable : (prefixWord ++ tailWord_522466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522466).length < 2 ^ (prefixWord ++ tailWord_522466).sum := by decide
  have hdescent : baseEnd_522466 < baseStart_522466 := by decide
  rcases family_descends (prefixWord ++ tailWord_522466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522467 : List Nat := [1, 1, 1, 8, 1, 8]
def baseStart_522467 : Nat := 118140960795 + 522467 * 2 ^ 59
def prefixEnd_522467 : Nat := 4983230072969 + 3 ^ 40 * 522467 * 2
def baseEnd_522467 : Nat := 8832154637455558161637

theorem tailTrace_522467 : CollatzResearch.WordTrace tailWord_522467 prefixEnd_522467 8832154637455558161637 := by
  unfold tailWord_522467
  simp only [CollatzResearch.WordTrace]
  refine ⟨19055936998198764104725655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12703957998799176069817103 19055936998198764104725655)
  ·
    refine ⟨28583905497298146157088483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19055936998198764104725655 28583905497298146157088483)
    ·
      refine ⟨42875858245947219235632725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28583905497298146157088483 42875858245947219235632725)
      ·
        refine ⟨502451463819693975417571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 42875858245947219235632725 502451463819693975417571)
        ·
          refine ⟨753677195729540963126357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502451463819693975417571 753677195729540963126357)
          ·
            refine ⟨8832154637455558161637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 753677195729540963126357 8832154637455558161637)
            ·
              rfl

theorem cell20_522467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 8].length) (baseStart_522467 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522467 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522467 prefixEnd_522467 := by exact prefixLift 522467
  have htrace : WordTrace (prefixWord ++ tailWord_522467) baseStart_522467 baseEnd_522467 := by
    simpa [prefixWord, tailWord_522467, baseEnd_522467] using wordTrace_append hprefix tailTrace_522467
  have hstable : (prefixWord ++ tailWord_522467).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522467).length < 2 ^ (prefixWord ++ tailWord_522467).sum := by decide
  have hdescent : baseEnd_522467 < baseStart_522467 := by decide
  rcases family_descends (prefixWord ++ tailWord_522467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522498 : List Nat := [3, 4, 1, 1, 2, 1, 1, 1, 6]
def baseStart_522498 : Nat := 118140960795 + 522498 * 2 ^ 59
def prefixEnd_522498 : Nat := 4983230072969 + 3 ^ 40 * 522498 * 2
def baseEnd_522498 : Nat := 238482324456001740330739

theorem tailTrace_522498 : CollatzResearch.WordTrace tailWord_522498 prefixEnd_522498 238482324456001740330739 := by
  unfold tailWord_522498
  simp only [CollatzResearch.WordTrace]
  refine ⟨4764266915271614099776037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12704711774057637599402765 4764266915271614099776037)
  ·
    refine ⟨893300046613427643708007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4764266915271614099776037 893300046613427643708007)
    ·
      refine ⟨1339950069920141465562011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 893300046613427643708007 1339950069920141465562011)
      ·
        refine ⟨2009925104880212198343017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1339950069920141465562011 2009925104880212198343017)
        ·
          refine ⟨1507443828660159148757263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2009925104880212198343017 1507443828660159148757263)
          ·
            refine ⟨2261165742990238723135895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1507443828660159148757263 2261165742990238723135895)
            ·
              refine ⟨3391748614485358084703843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2261165742990238723135895 3391748614485358084703843)
              ·
                refine ⟨5087622921728037127055765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3391748614485358084703843 5087622921728037127055765)
                ·
                  refine ⟨238482324456001740330739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5087622921728037127055765 238482324456001740330739)
                  ·
                    rfl

theorem cell20_522498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_522498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522498 prefixEnd_522498 := by exact prefixLift 522498
  have htrace : WordTrace (prefixWord ++ tailWord_522498) baseStart_522498 baseEnd_522498 := by
    simpa [prefixWord, tailWord_522498, baseEnd_522498] using wordTrace_append hprefix tailTrace_522498
  have hstable : (prefixWord ++ tailWord_522498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522498).length < 2 ^ (prefixWord ++ tailWord_522498).sum := by decide
  have hdescent : baseEnd_522498 < baseStart_522498 := by decide
  rcases family_descends (prefixWord ++ tailWord_522498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522505 : List Nat := [1, 2, 1, 1, 3, 5, 3, 4]
def baseStart_522505 : Nat := 118140960795 + 522505 * 2 ^ 59
def prefixEnd_522505 : Nat := 4983230072969 + 3 ^ 40 * 522505 * 2
def baseEnd_522505 : Nat := 79495173148913609032459

theorem tailTrace_522505 : CollatzResearch.WordTrace tailWord_522505 prefixEnd_522505 79495173148913609032459 := by
  unfold tailWord_522505
  simp only [CollatzResearch.WordTrace]
  refine ⟨19057322972061096594608969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12704881981374064396405979 19057322972061096594608969)
  ·
    refine ⟨14292992229045822445956727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19057322972061096594608969 14292992229045822445956727)
    ·
      refine ⟨21439488343568733668935091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14292992229045822445956727 21439488343568733668935091)
      ·
        refine ⟨32159232515353100503402637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21439488343568733668935091 32159232515353100503402637)
        ·
          refine ⟨12059712193257412688775989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32159232515353100503402637 12059712193257412688775989)
          ·
            refine ⟨1130598018117882439572749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12059712193257412688775989 1130598018117882439572749)
            ·
              refine ⟨423974256794205914839781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1130598018117882439572749 423974256794205914839781)
              ·
                refine ⟨79495173148913609032459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 423974256794205914839781 79495173148913609032459)
                ·
                  rfl

theorem cell20_522505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 4].length) (baseStart_522505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522505 prefixEnd_522505 := by exact prefixLift 522505
  have htrace : WordTrace (prefixWord ++ tailWord_522505) baseStart_522505 baseEnd_522505 := by
    simpa [prefixWord, tailWord_522505, baseEnd_522505] using wordTrace_append hprefix tailTrace_522505
  have hstable : (prefixWord ++ tailWord_522505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522505).length < 2 ^ (prefixWord ++ tailWord_522505).sum := by decide
  have hdescent : baseEnd_522505 < baseStart_522505 := by decide
  rcases family_descends (prefixWord ++ tailWord_522505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522525 : List Nat := [1, 4, 2, 3, 3, 1, 1, 2, 3]
def baseStart_522525 : Nat := 118140960795 + 522525 * 2 ^ 59
def prefixEnd_522525 : Nat := 4983230072969 + 3 ^ 40 * 522525 * 2
def baseEnd_522525 : Nat := 238494647991709646430629

theorem tailTrace_522525 : CollatzResearch.WordTrace tailWord_522525 prefixEnd_522525 238494647991709646430629 := by
  unfold tailWord_522525
  simp only [CollatzResearch.WordTrace]
  refine ⟨19058052431988640010337029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12705368287992426673558019 19058052431988640010337029)
  ·
    refine ⟨3573384830997870001938193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19058052431988640010337029 3573384830997870001938193)
    ·
      refine ⟨2680038623248402501453645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3573384830997870001938193 2680038623248402501453645)
      ·
        refine ⟨1005014483718150938045117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2680038623248402501453645 1005014483718150938045117)
        ·
          refine ⟨376880431394306601766919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1005014483718150938045117 376880431394306601766919)
          ·
            refine ⟨565320647091459902650379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376880431394306601766919 565320647091459902650379)
            ·
              refine ⟨847980970637189853975569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565320647091459902650379 847980970637189853975569)
              ·
                refine ⟨635985727977892390481677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 847980970637189853975569 635985727977892390481677)
                ·
                  refine ⟨238494647991709646430629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 635985727977892390481677 238494647991709646430629)
                  ·
                    rfl

theorem cell20_522525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_522525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522525 prefixEnd_522525 := by exact prefixLift 522525
  have htrace : WordTrace (prefixWord ++ tailWord_522525) baseStart_522525 baseEnd_522525 := by
    simpa [prefixWord, tailWord_522525, baseEnd_522525] using wordTrace_append hprefix tailTrace_522525
  have hstable : (prefixWord ++ tailWord_522525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522525).length < 2 ^ (prefixWord ++ tailWord_522525).sum := by decide
  have hdescent : baseEnd_522525 < baseStart_522525 := by decide
  rcases family_descends (prefixWord ++ tailWord_522525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522546 : List Nat := [3, 2, 1, 1, 5, 1, 3, 1, 3]
def baseStart_522546 : Nat := 118140960795 + 522546 * 2 ^ 59
def prefixEnd_522546 : Nat := 4983230072969 + 3 ^ 40 * 522546 * 2
def baseEnd_522546 : Nat := 238504232963926906730543

theorem tailTrace_522546 : CollatzResearch.WordTrace tailWord_522546 prefixEnd_522546 238504232963926906730543 := by
  unfold tailWord_522546
  simp only [CollatzResearch.WordTrace]
  refine ⟨4764704591228140149212873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12705878909941707064567661 4764704591228140149212873)
  ·
    refine ⟨3573528443421105111909655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4764704591228140149212873 3573528443421105111909655)
    ·
      refine ⟨5360292665131657667864483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3573528443421105111909655 5360292665131657667864483)
      ·
        refine ⟨8040438997697486501796725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5360292665131657667864483 8040438997697486501796725)
        ·
          refine ⟨753791156034139359543443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8040438997697486501796725 753791156034139359543443)
          ·
            refine ⟨1130686734051209039315165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 753791156034139359543443 1130686734051209039315165)
            ·
              refine ⟨424007525269203389743187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1130686734051209039315165 424007525269203389743187)
              ·
                refine ⟨636011287903805084614781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 424007525269203389743187 636011287903805084614781)
                ·
                  refine ⟨238504232963926906730543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 636011287903805084614781 238504232963926906730543)
                  ·
                    rfl

theorem cell20_522546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_522546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522546 prefixEnd_522546 := by exact prefixLift 522546
  have htrace : WordTrace (prefixWord ++ tailWord_522546) baseStart_522546 baseEnd_522546 := by
    simpa [prefixWord, tailWord_522546, baseEnd_522546] using wordTrace_append hprefix tailTrace_522546
  have hstable : (prefixWord ++ tailWord_522546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522546).length < 2 ^ (prefixWord ++ tailWord_522546).sum := by decide
  have hdescent : baseEnd_522546 < baseStart_522546 := by decide
  rcases family_descends (prefixWord ++ tailWord_522546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522574 : List Nat := [4, 1, 1, 1, 1, 1, 2, 7, 2]
def baseStart_522574 : Nat := 118140960795 + 522574 * 2 ^ 59
def prefixEnd_522574 : Nat := 4983230072969 + 3 ^ 40 * 522574 * 2
def baseEnd_522574 : Nat := 238517012926883253797095

theorem tailTrace_522574 : CollatzResearch.WordTrace tailWord_522574 prefixEnd_522574 238517012926883253797095 := by
  unfold tailWord_522574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2382479951101390172358847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12706559739207414252580517 2382479951101390172358847)
  ·
    refine ⟨3573719926652085258538271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2382479951101390172358847 3573719926652085258538271)
    ·
      refine ⟨5360579889978127887807407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3573719926652085258538271 5360579889978127887807407)
      ·
        refine ⟨8040869834967191831711111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5360579889978127887807407 8040869834967191831711111)
        ·
          refine ⟨12061304752450787747566667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8040869834967191831711111 12061304752450787747566667)
          ·
            refine ⟨18091957128676181621350001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12061304752450787747566667 18091957128676181621350001)
            ·
              refine ⟨13568967846507136216012501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18091957128676181621350001 13568967846507136216012501)
              ·
                refine ⟨318022683902511005062793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 13568967846507136216012501 318022683902511005062793)
                ·
                  refine ⟨238517012926883253797095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 318022683902511005062793 238517012926883253797095)
                  ·
                    rfl

theorem cell20_522574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_522574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522574 prefixEnd_522574 := by exact prefixLift 522574
  have htrace : WordTrace (prefixWord ++ tailWord_522574) baseStart_522574 baseEnd_522574 := by
    simpa [prefixWord, tailWord_522574, baseEnd_522574] using wordTrace_append hprefix tailTrace_522574
  have hstable : (prefixWord ++ tailWord_522574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522574).length < 2 ^ (prefixWord ++ tailWord_522574).sum := by decide
  have hdescent : baseEnd_522574 < baseStart_522574 := by decide
  rcases family_descends (prefixWord ++ tailWord_522574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522581 : List Nat := [1, 3, 2, 2, 4, 2, 6]
def baseStart_522581 : Nat := 118140960795 + 522581 * 2 ^ 59
def prefixEnd_522581 : Nat := 4983230072969 + 3 ^ 40 * 522581 * 2
def baseEnd_522581 : Nat := 26502245324180260062637

theorem tailTrace_522581 : CollatzResearch.WordTrace tailWord_522581 prefixEnd_522581 26502245324180260062637 := by
  unfold tailWord_522581
  simp only [CollatzResearch.WordTrace]
  refine ⟨19060094919785761574375597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12706729946523841049583731 19060094919785761574375597)
  ·
    refine ⟨7147535594919660590390849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19060094919785761574375597 7147535594919660590390849)
    ·
      refine ⟨5360651696189745442793137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7147535594919660590390849 5360651696189745442793137)
      ·
        refine ⟨4020488772142309082094853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5360651696189745442793137 4020488772142309082094853)
        ·
          refine ⟨753841644776682952892785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4020488772142309082094853 753841644776682952892785)
          ·
            refine ⟨565381233582512214669589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 753841644776682952892785 565381233582512214669589)
            ·
              refine ⟨26502245324180260062637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 565381233582512214669589 26502245324180260062637)
              ·
                rfl

theorem cell20_522581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 6].length) (baseStart_522581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522581 prefixEnd_522581 := by exact prefixLift 522581
  have htrace : WordTrace (prefixWord ++ tailWord_522581) baseStart_522581 baseEnd_522581 := by
    simpa [prefixWord, tailWord_522581, baseEnd_522581] using wordTrace_append hprefix tailTrace_522581
  have hstable : (prefixWord ++ tailWord_522581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522581).length < 2 ^ (prefixWord ++ tailWord_522581).sum := by decide
  have hdescent : baseEnd_522581 < baseStart_522581 := by decide
  rcases family_descends (prefixWord ++ tailWord_522581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522647 : List Nat := [1, 1, 3, 3, 1, 1, 2, 3, 5]
def baseStart_522647 : Nat := 118140960795 + 522647 * 2 ^ 59
def prefixEnd_522647 : Nat := 4983230072969 + 3 ^ 40 * 522647 * 2
def baseEnd_522647 : Nat := 238550332116019444363463

theorem tailTrace_522647 : CollatzResearch.WordTrace tailWord_522647 prefixEnd_522647 238550332116019444363463 := by
  unfold tailWord_522647
  simp only [CollatzResearch.WordTrace]
  refine ⟨19062502137546654846278195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12708334758364436564185463 19062502137546654846278195)
  ·
    refine ⟨28593753206319982269417293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19062502137546654846278195 28593753206319982269417293)
    ·
      refine ⟨10722657452369993351031485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28593753206319982269417293 10722657452369993351031485)
      ·
        refine ⟨4020996544638747506636807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10722657452369993351031485 4020996544638747506636807)
        ·
          refine ⟨6031494816958121259955211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4020996544638747506636807 6031494816958121259955211)
          ·
            refine ⟨9047242225437181889932817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6031494816958121259955211 9047242225437181889932817)
            ·
              refine ⟨6785431669077886417449613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9047242225437181889932817 6785431669077886417449613)
              ·
                refine ⟨2544536875904207406543605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6785431669077886417449613 2544536875904207406543605)
                ·
                  refine ⟨238550332116019444363463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2544536875904207406543605 238550332116019444363463)
                  ·
                    rfl

theorem cell20_522647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 5].length) (baseStart_522647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522647 prefixEnd_522647 := by exact prefixLift 522647
  have htrace : WordTrace (prefixWord ++ tailWord_522647) baseStart_522647 baseEnd_522647 := by
    simpa [prefixWord, tailWord_522647, baseEnd_522647] using wordTrace_append hprefix tailTrace_522647
  have hstable : (prefixWord ++ tailWord_522647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522647).length < 2 ^ (prefixWord ++ tailWord_522647).sum := by decide
  have hdescent : baseEnd_522647 < baseStart_522647 := by decide
  rcases family_descends (prefixWord ++ tailWord_522647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522709 : List Nat := [1, 3, 2, 3, 1, 2, 1, 3, 4]
def baseStart_522709 : Nat := 118140960795 + 522709 * 2 ^ 59
def prefixEnd_522709 : Nat := 4983230072969 + 3 ^ 40 * 522709 * 2
def baseEnd_522709 : Nat := 238578630605422784296543

theorem tailTrace_522709 : CollatzResearch.WordTrace tailWord_522709 prefixEnd_522709 238578630605422784296543 := by
  unfold tailWord_522709
  simp only [CollatzResearch.WordTrace]
  refine ⟨19064763463322039435035181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12709842308881359623356787 19064763463322039435035181)
  ·
    refine ⟨7149286298745764788138193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19064763463322039435035181 7149286298745764788138193)
    ·
      refine ⟨5361964724059323591103645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7149286298745764788138193 5361964724059323591103645)
      ·
        refine ⟨2010736771522246346663867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5361964724059323591103645 2010736771522246346663867)
        ·
          refine ⟨3016105157283369519995801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2010736771522246346663867 3016105157283369519995801)
          ·
            refine ⟨2262078867962527139996851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3016105157283369519995801 2262078867962527139996851)
            ·
              refine ⟨3393118301943790709995277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2262078867962527139996851 3393118301943790709995277)
              ·
                refine ⟨1272419363228921516248229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3393118301943790709995277 1272419363228921516248229)
                ·
                  refine ⟨238578630605422784296543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1272419363228921516248229 238578630605422784296543)
                  ·
                    rfl

theorem cell20_522709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_522709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522709 prefixEnd_522709 := by exact prefixLift 522709
  have htrace : WordTrace (prefixWord ++ tailWord_522709) baseStart_522709 baseEnd_522709 := by
    simpa [prefixWord, tailWord_522709, baseEnd_522709] using wordTrace_append hprefix tailTrace_522709
  have hstable : (prefixWord ++ tailWord_522709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522709).length < 2 ^ (prefixWord ++ tailWord_522709).sum := by decide
  have hdescent : baseEnd_522709 < baseStart_522709 := by decide
  rcases family_descends (prefixWord ++ tailWord_522709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522719 : List Nat := [1, 1, 2, 3, 3, 3, 3, 1, 3]
def baseStart_522719 : Nat := 118140960795 + 522719 * 2 ^ 59
def prefixEnd_522719 : Nat := 4983230072969 + 3 ^ 40 * 522719 * 2
def baseEnd_522719 : Nat := 238583194877907193963169

theorem tailTrace_522719 : CollatzResearch.WordTrace tailWord_522719 prefixEnd_522719 238583194877907193963169 := by
  unfold tailWord_522719
  simp only [CollatzResearch.WordTrace]
  refine ⟨19065128193285811142899211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12710085462190540761932807 19065128193285811142899211)
  ·
    refine ⟨28597692289928716714348817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19065128193285811142899211 28597692289928716714348817)
    ·
      refine ⟨21448269217446537535761613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28597692289928716714348817 21448269217446537535761613)
      ·
        refine ⟨8043100956542451575910605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21448269217446537535761613 8043100956542451575910605)
        ·
          refine ⟨3016162858703419340966477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8043100956542451575910605 3016162858703419340966477)
          ·
            refine ⟨1131061072013782252862429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3016162858703419340966477 1131061072013782252862429)
            ·
              refine ⟨424147902005168344823411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1131061072013782252862429 424147902005168344823411)
              ·
                refine ⟨636221853007752517235117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 424147902005168344823411 636221853007752517235117)
                ·
                  refine ⟨238583194877907193963169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 636221853007752517235117 238583194877907193963169)
                  ·
                    rfl

theorem cell20_522719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 3].length) (baseStart_522719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522719 prefixEnd_522719 := by exact prefixLift 522719
  have htrace : WordTrace (prefixWord ++ tailWord_522719) baseStart_522719 baseEnd_522719 := by
    simpa [prefixWord, tailWord_522719, baseEnd_522719] using wordTrace_append hprefix tailTrace_522719
  have hstable : (prefixWord ++ tailWord_522719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522719).length < 2 ^ (prefixWord ++ tailWord_522719).sum := by decide
  have hdescent : baseEnd_522719 < baseStart_522719 := by decide
  rcases family_descends (prefixWord ++ tailWord_522719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522733 : List Nat := [1, 5, 1, 3, 1, 2, 1, 6]
def baseStart_522733 : Nat := 118140960795 + 522733 * 2 ^ 59
def prefixEnd_522733 : Nat := 4983230072969 + 3 ^ 40 * 522733 * 2
def baseEnd_522733 : Nat := 79529861619795122498815

theorem tailTrace_522733 : CollatzResearch.WordTrace tailWord_522733 prefixEnd_522733 79529861619795122498815 := by
  unfold tailWord_522733
  simp only [CollatzResearch.WordTrace]
  refine ⟨19065638815235091533908853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12710425876823394355939235 19065638815235091533908853)
  ·
    refine ⟨1787403638928289831303955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19065638815235091533908853 1787403638928289831303955)
    ·
      refine ⟨2681105458392434746955933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1787403638928289831303955 2681105458392434746955933)
      ·
        refine ⟨1005414546897163030108475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2681105458392434746955933 1005414546897163030108475)
        ·
          refine ⟨1508121820345744545162713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1005414546897163030108475 1508121820345744545162713)
          ·
            refine ⟨1131091365259308408872035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1508121820345744545162713 1131091365259308408872035)
            ·
              refine ⟨1696637047888962613308053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1131091365259308408872035 1696637047888962613308053)
              ·
                refine ⟨79529861619795122498815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1696637047888962613308053 79529861619795122498815)
                ·
                  rfl

theorem cell20_522733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 6].length) (baseStart_522733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522733 prefixEnd_522733 := by exact prefixLift 522733
  have htrace : WordTrace (prefixWord ++ tailWord_522733) baseStart_522733 baseEnd_522733 := by
    simpa [prefixWord, tailWord_522733, baseEnd_522733] using wordTrace_append hprefix tailTrace_522733
  have hstable : (prefixWord ++ tailWord_522733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522733).length < 2 ^ (prefixWord ++ tailWord_522733).sum := by decide
  have hdescent : baseEnd_522733 < baseStart_522733 := by decide
  rcases family_descends (prefixWord ++ tailWord_522733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522764 : List Nat := [2, 2, 1, 2, 4, 3, 1, 1, 4]
def baseStart_522764 : Nat := 118140960795 + 522764 * 2 ^ 59
def prefixEnd_522764 : Nat := 4983230072969 + 3 ^ 40 * 522764 * 2
def baseEnd_522764 : Nat := 238603734104087037462985

theorem tailTrace_522764 : CollatzResearch.WordTrace tailWord_522764 prefixEnd_522764 238603734104087037462985 := by
  unfold tailWord_522764
  simp only [CollatzResearch.WordTrace]
  refine ⟨9533384739061391914143673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12711179652081855885524897 9533384739061391914143673)
  ·
    refine ⟨7150038554296043935607755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9533384739061391914143673 7150038554296043935607755)
    ·
      refine ⟨10725057831444065903411633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7150038554296043935607755 10725057831444065903411633)
      ·
        refine ⟨8043793373583049427558725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10725057831444065903411633 8043793373583049427558725)
        ·
          refine ⟨1508211257546821767667261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8043793373583049427558725 1508211257546821767667261)
          ·
            refine ⟨565579221580058162875223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1508211257546821767667261 565579221580058162875223)
            ·
              refine ⟨848368832370087244312835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565579221580058162875223 848368832370087244312835)
              ·
                refine ⟨1272553248555130866469253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 848368832370087244312835 1272553248555130866469253)
                ·
                  refine ⟨238603734104087037462985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1272553248555130866469253 238603734104087037462985)
                  ·
                    rfl

theorem cell20_522764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 4].length) (baseStart_522764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522764 prefixEnd_522764 := by exact prefixLift 522764
  have htrace : WordTrace (prefixWord ++ tailWord_522764) baseStart_522764 baseEnd_522764 := by
    simpa [prefixWord, tailWord_522764, baseEnd_522764] using wordTrace_append hprefix tailTrace_522764
  have hstable : (prefixWord ++ tailWord_522764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522764).length < 2 ^ (prefixWord ++ tailWord_522764).sum := by decide
  have hdescent : baseEnd_522764 < baseStart_522764 := by decide
  rcases family_descends (prefixWord ++ tailWord_522764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522830 : List Nat := [4, 1, 1, 1, 1, 2, 5, 5]
def baseStart_522830 : Nat := 118140960795 + 522830 * 2 ^ 59
def prefixEnd_522830 : Nat := 4983230072969 + 3 ^ 40 * 522830 * 2
def baseEnd_522830 : Nat := 79544619434161380420905

theorem tailTrace_522830 : CollatzResearch.WordTrace tailWord_522830 prefixEnd_522830 79544619434161380420905 := by
  unfold tailWord_522830
  simp only [CollatzResearch.WordTrace]
  refine ⟨2383647086985459637523743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12712784463922451400126629 2383647086985459637523743)
  ·
    refine ⟨3575470630478189456285615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2383647086985459637523743 3575470630478189456285615)
    ·
      refine ⟨5363205945717284184428423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3575470630478189456285615 5363205945717284184428423)
      ·
        refine ⟨8044808918575926276642635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5363205945717284184428423 8044808918575926276642635)
        ·
          refine ⟨12067213377863889414963953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8044808918575926276642635 12067213377863889414963953)
          ·
            refine ⟨9050410033397917061222965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12067213377863889414963953 9050410033397917061222965)
            ·
              refine ⟨848475940631054724489653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9050410033397917061222965 848475940631054724489653)
              ·
                refine ⟨79544619434161380420905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 848475940631054724489653 79544619434161380420905)
                ·
                  rfl

theorem cell20_522830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_522830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522830 prefixEnd_522830 := by exact prefixLift 522830
  have htrace : WordTrace (prefixWord ++ tailWord_522830) baseStart_522830 baseEnd_522830 := by
    simpa [prefixWord, tailWord_522830, baseEnd_522830] using wordTrace_append hprefix tailTrace_522830
  have hstable : (prefixWord ++ tailWord_522830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522830).length < 2 ^ (prefixWord ++ tailWord_522830).sum := by decide
  have hdescent : baseEnd_522830 < baseStart_522830 := by decide
  rcases family_descends (prefixWord ++ tailWord_522830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522875 : List Nat := [1, 1, 1, 1, 1, 4, 2, 6, 3]
def baseStart_522875 : Nat := 118140960795 + 522875 * 2 ^ 59
def prefixEnd_522875 : Nat := 4983230072969 + 3 ^ 40 * 522875 * 2
def baseEnd_522875 : Nat := 238654397528663984762531

theorem tailTrace_522875 : CollatzResearch.WordTrace tailWord_522875 prefixEnd_522875 238654397528663984762531 := by
  unfold tailWord_522875
  simp only [CollatzResearch.WordTrace]
  refine ⟨19070817980720649785578079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12713878653813766523718719 19070817980720649785578079)
  ·
    refine ⟨28606226971080974678367119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19070817980720649785578079 28606226971080974678367119)
    ·
      refine ⟨42909340456621462017550679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28606226971080974678367119 42909340456621462017550679)
      ·
        refine ⟨64364010684932193026326019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42909340456621462017550679 64364010684932193026326019)
        ·
          refine ⟨96546016027398289539489029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64364010684932193026326019 96546016027398289539489029)
          ·
            refine ⟨18102378005137179288654193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96546016027398289539489029 18102378005137179288654193)
            ·
              refine ⟨13576783503852884466490645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18102378005137179288654193 13576783503852884466490645)
              ·
                refine ⟨636411726743103959366749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13576783503852884466490645 636411726743103959366749)
                ·
                  refine ⟨238654397528663984762531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 636411726743103959366749 238654397528663984762531)
                  ·
                    rfl

theorem cell20_522875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 3].length) (baseStart_522875 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522875 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522875 prefixEnd_522875 := by exact prefixLift 522875
  have htrace : WordTrace (prefixWord ++ tailWord_522875) baseStart_522875 baseEnd_522875 := by
    simpa [prefixWord, tailWord_522875, baseEnd_522875] using wordTrace_append hprefix tailTrace_522875
  have hstable : (prefixWord ++ tailWord_522875).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522875).length < 2 ^ (prefixWord ++ tailWord_522875).sum := by decide
  have hdescent : baseEnd_522875 < baseStart_522875 := by decide
  rcases family_descends (prefixWord ++ tailWord_522875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522889 : List Nat := [1, 2, 1, 1, 4, 1, 1, 9]
def baseStart_522889 : Nat := 118140960795 + 522889 * 2 ^ 59
def prefixEnd_522889 : Nat := 4983230072969 + 3 ^ 40 * 522889 * 2
def baseEnd_522889 : Nat := 79553595836714052765269

theorem tailTrace_522889 : CollatzResearch.WordTrace tailWord_522889 prefixEnd_522889 79553595836714052765269 := by
  unfold tailWord_522889
  simp only [CollatzResearch.WordTrace]
  refine ⟨19071328602669930176587721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12714219068446620117725147 19071328602669930176587721)
  ·
    refine ⟨14303496452002447632440791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19071328602669930176587721 14303496452002447632440791)
    ·
      refine ⟨21455244678003671448661187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14303496452002447632440791 21455244678003671448661187)
      ·
        refine ⟨32182867017005507172991781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21455244678003671448661187 32182867017005507172991781)
        ·
          refine ⟨6034287565688532594935959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32182867017005507172991781 6034287565688532594935959)
          ·
            refine ⟨9051431348532798892403939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6034287565688532594935959 9051431348532798892403939)
            ·
              refine ⟨13577147022799198338605909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9051431348532798892403939 13577147022799198338605909)
              ·
                refine ⟨79553595836714052765269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13577147022799198338605909 79553595836714052765269)
                ·
                  rfl

theorem cell20_522889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 9].length) (baseStart_522889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522889 prefixEnd_522889 := by exact prefixLift 522889
  have htrace : WordTrace (prefixWord ++ tailWord_522889) baseStart_522889 baseEnd_522889 := by
    simpa [prefixWord, tailWord_522889, baseEnd_522889] using wordTrace_append hprefix tailTrace_522889
  have hstable : (prefixWord ++ tailWord_522889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522889).length < 2 ^ (prefixWord ++ tailWord_522889).sum := by decide
  have hdescent : baseEnd_522889 < baseStart_522889 := by decide
  rcases family_descends (prefixWord ++ tailWord_522889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522912 : List Nat := [2, 1, 1, 4, 5, 1, 1, 3, 2]
def baseStart_522912 : Nat := 118140960795 + 522912 * 2 ^ 59
def prefixEnd_522912 : Nat := 4983230072969 + 3 ^ 40 * 522912 * 2
def baseEnd_522912 : Nat := 238671285336856300529047

theorem tailTrace_522912 : CollatzResearch.WordTrace tailWord_522912 prefixEnd_522912 238671285336856300529047 := by
  unfold tailWord_522912
  simp only [CollatzResearch.WordTrace]
  refine ⟨9536083740793302552337495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12714778321057736736449993 9536083740793302552337495)
  ·
    refine ⟨14304125611189953828506243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9536083740793302552337495 14304125611189953828506243)
    ·
      refine ⟨21456188416784930742759365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14304125611189953828506243 21456188416784930742759365)
      ·
        refine ⟨4023035328147174514267381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21456188416784930742759365 4023035328147174514267381)
        ·
          refine ⟨377159562013797610712567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4023035328147174514267381 377159562013797610712567)
          ·
            refine ⟨565739343020696416068851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377159562013797610712567 565739343020696416068851)
            ·
              refine ⟨848609014531044624103277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565739343020696416068851 848609014531044624103277)
              ·
                refine ⟨318228380449141734038729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 848609014531044624103277 318228380449141734038729)
                ·
                  refine ⟨238671285336856300529047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 318228380449141734038729 238671285336856300529047)
                  ·
                    rfl

theorem cell20_522912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 3, 2].length) (baseStart_522912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522912 prefixEnd_522912 := by exact prefixLift 522912
  have htrace : WordTrace (prefixWord ++ tailWord_522912) baseStart_522912 baseEnd_522912 := by
    simpa [prefixWord, tailWord_522912, baseEnd_522912] using wordTrace_append hprefix tailTrace_522912
  have hstable : (prefixWord ++ tailWord_522912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522912).length < 2 ^ (prefixWord ++ tailWord_522912).sum := by decide
  have hdescent : baseEnd_522912 < baseStart_522912 := by decide
  rcases family_descends (prefixWord ++ tailWord_522912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522927 : List Nat := [1, 1, 2, 1, 2, 5, 8]
def baseStart_522927 : Nat := 118140960795 + 522927 * 2 ^ 59
def prefixEnd_522927 : Nat := 4983230072969 + 3 ^ 40 * 522927 * 2
def baseEnd_522927 : Nat := 26519792416175879447665

theorem tailTrace_522927 : CollatzResearch.WordTrace tailWord_522927 prefixEnd_522927 26519792416175879447665 := by
  unfold tailWord_522927
  simp only [CollatzResearch.WordTrace]
  refine ⟨19072714576532262666471035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12715143051021508444314023 19072714576532262666471035)
  ·
    refine ⟨28609071864798393999706553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19072714576532262666471035 28609071864798393999706553)
    ·
      refine ⟨21456803898598795499779915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28609071864798393999706553 21456803898598795499779915)
      ·
        refine ⟨32185205847898193249669873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21456803898598795499779915 32185205847898193249669873)
        ·
          refine ⟨24138904385923644937252405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32185205847898193249669873 24138904385923644937252405)
          ·
            refine ⟨2263022286180341712867413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24138904385923644937252405 2263022286180341712867413)
            ·
              refine ⟨26519792416175879447665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2263022286180341712867413 26519792416175879447665)
              ·
                rfl

theorem cell20_522927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 8].length) (baseStart_522927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522927 prefixEnd_522927 := by exact prefixLift 522927
  have htrace : WordTrace (prefixWord ++ tailWord_522927) baseStart_522927 baseEnd_522927 := by
    simpa [prefixWord, tailWord_522927, baseEnd_522927] using wordTrace_append hprefix tailTrace_522927
  have hstable : (prefixWord ++ tailWord_522927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522927).length < 2 ^ (prefixWord ++ tailWord_522927).sum := by decide
  have hdescent : baseEnd_522927 < baseStart_522927 := by decide
  rcases family_descends (prefixWord ++ tailWord_522927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_522944 : List Nat := [2, 1, 1, 2, 4, 3, 2, 5]
def baseStart_522944 : Nat := 118140960795 + 522944 * 2 ^ 59
def prefixEnd_522944 : Nat := 4983230072969 + 3 ^ 40 * 522944 * 2
def baseEnd_522944 : Nat := 79561963669602137154083

theorem tailTrace_522944 : CollatzResearch.WordTrace tailWord_522944 prefixEnd_522944 79561963669602137154083 := by
  unfold tailWord_522944
  simp only [CollatzResearch.WordTrace]
  refine ⟨9536667308735337284919943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12715556411647116379893257 9536667308735337284919943)
  ·
    refine ⟨14305000963103005927379915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9536667308735337284919943 14305000963103005927379915)
    ·
      refine ⟨21457501444654508891069873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14305000963103005927379915 21457501444654508891069873)
      ·
        refine ⟨16093126083490881668302405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21457501444654508891069873 16093126083490881668302405)
        ·
          refine ⟨3017461140654540312806701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16093126083490881668302405 3017461140654540312806701)
          ·
            refine ⟨1131547927745452617302513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3017461140654540312806701 1131547927745452617302513)
            ·
              refine ⟨848660945809089462976885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1131547927745452617302513 848660945809089462976885)
              ·
                refine ⟨79561963669602137154083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 848660945809089462976885 79561963669602137154083)
                ·
                  rfl

theorem cell20_522944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 5].length) (baseStart_522944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_522944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_522944 prefixEnd_522944 := by exact prefixLift 522944
  have htrace : WordTrace (prefixWord ++ tailWord_522944) baseStart_522944 baseEnd_522944 := by
    simpa [prefixWord, tailWord_522944, baseEnd_522944] using wordTrace_append hprefix tailTrace_522944
  have hstable : (prefixWord ++ tailWord_522944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_522944).length < 2 ^ (prefixWord ++ tailWord_522944).sum := by decide
  have hdescent : baseEnd_522944 < baseStart_522944 := by decide
  rcases family_descends (prefixWord ++ tailWord_522944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523026 : List Nat := [3, 2, 4, 1, 2, 1, 2, 3, 2]
def baseStart_523026 : Nat := 118140960795 + 523026 * 2 ^ 59
def prefixEnd_523026 : Nat := 4983230072969 + 3 ^ 40 * 523026 * 2
def baseEnd_523026 : Nat := 238723318043178570728581

theorem tailTrace_523026 : CollatzResearch.WordTrace tailWord_523026 prefixEnd_523026 238723318043178570728581 := by
  unfold tailWord_523026
  simp only [CollatzResearch.WordTrace]
  refine ⟨4769081350793400643581233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12717550268782401716216621 4769081350793400643581233)
  ·
    refine ⟨3576811013095050482685925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4769081350793400643581233 3576811013095050482685925)
    ·
      refine ⟨670652064955321965503611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3576811013095050482685925 670652064955321965503611)
      ·
        refine ⟨1005978097432982948255417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670652064955321965503611 1005978097432982948255417)
        ·
          refine ⟨754483573074737211191563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1005978097432982948255417 754483573074737211191563)
          ·
            refine ⟨1131725359612105816787345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754483573074737211191563 1131725359612105816787345)
            ·
              refine ⟨848794019709079362590509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1131725359612105816787345 848794019709079362590509)
              ·
                refine ⟨318297757390904760971441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 848794019709079362590509 318297757390904760971441)
                ·
                  refine ⟨238723318043178570728581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 318297757390904760971441 238723318043178570728581)
                  ·
                    rfl

theorem cell20_523026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_523026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523026 prefixEnd_523026 := by exact prefixLift 523026
  have htrace : WordTrace (prefixWord ++ tailWord_523026) baseStart_523026 baseEnd_523026 := by
    simpa [prefixWord, tailWord_523026, baseEnd_523026] using wordTrace_append hprefix tailTrace_523026
  have hstable : (prefixWord ++ tailWord_523026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523026).length < 2 ^ (prefixWord ++ tailWord_523026).sum := by decide
  have hdescent : baseEnd_523026 < baseStart_523026 := by decide
  rcases family_descends (prefixWord ++ tailWord_523026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523034 : List Nat := [3, 1, 1, 3, 2, 1, 1, 2, 6]
def baseStart_523034 : Nat := 118140960795 + 523034 * 2 ^ 59
def prefixEnd_523034 : Nat := 4983230072969 + 3 ^ 40 * 523034 * 2
def baseEnd_523034 : Nat := 238726969461166098461881

theorem tailTrace_523034 : CollatzResearch.WordTrace tailWord_523034 prefixEnd_523034 238726969461166098461881 := by
  unfold tailWord_523034
  simp only [CollatzResearch.WordTrace]
  refine ⟨4769154296786154985154039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12717744791429746627077437 4769154296786154985154039)
  ·
    refine ⟨7153731445179232477731059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4769154296786154985154039 7153731445179232477731059)
    ·
      refine ⟨10730597167768848716596589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7153731445179232477731059 10730597167768848716596589)
      ·
        refine ⟨4023973937913318268723721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10730597167768848716596589 4023973937913318268723721)
        ·
          refine ⟨3017980453434988701542791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4023973937913318268723721 3017980453434988701542791)
          ·
            refine ⟨4526970680152483052314187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3017980453434988701542791 4526970680152483052314187)
            ·
              refine ⟨6790456020228724578471281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4526970680152483052314187 6790456020228724578471281)
              ·
                refine ⟨5092842015171543433853461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6790456020228724578471281 5092842015171543433853461)
                ·
                  refine ⟨238726969461166098461881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5092842015171543433853461 238726969461166098461881)
                  ·
                    rfl

theorem cell20_523034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_523034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523034 prefixEnd_523034 := by exact prefixLift 523034
  have htrace : WordTrace (prefixWord ++ tailWord_523034) baseStart_523034 baseEnd_523034 := by
    simpa [prefixWord, tailWord_523034, baseEnd_523034] using wordTrace_append hprefix tailTrace_523034
  have hstable : (prefixWord ++ tailWord_523034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523034).length < 2 ^ (prefixWord ++ tailWord_523034).sum := by decide
  have hdescent : baseEnd_523034 < baseStart_523034 := by decide
  rcases family_descends (prefixWord ++ tailWord_523034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523037 : List Nat := [1, 4, 2, 4, 1, 1, 7]
def baseStart_523037 : Nat := 118140960795 + 523037 * 2 ^ 59
def prefixEnd_523037 : Nat := 4983230072969 + 3 ^ 40 * 523037 * 2
def baseEnd_523037 : Nat := 26525370971434602373541

theorem tailTrace_523037 : CollatzResearch.WordTrace tailWord_523037 prefixEnd_523037 26525370971434602373541 := by
  unfold tailWord_523037
  simp only [CollatzResearch.WordTrace]
  refine ⟨19076726606133751452975365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12717817737422500968650243 19076726606133751452975365)
  ·
    refine ⟨3576886238650078397432881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19076726606133751452975365 3576886238650078397432881)
    ·
      refine ⟨2682664678987558798074661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3576886238650078397432881 2682664678987558798074661)
      ·
        refine ⟨502999627310167274638999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2682664678987558798074661 502999627310167274638999)
        ·
          refine ⟨754499440965250911958499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502999627310167274638999 754499440965250911958499)
          ·
            refine ⟨1131749161447876367937749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754499440965250911958499 1131749161447876367937749)
            ·
              refine ⟨26525370971434602373541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1131749161447876367937749 26525370971434602373541)
              ·
                rfl

theorem cell20_523037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 7].length) (baseStart_523037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523037 prefixEnd_523037 := by exact prefixLift 523037
  have htrace : WordTrace (prefixWord ++ tailWord_523037) baseStart_523037 baseEnd_523037 := by
    simpa [prefixWord, tailWord_523037, baseEnd_523037] using wordTrace_append hprefix tailTrace_523037
  have hstable : (prefixWord ++ tailWord_523037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523037).length < 2 ^ (prefixWord ++ tailWord_523037).sum := by decide
  have hdescent : baseEnd_523037 < baseStart_523037 := by decide
  rcases family_descends (prefixWord ++ tailWord_523037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523041 : List Nat := [1, 2, 3, 2, 1, 2, 9]
def baseStart_523041 : Nat := 118140960795 + 523041 * 2 ^ 59
def prefixEnd_523041 : Nat := 4983230072969 + 3 ^ 40 * 523041 * 2
def baseEnd_523041 : Nat := 26525573827989465025391

theorem tailTrace_523041 : CollatzResearch.WordTrace tailWord_523041 prefixEnd_523041 26525573827989465025391 := by
  unfold tailWord_523041
  simp only [CollatzResearch.WordTrace]
  refine ⟨19076872498119260136120977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12717914998746173424080651 19076872498119260136120977)
  ·
    refine ⟨14307654373589445102090733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19076872498119260136120977 14307654373589445102090733)
    ·
      refine ⟨5365370390096041913284025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14307654373589445102090733 5365370390096041913284025)
      ·
        refine ⟨4024027792572031434963019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5365370390096041913284025 4024027792572031434963019)
        ·
          refine ⟨6036041688858047152444529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4024027792572031434963019 6036041688858047152444529)
          ·
            refine ⟨4527031266643535364333397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6036041688858047152444529 4527031266643535364333397)
            ·
              refine ⟨26525573827989465025391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4527031266643535364333397 26525573827989465025391)
              ·
                rfl

theorem cell20_523041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 9].length) (baseStart_523041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523041 prefixEnd_523041 := by exact prefixLift 523041
  have htrace : WordTrace (prefixWord ++ tailWord_523041) baseStart_523041 baseEnd_523041 := by
    simpa [prefixWord, tailWord_523041, baseEnd_523041] using wordTrace_append hprefix tailTrace_523041
  have hstable : (prefixWord ++ tailWord_523041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523041).length < 2 ^ (prefixWord ++ tailWord_523041).sum := by decide
  have hdescent : baseEnd_523041 < baseStart_523041 := by decide
  rcases family_descends (prefixWord ++ tailWord_523041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523044 : List Nat := [2, 3, 1, 3, 3, 1, 1, 1, 5]
def baseStart_523044 : Nat := 118140960795 + 523044 * 2 ^ 59
def prefixEnd_523044 : Nat := 4983230072969 + 3 ^ 40 * 523044 * 2
def baseEnd_523044 : Nat := 238731533733650508128507

theorem tailTrace_523044 : CollatzResearch.WordTrace tailWord_523044 prefixEnd_523044 238731533733650508128507 := by
  unfold tailWord_523044
  simp only [CollatzResearch.WordTrace]
  refine ⟨9538490958554195824240093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12717987944738927765653457 9538490958554195824240093)
  ·
    refine ⟨3576934109457823434090035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9538490958554195824240093 3576934109457823434090035)
    ·
      refine ⟨5365401164186735151135053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3576934109457823434090035 5365401164186735151135053)
      ·
        refine ⟨2012025436570025681675645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5365401164186735151135053 2012025436570025681675645)
        ·
          refine ⟨754509538713759630628367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2012025436570025681675645 754509538713759630628367)
          ·
            refine ⟨1131764308070639445942551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754509538713759630628367 1131764308070639445942551)
            ·
              refine ⟨1697646462105959168913827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1131764308070639445942551 1697646462105959168913827)
              ·
                refine ⟨2546469693158938753370741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1697646462105959168913827 2546469693158938753370741)
                ·
                  refine ⟨238731533733650508128507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2546469693158938753370741 238731533733650508128507)
                  ·
                    rfl

theorem cell20_523044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_523044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523044 prefixEnd_523044 := by exact prefixLift 523044
  have htrace : WordTrace (prefixWord ++ tailWord_523044) baseStart_523044 baseEnd_523044 := by
    simpa [prefixWord, tailWord_523044, baseEnd_523044] using wordTrace_append hprefix tailTrace_523044
  have hstable : (prefixWord ++ tailWord_523044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523044).length < 2 ^ (prefixWord ++ tailWord_523044).sum := by decide
  have hdescent : baseEnd_523044 < baseStart_523044 := by decide
  rcases family_descends (prefixWord ++ tailWord_523044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523061 : List Nat := [1, 3, 3, 1, 3, 2, 3, 1, 3]
def baseStart_523061 : Nat := 118140960795 + 523061 * 2 ^ 59
def prefixEnd_523061 : Nat := 4983230072969 + 3 ^ 40 * 523061 * 2
def baseEnd_523061 : Nat := 238739292996874004561771

theorem tailTrace_523061 : CollatzResearch.WordTrace tailWord_523061 prefixEnd_523061 238739292996874004561771 := by
  unfold tailWord_523061
  simp only [CollatzResearch.WordTrace]
  refine ⟨19077601958046803551849037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12718401305364535701232691 19077601958046803551849037)
  ·
    refine ⟨7154100734267551331943389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19077601958046803551849037 7154100734267551331943389)
    ·
      refine ⟨2682787775350331749478771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7154100734267551331943389 2682787775350331749478771)
      ·
        refine ⟨4024181663025497624218157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2682787775350331749478771 4024181663025497624218157)
        ·
          refine ⟨1509068123634561609081809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4024181663025497624218157 1509068123634561609081809)
          ·
            refine ⟨1131801092725921206811357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1509068123634561609081809 1131801092725921206811357)
            ·
              refine ⟨424425409772220452554259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1131801092725921206811357 424425409772220452554259)
              ·
                refine ⟨636638114658330678831389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 424425409772220452554259 636638114658330678831389)
                ·
                  refine ⟨238739292996874004561771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 636638114658330678831389 238739292996874004561771)
                  ·
                    rfl

theorem cell20_523061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 3].length) (baseStart_523061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523061 prefixEnd_523061 := by exact prefixLift 523061
  have htrace : WordTrace (prefixWord ++ tailWord_523061) baseStart_523061 baseEnd_523061 := by
    simpa [prefixWord, tailWord_523061, baseEnd_523061] using wordTrace_append hprefix tailTrace_523061
  have hstable : (prefixWord ++ tailWord_523061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523061).length < 2 ^ (prefixWord ++ tailWord_523061).sum := by decide
  have hdescent : baseEnd_523061 < baseStart_523061 := by decide
  rcases family_descends (prefixWord ++ tailWord_523061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523103 : List Nat := [1, 1, 2, 3, 1, 3, 2, 4, 3]
def baseStart_523103 : Nat := 118140960795 + 523103 * 2 ^ 59
def prefixEnd_523103 : Nat := 4983230072969 + 3 ^ 40 * 523103 * 2
def baseEnd_523103 : Nat := 238758462941308525161599

theorem tailTrace_523103 : CollatzResearch.WordTrace tailWord_523103 prefixEnd_523103 238758462941308525161599 := by
  unfold tailWord_523103
  simp only [CollatzResearch.WordTrace]
  refine ⟨19079133823894644724877963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12719422549263096483251975 19079133823894644724877963)
  ·
    refine ⟨28618700735841967087316945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19079133823894644724877963 28618700735841967087316945)
    ·
      refine ⟨21464025551881475315487709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28618700735841967087316945 21464025551881475315487709)
      ·
        refine ⟨8049009581955553243307891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21464025551881475315487709 8049009581955553243307891)
        ·
          refine ⟨12073514372933329864961837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8049009581955553243307891 12073514372933329864961837)
          ·
            refine ⟨4527567889849998699360689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12073514372933329864961837 4527567889849998699360689)
            ·
              refine ⟨3395675917387499024520517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4527567889849998699360689 3395675917387499024520517)
              ·
                refine ⟨636689234510156067097597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3395675917387499024520517 636689234510156067097597)
                ·
                  refine ⟨238758462941308525161599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 636689234510156067097597 238758462941308525161599)
                  ·
                    rfl

theorem cell20_523103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 3].length) (baseStart_523103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523103 prefixEnd_523103 := by exact prefixLift 523103
  have htrace : WordTrace (prefixWord ++ tailWord_523103) baseStart_523103 baseEnd_523103 := by
    simpa [prefixWord, tailWord_523103, baseEnd_523103] using wordTrace_append hprefix tailTrace_523103
  have hstable : (prefixWord ++ tailWord_523103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523103).length < 2 ^ (prefixWord ++ tailWord_523103).sum := by decide
  have hdescent : baseEnd_523103 < baseStart_523103 := by decide
  rcases family_descends (prefixWord ++ tailWord_523103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523120 : List Nat := [2, 1, 1, 1, 4, 1, 6, 1, 3]
def baseStart_523120 : Nat := 118140960795 + 523120 * 2 ^ 59
def prefixEnd_523120 : Nat := 4983230072969 + 3 ^ 40 * 523120 * 2
def baseEnd_523120 : Nat := 238766222204532021594863

theorem tailTrace_523120 : CollatzResearch.WordTrace tailWord_523120 prefixEnd_523120 238766222204532021594863 := by
  unfold tailWord_523120
  simp only [CollatzResearch.WordTrace]
  refine ⟨9539876932416528314123407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12719835909888704418831209 9539876932416528314123407)
  ·
    refine ⟨14309815398624792471185111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9539876932416528314123407 14309815398624792471185111)
    ·
      refine ⟨21464723097937188706777667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14309815398624792471185111 21464723097937188706777667)
      ·
        refine ⟨32197084646905783060166501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21464723097937188706777667 32197084646905783060166501)
        ·
          refine ⟨6036953371294834323781219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32197084646905783060166501 6036953371294834323781219)
          ·
            refine ⟨9055430056942251485671829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6036953371294834323781219 9055430056942251485671829)
            ·
              refine ⟨424473283919168038390867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9055430056942251485671829 424473283919168038390867)
              ·
                refine ⟨636709925878752057586301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 424473283919168038390867 636709925878752057586301)
                ·
                  refine ⟨238766222204532021594863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 636709925878752057586301 238766222204532021594863)
                  ·
                    rfl

theorem cell20_523120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 3].length) (baseStart_523120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523120 prefixEnd_523120 := by exact prefixLift 523120
  have htrace : WordTrace (prefixWord ++ tailWord_523120) baseStart_523120 baseEnd_523120 := by
    simpa [prefixWord, tailWord_523120, baseEnd_523120] using wordTrace_append hprefix tailTrace_523120
  have hstable : (prefixWord ++ tailWord_523120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523120).length < 2 ^ (prefixWord ++ tailWord_523120).sum := by decide
  have hdescent : baseEnd_523120 < baseStart_523120 := by decide
  rcases family_descends (prefixWord ++ tailWord_523120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523220 : List Nat := [2, 4, 1, 2, 1, 2, 2, 4, 2]
def baseStart_523220 : Nat := 118140960795 + 523220 * 2 ^ 59
def prefixEnd_523220 : Nat := 4983230072969 + 3 ^ 40 * 523220 * 2
def baseEnd_523220 : Nat := 238811864929376118261121

theorem tailTrace_523220 : CollatzResearch.WordTrace tailWord_523220 prefixEnd_523220 238811864929376118261121 := by
  unfold tailWord_523220
  simp only [CollatzResearch.WordTrace]
  refine ⟨9541700582235386853443557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12722267442980515804591409 9541700582235386853443557)
  ·
    refine ⟨1789068859169135035020667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9541700582235386853443557 1789068859169135035020667)
    ·
      refine ⟨2683603288753702552531001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1789068859169135035020667 2683603288753702552531001)
      ·
        refine ⟨2012702466565276914398251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2683603288753702552531001 2012702466565276914398251)
        ·
          refine ⟨3019053699847915371597377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2012702466565276914398251 3019053699847915371597377)
          ·
            refine ⟨2264290274885936528698033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3019053699847915371597377 2264290274885936528698033)
            ·
              refine ⟨1698217706164452396523525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2264290274885936528698033 1698217706164452396523525)
              ·
                refine ⟨318415819905834824348161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1698217706164452396523525 318415819905834824348161)
                ·
                  refine ⟨238811864929376118261121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 318415819905834824348161 238811864929376118261121)
                  ·
                    rfl

theorem cell20_523220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_523220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523220 prefixEnd_523220 := by exact prefixLift 523220
  have htrace : WordTrace (prefixWord ++ tailWord_523220) baseStart_523220 baseEnd_523220 := by
    simpa [prefixWord, tailWord_523220, baseEnd_523220] using wordTrace_append hprefix tailTrace_523220
  have hstable : (prefixWord ++ tailWord_523220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523220).length < 2 ^ (prefixWord ++ tailWord_523220).sum := by decide
  have hdescent : baseEnd_523220 < baseStart_523220 := by decide
  rcases family_descends (prefixWord ++ tailWord_523220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523224 : List Nat := [2, 1, 2, 2, 2, 3, 1, 3, 4]
def baseStart_523224 : Nat := 118140960795 + 523224 * 2 ^ 59
def prefixEnd_523224 : Nat := 4983230072969 + 3 ^ 40 * 523224 * 2
def baseEnd_523224 : Nat := 238813690638369882127771

theorem tailTrace_523224 : CollatzResearch.WordTrace tailWord_523224 prefixEnd_523224 238813690638369882127771 := by
  unfold tailWord_523224
  simp only [CollatzResearch.WordTrace]
  refine ⟨9541773528228141195016363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12722364704304188260021817 9541773528228141195016363)
  ·
    refine ⟨14312660292342211792524545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9541773528228141195016363 14312660292342211792524545)
    ·
      refine ⟨10734495219256658844393409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14312660292342211792524545 10734495219256658844393409)
      ·
        refine ⟨8050871414442494133295057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10734495219256658844393409 8050871414442494133295057)
        ·
          refine ⟨6038153560831870599971293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8050871414442494133295057 6038153560831870599971293)
          ·
            refine ⟨2264307585311951474989235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6038153560831870599971293 2264307585311951474989235)
            ·
              refine ⟨3396461377967927212483853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2264307585311951474989235 3396461377967927212483853)
              ·
                refine ⟨1273673016737972704681445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3396461377967927212483853 1273673016737972704681445)
                ·
                  refine ⟨238813690638369882127771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1273673016737972704681445 238813690638369882127771)
                  ·
                    rfl

theorem cell20_523224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_523224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523224 prefixEnd_523224 := by exact prefixLift 523224
  have htrace : WordTrace (prefixWord ++ tailWord_523224) baseStart_523224 baseEnd_523224 := by
    simpa [prefixWord, tailWord_523224, baseEnd_523224] using wordTrace_append hprefix tailTrace_523224
  have hstable : (prefixWord ++ tailWord_523224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523224).length < 2 ^ (prefixWord ++ tailWord_523224).sum := by decide
  have hdescent : baseEnd_523224 < baseStart_523224 := by decide
  rcases family_descends (prefixWord ++ tailWord_523224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523317 : List Nat := [1, 3, 3, 1, 1, 1, 1, 7, 2]
def baseStart_523317 : Nat := 118140960795 + 523317 * 2 ^ 59
def prefixEnd_523317 : Nat := 4983230072969 + 3 ^ 40 * 523317 * 2
def baseEnd_523317 : Nat := 238856138372474892027391

theorem tailTrace_523317 : CollatzResearch.WordTrace tailWord_523317 prefixEnd_523317 238856138372474892027391 := by
  unfold tailWord_523317
  simp only [CollatzResearch.WordTrace]
  refine ⟨19086939045119359273168205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12724626030079572848778803 19086939045119359273168205)
  ·
    refine ⟨7157602141919759727438077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19086939045119359273168205 7157602141919759727438077)
    ·
      refine ⟨2684100803219909897789279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7157602141919759727438077 2684100803219909897789279)
      ·
        refine ⟨4026151204829864846683919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2684100803219909897789279 4026151204829864846683919)
        ·
          refine ⟨6039226807244797270025879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4026151204829864846683919 6039226807244797270025879)
          ·
            refine ⟨9058840210867195905038819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6039226807244797270025879 9058840210867195905038819)
            ·
              refine ⟨13588260316300793857558229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9058840210867195905038819 13588260316300793857558229)
              ·
                refine ⟨318474851163299856036521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 13588260316300793857558229 318474851163299856036521)
                ·
                  refine ⟨238856138372474892027391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 318474851163299856036521 238856138372474892027391)
                  ·
                    rfl

theorem cell20_523317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 7, 2].length) (baseStart_523317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523317 prefixEnd_523317 := by exact prefixLift 523317
  have htrace : WordTrace (prefixWord ++ tailWord_523317) baseStart_523317 baseEnd_523317 := by
    simpa [prefixWord, tailWord_523317, baseEnd_523317] using wordTrace_append hprefix tailTrace_523317
  have hstable : (prefixWord ++ tailWord_523317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523317).length < 2 ^ (prefixWord ++ tailWord_523317).sum := by decide
  have hdescent : baseEnd_523317 < baseStart_523317 := by decide
  rcases family_descends (prefixWord ++ tailWord_523317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523331 : List Nat := [1, 1, 1, 3, 1, 2, 6, 2, 3]
def baseStart_523331 : Nat := 118140960795 + 523331 * 2 ^ 59
def prefixEnd_523331 : Nat := 4983230072969 + 3 ^ 40 * 523331 * 2
def baseEnd_523331 : Nat := 238862528353953065560667

theorem tailTrace_523331 : CollatzResearch.WordTrace tailWord_523331 prefixEnd_523331 238862528353953065560667 := by
  unfold tailWord_523331
  simp only [CollatzResearch.WordTrace]
  refine ⟨19087449667068639664177847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12724966444712426442785231 19087449667068639664177847)
  ·
    refine ⟨28631174500602959496266771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19087449667068639664177847 28631174500602959496266771)
    ·
      refine ⟨42946761750904439244400157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28631174500602959496266771 42946761750904439244400157)
      ·
        refine ⟨16105035656589164716650059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42946761750904439244400157 16105035656589164716650059)
        ·
          refine ⟨24157553484883747074975089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16105035656589164716650059 24157553484883747074975089)
          ·
            refine ⟨18118165113662810306231317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24157553484883747074975089 18118165113662810306231317)
            ·
              refine ⟨849288989702944233104593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18118165113662810306231317 849288989702944233104593)
              ·
                refine ⟨636966742277208174828445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 849288989702944233104593 636966742277208174828445)
                ·
                  refine ⟨238862528353953065560667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 636966742277208174828445 238862528353953065560667)
                  ·
                    rfl

theorem cell20_523331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 3].length) (baseStart_523331 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523331 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523331 prefixEnd_523331 := by exact prefixLift 523331
  have htrace : WordTrace (prefixWord ++ tailWord_523331) baseStart_523331 baseEnd_523331 := by
    simpa [prefixWord, tailWord_523331, baseEnd_523331] using wordTrace_append hprefix tailTrace_523331
  have hstable : (prefixWord ++ tailWord_523331).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523331).length < 2 ^ (prefixWord ++ tailWord_523331).sum := by decide
  have hdescent : baseEnd_523331 < baseStart_523331 := by decide
  rcases family_descends (prefixWord ++ tailWord_523331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523341 : List Nat := [1, 6, 1, 1, 1, 4, 1, 5]
def baseStart_523341 : Nat := 118140960795 + 523341 * 2 ^ 59
def prefixEnd_523341 : Nat := 4983230072969 + 3 ^ 40 * 523341 * 2
def baseEnd_523341 : Nat := 79622364208812491742431

theorem tailTrace_523341 : CollatzResearch.WordTrace tailWord_523341 prefixEnd_523341 79622364208812491742431 := by
  unfold tailWord_523341
  simp only [CollatzResearch.WordTrace]
  refine ⟨19087814397032411372041877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12725209598021607581361251 19087814397032411372041877)
  ·
    refine ⟨894741299860894283064463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19087814397032411372041877 894741299860894283064463)
    ·
      refine ⟨1342111949791341424596695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 894741299860894283064463 1342111949791341424596695)
      ·
        refine ⟨2013167924687012136895043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1342111949791341424596695 2013167924687012136895043)
        ·
          refine ⟨3019751887030518205342565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2013167924687012136895043 3019751887030518205342565)
          ·
            refine ⟨566203478818222163501731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3019751887030518205342565 566203478818222163501731)
            ·
              refine ⟨849305218227333245252597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 566203478818222163501731 849305218227333245252597)
              ·
                refine ⟨79622364208812491742431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 849305218227333245252597 79622364208812491742431)
                ·
                  rfl

theorem cell20_523341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 5].length) (baseStart_523341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523341 prefixEnd_523341 := by exact prefixLift 523341
  have htrace : WordTrace (prefixWord ++ tailWord_523341) baseStart_523341 baseEnd_523341 := by
    simpa [prefixWord, tailWord_523341, baseEnd_523341] using wordTrace_append hprefix tailTrace_523341
  have hstable : (prefixWord ++ tailWord_523341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523341).length < 2 ^ (prefixWord ++ tailWord_523341).sum := by decide
  have hdescent : baseEnd_523341 < baseStart_523341 := by decide
  rcases family_descends (prefixWord ++ tailWord_523341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_523345 : List Nat := [1, 2, 2, 1, 3, 1, 5, 5]
def baseStart_523345 : Nat := 118140960795 + 523345 * 2 ^ 59
def prefixEnd_523345 : Nat := 4983230072969 + 3 ^ 40 * 523345 * 2
def baseEnd_523345 : Nat := 79622972778477079697981

theorem tailTrace_523345 : CollatzResearch.WordTrace tailWord_523345 prefixEnd_523345 79622972778477079697981 := by
  unfold tailWord_523345
  simp only [CollatzResearch.WordTrace]
  refine ⟨19087960289017920055187489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12725306859345280036791659 19087960289017920055187489)
  ·
    refine ⟨14315970216763440041390617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19087960289017920055187489 14315970216763440041390617)
    ·
      refine ⟨10736977662572580031042963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14315970216763440041390617 10736977662572580031042963)
      ·
        refine ⟨16105466493858870046564445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10736977662572580031042963 16105466493858870046564445)
        ·
          refine ⟨6039549935197076267461667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16105466493858870046564445 6039549935197076267461667)
          ·
            refine ⟨9059324902795614401192501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6039549935197076267461667 9059324902795614401192501)
            ·
              refine ⟨849311709637088850111797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9059324902795614401192501 849311709637088850111797)
              ·
                refine ⟨79622972778477079697981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 849311709637088850111797 79622972778477079697981)
                ·
                  rfl

theorem cell20_523345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 5].length) (baseStart_523345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_523345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_523345 prefixEnd_523345 := by exact prefixLift 523345
  have htrace : WordTrace (prefixWord ++ tailWord_523345) baseStart_523345 baseEnd_523345 := by
    simpa [prefixWord, tailWord_523345, baseEnd_523345] using wordTrace_append hprefix tailTrace_523345
  have hstable : (prefixWord ++ tailWord_523345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_523345).length < 2 ^ (prefixWord ++ tailWord_523345).sum := by decide
  have hdescent : baseEnd_523345 < baseStart_523345 := by decide
  rcases family_descends (prefixWord ++ tailWord_523345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
